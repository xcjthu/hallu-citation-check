# 幻觉引用检测工具 (Citation Hallucination Checker)

逐条核对 LaTeX `.bib` 文件中的参考文献，自动发现 **AI 生成 / 手写引用里常见的"幻觉"**：
不存在的 arXiv 编号、对不上的 DOI、被编造或写错的作者、错误的年份、指向另一篇论文的标识符等。

- **纯 Python 标准库**，无需 `pip install`，无需 API key。
- **信源以 DBLP 为主**，并联合 arXiv / Crossref / OpenReview 做权威核对，外加 URL 存活性检查。
- 输出**可筛选、可搜索的 HTML 报告**（默认）和可选的 JSON。

---

## 安装

无需安装依赖，只要有 Python 3.8+：

```bash
python3 --version   # 3.8 或更高
```

把 `check_citations.py` 放到任意目录即可运行。

---

## 快速开始

```bash
# 检查一个 bib 文件，生成 report.html（默认）
python3 check_citations.py example-bib.bib
```

跑完后：
- 终端会**逐条**打印结果（带颜色、带进度 `[12/70]`）；
- 当前目录生成 **`report.html`** —— 用浏览器打开即可（macOS 可 `open report.html`）。

---

## 命令行用法

```
python3 check_citations.py <bibfile> [选项]
```

| 选项 | 说明 |
|------|------|
| `<bibfile>` | 必填，待检查的 `.bib` 文件路径 |
| `--html FILE` | 写出 HTML 报告，默认 `report.html`；传 `--html ''` 可跳过 |
| `--json FILE` | 额外写出一份机器可读的 JSON 报告 |
| `--only KEY [KEY ...]` | 只检查指定的 cite key（调试 / 复查单条时用） |
| `--delay 秒` | 每次网络请求之间的间隔，默认 `0.8`（对 DBLP/arXiv 礼貌一点） |
| `--no-cache` | 不读写本地缓存，强制全部重新联网核对 |
| `--verbose` | 打印每一次 HTTP 请求（排查网络问题用） |

### 常用示例

```bash
# 同时导出 JSON
python3 check_citations.py refs.bib --json report.json

# 只复查某几条
python3 check_citations.py refs.bib --only shao2024deepseekmath vodrahalli2024mrcr

# 网络不稳 / 被限流时，放慢请求
python3 check_citations.py refs.bib --delay 1.5

# 指定报告输出位置
python3 check_citations.py refs.bib --html out/report.html --json out/report.json
```

### 退出码（方便接入 CI）

- 退出码 `1`：存在 **SUSPECT（疑似幻觉）** 条目；
- 退出码 `0`：没有 SUSPECT。

```bash
python3 check_citations.py refs.bib --html '' || echo "发现疑似幻觉引用！"
```

---

## 检测逻辑

对每一条引用，工具会提取 **标题、作者、年份** 以及任何唯一标识（arXiv id / DOI / OpenReview id / URL），
然后按条目类型选择权威信源核对：

| 标识 / 类型 | 使用的信源 | 核对内容 |
|------------|-----------|---------|
| `arXiv:XXXX.XXXXX` | **arXiv API** | 编号是否真实存在、标题/作者是否吻合 |
| `doi = {...}` | **Crossref** | DOI 能否解析、标题/作者/年份/venue |
| `openreview.net?id=` | **OpenReview API** | 真实发表会议 + 年份（ICLR/NeurIPS/COLM…） |
| 已发表论文（通用） | **DBLP**（主信源） | 标题/作者/年份/venue 交叉核对 |
| `@misc` / `@software`（博客、模型卡、仓库） | **URL 存活性** | 链接是否可达（无法用学术库验证） |

几个关键设计：
- **年份以"发表年优先"**：会议论文的引用年份通常比 arXiv 预印本晚一年，这种 1 年差是**正常**的，不会误报。
- **标识符指向另一篇论文** = 强幻觉信号（例如 arXiv 编号存在，但对应的是完全不同的标题）。
- **作者部分编造**会被识别：哪怕第一作者对得上，只要多个署名不在真实作者列表里，就会告警。
- **机构 / 团队署名**（如 `{{OpenAI}}`、`{{Qwen Team}}`）自动跳过逐人核对，不会误判。

---

## 报告怎么看

### 判定等级

| 图标 | 等级 | 含义 |
|------|------|------|
| ❌ | **SUSPECT** | 疑似幻觉：标识符不存在 / 解析失败，或标题完全对不上 |
| ⚠️ | **WARNING** | 明显不符：作者列表对不上、仓库 404 等，需人工核对 |
| 🟡 | **MINOR** | 小差异：个别作者对不上、轻微年份差等 |
| ℹ️ | **UNVERIFIABLE** | 无学术信源可验证（博客 / 模型卡 / 代码仓库），仅检查了链接可达性 |
| ✅ | **OK** | 标题、作者、年份均已核对一致 |

### HTML 报告特性

- 顶部按等级**一键筛选**（All / SUSPECT / WARNING / …），并可按 key/标题**搜索**；
- 卡片按"最该关注的在最上面"排序；
- 每条展示可点击的 **arXiv / DOI / OpenReview** 链接和**匹配到的真实记录**（含真实 venue）；
- **作者对不上时**会并排显示「你写的」vs「权威来源」两栏，把**对不上的名字标红 + ✗**，一眼看出差异。

---

## 缓存

为加快重复运行，工具会把联网结果缓存在当前目录的 **`.citecheck_cache.json`**。
- 改完 bib 想重查 → 直接再跑即可（已查过的条目秒出）；
- 想强制全部重新联网 → 加 `--no-cache`，或删掉该缓存文件。

---

## 常见问题

**Q：某条显示 UNVERIFIABLE，是不是引用有问题？**
不一定。博客、模型卡、GitHub 仓库这类来源**本就无法用学术数据库核对**，工具只能检查链接是否可达。需要你自己判断该来源是否可靠。

**Q：某个 URL 显示"could not reach"（无法访问）？**
通常是对方网站的反爬（如 Cloudflare）挡住了脚本请求，**不代表链接失效**。这种情况会标为 UNVERIFIABLE（ℹ️）而非 WARNING，请用浏览器手动确认。只有服务器明确返回 **404 / 410** 才会判为 WARNING（资源不存在）。

**Q：DBLP 偶尔查不到？**
DBLP 有访问频率限制。被限流时工具会自动回退到 arXiv 等其它信源，结果仍然可靠；如频繁出现可加大 `--delay`。

**Q：年份提示"off by 1"会算错吗？**
不会判为错误。预印本与正式发表常差一年，工具默认接受这种差异（仅在能确认会议年份时做精确比对）。

---

## 工作原理一句话

> 把每条引用拆成"标题 / 作者 / 年份 / 唯一标识"，分别去 DBLP、arXiv、Crossref、OpenReview 上找真身，
> 比对不上的地方就是潜在的幻觉 —— 并在 HTML 里把差异直接标给你看。
