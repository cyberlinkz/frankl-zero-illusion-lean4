"""
build_pdf.py - Publication-Grade Academic PDF Generator for Frankl Lab
Milestone 40: High-fidelity typesetting of Frankl_Zero_Illusion_Preprint.pdf
"""

import os
import re
import sys
import shutil
import http.server
import threading
import socket
from pathlib import Path

def find_free_port():
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(('127.0.0.1', 0))
        return s.getsockname()[1]

def markdown_to_academic_html(md_text: str) -> str:
    """
    Converts PAPER_ENGLISH.md to publication-grade academic HTML
    with full MathJax 3 support, booktabs tables, theorem callouts,
    and LaTeX-identical typography.
    """
    # Step 1: Protect math blocks from markdown processing
    disp_math = []
    def _save_disp(m):
        disp_math.append(m.group(0))
        return f"XQMATHDISP{len(disp_math) - 1}Z"
    
    # Match $$ ... $$ across multiple lines
    text = re.sub(r'\$\$(.*?)\$\$', _save_disp, md_text, flags=re.DOTALL)
    
    inl_math = []
    def _save_inl(m):
        inl_math.append(m.group(0))
        return f"XQMATHINL{len(inl_math) - 1}Z"
    
    # Match $ ... $ inline (excluding escaped \$, and not spanning empty lines)
    text = re.sub(r'(?<!\\)\$(.*?)(?<!\\)\$', _save_inl, text)

    # Step 2: Extract Title, Author metadata block
    lines = text.split('\n')
    title = ""
    author_info = []
    abstract_lines = []
    body_lines = []
    
    state = "TITLE"
    i = 0
    while i < len(lines):
        line = lines[i]
        if state == "TITLE":
            if line.startswith("# "):
                title = line[2:].strip()
                state = "METADATA"
            i += 1
        elif state == "METADATA":
            if line.startswith("## Abstract"):
                state = "ABSTRACT"
                i += 1
            elif line.strip() == "---":
                i += 1
            else:
                if line.strip():
                    author_info.append(line.strip())
                i += 1
        elif state == "ABSTRACT":
            if line.strip() == "---":
                state = "BODY"
                i += 1
            else:
                abstract_lines.append(line)
                i += 1
        else: # BODY
            body_lines.append(line)
            i += 1
            
    abstract_text = "\n".join(abstract_lines).strip()
    body_text = "\n".join(body_lines).strip()

    # Step 3: Parse markdown tables to HTML with academic booktabs style
    def convert_tables(txt: str) -> str:
        lines = txt.split('\n')
        out = []
        in_table = False
        table_rows = []

        def flush_table():
            nonlocal table_rows
            if not table_rows:
                return ""
            html_rows = []
            is_header = True
            for r in table_rows:
                # check if separator row like |:---|:---|
                if re.match(r'^\s*\|?\s*[-:]+[-| :]+[-:]+\s*\|?\s*$', r):
                    is_header = False
                    continue
                cells = [c.strip() for c in r.strip().strip('|').split('|')]
                tag = 'th' if is_header else 'td'
                cell_html = "".join([f"<{tag}>{c}</{tag}>" for c in cells])
                html_rows.append(f"<tr>{cell_html}</tr>")
            table_rows = []
            return '<div class="academic-table-container"><table class="academic-table">\n' + "\n".join(html_rows) + '\n</table></div>'

        for line in lines:
            if line.strip().startswith('|') and '|' in line.strip()[1:]:
                table_rows.append(line)
                in_table = True
            else:
                if in_table:
                    out.append(flush_table())
                    in_table = False
                out.append(line)
        if in_table:
            out.append(flush_table())
        return "\n".join(out)

    body_text = convert_tables(body_text)

    # Step 4: Parse headers, theorems, definitions, proofs
    import markdown_it
    md = markdown_it.MarkdownIt("commonmark", {"html": True}).enable("table")
    raw_html = md.render(body_text)

    # Step 5: Post-process HTML for Theorem, Definition, Lemma, Proof, Remark boxes
    # Wrap Definition, Theorem, Lemma, Corollary, Proposition in styled divs
    def style_theorems(html_str: str) -> str:
        # Match <h3>Definition ...</h3>, <h3>Theorem ...</h3>, etc.
        pattern = r'(<h3>(Definition|Theorem|Lemma|Corollary|Proposition|Remark)\s+([^<]+)</h3>\s*<p>(.*?)</p>)'
        
        def _replace_thm(m):
            kind = m.group(2)
            number_title = m.group(3).strip()
            content = m.group(4).strip()
            box_class = "theorem-box"
            badge_class = kind.lower()
            return f'''<div class="{box_class} {badge_class}">
<div class="thm-header"><span class="thm-kind">{kind} {number_title}</span></div>
<div class="thm-body">{content}</div>
</div>'''
        
        return re.sub(pattern, _replace_thm, html_str, flags=re.DOTALL)

    raw_html = style_theorems(raw_html)

    # Style Proof sections
    raw_html = re.sub(r'<p><strong>Proof\.?</strong>\s*(.*?)</p>', 
                      r'<div class="proof-block"><span class="proof-label">Proof.</span> \1</div>', 
                      raw_html, flags=re.DOTALL)

    # Step 6: Restore math expressions in body and abstract
    for idx, math_str in enumerate(disp_math):
        raw_html = raw_html.replace(f"XQMATHDISP{idx}Z", math_str)
    for idx, math_str in enumerate(inl_math):
        raw_html = raw_html.replace(f"XQMATHINL{idx}Z", math_str)

    # Render and restore math in abstract
    abstract_html = md.render(abstract_text)
    for idx, math_str in enumerate(disp_math):
        abstract_html = abstract_html.replace(f"XQMATHDISP{idx}Z", math_str)
    for idx, math_str in enumerate(inl_math):
        abstract_html = abstract_html.replace(f"XQMATHINL{idx}Z", math_str)

    # Step 7: Build Author Header
    author_html_parts = []
    for line in author_info:
        clean = line.replace('**', '').replace('*', '').replace('`', '').strip()
        if '@' in clean:
            author_html_parts.append(f'<div class="author-email"><code>{clean}</code></div>')
        elif 'Baku' in clean or 'Azerbaijan' in clean or 'Investigator' in clean or 'Researcher' in clean:
            author_html_parts.append(f'<div class="author-affil">{clean}</div>')
        elif 'October' in clean or '2026' in clean:
            author_html_parts.append(f'<div class="paper-date">{clean}</div>')
        else:
            author_html_parts.append(f'<div class="author-name">{clean}</div>')
    authors_block = "\n".join(author_html_parts)

    full_html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{title}</title>

<!-- MathJax 3 configuration -->
<script>
window.MathJax = {{
  tex: {{
    inlineMath: [['$', '$'], ['\\\\(', '\\\\)']],
    displayMath: [['$$', '$$'], ['\\\\[', '\\\\]']],
    processEscapes: true,
    processEnvironments: true,
    packages: {{'[+]': ['ams', 'base', 'autoload']}}
  }},
  options: {{
    skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code']
  }},
  startup: {{
    pageReady: () => {{
      return MathJax.startup.defaultPageReady().then(() => {{
        console.log('MathJax typesetting finished successfully.');
        document.body.setAttribute('data-mathjax-ready', 'true');
      }});
    }}
  }}
}};
</script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>

<style>
@import url('https://fonts.googleapis.com/css2?family=Libertinus+Serif:ital,wght@0,400;0,600;0,700;1,400;1,600&family=JetBrains+Mono:wght@400;600&display=swap');

@page {{
  size: letter;
  margin: 22mm 20mm 22mm 20mm;
}}

*, *:before, *:after {{
  box-sizing: border-box;
}}

body {{
  font-family: 'Libertinus Serif', 'Times New Roman', Times, 'TeX Gyre Termes', Georgia, serif;
  font-size: 10.2pt;
  line-height: 1.48;
  color: #111111;
  text-align: justify;
  text-justify: inter-word;
  background-color: #ffffff;
  margin: 0;
  padding: 0;
}}

/* Title and Metadata */
.header-container {{
  text-align: center;
  margin-bottom: 22pt;
  padding-bottom: 14pt;
  border-bottom: 1.5px solid #2b4c7e;
}}

h1.paper-title {{
  font-size: 17pt;
  font-weight: 700;
  line-height: 1.25;
  color: #1a2a44;
  margin: 0 0 14pt 0;
  letter-spacing: -0.01em;
}}

.author-name {{
  font-size: 12pt;
  font-weight: 700;
  color: #222222;
  margin-bottom: 2pt;
}}

.author-affil {{
  font-size: 9.5pt;
  font-style: italic;
  color: #444444;
  line-height: 1.35;
}}

.author-email {{
  font-size: 9pt;
  margin-top: 3pt;
  color: #2b4c7e;
}}

.author-email code {{
  background: #f0f4f9;
  padding: 1px 5px;
  border-radius: 3px;
  font-family: 'JetBrains Mono', monospace;
}}

.paper-date {{
  font-size: 9.5pt;
  font-weight: 600;
  color: #555555;
  margin-top: 6pt;
}}

/* Abstract Box */
.abstract-container {{
  margin: 0 16pt 20pt 16pt;
  padding: 12pt 16pt;
  background-color: #f9fafc;
  border-left: 3px solid #2b4c7e;
  border-right: 1px solid #e2e8f0;
  border-top: 1px solid #e2e8f0;
  border-bottom: 1px solid #e2e8f0;
  border-radius: 4px;
}}

.abstract-title {{
  text-align: center;
  font-size: 11pt;
  font-weight: 700;
  text-transform: uppercase;
  letter-spacing: 0.08em;
  color: #1a2a44;
  margin-bottom: 8pt;
}}

.abstract-content {{
  font-size: 9.5pt;
  line-height: 1.44;
  color: #222222;
}}

.abstract-content p {{
  margin: 0 0 6pt 0;
}}

.abstract-content ol, .abstract-content ul {{
  margin: 4pt 0 6pt 16pt;
  padding: 0;
}}

.abstract-content li {{
  margin-bottom: 3pt;
}}

/* Section Headings */
h2 {{
  font-size: 12.5pt;
  font-weight: 700;
  color: #1a2a44;
  border-bottom: 0.8px solid #cbd5e1;
  padding-bottom: 3pt;
  margin: 18pt 0 8pt 0;
  break-after: avoid;
  page-break-after: avoid;
}}

h3 {{
  font-size: 10.8pt;
  font-weight: 700;
  color: #2b4c7e;
  margin: 14pt 0 6pt 0;
  break-after: avoid;
  page-break-after: avoid;
}}

h4 {{
  font-size: 10.2pt;
  font-weight: 700;
  color: #334155;
  margin: 10pt 0 4pt 0;
  break-after: avoid;
  page-break-after: avoid;
}}

p {{
  margin: 0 0 8pt 0;
  text-indent: 0;
}}

/* Theorem, Lemma, Definition, Remark Callout Boxes */
.theorem-box {{
  margin: 12pt 0;
  padding: 9pt 13pt;
  border-radius: 4px;
  background-color: #f8fafc;
  border-left: 3.5px solid #2b4c7e;
  border-top: 1px solid #edf2f7;
  border-right: 1px solid #edf2f7;
  border-bottom: 1px solid #edf2f7;
  break-inside: avoid-page;
  page-break-inside: avoid;
}}

.theorem-box.definition {{
  border-left-color: #0d9488;
  background-color: #f0fdfa;
}}

.theorem-box.lemma {{
  border-left-color: #4f46e5;
  background-color: #f5f3ff;
}}

.theorem-box.remark {{
  border-left-color: #ca8a04;
  background-color: #fefce8;
}}

.thm-header {{
  font-weight: 700;
  color: #0f172a;
  margin-bottom: 4pt;
}}

.thm-kind {{
  font-style: normal;
  font-weight: 700;
}}

.thm-body {{
  font-style: italic;
  color: #1e293b;
  line-height: 1.45;
}}

.thm-body mjx-container {{
  font-style: normal;
}}

/* Proof Block */
.proof-block {{
  margin: 6pt 0 12pt 0;
  padding-left: 4pt;
  color: #1f2937;
  line-height: 1.45;
}}

.proof-label {{
  font-style: italic;
  font-weight: 700;
  color: #0f172a;
}}

/* Blockquotes */
blockquote {{
  margin: 10pt 14pt;
  padding: 8pt 14pt;
  background-color: #f1f5f9;
  border-left: 3.5px solid #475569;
  font-style: italic;
  border-radius: 2px;
}}

/* Tables - Academic Booktabs Style */
.academic-table-container {{
  margin: 14pt auto;
  text-align: center;
  break-inside: avoid-page;
  page-break-inside: avoid;
}}

table.academic-table {{
  margin: 0 auto;
  border-collapse: collapse;
  font-size: 8.8pt;
  line-height: 1.35;
  width: 95%;
  border-top: 1.8px solid #0f172a;
  border-bottom: 1.8px solid #0f172a;
}}

table.academic-table th {{
  border-bottom: 1.2px solid #0f172a;
  padding: 5pt 7pt;
  font-weight: 700;
  background-color: #f8fafc;
  color: #0f172a;
}}

table.academic-table td {{
  padding: 4.5pt 7pt;
  border-bottom: 0.5px solid #e2e8f0;
  color: #1e293b;
}}

table.academic-table tr:last-child td {{
  border-bottom: none;
}}

/* Code Blocks */
pre {{
  background-color: #f8fafc;
  border: 1px solid #e2e8f0;
  border-left: 3px solid #64748b;
  padding: 8pt 11pt;
  font-family: 'JetBrains Mono', Consolas, monospace;
  font-size: 8.2pt;
  line-height: 1.38;
  color: #0f172a;
  border-radius: 3px;
  overflow-x: auto;
  margin: 10pt 0;
  break-inside: avoid-page;
  page-break-inside: avoid;
}}

code {{
  font-family: 'JetBrains Mono', Consolas, monospace;
  font-size: 8.8pt;
  background-color: #f1f5f9;
  padding: 1px 4pt;
  border-radius: 2px;
}}

/* Lists */
ul, ol {{
  margin: 6pt 0 8pt 18pt;
  padding: 0;
}}

li {{
  margin-bottom: 3pt;
}}

/* Footnotes & References */
ol li {{
  line-height: 1.4;
}}

/* MathJax Sizing Adjustments */
mjx-container[jax="CHTML"][display="true"] {{
  margin: 8pt 0 !important;
}}
</style>
</head>
<body>

<div class="header-container">
  <h1 class="paper-title">{title}</h1>
  {authors_block}
</div>

<div class="abstract-container">
  <div class="abstract-title">Abstract</div>
  <div class="abstract-content">
    {abstract_html}
  </div>
</div>

<div class="paper-body">
{raw_html}
</div>

</body>
</html>
"""
    return full_html


def run_html_server_and_compile_pdf(html_content: str, output_pdf: Path) -> int:
    """
    Serves the academic HTML locally and drives headless Chrome via Playwright
    to produce a publication-grade PDF with vector MathJax equations.
    """
    from playwright.sync_api import sync_playwright

    port = find_free_port()
    html_bytes = html_content.encode('utf-8')

    class LocalHandler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(html_bytes)))
            self.end_headers()
            self.wfile.write(html_bytes)
        def log_message(self, format, *args):
            pass

    httpd = http.server.HTTPServer(('127.0.0.1', port), LocalHandler)
    server_thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    server_thread.start()

    chrome_candidates = [
        r"C:\Program Files\Google\Chrome\Application\chrome.exe",
        r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
        r"C:\Program Files\Microsoft\Edge\Application\msedge.exe"
    ]
    exec_path = None
    for p in chrome_candidates:
        if os.path.exists(p):
            exec_path = p
            break
            
    if not exec_path:
        raise RuntimeError("No Chrome or Edge browser executable found on system!")

    print(f"[*] Launching headless browser: {exec_path}")
    print(f"[*] Serving preprint HTML at http://127.0.0.1:{port}/")

    with sync_playwright() as p:
        browser = p.chromium.launch(executable_path=exec_path, headless=True)
        context = browser.new_context(
            viewport={'width': 1200, 'height': 1600},
            device_scale_factor=2
        )
        page = context.new_page()

        # Listen to console logs
        page.on("console", lambda msg: print(f"  [Browser Console] {msg.text}"))

        page.goto(f"http://127.0.0.1:{port}/", wait_until="networkidle", timeout=60000)

        # Wait for MathJax typesetting completion flag
        print("[*] Waiting for MathJax 3 to typeset all mathematical formulas...")
        try:
            page.wait_for_selector('body[data-mathjax-ready="true"]', timeout=45000)
            print("[+] MathJax typesetting confirmed ready!")
        except Exception as e:
            print(f"[!] Warning: MathJax readiness timeout: {e}. Checking containers...")

        # Count math elements
        math_count = len(page.query_selector_all('mjx-container'))
        print(f"[+] Total rendered MathJax math containers in DOM: {math_count}")

        header_template = """
        <div style="font-family: 'Times New Roman', serif; font-size: 8pt; color: #555555; width: 100%; display: flex; justify-content: space-between; padding: 0 20mm; margin: 0 auto; border-bottom: 0.5px solid #d0d7de;">
            <span>Quotient-Fiber Stratification for Frankl's Conjecture</span>
            <span>Ahmad Hasanov (Frankl Lab, October 2026)</span>
        </div>
        """

        footer_template = """
        <div style="font-family: 'Times New Roman', serif; font-size: 8.5pt; color: #444444; width: 100%; text-align: center; margin: 0 auto;">
            Page <span class="pageNumber"></span> of <span class="totalPages"></span>
        </div>
        """

        print(f"[*] Printing publication-grade PDF to {output_pdf}...")
        page.pdf(
            path=str(output_pdf),
            format="Letter",
            print_background=True,
            display_header_footer=True,
            header_template=header_template,
            footer_template=footer_template,
            margin={
                "top": "24mm",
                "bottom": "22mm",
                "left": "20mm",
                "right": "20mm"
            }
        )
        browser.close()

    httpd.shutdown()
    print("[+] PDF rendering completed successfully.")
    return math_count


def verify_generated_pdf(pdf_path: Path):
    """
    Exhaustively verifies that the generated PDF conforms to publication standards:
    - Exists on disk
    - Size > 100 KB
    - Starts with %PDF- header
    - Multi-page document with valid text content
    """
    import pypdf

    assert pdf_path.exists(), f"File does not exist: {pdf_path}"
    file_size = pdf_path.stat().st_size
    assert file_size > 100 * 1024, f"File size {file_size} bytes is below 100 KB threshold!"

    with open(pdf_path, 'rb') as f:
        header = f.read(5)
        assert header == b'%PDF-', f"File does not start with %PDF- header! Found: {header}"

    reader = pypdf.PdfReader(str(pdf_path))
    num_pages = len(reader.pages)
    assert num_pages >= 10, f"Expected multi-page paper (>=10 pages), got {num_pages} pages!"

    # Extract sample text and verify core sections
    full_text = ""
    for idx, page in enumerate(reader.pages):
        full_text += f"\n--- PAGE {idx+1} ---\n" + page.extract_text()

    required_keywords = [
        "Quotient-Fiber Stratification",
        "Ahmad Hasanov",
        "akhmad.hasanov@gmail.com",
        "Poonen local obstruction",
        "Universal Top-Fiber Absorption",
        "Strict Quotient Compression",
        "Rényi-2",
        "Refined Fiber-Base Balance",
        "Master Structural Resolution",
        "Lean 4",
        "References"
    ]

    for kw in required_keywords:
        assert kw in full_text or kw.replace("\u00e9", "e") in full_text, f"Missing required keyword: {kw}"

    print(f"\n=======================================================")
    print(f"PDF VERIFICATION SUMMARY FOR: {pdf_path.name}")
    print(f"=======================================================")
    print(f"Path: {pdf_path.resolve()}")
    print(f"File Size: {file_size:,} bytes ({file_size / 1024:.2f} KB)")
    print(f"Page Count: {num_pages} pages")
    print(f"PDF Header: %PDF- verified valid")
    print(f"Keyword Integrity: All core academic sections present")
    print(f"=======================================================\n")
    return num_pages, file_size


def main():
    paper_dir = Path(__file__).resolve().parent
    md_file = paper_dir / "PAPER_ENGLISH.md"
    target_pdf = paper_dir / "Frankl_Zero_Illusion_Preprint.pdf"
    copy_pdf = paper_dir / "main.pdf"

    if not md_file.exists():
        print(f"Error: {md_file} not found!")
        sys.exit(1)

    print(f"[*] Reading source paper: {md_file}")
    with open(md_file, "r", encoding="utf-8") as f:
        md_content = f.read()

    print("[*] Converting Markdown to publication-grade academic HTML...")
    html_content = markdown_to_academic_html(md_content)

    print("[*] Generating Frankl_Zero_Illusion_Preprint.pdf...")
    math_count = run_html_server_and_compile_pdf(html_content, target_pdf)

    print(f"[*] Copying {target_pdf.name} to {copy_pdf.name}...")
    shutil.copyfile(target_pdf, copy_pdf)

    print("[*] Verifying generated PDF deliverables...")
    pages, size = verify_generated_pdf(target_pdf)
    verify_generated_pdf(copy_pdf)

    print("[*] ALL DELIVERABLES SUCCESSFULLY PRODUCED AND VERIFIED!")


if __name__ == "__main__":
    main()
