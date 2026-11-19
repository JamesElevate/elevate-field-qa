"""Rebuild index.html from src/ (page template + engine + render + logo)."""
import pathlib
S = pathlib.Path(__file__).parent / "src"
page = (S / "page.html").read_text()
out = page.replace("{{LOGO}}", (S / "logo.txt").read_text().strip()).replace("{{ENGINE}}", (S / "engine.js").read_text()).replace("{{RENDER}}", (S / "render.js").read_text())
(pathlib.Path(__file__).parent / "index.html").write_text(out)
print("built index.html", len(out))
