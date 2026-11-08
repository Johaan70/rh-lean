#!/usr/bin/env python3
"""Sett data.json inn i mal.html.

Lager to filer:
  index.html  – fullstendig HTML-dokument (GitHub Pages)
  side.html   – bare innholdet (for innbygging der dokumentskallet legges på utenfra)
"""
from pathlib import Path

her = Path(__file__).parent
mal = (her / "mal.html").read_text(encoding="utf-8")
data = (her / "data.json").read_text(encoding="utf-8")
assert "/*DATA*/null" in mal
innhold = mal.replace("/*DATA*/null", data)
(her / "side.html").write_text(innhold, encoding="utf-8")
hode = ('<!doctype html>\n<html lang="nb">\n<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n')
(her / "index.html").write_text(hode + innhold, encoding="utf-8")
print("skrev index.html og side.html")
