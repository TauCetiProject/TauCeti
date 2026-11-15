"""Build real Verso sites and check the rendered navigation, archives, and posts.

Run from web/: python3 tests/test_blog.py
"""

from html.parser import HTMLParser
from pathlib import Path
import subprocess
import tempfile
import unittest
from urllib.parse import urljoin, urlsplit


WEB = Path(__file__).resolve().parents[1]


class Page(HTMLParser):
    def __init__(self, path):
        super().__init__()
        self.base = None
        self.nav_links = []
        self.links = []
        self.images = []
        self.in_nav = False
        self.html = path.read_text()
        self.feed(self.html)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "base":
            self.base = attrs["href"]
        if tag == "nav":
            self.in_nav = True
        if tag == "a":
            self.links.append(attrs["href"])
            if self.in_nav:
                self.nav_links.append(attrs["href"])
        if tag == "img":
            self.images.append(attrs["src"])

    def handle_endtag(self, tag):
        if tag == "nav":
            self.in_nav = False


class BlogTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        subprocess.run(["lake", "build", "Site.Theme", "Site.Blog"], cwd=WEB, check=True)
        cls.temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.temp.cleanup)
        cls.sites = {}
        for mode in ("empty", "draft", "published"):
            output = Path(cls.temp.name) / mode
            subprocess.run(
                ["lake", "env", "lean", "--run", "tests/Blog.lean", mode,
                 "--output", str(output)], cwd=WEB, check=True,
            )
            cls.sites[mode] = output

    def test_no_blog_tab_without_published_posts(self):
        for mode in ("empty", "draft"):
            for path in self.sites[mode].rglob("index.html"):
                with self.subTest(mode=mode, page=path):
                    page = Page(path)
                    self.assertNotIn("blog/", page.nav_links)
                    self.assertNotIn("Unpublished draft", page.html)
                    self.assertNotIn("First post", page.html)
            self.assertEqual(list(self.sites[mode].glob("blog/*/index.html")), [])

    def test_blog_tab_on_every_page_when_published(self):
        for path in self.sites["published"].rglob("index.html"):
            with self.subTest(page=path):
                self.assertEqual(Page(path).nav_links.count("blog/"), 1)

    def test_archive_and_category_link_to_post(self):
        output = self.sites["published"]
        for path in ("blog/index.html", "blog/updates/index.html"):
            with self.subTest(page=path):
                page = Page(output / path)
                self.assertIn("First post", page.html)
                self.assertIn("Test Author", page.html)
                self.assertIn("2026-10-28", page.html)
                self.assertIn("blog/2026-10-28-first-post", page.links)

    def test_post_body_and_metadata(self):
        page = Page(self.sites["published"] / "blog/2026-10-28-first-post/index.html")
        for text in ("First post", "Test Author", "2026-10-28", "formatted text"):
            self.assertIn(text, page.html)
        self.assertIn("<em>", page.html)

    def test_drafts_are_never_published(self):
        for path in self.sites["published"].rglob("*.html"):
            self.assertNotIn("Unpublished draft", path.read_text())
        self.assertFalse((self.sites["published"] / "blog/2026-10-28-unpublished-draft").exists())

    def test_nested_pages_resolve_navigation_and_assets(self):
        output = self.sites["published"]
        for path in output.rglob("index.html"):
            page = Page(path)
            # Resolve URLs as a browser does, including Verso's <base> element.
            url = "https://example.test/" + path.relative_to(output).as_posix()
            base = urljoin(url, page.base)
            for link in [*page.nav_links, *page.links, *page.images, "static/style.css"]:
                target = urlsplit(urljoin(base, link))
                if target.netloc != "example.test":
                    continue
                local = output / target.path.lstrip("/")
                if local.is_dir():
                    local /= "index.html"
                # The fixture includes only Home, About, and Blog from the production site.
                if target.path.strip("/") in {"statistics", "progress", "ci", "team", "docs"}:
                    continue
                with self.subTest(page=path, link=link):
                    self.assertTrue(local.is_file(), str(local))


if __name__ == "__main__":
    unittest.main()
