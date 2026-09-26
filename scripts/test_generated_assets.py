#!/usr/bin/env python3
"""The generated-asset list must cover what the generators write and what the site asks for.

Two lists drifted apart once already: `pages.yml` carried a hand-written allowlist while
`pr_stats_graphs.ASSET_NAMES` grew two entries, so the roadmap/contributor grids were
generated and then dropped on the floor between jobs. Nothing failed -- the artifact was
simply missing them, and the site referenced two images that never arrived.
"""

import pathlib
import re
import unittest

import generated_assets
import pr_stats_graphs

ROOT = pathlib.Path(__file__).resolve().parent.parent


class GeneratedAssets(unittest.TestCase):
    def test_it_covers_every_pr_statistics_asset(self):
        for name in pr_stats_graphs.ASSET_NAMES:
            self.assertIn(name, generated_assets.GENERATED_ASSETS, name)

    def test_it_names_nothing_twice(self):
        assets = generated_assets.GENERATED_ASSETS
        self.assertEqual(sorted(assets), sorted(set(assets)))

    def test_the_workflow_derives_the_list_rather_than_restating_it(self):
        """A hand-written copy in the workflow is the failure this module exists to prevent."""
        workflow = (ROOT / ".github/workflows/pages.yml").read_text(encoding="utf-8")
        self.assertIn("python3 scripts/generated_assets.py", workflow)

    def test_every_generated_image_the_site_asks_for_is_carried(self):
        referenced = set()
        for page in (ROOT / "web/Site").glob("*.lean"):
            referenced |= set(re.findall(r'src="static/([A-Za-z0-9._-]+)"',
                                         page.read_text(encoding="utf-8")))
        self.assertTrue(referenced, "found no static references; the pattern has gone stale")
        carried = set(generated_assets.GENERATED_ASSETS)
        committed = {path.name for path in (ROOT / "web/static_files").iterdir()}
        for name in sorted(referenced):
            # Either a generated asset that build-data hands over, or a committed static file.
            self.assertTrue(name in carried or name in committed, name)


if __name__ == "__main__":
    unittest.main()
