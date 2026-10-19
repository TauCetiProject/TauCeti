import importlib.util
import io
import json
import unittest
import zipfile
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "summary", Path(__file__).with_name("ci_live_summary.py")
)
summary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(summary)


class SummaryTests(unittest.TestCase):
    def test_artifact_is_data_only_and_cannot_supply_producer_identity(self):
        archive = io.BytesIO()
        with zipfile.ZipFile(archive, "w") as z:
            z.writestr(
                "telemetry.json",
                json.dumps(
                    {
                        "schema": "tauceti-ci.telemetry/v1",
                        "phases": [{"phase": "build", "seconds": 42}],
                        "meta": {
                            "head_sha": "forged",
                            "merge_engine": "bors",
                            "batch_members": "forged",
                        },
                        "trust": "trusted",
                    }
                ),
            )
            z.writestr("../../execute.sh", "exit 1")
        self.assertEqual(
            summary.telemetry(archive.getvalue()),
            {"phases": [{"phase": "build", "seconds": 42}]},
        )

    def test_excerpts_ignore_script_echoes_and_successful_module_names(self):
        log = "\n".join(
            [
                '\x1b[36;1mecho "Killed"',
                "✔ Built KilledByRank",
                "+ echo error",
                "2026-10-18T12:00:00Z error: old.lean:1:1",
                "2026-10-18T12:01:30Z src.lean:4:5: error: unknown identifier",
                "2026-10-18T12:03:00Z error: later.lean:1:1",
            ]
        )
        self.assertEqual(
            summary.excerpt(
                log,
                {
                    "started_at": "2026-10-18T12:01:00Z",
                    "completed_at": "2026-10-18T12:02:00Z",
                },
            ),
            ["src.lean:4:5: error: unknown identifier"],
        )

    def test_oversized_artifact_is_rejected_before_inflating(self):
        archive = io.BytesIO()
        with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as z:
            z.writestr("telemetry.json", " " * (1024 * 1024 + 1))
        with self.assertRaises(ValueError):
            summary.telemetry(archive.getvalue())


if __name__ == "__main__":
    unittest.main()
