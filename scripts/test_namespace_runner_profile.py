"""A provider profile can replace slot queues only after explicit confirmation."""
import json
import unittest

from namespace_runner_profile import target


class NamespaceProfile(unittest.TestCase):
    def select(self, **changes):
        args = dict(runner=json.dumps(["nscloud-ubuntu-24.04-amd64-8x16-with-features"]),
                    pool="namespace", profile="", profile_cap="", build_cap="8")
        return target(**dict(args, **changes))

    def test_unconfigured_preserves_the_existing_runner_and_slot_guard(self):
        self.assertEqual(self.select()["namespace_profile_limited"], "false")
        self.assertIn("nscloud-", self.select()["runner"])

    def test_profile_routes_before_confirmation_but_retains_the_slot_guard(self):
        selected = self.select(profile="namespace-profile-ci")
        self.assertEqual(json.loads(selected["runner"]), ["namespace-profile-ci", "namespace-features:container.privileged=true"])
        self.assertEqual(selected["namespace_profile_limited"], "false")

    def test_only_a_matching_confirmed_provider_cap_replaces_slot_queues(self):
        self.assertEqual(self.select(profile="namespace-profile-ci", profile_cap="8")["namespace_profile_limited"], "true")
        for cap in ("7", "0", "65", "eight"):
            with self.subTest(cap=cap), self.assertRaises(ValueError):
                self.select(profile="namespace-profile-ci", profile_cap=cap)

    def test_native_and_github_choices_ignore_profile_settings(self):
        for pool in ("fleet", "tauchonki2", "github"):
            selected = self.select(pool=pool, runner='"original"', profile="invalid", profile_cap="bad")
            self.assertEqual(selected, dict(runner='"original"', namespace_profile_limited="false"))

    def test_confirmation_without_a_profile_cannot_disable_slot_groups(self):
        self.assertEqual(self.select(profile_cap="8")["namespace_profile_limited"], "false")

    def test_multiple_labels_and_output_injection_are_rejected(self):
        for label in ('["namespace-profile-ci"]', "namespace-profile-ci\nrunner=ubuntu-24.04", "nscloud-generic", "namespace-profile-"):
            with self.subTest(label=label), self.assertRaises(ValueError):
                self.select(profile=label)
