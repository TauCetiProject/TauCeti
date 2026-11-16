#!/usr/bin/env python3
"""Select an operator-configured Namespace profile after pool selection.

Setting a profile label alone retains GitHub's existing slot groups for a live
transition. NAMESPACE_PROFILE_CAP is an operator assertion of the provider's
configured limit; set it only after old generic Namespace jobs have finished.
"""
import json
import os
import re


def target(*, runner, pool, profile, profile_cap, build_cap):
    result = dict(runner=runner, namespace_profile_limited="false")
    if pool != "namespace" or not profile:
        return result
    if not re.fullmatch(r"namespace-profile-[A-Za-z0-9][A-Za-z0-9_.-]{0,127}", profile):
        raise ValueError("NAMESPACE_RUNNER_PROFILE must be one Namespace profile label")
    result["runner"] = json.dumps([profile, "namespace-features:container.privileged=true"], separators=(",", ":"))
    if profile_cap:
        if (not re.fullmatch(r"[1-9][0-9]?", profile_cap)
                or not 1 <= int(profile_cap) <= 64 or profile_cap != build_cap):
            raise ValueError("NAMESPACE_PROFILE_CAP must match the runtime build cap (1–64)")
        result["namespace_profile_limited"] = "true"
    return result


if __name__ == "__main__":
    values = target(runner=os.environ["PICKER_RUNNER"], pool=os.environ["PICKER_POOL"],
                    profile=os.environ.get("NAMESPACE_RUNNER_PROFILE", "").strip(),
                    profile_cap=os.environ.get("NAMESPACE_PROFILE_CAP", "").strip(),
                    build_cap=os.environ["PICKER_NAMESPACE_CAP"])
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        for key, value in values.items():
            print(f"{key}={value}", file=output)
