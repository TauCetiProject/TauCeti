#!/usr/bin/env bash
# Exercise the staging mount boundary with trusted synthetic Lean code only.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
pin="$(cat warm-input/project/lean-toolchain)"
compiler="$(ELAN_TOOLCHAIN="$pin" elan which lean)"
fixture="$RUNNER_TEMP/cache-boundary-probe"
mkdir -p "$fixture/.lake"
printf 'module\ntheorem cache_boundary_canary : 1 = 1 := rfl\n' > "$fixture/Canary.lean"
test -d "$MATHLIB_CACHE_DIR"
test -n "$(find "$MATHLIB_CACHE_DIR" -name '*.ltar' -print -quit)"
env -i /usr/bin/bwrap --tmpfs / \
  --ro-bind /usr /usr --ro-bind /etc /etc \
  --symlink usr/bin /bin --symlink usr/sbin /sbin \
  --symlink usr/lib /lib --symlink usr/lib64 /lib64 \
  --dev /dev --proc /proc --tmpfs /tmp \
  --ro-bind "$HOME/.elan" "$HOME/.elan" \
  --ro-bind "$fixture" "$fixture" --bind "$fixture/.lake" "$fixture/.lake" \
  --remount-ro / \
  --setenv PATH "$HOME/.elan/bin:/usr/bin:/bin" --setenv HOME "$HOME" \
  --setenv COMPILER "$compiler" --setenv HOST_CACHE "$MATHLIB_CACHE_DIR" \
  --setenv FIXTURE "$fixture" \
  --unshare-user --unshare-ipc --unshare-pid --unshare-net --unshare-uts \
  --unshare-cgroup --disable-userns --die-with-parent --new-session \
  -- bash -euo pipefail -c '
    test ! -e "$HOST_CACHE"
    test -z "${GH_TOKEN:-}${GITHUB_TOKEN:-}${LAKE_CACHE_KEY:-}"
    test "$(tr "\0" "\n" < /proc/1/environ | grep -c . || true)" = 0
    if touch "$HOME/.elan/cache-poison-canary"; then exit 1; fi
    if touch "$COMPILER"; then exit 1; fi
    if unshare --user --map-root-user true; then exit 1; fi
    if curl -sS --max-time 5 https://example.com >/dev/null; then exit 1; fi
    "$COMPILER" -o "$FIXTURE/.lake/Canary.olean" "$FIXTURE/Canary.lean"
    test -s "$FIXTURE/.lake/Canary.olean"
  '
echo 'Sandbox probe passed: compilation works; toolchain writes, host cache, tokens, network and nested user namespaces denied.'
