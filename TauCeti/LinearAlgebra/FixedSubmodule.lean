/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed submodules under restriction

This file supplements Mathlib's `LinearMap.fixedSubmodule`, the submodule of vectors fixed by a
linear endomorphism, with its behaviour under restriction to an invariant submodule.

## Main results

* `LinearMap.fixedSubmodule_restrict`: the fixed submodule of the restriction of `f` to an
  invariant submodule `p` is the part of the fixed submodule of `f` that lies in `p`.
-/

public section

namespace TauCeti

/-- If `f` maps a submodule `p` into itself, then the fixed submodule of the restriction of `f`
to `p` is the part of the fixed submodule of `f` that lies in `p`. -/
theorem _root_.LinearMap.fixedSubmodule_restrict {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] {f : V →ₗ[R] V} {p : Submodule R V} (hf : ∀ x ∈ p, f x ∈ p) :
    (f.restrict hf).fixedSubmodule = f.fixedSubmodule.comap p.subtype := by
  ext x
  -- `x` is fixed by the restriction iff its value in `V` is fixed by `f`, since the restriction
  -- acts on `x` as `f` acts on `(x : V)`.
  rw [LinearMap.mem_fixedSubmodule_iff, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.mem_fixedSubmodule_iff, Subtype.ext_iff, LinearMap.coe_restrict_apply]

end TauCeti
