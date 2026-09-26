/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed submodules under commuting endomorphisms and restriction

This file supplements Mathlib's `LinearMap.fixedSubmodule`, the submodule of vectors fixed by a
linear endomorphism, with its invariance under commuting endomorphisms and its behaviour under
restriction to an invariant submodule.

## Main results

* `Commute.apply_mem_fixedSubmodule`: an endomorphism commuting with `g` maps the fixed submodule
  of `g` into itself.
* `LinearMap.fixedSubmodule_restrict`: the fixed submodule of the restriction of `f` to an
  invariant submodule `p` is the part of the fixed submodule of `f` that lies in `p`.
-/

public section

namespace TauCeti

/-- An endomorphism commuting with `g` maps the fixed submodule of `g` into itself. -/
theorem _root_.Commute.apply_mem_fixedSubmodule {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] {f g : Module.End R V} (h : Commute g f) {x : V} (hx : x ∈ g.fixedSubmodule) :
    f x ∈ g.fixedSubmodule := by
  simpa [LinearMap.mem_fixedSubmodule_iff.1 hx] using LinearMap.congr_fun h.eq x

/-- If `f` maps a submodule `p` into itself, then the fixed submodule of the restriction of `f`
to `p` is the part of the fixed submodule of `f` that lies in `p`. -/
theorem _root_.LinearMap.fixedSubmodule_restrict {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] {f : V →ₗ[R] V} {p : Submodule R V} (hf : ∀ x ∈ p, f x ∈ p) :
    (f.restrict hf).fixedSubmodule = f.fixedSubmodule.comap p.subtype :=
  Submodule.ext fun _ => Subtype.ext_iff

end TauCeti
