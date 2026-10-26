/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed submodules under restriction and equivalence

This file supplements Mathlib's `LinearMap.fixedSubmodule`, the submodule of vectors fixed by a
linear endomorphism, with its behaviour under restriction to an invariant submodule and
transport by an intertwining linear equivalence.

## Main results

* `LinearEquiv.map_fixedSubmodule`: an intertwining equivalence maps one fixed submodule
  onto the other.
* `LinearEquiv.fixedSubmoduleCongr`: the resulting equivalence of fixed submodules.

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

namespace LinearEquiv

variable {R U W : Type*} [Semiring R] [AddCommMonoid U] [AddCommMonoid W]
  [Module R U] [Module R W] {f : U →ₗ[R] U} {g : W →ₗ[R] W}

/-- An intertwining linear equivalence maps the fixed submodule of its source endomorphism
onto the fixed submodule of its target endomorphism. -/
theorem map_fixedSubmodule (e : U ≃ₗ[R] W)
    (h : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    f.fixedSubmodule.map e.toLinearMap = g.fixedSubmodule := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearMap.mem_fixedSubmodule_iff]
  have he (x : U) : e (f x) = g (e x) := LinearMap.congr_fun h x
  rw [← e.injective.eq_iff, he, LinearEquiv.apply_symm_apply]

/-- Restrict an intertwining linear equivalence to the fixed submodules. -/
def fixedSubmoduleCongr (e : U ≃ₗ[R] W)
    (h : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    f.fixedSubmodule ≃ₗ[R] g.fixedSubmodule :=
  e.ofSubmodules _ _ (e.map_fixedSubmodule h)

/-- The restricted equivalence acts by the original equivalence on ambient vectors. -/
@[simp]
theorem fixedSubmoduleCongr_apply (e : U ≃ₗ[R] W)
    (h : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) (x : f.fixedSubmodule) :
    (e.fixedSubmoduleCongr h x : W) = e x := by
  simp [fixedSubmoduleCongr]

/-- The inverse restricted equivalence acts by the original inverse on ambient vectors. -/
@[simp]
theorem fixedSubmoduleCongr_symm_apply (e : U ≃ₗ[R] W)
    (h : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) (y : g.fixedSubmodule) :
    ((e.fixedSubmoduleCongr h).symm y : U) = e.symm y := by
  simp [fixedSubmoduleCongr]

end LinearEquiv
