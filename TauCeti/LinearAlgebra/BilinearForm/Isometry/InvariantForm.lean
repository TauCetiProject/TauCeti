/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Forms invariant under the transvections of an alternating form

For an alternating bilinear form `ω` and a vector `v`, the transvection `x ↦ x + ω v x • v`
(Mathlib's `LinearMap.transvection (ω v) v`) preserves `ω`
(`LinearMap.BilinForm.IsAlt.isIsometry_transvection`). When `ω` is left-separating over a field,
these transvections already pin down `ω` up to a scalar: every bilinear form they preserve is a
multiple of `ω` (`LinearMap.BilinForm.exists_eq_smul_of_forall_isIsometry_transvection`).
In particular, the invariant bilinear forms of a symplectic group on its standard representation
are spanned by the symplectic form; this span is a line when the representation is nonzero.

## Main results

* `LinearMap.BilinForm.IsAlt.isIsometry_transvection`: the transvections `x ↦ x + ω v x • v` are
  isometries of an alternating form `ω`.
* `LinearMap.BilinForm.exists_eq_smul_of_forall_isIsometry_transvection`: a bilinear form
  preserved by all of them is a scalar multiple of `ω`, when `ω` is left-separating.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III, §§3–5.
-/

public section

open TauCeti.BilinForm

namespace LinearMap.BilinForm

/-- **Symplectic transvections are isometries.** For an alternating form `ω` and a vector `v`, the
transvection `x ↦ x + ω v x • v` preserves `ω`. -/
theorem IsAlt.isIsometry_transvection {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ω : LinearMap.BilinForm R M} (hω : ω.IsAlt) (v : M) :
    IsIsometry ω (LinearMap.transvection (ω v) v) := by
  refine isIsometry_iff.mpr fun x y => ?_
  have hxv := hω.neg_eq x v
  simp only [LinearMap.transvection.apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, hω.self_eq_zero, smul_eq_mul, ← hxv]
  ring

/-- **Transvections determine a form up to a scalar.** Over a field, a bilinear form `B` preserved
by every map `x ↦ x + ω v x • v` attached to a left-separating form `ω` is a scalar multiple of
`ω`. When `ω` is alternating these maps are its transvections, which preserve `ω`
(`LinearMap.BilinForm.IsAlt.isIsometry_transvection`). -/
theorem exists_eq_smul_of_forall_isIsometry_transvection {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ω B : LinearMap.BilinForm K V} (hsep : ω.SeparatingLeft)
    (hB : ∀ v, IsIsometry B (LinearMap.transvection (ω v) v)) :
    ∃ c : K, B = c • ω := by
  have hinj : Function.Injective ω :=
    LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hsep)
  -- Expanding the invariance of `B` under the transvection along `v` at a vector `x` with
  -- `ω v x = 1` shows that `B v` is a multiple of `ω v`.
  have hline : ∀ v, ∃ μ : K, B v = ω (μ • v) := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, by simp [hv]⟩
    obtain ⟨x, hx⟩ : ∃ x, ω v x = 1 := by
      obtain ⟨y, hy⟩ : ∃ y, ω v y ≠ 0 := by
        by_contra! h
        exact hv (hsep v h)
      exact ⟨(ω v y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]⟩
    refine ⟨-(B x v + B v v), LinearMap.ext fun z => ?_⟩
    have h := isIsometry_iff.mp (hB v) x z
    simp only [LinearMap.transvection.apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hx, one_smul] at h ⊢
    linear_combination h
  -- `B` factors through `ω` as `B v = ω (T v)`, and `T v` is a multiple of `v` for every `v`.
  have hmem : ∀ v, B v ∈ LinearMap.range ω := fun v =>
    let ⟨μ, hμ⟩ := hline v
    ⟨μ • v, hμ.symm⟩
  let e := LinearEquiv.ofInjective ω hinj
  let T : V →ₗ[K] V := e.symm.toLinearMap ∘ₗ B.codRestrict _ hmem
  have hT : ∀ v, ω (T v) = B v := fun v => by
    rw [← LinearEquiv.ofInjective_apply ω (h := hinj)]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨B v, hmem v⟩)
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := T) fun v => by
    obtain ⟨μ, hμ⟩ := hline v
    have hTv : T v = μ • v := hinj (by rw [hT, hμ])
    rw [LinearIndependent.pair_iff]
    push Not
    exact ⟨μ, -1, by rw [hTv, neg_one_smul, add_neg_cancel], by simp⟩
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  rw [← hT, hc, LinearMap.smul_apply, one_apply_eq_self, map_smul, LinearMap.smul_apply]

end LinearMap.BilinForm
