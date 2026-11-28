/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.State.Tracial
import TauCeti.Analysis.CStarAlgebra.State.Extension
import TauCeti.RingTheory.TraceFunctional.Star

/-!
# Extension of tracial states from closed ideals

Let `I` be a closed two-sided ideal of a possibly nonunital C⋆-algebra `A`, a nonunital
C⋆-algebra in its own right (`TwoSidedIdeal.nonUnitalCStarAlgebra`) with the order induced from
`A` (`TwoSidedIdeal.instStarOrderedRingOfIsClosed`). Every positive functional `τ` of `I` extends
uniquely to a positive functional `γ` of `A` of the same norm, in particular every state to a
state, with `γ(a) = lim_e τ(eae)` along every increasing approximate unit `e` of `I`, and the
extension of a tracial functional is tracial. The extension formula, uniqueness and existence are
first proved along a star homomorphism `f : B → A` of C⋆-algebras, and specialized to the
inclusion of `I`.

## Main declarations

The estimates for positive contractions
(`PositiveContinuousLinearMap.norm_apply_sub_apply_mul_sq_le` and its variants) are in
`TauCeti.Analysis.CStarAlgebra.State.Unitization`, and the extension formula, uniqueness and
existence along a star homomorphism (`PositiveContinuousLinearMap.tendsto_apply_map_mul_mul_map`,
`eq_of_apply_map_eq`, `exists_apply_map_eq`) in `TauCeti.Analysis.CStarAlgebra.State.Extension`.
This file specializes them to a closed ideal. The unitization case `A ⊆ Unitization ℂ A`
(`PositiveContinuousLinearMap.eq_unitization_of_apply_inr_eq`) is in the latter file.

* `PositiveContinuousLinearMap.tendsto_apply_mul_mul_of_apply_coe_eq` and
  `tendsto_apply_mul_mul_of_apply_coe_eq'`: a positive functional `γ` with `‖γ‖ ≤ ‖τ‖`
  restricting to `τ` on `I` satisfies `γ(a) = lim_e γ(eae) = lim_e τ(eae)` along every increasing
  approximate unit of `I`.
* `PositiveContinuousLinearMap.eq_of_apply_coe_eq`: uniqueness of the extension from a closed
  ideal.
* `PositiveContinuousLinearMap.exists_apply_coe_eq`: a positive functional extends from a closed
  ideal without increasing its norm.
* `PositiveContinuousLinearMap.existsUnique_apply_coe_eq`: a positive functional of `I` has
  exactly one extension to a positive functional of `A` of the same norm; for a state, exactly one
  extension to a state.
* `PositiveContinuousLinearMap.re_apply_mul_star_le_of_apply_coe_eq`: an extension `γ` of a
  positive tracial functional of `I` satisfies `Re γ(a a⋆) ≤ Re γ(a⋆ a)`.
* `PositiveContinuousLinearMap.map_mul_comm_of_apply_coe_eq`: the extension of a positive tracial
  functional is tracial.
* `PositiveContinuousLinearMap.isTracialState_of_apply_coe_eq`: the extension of a tracial state
  is a tracial state.
* `PositiveContinuousLinearMap.IsTracialState.existsUnique_isTracialState_apply_coe_eq`: a
  tracial state of `I` extends uniquely to a tracial state of `A`.

## Implementation notes

Existence is `exists_apply_map_eq` applied to the inclusion `I.starAlgHom`, which extends the
state `τ / ‖τ‖` with `TauCeti.surjOn_pullbackFunctional_stateSpace` and rescales (the zero
functional when `τ = 0`). The rest rests on one estimate: for a positive functional `γ` and a
positive contraction `e`, the Cauchy–Schwarz inequality for the extension of `γ` to `A⁺¹` and
`(1 - e)² ≤ 1 - e` give
`‖γ y - γ (y e)‖² ≤ ‖γ‖ (‖γ‖ - Re γ e) ‖y‖²`. Along an increasing approximate unit of `I`,
`τ e → ‖τ‖`, so `γ(a) = lim_e γ(eae) = lim_e τ(eae)` for every extension `γ` of norm at most
`‖τ‖`, which gives uniqueness. Traciality follows from the polarization criterion: for `a ∈ A`,
`γ(a a⋆) = lim_e τ((ea)(ea)⋆) = lim_e τ((ea)⋆(ea)) = lim_e γ(a⋆ e² a) ≤ γ(a⋆ a)`, using only the
traciality of `τ` on `I`, and the reverse inequality is the same statement for `a⋆`. This argument
replaces the GNS construction of Brown's proof and uses no von Neumann algebra.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Proposition 3.5.12.
-/

public section

open Filter Topology
open scoped ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

section Ideal

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

/-- **The extension formula** for a closed ideal: if `γ` is a positive functional of norm at most
`‖τ‖` on `A` that restricts to a positive functional `τ` of a closed ideal `I`, then
`γ(a) = lim_e γ(eae)` along every increasing approximate unit `e` of `I`. See
`tendsto_apply_mul_mul_of_apply_coe_eq'` for the same limit written with `τ`. -/
theorem tendsto_apply_mul_mul_of_apply_coe_eq {τ : I →P[ℂ] ℂ}
    {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ ‖(τ : I →L[ℂ] ℂ)‖) (h : ∀ c : I, γ c = τ c)
    {l : Filter I} (hl : l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e : I ↦ γ ((e : A) * a * e)) l (𝓝 (γ a)) := by
  simpa [TwoSidedIdeal.starAlgHom_apply] using
    tendsto_apply_map_mul_mul_map I.starAlgHom hγ (by simpa using h) hl a

/-- **The extension formula** for a closed ideal, written with `τ`: `γ(a) = lim_e τ(eae)` along
every increasing approximate unit `e` of `I`. -/
theorem tendsto_apply_mul_mul_of_apply_coe_eq' {τ : I →P[ℂ] ℂ}
    {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ ‖(τ : I →L[ℂ] ℂ)‖) (h : ∀ c : I, γ c = τ c)
    {l : Filter I} (hl : l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e : I ↦ τ ⟨(e : A) * a * e, I.mul_mem_left _ _ e.property⟩) l (𝓝 (γ a)) :=
  (tendsto_apply_mul_mul_of_apply_coe_eq hγ h hl a).congr fun _ ↦ h _

/-- **Uniqueness of the extension** from a closed ideal: two positive functionals of norm at most
`‖τ‖` on `A` that restrict to the same positive functional `τ` of a closed ideal are equal. -/
theorem eq_of_apply_coe_eq {τ : I →P[ℂ] ℂ} {γ₁ γ₂ : A →P[ℂ] ℂ}
    (hγ₁ : ‖(γ₁ : A →L[ℂ] ℂ)‖ ≤ ‖(τ : I →L[ℂ] ℂ)‖) (hγ₂ : ‖(γ₂ : A →L[ℂ] ℂ)‖ ≤ ‖(τ : I →L[ℂ] ℂ)‖)
    (h₁ : ∀ c : I, γ₁ c = τ c) (h₂ : ∀ c : I, γ₂ c = τ c) : γ₁ = γ₂ :=
  eq_of_apply_map_eq I.starAlgHom
    (fun e a ↦ ⟨⟨(e : A) * a * e, I.mul_mem_left _ _ e.property⟩,
      by simp [TwoSidedIdeal.starAlgHom_apply]⟩) hγ₁ hγ₂
    (by simpa using h₁) (by simpa using h₂)

/-- **Existence of the extension** from a closed ideal: every positive functional on a closed
ideal `I` of `A` is the restriction of a positive functional on `A` of the same norm. -/
theorem exists_apply_coe_eq (τ : I →P[ℂ] ℂ) :
    ∃ γ : A →P[ℂ] ℂ, ‖(γ : A →L[ℂ] ℂ)‖ = ‖(τ : I →L[ℂ] ℂ)‖ ∧ ∀ c : I, γ c = τ c := by
  simpa using exists_apply_map_eq I.starAlgHom I.starAlgHom_injective τ

/-- **Extension of positive functionals from closed ideals.** A positive functional `τ` of a
closed ideal `I` of `A` is the restriction of exactly one positive functional on `A` of the same
norm, given by `lim_e τ(eae)` along every increasing approximate unit of `I`
(`tendsto_apply_mul_mul_of_apply_coe_eq'`). For a state `τ`, this is the unique extension to a
state of `A`. -/
theorem existsUnique_apply_coe_eq (τ : I →P[ℂ] ℂ) :
    ∃! γ : A →P[ℂ] ℂ, ‖(γ : A →L[ℂ] ℂ)‖ = ‖(τ : I →L[ℂ] ℂ)‖ ∧ ∀ c : I, γ c = τ c := by
  obtain ⟨γ, hγ, h⟩ := exists_apply_coe_eq τ
  exact ⟨γ, ⟨hγ, h⟩, fun γ' ⟨hγ', h'⟩ ↦ eq_of_apply_coe_eq hγ'.le hγ.le h' h⟩

/-- A positive functional `γ` on `A` with `‖γ‖ ≤ ‖τ‖` restricting to a positive functional `τ` of a
closed ideal `I` with `τ (x * y) = τ (y * x)` satisfies `Re γ(a a⋆) ≤ Re γ(a⋆ a)`. -/
theorem re_apply_mul_star_le_of_apply_coe_eq {τ : I →P[ℂ] ℂ}
    (hτ : ∀ x y : I, τ (x * y) = τ (y * x)) {γ : A →P[ℂ] ℂ}
    (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ ‖(τ : I →L[ℂ] ℂ)‖) (h : ∀ c : I, γ c = τ c) (a : A) :
    (γ (a * star a)).re ≤ (γ (star a * a)).re := by
  -- `γ(a a⋆) = lim_e τ((ea)(ea)⋆) = lim_e τ((ea)⋆(ea)) = lim_e γ(a⋆ e² a) ≤ γ(a⋆ a)`
  have hl := CStarAlgebra.increasingApproximateUnit (A := I)
  have := hl.neBot
  have hlim := (Complex.continuous_re.tendsto _).comp
    (tendsto_apply_mul_mul_of_apply_coe_eq hγ h hl (a * star a))
  refine le_of_tendsto hlim ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he he1
  have he' : 0 ≤ (e : A) := by exact_mod_cast he
  have he1' : ‖(e : A)‖ ≤ 1 := by exact_mod_cast he1
  let x : I := ⟨(e : A) * a, I.mul_mem_right _ _ e.property⟩
  have hx : γ ((e : A) * (a * star a) * e) = γ (star a * ((e : A) * e) * a) := by
    have h1 : (e : A) * (a * star a) * e = ((x * star x : I) : A) := by
      simp only [MulMemClass.coe_mul, TwoSidedIdeal.coe_star, x, star_mul, he'.star_eq]
      noncomm_ring
    have h2 : star a * ((e : A) * e) * a = ((star x * x : I) : A) := by
      simp only [MulMemClass.coe_mul, TwoSidedIdeal.coe_star, x, star_mul, he'.star_eq]
      noncomm_ring
    rw [h1, h2, h, h, hτ]
  have hee : ‖(e : A) * e‖ ≤ 1 :=
    (norm_mul_le _ _).trans ((mul_le_mul he1' he1' (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))
  have hsa : IsSelfAdjoint ((e : A) * e) := by
    simpa [he'.star_eq] using IsSelfAdjoint.star_mul_self (e : A)
  have hmono : (γ (star a * ((e : A) * e) * a)).re ≤ (γ (‖(e : A) * e‖ • (star a * a))).re :=
    (Complex.le_def.mp (γ.mono (CStarAlgebra.star_left_conjugate_le_norm_smul a _ hsa))).1
  have hnn : 0 ≤ (γ (star a * a)).re :=
    (Complex.le_def.mp (γ.map_nonneg (star_mul_self_nonneg a))).1
  simp only [Function.comp_apply, hx]
  refine hmono.trans ?_
  rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_le_of_le_one_left hnn hee

/-- **The extension of a tracial functional is tracial.** If a positive functional `γ` on `A` with
`‖γ‖ ≤ ‖τ‖` restricts to a positive functional `τ` of a closed ideal `I` with
`τ (x * y) = τ (y * x)`, then `γ (a * b) = γ (b * a)`. -/
theorem map_mul_comm_of_apply_coe_eq {τ : I →P[ℂ] ℂ} (hτ : ∀ x y : I, τ (x * y) = τ (y * x))
    {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ ‖(τ : I →L[ℂ] ℂ)‖) (h : ∀ c : I, γ c = τ c)
    (a b : A) : γ (a * b) = γ (b * a) := by
  have hle := re_apply_mul_star_le_of_apply_coe_eq hτ hγ h
  have hstar (a : A) : γ (star a * a) = γ (a * star a) := by
    refine Complex.ext ?_ ?_
    · simpa using le_antisymm (by simpa using hle (star a)) (hle a)
    · rw [← (Complex.le_def.mp (γ.map_nonneg (star_mul_self_nonneg a))).2,
        ← (Complex.le_def.mp (γ.map_nonneg (mul_star_self_nonneg a))).2]
  exact (LinearMap.forall_map_mul_comm_iff_forall_map_star_mul_self (γ : A →ₗ[ℂ] ℂ)).mpr
    hstar a b

/-- **The extension of a tracial state is tracial.** If a positive functional `γ` of norm at most
one on `A` restricts to a tracial state of a closed ideal `I`, then `γ` is a tracial state. -/
theorem isTracialState_of_apply_coe_eq {τ : I →P[ℂ] ℂ} (hτ : τ.IsTracialState)
    {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ 1) (h : ∀ c : I, γ c = τ c) :
    γ.IsTracialState := by
  have hγτ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ ‖(τ : I →L[ℂ] ℂ)‖ := hγ.trans hτ.norm_eq_one.ge
  exact isTracialState_iff.mpr
    ⟨(norm_eq_of_apply_map_eq I.starAlgHom hγτ (by simpa using h)).trans hτ.norm_eq_one,
      map_mul_comm_of_apply_coe_eq hτ.map_mul_comm hγτ h⟩

/-- **Extension of tracial states from closed ideals.** Every tracial state of a closed ideal `I`
of `A` extends uniquely to a tracial state of `A`. -/
theorem IsTracialState.existsUnique_isTracialState_apply_coe_eq {τ : I →P[ℂ] ℂ}
    (hτ : τ.IsTracialState) : ∃! γ : A →P[ℂ] ℂ, γ.IsTracialState ∧ ∀ c : I, γ c = τ c := by
  obtain ⟨γ, ⟨hγ, h⟩, huniq⟩ := existsUnique_apply_coe_eq (A := A) τ
  exact ⟨γ, ⟨isTracialState_of_apply_coe_eq hτ (hγ.trans hτ.norm_eq_one).le h, h⟩,
    fun γ' ⟨hγ', h'⟩ ↦ huniq γ' ⟨hγ'.norm_eq_one.trans hτ.norm_eq_one.symm, h'⟩⟩

end Ideal

end PositiveContinuousLinearMap
