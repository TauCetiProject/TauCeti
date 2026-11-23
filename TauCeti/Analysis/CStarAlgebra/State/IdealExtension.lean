/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.State.Tracial
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import TauCeti.Analysis.CStarAlgebra.State.Extension

/-!
# Extension of tracial states from closed ideals

Let `I` be a closed two-sided ideal of a possibly nonunital C⋆-algebra `A`, a nonunital
C⋆-algebra in its own right (`TwoSidedIdeal.nonUnitalCStarAlgebra`) with the order induced from
`A`. Every tracial state `τ` of `I` extends uniquely to a state `γ` of `A`, the extension is
tracial, and `γ(a) = lim_e τ(eae)` along every increasing approximate unit `e` of `I`.

## Main declarations

* `TwoSidedIdeal.instStarOrderedRingOfIsClosed`: the order of `A` restricted to a closed ideal `I`
  is the C⋆-algebra order of `I`.
* `PositiveContinuousLinearMap.norm_apply_sub_apply_mul_sq_le`: for a positive functional `γ` and
  a positive contraction `e`, `‖γ y - γ (y e)‖² ≤ ‖γ‖ (‖γ‖ - Re γ e) ‖y‖²`, with the left and
  two-sided variants `norm_apply_sub_apply_mul_left_sq_le` and `norm_apply_sub_apply_mul_mul_le`.
* `PositiveContinuousLinearMap.tendsto_apply_mul_mul_of_apply_coe_eq`: a functional `γ` of norm at
  most one restricting to a state `τ` of `I` satisfies `γ(a) = lim_e τ(eae)` along every increasing
  approximate unit of `I`.
* `PositiveContinuousLinearMap.eq_of_apply_coe_eq`: uniqueness of the extension.
* `PositiveContinuousLinearMap.exists_apply_coe_eq`: every state of `I` extends to a state of `A`.
* `PositiveContinuousLinearMap.isTracialState_of_apply_coe_eq`: the extension of a tracial state
  is tracial.
* `PositiveContinuousLinearMap.IsTracialState.existsUnique_apply_coe_eq` and
  `PositiveContinuousLinearMap.IsTracialState.existsUnique_isTracialState_apply_coe_eq`: a
  tracial state of `I` has exactly one extension to a state of `A`, and it is tracial.

## Implementation notes

Existence comes from extending the unitization `τ⁺¹` of `τ` along the injective unital
star homomorphism `I⁺¹ → A⁺¹` (`TauCeti.surjOn_pullbackFunctional_stateSpace`) and restricting to
`A`. The rest rests on one estimate: for a positive functional `γ` and a positive contraction `e`,
the Cauchy–Schwarz inequality for the extension of `γ` to `A⁺¹` and `(1 - e)² ≤ 1 - e` give
`‖γ y - γ (y e)‖² ≤ ‖γ‖ (‖γ‖ - Re γ e) ‖y‖²`. Along an increasing approximate unit of `I`,
`τ e → ‖τ‖ = 1`, so `γ(a) = lim_e γ(eae) = lim_e τ(eae)` for every extension `γ` of norm at most
one, which gives uniqueness. Traciality follows from the polarization criterion: for `a ∈ A`,
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

namespace TwoSidedIdeal

/-- A two-sided ideal contains `x a x` for every `x` in it. -/
theorem mul_mul_mem {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R) {x : R}
    (hx : x ∈ I) (a : R) : x * a * x ∈ I :=
  I.mul_mem_right _ _ (I.mul_mem_right _ _ hx)

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- The order of a C⋆-algebra restricted to a closed two-sided ideal `I` is the C⋆-algebra order
of `I`: a positive element of `A` lying in `I` is `s⋆s` for some `s ∈ I`, namely its square
root. -/
instance instStarOrderedRingOfIsClosed : StarOrderedRing I :=
  .of_nonneg_iff' add_le_add_right fun x ↦ by
    refine ⟨fun hx ↦ ?_, ?_⟩
    · have hx' : 0 ≤ (x : A) := hx
      refine ⟨⟨cfcₙ Real.sqrt (x : A), I.cfcₙ_mem_of_isClosed (𝕜 := ℝ) _ x.property⟩, ?_⟩
      apply Subtype.ext
      change (x : A) = star (cfcₙ Real.sqrt (x : A)) * cfcₙ Real.sqrt (x : A)
      rw [IsSelfAdjoint.star_eq (by cfc_tac), ← cfcₙ_mul ..]
      convert (cfcₙ_id' ℝ (x : A)).symm using 1
      exact cfcₙ_congr fun r hr ↦ by grind [Real.mul_self_sqrt]
    · rintro ⟨s, rfl⟩
      exact star_mul_self_nonneg (s : A)

end TwoSidedIdeal

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- From `‖z‖² ≤ c ‖y‖²` to `‖z‖ ≤ √c ‖y‖`. -/
private theorem norm_le_sqrt_mul_of_sq_le {z : ℂ} {y : A} {c : ℝ} (h : ‖z‖ ^ 2 ≤ c * ‖y‖ ^ 2) :
    ‖z‖ ≤ Real.sqrt c * ‖y‖ := by
  calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
    _ ≤ Real.sqrt (c * ‖y‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt c * ‖y‖ := by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg y)]

/-- **The approximate unit estimate.** For a positive functional `γ` and a positive contraction
`e`, `‖γ y - γ (y e)‖² ≤ ‖γ‖ (‖γ‖ - Re γ e) ‖y‖²`: the Cauchy–Schwarz inequality for the extension
of `γ` to the unitization, with `(1 - e)² ≤ 1 - e`. -/
theorem norm_apply_sub_apply_mul_sq_le (γ : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (y : A) :
    ‖γ y - γ (y * e)‖ ^ 2 ≤
      ‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re) * ‖y‖ ^ 2 := by
  set N := ‖(γ : A →L[ℂ] ℂ)‖
  set u : Unitization ℂ A := star (y : Unitization ℂ A)
  set v : Unitization ℂ A := 1 - (e : Unitization ℂ A)
  have hkey : γ y - γ (y * e) = γ.unitization (star u * v) := by
    simp only [u, v, star_star, mul_sub, mul_one, ← Unitization.inr_mul, map_sub,
      unitization_apply_inr]
  have hcs := PositiveLinearMap.norm_map_star_mul_sq_le γ.unitization u v
  have h1 : ‖γ.unitization (star u * u)‖ ≤ N * ‖y‖ ^ 2 := by
    simp only [u, star_star, ← Unitization.inr_star, ← Unitization.inr_mul, unitization_apply_inr]
    calc ‖γ (y * star y)‖ ≤ N * ‖y * star y‖ := (γ : A →L[ℂ] ℂ).le_opNorm _
      _ = N * ‖y‖ ^ 2 := by rw [CStarRing.norm_self_mul_star, sq]
  have hval : γ.unitization (star v * v) = N - γ e - γ e + γ (e * e) := by
    have hv : star v * v =
        1 - (e : Unitization ℂ A) - e + ((e * e : A) : Unitization ℂ A) := by
      simp only [v, star_sub, star_one, ← Unitization.inr_star, he.star_eq, Unitization.inr_mul]
      noncomm_ring
    rw [hv, map_add, map_sub, map_sub, unitization_apply_one, unitization_apply_inr,
      unitization_apply_inr]
  have hnn : 0 ≤ γ.unitization (star v * v) := γ.unitization.map_nonneg (star_mul_self_nonneg v)
  have hee : (γ (e * e)).re ≤ (γ e).re :=
    (Complex.le_def.mp (γ.mono (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he he1))).1
  have h2 : ‖γ.unitization (star v * v)‖ ≤ N - (γ e).re := by
    rw [← Complex.re_eq_norm.mpr hnn, hval]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    linarith
  rw [hkey]
  calc ‖γ.unitization (star u * v)‖ ^ 2
      ≤ ‖γ.unitization (star u * u)‖ * ‖γ.unitization (star v * v)‖ := hcs
    _ ≤ (N * ‖y‖ ^ 2) * (N - (γ e).re) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = N * (N - (γ e).re) * ‖y‖ ^ 2 := by ring

/-- The left-hand version of `norm_apply_sub_apply_mul_sq_le`:
`‖γ y - γ (e y)‖² ≤ ‖γ‖ (‖γ‖ - Re γ e) ‖y‖²` for a positive contraction `e`. -/
theorem norm_apply_sub_apply_mul_left_sq_le (γ : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (y : A) :
    ‖γ y - γ (e * y)‖ ^ 2 ≤
      ‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re) * ‖y‖ ^ 2 := by
  have h := norm_apply_sub_apply_mul_sq_le γ he he1 (star y)
  have hs : star y * e = star (e * y) := by rw [star_mul, he.star_eq]
  rwa [hs, map_star, map_star, ← star_sub, norm_star, norm_star] at h

/-- The two-sided version of `norm_apply_sub_apply_mul_sq_le`:
`‖γ y - γ (e y e)‖ ≤ 2 √(‖γ‖ (‖γ‖ - Re γ e)) ‖y‖` for a positive contraction `e`. -/
theorem norm_apply_sub_apply_mul_mul_le (γ : A →P[ℂ] ℂ) {e : A} (he : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (y : A) :
    ‖γ y - γ (e * y * e)‖ ≤
      2 * Real.sqrt (‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re)) * ‖y‖ := by
  set c := ‖(γ : A →L[ℂ] ℂ)‖ * (‖(γ : A →L[ℂ] ℂ)‖ - (γ e).re)
  have h1 := norm_le_sqrt_mul_of_sq_le (norm_apply_sub_apply_mul_left_sq_le γ he he1 y)
  have h2 := norm_le_sqrt_mul_of_sq_le (norm_apply_sub_apply_mul_sq_le γ he he1 (e * y))
  have hey : ‖e * y‖ ≤ ‖y‖ := (norm_mul_le e y).trans (mul_le_of_le_one_left (norm_nonneg y) he1)
  calc ‖γ y - γ (e * y * e)‖ ≤ ‖γ y - γ (e * y)‖ + ‖γ (e * y) - γ (e * y * e)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt c * ‖y‖ + Real.sqrt c * ‖y‖ :=
        add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hey (Real.sqrt_nonneg c)))
    _ = 2 * Real.sqrt c * ‖y‖ := by ring

section Ideal

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

omit [StarOrderedRing A] in
/-- A functional of norm at most one restricting to a functional of norm one on a closed ideal has
norm one. -/
theorem norm_eq_one_of_apply_coe_eq {τ : I →P[ℂ] ℂ} (hτ : ‖(τ : I →L[ℂ] ℂ)‖ = 1)
    {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ 1) (h : ∀ c : I, γ c = τ c) :
    ‖(γ : A →L[ℂ] ℂ)‖ = 1 := by
  refine le_antisymm hγ (hτ ▸ ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun c ↦ ?_)
  change ‖τ c‖ ≤ ‖(γ : A →L[ℂ] ℂ)‖ * ‖(c : A)‖
  rw [← h c]
  exact (γ : A →L[ℂ] ℂ).le_opNorm (c : A)

/-- **The extension formula.** If `γ` is a positive functional of norm at most one on `A` that
restricts to a functional `τ` of norm one on a closed ideal `I`, then `γ(a) = lim_e γ(eae)` along
every increasing approximate unit `e` of `I`. See `tendsto_apply_mul_mul_of_apply_coe_eq'` for the
same limit written with `τ`. -/
theorem tendsto_apply_mul_mul_of_apply_coe_eq {τ : I →P[ℂ] ℂ} (hτ : ‖(τ : I →L[ℂ] ℂ)‖ = 1)
    {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ 1) (h : ∀ c : I, γ c = τ c) {l : Filter I}
    (hl : l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e : I ↦ γ ((e : A) * a * e)) l (𝓝 (γ a)) := by
  have hN := norm_eq_one_of_apply_coe_eq hτ hγ h
  have hlim : Tendsto (fun e : I ↦ 2 * Real.sqrt (1 * (1 - (τ e).re)) * ‖a‖) l (𝓝 0) := by
    have hre : Tendsto (fun e : I ↦ (τ e).re) l (𝓝 1) := by
      have := (Complex.continuous_re.tendsto _).comp (τ.tendsto_nhds_opNorm hl)
      rw [hτ] at this
      simpa [Function.comp_def] using this
    have := ((((hre.const_sub 1).const_mul 1).sqrt).const_mul 2).mul_const ‖a‖
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he he1
  rw [norm_sub_rev, ← hN, ← h e]
  exact norm_apply_sub_apply_mul_mul_le γ (e := (e : A)) he he1 a

/-- **The extension formula**, written with `τ`: `γ(a) = lim_e τ(eae)` along every increasing
approximate unit `e` of `I`. -/
theorem tendsto_apply_mul_mul_of_apply_coe_eq' {τ : I →P[ℂ] ℂ} (hτ : ‖(τ : I →L[ℂ] ℂ)‖ = 1)
    {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ 1) (h : ∀ c : I, γ c = τ c) {l : Filter I}
    (hl : l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e : I ↦ τ ⟨(e : A) * a * e, I.mul_mul_mem e.property a⟩) l (𝓝 (γ a)) :=
  (tendsto_apply_mul_mul_of_apply_coe_eq hτ hγ h hl a).congr fun e ↦
    h ⟨_, I.mul_mul_mem e.property a⟩

/-- **Uniqueness of the extension.** Two positive functionals of norm at most one on `A` that
restrict to the same functional of norm one on a closed ideal are equal. -/
theorem eq_of_apply_coe_eq {τ : I →P[ℂ] ℂ} (hτ : ‖(τ : I →L[ℂ] ℂ)‖ = 1) {γ₁ γ₂ : A →P[ℂ] ℂ}
    (hγ₁ : ‖(γ₁ : A →L[ℂ] ℂ)‖ ≤ 1) (hγ₂ : ‖(γ₂ : A →L[ℂ] ℂ)‖ ≤ 1) (h₁ : ∀ c : I, γ₁ c = τ c)
    (h₂ : ∀ c : I, γ₂ c = τ c) : γ₁ = γ₂ := by
  have hl := CStarAlgebra.increasingApproximateUnit (A := I)
  have := hl.neBot
  exact ext fun a ↦ tendsto_nhds_unique (tendsto_apply_mul_mul_of_apply_coe_eq' hτ hγ₁ h₁ hl a)
    (tendsto_apply_mul_mul_of_apply_coe_eq' hτ hγ₂ h₂ hl a)

/-- **Existence of the extension.** Every positive functional of norm one on a closed ideal `I` of
`A` is the restriction of a positive functional of norm one on `A`. -/
theorem exists_apply_coe_eq {τ : I →P[ℂ] ℂ} (hτ : ‖(τ : I →L[ℂ] ℂ)‖ = 1) :
    ∃ γ : A →P[ℂ] ℂ, ‖(γ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ c : I, γ c = τ c := by
  let f := Unitization.starMap I.starAlgHom
  have hτ' : StrongDual.toWeakDual (τ.unitization : Unitization ℂ I →L[ℂ] ℂ) ∈
      TauCeti.stateSpace (Unitization ℂ I) := by
    rw [toWeakDual_mem_stateSpace_iff, norm_unitization, hτ]
  obtain ⟨φ, hφ, hφτ⟩ := TauCeti.surjOn_pullbackFunctional_stateSpace f
    (Unitization.starMap_injective I.starAlgHom_injective) hτ'
  obtain ⟨ω, hω1, hωφ⟩ := TauCeti.mem_stateSpace_iff_exists_positiveLinearMap.mp hφ
  let γ : A →P[ℂ] ℂ := (ofClass ω).comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A))
  have hγ : ∀ c : I, γ c = τ c := fun c ↦ by
    have h1 := DFunLike.congr_fun hφτ (c : Unitization ℂ I)
    have h2 := DFunLike.congr_fun hωφ (f (c : Unitization ℂ I))
    simp only [TauCeti.pullbackFunctional_apply, StrongDual.toWeakDual_apply] at h1 h2
    rw [← h2] at h1
    simpa [γ, f] using h1
  refine ⟨γ, norm_eq_one_of_apply_coe_eq hτ ?_ hγ, hγ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a ↦ ?_
  have := (ofClass ω : Unitization ℂ A →L[ℂ] ℂ).le_opNorm (a : Unitization ℂ A)
  rw [hω1, one_mul, Unitization.norm_inr] at this
  change ‖(ofClass ω : Unitization ℂ A →L[ℂ] ℂ) (a : Unitization ℂ A)‖ ≤ 1 * ‖a‖
  rwa [one_mul]

/-- **The extension of a tracial state is tracial.** If a positive functional `γ` of norm at most
one on `A` restricts to a tracial state of a closed ideal `I`, then `γ` is a tracial state. Only
the traciality of `τ` on `I` enters: `γ(a a⋆) = lim_e τ((ea)(ea)⋆) = lim_e γ(a⋆ e² a) ≤ γ(a⋆ a)`. -/
theorem isTracialState_of_apply_coe_eq {τ : I →P[ℂ] ℂ} (hτ : τ.IsTracialState)
    {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ 1) (h : ∀ c : I, γ c = τ c) :
    γ.IsTracialState := by
  have hτ1 := hτ.norm_eq_one
  have hN := norm_eq_one_of_apply_coe_eq hτ1 hγ h
  have hl := CStarAlgebra.increasingApproximateUnit (A := I)
  have := hl.neBot
  -- `Re γ(a a⋆) ≤ Re γ(a⋆ a)`
  have hle : ∀ a : A, (γ (a * star a)).re ≤ (γ (star a * a)).re := fun a ↦ by
    have hlim := (Complex.continuous_re.tendsto _).comp
      (tendsto_apply_mul_mul_of_apply_coe_eq hτ1 hγ h hl (a * star a))
    refine le_of_tendsto hlim ?_
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he he1
    have he' : 0 ≤ (e : A) := he
    have he1' : ‖(e : A)‖ ≤ 1 := he1
    let x : I := ⟨(e : A) * a, I.mul_mem_right _ _ e.property⟩
    have hx : γ ((e : A) * (a * star a) * e) = γ (star a * ((e : A) * e) * a) := by
      have h1 : (e : A) * (a * star a) * e = ((x * star x : I) : A) := by
        change _ = (e : A) * a * star ((e : A) * a)
        rw [star_mul, he'.star_eq]; noncomm_ring
      have h2 : star a * ((e : A) * e) * a = ((star x * x : I) : A) := by
        change _ = star ((e : A) * a) * ((e : A) * a)
        rw [star_mul, he'.star_eq]; noncomm_ring
      rw [h1, h2, h, h, hτ.map_mul_comm]
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
  refine isTracialState_iff_map_star_mul_self.mpr ⟨hN, fun a ↦ Complex.ext ?_ ?_⟩
  · simpa using le_antisymm (by simpa using hle (star a)) (hle a)
  · rw [← (Complex.le_def.mp (γ.map_nonneg (star_mul_self_nonneg a))).2,
      ← (Complex.le_def.mp (γ.map_nonneg (mul_star_self_nonneg a))).2]

/-- **Extension of tracial states from closed ideals.** A tracial state `τ` of a closed ideal `I`
of `A` is the restriction of exactly one state of `A`; that state is tracial
(`isTracialState_of_apply_coe_eq`) and given by `lim_e τ(eae)` along every increasing approximate
unit of `I` (`tendsto_apply_mul_mul_of_apply_coe_eq'`). -/
theorem IsTracialState.existsUnique_apply_coe_eq {τ : I →P[ℂ] ℂ} (hτ : τ.IsTracialState) :
    ∃! γ : A →P[ℂ] ℂ, ‖(γ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ c : I, γ c = τ c := by
  obtain ⟨γ, hγ, h⟩ := exists_apply_coe_eq hτ.norm_eq_one
  exact ⟨γ, ⟨hγ, h⟩, fun γ' ⟨hγ', h'⟩ ↦
    eq_of_apply_coe_eq hτ.norm_eq_one hγ'.le hγ.le h' h⟩

/-- **Extension of tracial states from closed ideals.** Every tracial state of a closed ideal `I`
of `A` extends uniquely to a tracial state of `A`. -/
theorem IsTracialState.existsUnique_isTracialState_apply_coe_eq {τ : I →P[ℂ] ℂ}
    (hτ : τ.IsTracialState) : ∃! γ : A →P[ℂ] ℂ, γ.IsTracialState ∧ ∀ c : I, γ c = τ c := by
  obtain ⟨γ, ⟨hγ, h⟩, huniq⟩ := hτ.existsUnique_apply_coe_eq
  exact ⟨γ, ⟨isTracialState_of_apply_coe_eq hτ hγ.le h, h⟩, fun γ' ⟨hγ', h'⟩ ↦
    huniq γ' ⟨hγ'.norm_eq_one, h'⟩⟩

end Ideal

end PositiveContinuousLinearMap
