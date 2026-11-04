/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.MeasureTheory.Group.Action
public import TauCeti.MeasureTheory.Group.Integral
public import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The isotropy-index formula for averaged integrals over finite actions

The local integral over a finite quotient chart `U/G` is `|G|⁻¹ ∫_U`, counted with the full
group `G`, including any elements that act trivially. Shrinking the chart around a point
replaces `G` by the subgroup `H` preserving a smaller piece `V`, and the two normalizations
must agree. This file proves that agreement for an invariant measure and an invariant integrand.

Suppose `H ≤ G` has finite index, `H` maps `V` onto itself, and every `g ∉ H` moves `V` off
itself. Then the translates `g • V` are indexed by the cosets `G ⧸ H` and are pairwise
disjoint, so the integral over `⋃ g, g • V` is `[G : H]` times the integral over `V`. When `G` is
finite, `|G| = |H| [G : H]` turns this into the weighted form
`|G|⁻¹ ∫_{⋃ g, g • V} f = |H|⁻¹ ∫_V f`.

In a linearizing chart the group acts linearly on a finite-dimensional real vector space. An
element of finite order acts there by a linear map whose determinant has finite order in `ℝ`,
hence absolute value one, so it preserves every additive Haar measure. Finite linear actions
therefore satisfy the invariance hypothesis for Lebesgue measure. No faithfulness assumption is
made anywhere: the ineffective kernel stays in `G`, in `H`, and in both weights.

The covering and disjointness of the translates by coset representatives are
`QuotientGroup.iUnion_out_smul_eq` and `QuotientGroup.pairwise_disjoint_out_smul`; the invariance
of a translated set integral is `TauCeti.setIntegral_smul_set`; and the invariance of additive
Haar measure under finite linear actions is `MeasureTheory.Measure.smulInvariantMeasure_addHaar`.

## Main results

* `TauCeti.setIntegral_iUnion_smul_eq_index_smul`: the integral over `⋃ g, g • V` is
  `H.index` times the integral over `V`.
* `TauCeti.inv_card_smul_setIntegral_iUnion_smul`: the weighted form
  `|G|⁻¹ ∫_{⋃ g, g • V} f = |H|⁻¹ ∫_V f` for a finite group.
* `MeasureTheory.Measure.inv_card_smul_setIntegral_iUnion_smul_addHaar`: the weighted formula
  for a finite linear action and an additive Haar measure.
-/

public section

open MeasureTheory Set

open scoped Pointwise

namespace TauCeti

section Index

variable {G α E : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
  {μ : Measure α} [SMulInvariantMeasure G α μ] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The isotropy-index formula.** Let `H ≤ G` have finite index, map `V` onto itself, and be
exactly the set of elements not moving `V` off itself. For a `G`-invariant measure and a
`G`-invariant integrand, the integral over `⋃ g, g • V` is `[G : H]` times the integral over
`V`. No integrability hypothesis is needed: both sides vanish together. -/
theorem setIntegral_iUnion_smul_eq_index_smul {H : Subgroup G} [H.FiniteIndex] {V : Set α}
    (hV : MeasurableSet V) (hH : ∀ h ∈ H, h • V = V) (hdisj : ∀ g ∉ H, Disjoint (g • V) V)
    {f : α → E} (hf : ∀ (g : G) x, f (g • x) = f x) :
    ∫ x in ⋃ g : G, g • V, f x ∂μ = H.index • ∫ x in V, f x ∂μ := by
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  by_cases hfV : IntegrableOn f V μ
  · rw [← QuotientGroup.iUnion_out_smul_eq hH,
      integral_iUnion_fintype (fun q => hV.const_smul _)
        (QuotientGroup.pairwise_disjoint_out_smul hdisj)
        fun q => (integrableOn_smul_set_iff (hf _) V).2 hfV]
    simp_rw [setIntegral_smul_set (hf _)]
    rw [Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
  · -- Without integrability on `V`, the larger union is not integrable either.
    have hfU : ¬IntegrableOn f (⋃ g : G, g • V) μ := fun hU =>
      hfV (hU.mono_set (subset_iUnion_of_subset 1 (by rw [one_smul])))
    rw [integral_undef hfU, integral_undef hfV, smul_zero]

/-- **The weighted isotropy-index formula.** For a finite group `G` and `H ≤ G` mapping `V`
onto itself while every `g ∉ H` moves `V` off itself, the chart integral weighted by `|G|⁻¹`
over `⋃ g, g • V` equals the integral over `V` weighted by `|H|⁻¹`. Both weights count every
group element, including those acting trivially. -/
theorem inv_card_smul_setIntegral_iUnion_smul [Finite G] {H : Subgroup G} {V : Set α}
    (hV : MeasurableSet V) (hH : ∀ h ∈ H, h • V = V) (hdisj : ∀ g ∉ H, Disjoint (g • V) V)
    {f : α → E} (hf : ∀ (g : G) x, f (g • x) = f x) :
    (Nat.card G : ℝ)⁻¹ • ∫ x in ⋃ g : G, g • V, f x ∂μ =
      (Nat.card H : ℝ)⁻¹ • ∫ x in V, f x ∂μ := by
  rw [setIntegral_iUnion_smul_eq_index_smul hV hH hdisj hf, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    ← H.card_mul_index]
  have : (H.index : ℝ) ≠ 0 := Nat.cast_ne_zero.2 H.index_ne_zero_of_finite
  congr 1
  push_cast
  field_simp

end Index

end TauCeti

namespace MeasureTheory.Measure

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The weighted isotropy-index formula in a linear chart.** For a finite group acting
linearly on a finite-dimensional real space and an additive Haar measure, the chart integral
weighted by `|G|⁻¹` over `⋃ g, g • V` equals the integral over `V` weighted by `|H|⁻¹`, when
`H` maps `V` onto itself and every `g ∉ H` moves `V` off itself. -/
theorem inv_card_smul_setIntegral_iUnion_smul_addHaar {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [Group G] [Finite G] [DistribMulAction G E] [SMulCommClass G ℝ E]
    {H : Subgroup G} {V : Set E} (hV : MeasurableSet V) (hH : ∀ h ∈ H, h • V = V)
    (hdisj : ∀ g ∉ H, Disjoint (g • V) V) {f : E → F} (hf : ∀ (g : G) x, f (g • x) = f x) :
    (Nat.card G : ℝ)⁻¹ • ∫ x in ⋃ g : G, g • V, f x ∂μ =
      (Nat.card H : ℝ)⁻¹ • ∫ x in V, f x ∂μ :=
  have := smulInvariantMeasure_addHaar (G := G) μ
  have := measurableConstSMul_of_finiteDimensional (G := G) (E := E)
  TauCeti.inv_card_smul_setIntegral_iUnion_smul hV hH hdisj hf

end MeasureTheory.Measure
