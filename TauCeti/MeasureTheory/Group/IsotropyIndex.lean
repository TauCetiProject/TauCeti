/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

## Main results

* `TauCeti.setIntegral_smul_set`, `TauCeti.integrableOn_smul_set_iff`: an integrand invariant
  under `g` has the same integral, and the same integrability, on `g • V` as on `V`.
* `TauCeti.setIntegral_iUnion_smul_eq_index_smul`: the integral over `⋃ g, g • V` is
  `H.index` times the integral over `V`.
* `TauCeti.inv_card_smul_setIntegral_iUnion_smul`: the weighted form
  `|G|⁻¹ ∫_{⋃ g, g • V} f = |H|⁻¹ ∫_V f` for a finite group.
* `TauCeti.addHaar_preimage_smul_of_isOfFinOrder`: an element of finite order acting linearly
  on a finite-dimensional real space preserves every additive Haar measure.
* `TauCeti.smulInvariantMeasure_addHaar`: a finite group acting linearly preserves every
  additive Haar measure.
* `TauCeti.inv_card_smul_setIntegral_iUnion_smul_addHaar`: the weighted formula for a finite
  linear action and an additive Haar measure.
-/

public section

open Function MeasureTheory Set

open scoped Pointwise

namespace TauCeti

section Index

variable {G α E : Type*} [Group G] [MulAction G α]

/-- The translates of `V` by the canonical coset representatives cover `⋃ g, g • V`, when `H`
maps `V` onto itself. -/
private theorem iUnion_out_smul_eq {H : Subgroup G} {V : Set α} (hH : ∀ h ∈ H, h • V = V) :
    ⋃ q : G ⧸ H, (q.out : G) • V = ⋃ g : G, g • V := by
  refine subset_antisymm (iUnion_subset fun q => subset_iUnion (fun g : G => g • V) _) ?_
  refine iUnion_subset fun g => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  -- `g = out * h⁻¹`, and `h⁻¹` maps `V` onto itself.
  have hg : g • V = ((g : G ⧸ H).out : G) • V := by
    rw [hh, mul_smul, hH _ h.2]
  exact hg ▸ subset_iUnion (fun q : G ⧸ H => (q.out : G) • V) _

/-- Translates of `V` by distinct coset representatives are disjoint, when every `g ∉ H` moves
`V` off itself. -/
private theorem pairwise_disjoint_out_smul {H : Subgroup G} {V : Set α}
    (hdisj : ∀ g ∉ H, Disjoint (g • V) V) :
    Pairwise (Disjoint on (fun q : G ⧸ H => (q.out : G) • V)) := by
  intro q q' hqq'
  have hmem : ((q'.out : G))⁻¹ * q.out ∉ H := fun hm => by
    have h := (QuotientGroup.eq (s := H) (a := q'.out) (b := q.out)).2 hm
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    exact hqq' h.symm
  have := (Set.disjoint_smul_set (a := (q'.out : G))).2 (hdisj _ hmem)
  rwa [smul_smul, mul_inv_cancel_left] at this

variable [MeasurableSpace α] [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  [NormedAddCommGroup E]

/-- For an invariant measure, an integrand invariant under `g` is integrable on `g • V` exactly
when it is integrable on `V`. -/
theorem integrableOn_smul_set_iff {g : G} {f : α → E} (hf : ∀ x, f (g • x) = f x)
    (V : Set α) : IntegrableOn f (g • V) μ ↔ IntegrableOn f V μ := by
  rw [← image_smul, (measurePreserving_smul g μ).integrableOn_image
    (measurableEmbedding_const_smul g)]
  exact iff_of_eq (congrArg (IntegrableOn · V μ) (funext hf))

variable [NormedSpace ℝ E]

/-- For an invariant measure, an integrand invariant under `g` has the same integral over
`g • V` as over `V`. No integrability or measurability hypothesis is needed. -/
theorem setIntegral_smul_set {g : G} {f : α → E} (hf : ∀ x, f (g • x) = f x)
    (V : Set α) : ∫ x in g • V, f x ∂μ = ∫ x in V, f x ∂μ := by
  rw [← image_smul, (measurePreserving_smul g μ).setIntegral_image_emb
    (measurableEmbedding_const_smul g) f V]
  simp_rw [hf]

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
  · rw [← iUnion_out_smul_eq hH, integral_iUnion_fintype (fun q => hV.const_smul _)
      (pairwise_disjoint_out_smul hdisj) fun q => (integrableOn_smul_set_iff (hf _) V).2 hfV]
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
    ← H.card_mul_index, Nat.cast_mul, mul_inv, mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 H.index_ne_zero_of_finite), mul_one]

end Index

section Linear

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- An element of finite order acting linearly on a finite-dimensional real space preserves
every additive Haar measure. Its determinant has finite order in `ℝ`, hence absolute value
one. -/
theorem addHaar_preimage_smul_of_isOfFinOrder [Monoid G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] {g : G} (hg : IsOfFinOrder g) (s : Set E) :
    μ ((g • ·) ⁻¹' s) = μ s := by
  set L := DistribMulAction.toModuleEnd ℝ E g
  have habs : |LinearMap.det L| = 1 :=
    ((((absHom (α := ℝ)).toMonoidHom).comp
      (LinearMap.det.comp (DistribMulAction.toModuleEnd ℝ E))).isOfFinOrder hg).eq_one
      (abs_nonneg _)
  have hdet : LinearMap.det L ≠ 0 := fun h => by simp [h] at habs
  have h := Measure.addHaar_preimage_linearMap μ hdet s
  rwa [abs_inv, habs, inv_one, ENNReal.ofReal_one, one_mul] at h

/-- A finite group acting linearly on a finite-dimensional real space preserves every additive
Haar measure. -/
theorem smulInvariantMeasure_addHaar [Group G] [Finite G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] : SMulInvariantMeasure G E μ :=
  ⟨fun g s _ => addHaar_preimage_smul_of_isOfFinOrder μ (isOfFinOrder_of_finite g) s⟩

/-- Every linear action on a finite-dimensional real space has measurable translations. -/
theorem measurableConstSMul_of_finiteDimensional [Monoid G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] : MeasurableConstSMul G E :=
  ⟨fun g => (LinearMap.continuous_of_finiteDimensional
    (DistribMulAction.toModuleEnd ℝ E g)).measurable⟩

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
  inv_card_smul_setIntegral_iUnion_smul hV hH hdisj hf

end Linear

end TauCeti
