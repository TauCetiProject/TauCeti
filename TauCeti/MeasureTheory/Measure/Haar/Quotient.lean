/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Quotient
public import TauCeti.Topology.Algebra.InfiniteSum.Automorphize
-- Proof-only: uniqueness of Haar measures on a compact group.
import Mathlib.MeasureTheory.Measure.Haar.Unique
-- Proof-only: fundamental domains have finite measure when the quotient is compact.
import TauCeti.MeasureTheory.Group.FundamentalDomain.Compact
-- Proof-only: a group with a finite Haar measure is compact.
import TauCeti.MeasureTheory.Group.Measure

/-!
# Weil's formula

Let `μ` be a right-invariant measure on a group `G`, let the right action of a countable
subgroup `Γ` on `G` have a fundamental domain, and let `ν` be the quotient measure on `G ⧸ Γ`.
**Weil's formula** unfolds an integral over `G` into an integral over `G ⧸ Γ` of the sum over
each coset: `∫ f dμ = ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν(g Γ)`.

Mathlib proves this for integrable functions with values in a normed space
(`QuotientGroup.integral_eq_integral_automorphize`). This file gives the companion statement
for nonnegative measurable functions with values in `ℝ≥0∞`, which needs no integrability
hypothesis.

It then normalises the formula when `G ⧸ Γ` is a compact group. Let `Γ` be a countable normal
subgroup of a locally compact group `G`, let `μ` be left invariant, invariant under right
multiplication by `Γ` and finite on compact sets, and let `𝓕` be a fundamental domain for the
right action of `Γ`. The image of `μ` restricted to `𝓕` is left invariant on `G ⧸ Γ`, and when
`G ⧸ Γ` carries a Haar probability measure `ν` it is `μ 𝓕 • ν`. So, for `μ` also right invariant,
the mean over `G ⧸ Γ` of the sum of an integrable function `f` over the cosets is
`(μ 𝓕)⁻¹ ∫ f dμ`. For an abelian group `G` this is the formula for the mean of the periodic
function `x ↦ ∑_{γ ∈ Γ} f (x + γ)`, which turns Fourier coefficients of periodisations on `G ⧸ Γ`
into integrals over `G`.

## Main results

* `MulAction.lintegral_eq_lintegral_automorphize`: Weil's formula for nonnegative measurable
  functions, for an invariant measure under a countable group action with a fundamental domain.
* `QuotientGroup.lintegral_eq_lintegral_automorphize`: Weil's formula for nonnegative measurable
  functions on a group and its quotient `G ⧸ Γ`.
* `MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_quotientMeasure`: for a normal subgroup
  and a left invariant measure invariant under right multiplication by `Γ`, the quotient measure
  of a fundamental domain is left invariant.
* `MeasureTheory.IsFundamentalDomain.quotientMeasure_eq_smul`: it is `μ 𝓕` times any Haar
  probability measure on `G ⧸ Γ`.
* `MeasureTheory.IsFundamentalDomain.integral_eq_measureReal_smul_integral_automorphize`:
  `∫ f dμ = μ 𝓕 • ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν`.
* `MeasureTheory.IsFundamentalDomain.integral_eq_inv_measureReal_smul_integral_of_hasSum`: the
  mean of `Φ (g Γ) = ∑_{γ ∈ Γ} f (g γ)` over `G ⧸ Γ` is `(μ 𝓕)⁻¹ • ∫ f dμ`.

Each of the last four has an additive version (`IsAddFundamentalDomain.addQuotientMeasure_eq_smul`
and so on).

## Provenance

The mean over a compact quotient is adapted from `New.quotMean_tsum_eq_integral` and
`New.average_quotMeasure_eq_quotMean` (file `src/Lib/Adelic/QuotientMeasure/Basic.lean`) in
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). There
the group is abelian and the quotient integral is taken against a cutoff weight; here `Γ` is a
normal subgroup with a fundamental domain, and the proofs, through Mathlib's unfolding
`QuotientGroup.integral_eq_integral_automorphize` and uniqueness of Haar measure on the compact
group `G ⧸ Γ`, are new.

## References

* N. Bourbaki, *Intégration*, chapitre VII, §2, Hermann, 1963.
* A. Deitmar, S. Echterhoff, *Principles of Harmonic Analysis*, 2nd ed., Springer, 2014, §1.5.
-/

public section

open MeasureTheory

open scoped ENNReal

/-- **Weil's formula** for nonnegative measurable functions on a space with a group action. Let `μ`
be a measure on `α` invariant under a countable group `G` whose action has a fundamental domain,
and let `ν` be the quotient measure on the orbit space. Then the integral of `f` over `α` is the
integral over the orbit space of the sum of `f` over each orbit, `MulAction.automorphize f`. -/
@[to_additive /-- **Weil's formula** for nonnegative measurable functions on a space with an
additive group action. Let `μ` be a measure on `α` invariant under a countable additive group `G`
whose action has a fundamental domain, and let `ν` be the quotient measure on the orbit space.
Then the integral of `f` over `α` is the integral over the orbit space of the sum of `f` over each
orbit, `AddAction.automorphize f`. -/]
theorem MulAction.lintegral_eq_lintegral_automorphize {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] [Countable G] [MeasurableConstSMul G α] {μ : Measure α}
    [SMulInvariantMeasure G α μ] [HasFundamentalDomain G α μ]
    (ν : Measure (Quotient (orbitRel G α))) [QuotientMeasureEqMeasurePreimage μ ν]
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ∫⁻ x, automorphize f x ∂ν := by
  obtain ⟨s, hs⟩ := ‹HasFundamentalDomain G α μ›.ExistsIsFundamentalDomain
  have hmeas : Measurable (automorphize f : Quotient (orbitRel G α) → ℝ≥0∞) := by
    refine measurable_from_quotient.mpr ?_
    simp only [Function.comp_def, Quotient.mk''_eq_mk, automorphize_mk]
    exact Measurable.tsum fun g ↦ hf.comp (measurable_const_smul g)
  rw [← (hs.measurePreserving_quotient_mk ν).lintegral_comp hmeas, hs.lintegral_eq_tsum'' f]
  simp only [automorphize_mk]
  exact (lintegral_tsum fun g ↦ (hf.comp (measurable_const_smul g)).aemeasurable).symm

/-- **Weil's formula** for nonnegative measurable functions. Let `μ` be a right-invariant measure
on `G`, let the right action of a countable subgroup `Γ` on `G` have a fundamental domain, and let
`ν` be the quotient measure on `G ⧸ Γ`. Then `∫ f dμ = ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν(g Γ)`; the
inner sum is `QuotientGroup.automorphize f`, which is constant on each left coset `g Γ`. This is
the nonnegative companion of Mathlib's `QuotientGroup.integral_eq_integral_automorphize`. -/
@[to_additive /-- **Weil's formula** for nonnegative measurable functions on an additive group.
Let `μ` be a right-invariant measure on `G`, let the action of a countable subgroup `Γ` on `G` by
right addition have a fundamental domain, and let `ν` be the quotient measure on `G ⧸ Γ`. Then the
integral of `f` over `G` is the integral over `G ⧸ Γ` of `QuotientAddGroup.automorphize f`. This
is the nonnegative companion of Mathlib's `QuotientAddGroup.integral_eq_integral_automorphize`. -/]
theorem QuotientGroup.lintegral_eq_lintegral_automorphize {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableConstSMul Gᵐᵒᵖ G] {Γ : Subgroup G} [Countable Γ]
    {μ : Measure G} [μ.IsMulRightInvariant] [HasFundamentalDomain Γ.op G μ]
    (ν : Measure (G ⧸ Γ)) [QuotientMeasureEqMeasurePreimage μ ν] {f : G → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ g, f g ∂μ = ∫⁻ x, automorphize f x ∂ν := by
  -- `QuotientGroup.automorphize` is by definition `MulAction.automorphize` for the right action
  -- of `Γ.op`, and `G ⧸ Γ` is by definition the orbit quotient of that action.
  exact MulAction.lintegral_eq_lintegral_automorphize (G := Γ.op) ν hf

/-! ### The mean over a compact quotient -/

section CompactQuotient

open Set MeasureTheory.Measure

open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {Γ : Subgroup G} [Γ.Normal] [Countable Γ] [MeasurableSpace (G ⧸ Γ)]
  [BorelSpace (G ⧸ Γ)] {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G}

namespace MeasureTheory.IsFundamentalDomain

/-- Let `Γ` be a countable normal subgroup of `G`, let `μ` be a left invariant measure that is
invariant under right multiplication by `Γ`, and let `𝓕` be a fundamental domain for the right
action of `Γ`. The image of `μ` restricted to `𝓕` under the projection `G → G ⧸ Γ` is a left
invariant measure on the group `G ⧸ Γ`. -/
@[to_additive /-- Let `Γ` be a countable normal subgroup of `G`, let `μ` be a left invariant
measure that is invariant under right addition of `Γ`, and let `𝓕` be a fundamental domain for the
action of `Γ` by right addition. The image of `μ` restricted to `𝓕` under the projection
`G → G ⧸ Γ` is a left invariant measure on the additive group `G ⧸ Γ`. -/]
theorem isMulLeftInvariant_quotientMeasure [SMulInvariantMeasure Γ.op G μ]
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μ) :
    ((μ.restrict 𝓕).map (QuotientGroup.mk : G → G ⧸ Γ)).IsMulLeftInvariant := by
  have hmk : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk'.measurable
  refine ⟨QuotientGroup.mk_surjective.forall.2 fun g ↦ ?_⟩
  ext U hU
  set A := (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U
  -- the preimage of `U` is invariant under right multiplication by `Γ`
  have hA : ∀ γ : Γ.op, (fun x ↦ γ • x) ⁻¹' A = A := fun γ ↦ by
    ext x
    simp [A, Subgroup.smul_def, MulOpposite.smul_eq_mul_unop,
      QuotientGroup.mk_mul_of_mem x (Subgroup.mem_op.1 γ.property)]
  -- left multiplication by `g` moves `𝓕` to another fundamental domain `g • 𝓕`
  have hpre : (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' ((↑g * ·) ⁻¹' U) ∩ 𝓕 =
      (g * ·) ⁻¹' (A ∩ g • 𝓕) := by
    ext x
    simp [A, mem_smul_set_iff_inv_smul_mem]
  have hU' : MeasurableSet (((g : G ⧸ Γ) * ·) ⁻¹' U) := measurable_const_mul _ hU
  have hleft : ((μ.restrict 𝓕).map QuotientGroup.mk).map ((g : G ⧸ Γ) * ·) U =
      μ ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' (((g : G ⧸ Γ) * ·) ⁻¹' U) ∩ 𝓕) := by
    rw [map_apply (measurable_const_mul _) hU, map_apply hmk hU', restrict_apply (hmk hU')]
  have hright : (μ.restrict 𝓕).map QuotientGroup.mk U = μ (A ∩ 𝓕) := by
    rw [map_apply hmk hU, restrict_apply (hmk hU)]
  rw [hleft, hright, hpre, measure_preimage_mul]
  exact (h𝓕.smul_of_comm g).measure_set_eq h𝓕 (hmk hU) hA

variable [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]

/-- Let `Γ` be a countable normal subgroup of a locally compact group `G`, let `μ` be a left
invariant measure on `G`, finite on compact sets and invariant under right multiplication by `Γ`,
and let `𝓕` be a fundamental domain for the right action of `Γ`. If `ν` is a Haar probability
measure on `G ⧸ Γ`, then the image of `μ` restricted to `𝓕` under the projection is `μ 𝓕 • ν`. -/
@[to_additive addQuotientMeasure_eq_smul /-- Let `Γ` be a countable normal subgroup of a locally
compact additive group `G`, let `μ` be a left invariant measure on `G`, finite on compact sets and
invariant under right addition of `Γ`, and let `𝓕` be a fundamental domain for the action of `Γ`
by right addition. If `ν` is an additive Haar probability measure on `G ⧸ Γ`, then the image of
`μ` restricted to `𝓕` under the projection is `μ 𝓕 • ν`. -/]
theorem quotientMeasure_eq_smul [SMulInvariantMeasure Γ.op G μ]
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μ) (ν : Measure (G ⧸ Γ)) [ν.IsHaarMeasure]
    [IsProbabilityMeasure ν] :
    (μ.restrict 𝓕).map (QuotientGroup.mk : G → G ⧸ Γ) = μ 𝓕 • ν := by
  have hmk : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk'.measurable
  have : CompactSpace (G ⧸ Γ) := ν.compactSpace_of_isMulLeftInvariant_of_isFiniteMeasure
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.mpr h𝓕.measure_lt_top_of_compactSpace_quotientGroup.ne
  have := h𝓕.isMulLeftInvariant_quotientMeasure
  have h := isMulInvariant_eq_smul_of_compactSpace ((μ.restrict 𝓕).map QuotientGroup.mk) ν
  have huniv := congrArg (fun m : Measure (G ⧸ Γ) ↦ m univ) h
  rw [map_apply hmk MeasurableSet.univ, preimage_univ, restrict_apply_univ] at huniv
  rw [h, huniv]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Weil's formula over a compact quotient.** Let `μ` be a left and right invariant measure on
a locally compact group `G`, finite on compact sets, let `Γ` be a countable normal subgroup and
`𝓕` a fundamental domain for the right action of `Γ`, and let `ν` be a Haar probability measure on
`G ⧸ Γ`. For integrable `f`, `∫ f dμ = μ 𝓕 • ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν(g Γ)`. -/
@[to_additive integral_eq_measureReal_smul_integral_automorphize /-- **Weil's formula over a
compact quotient.** Let `μ` be a left and right invariant measure on a locally compact additive
group `G`, finite on compact sets, let `Γ` be a countable normal subgroup and `𝓕` a fundamental
domain for the action of `Γ` by right addition, and let `ν` be an additive Haar probability measure
on `G ⧸ Γ`. For integrable `f`, the integral of `f` is `μ 𝓕` times the integral of
`QuotientAddGroup.automorphize f` against `ν`. -/]
theorem integral_eq_measureReal_smul_integral_automorphize [μ.IsMulRightInvariant]
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μ) (ν : Measure (G ⧸ Γ)) [ν.IsHaarMeasure]
    [IsProbabilityMeasure ν] {f : G → E} (hf : Integrable f μ)
    (hf' : AEStronglyMeasurable (QuotientGroup.automorphize f) ν) :
    ∫ x, f x ∂μ = μ.real 𝓕 • ∫ q, QuotientGroup.automorphize f q ∂ν := by
  have hν := h𝓕.quotientMeasure_eq_smul ν
  rw [QuotientGroup.integral_eq_integral_automorphize h𝓕 hf (hν ▸ hf'.smul_measure _), hν,
    integral_smul_measure, measureReal_def]

/-- **The mean of a periodic function over a compact quotient.** Let `μ` be a nonzero left and
right invariant measure on a locally compact group `G`, finite on compact sets, let `Γ` be a
countable normal subgroup and `𝓕` a fundamental domain for the right action of `Γ`, and let `ν`
be the Haar probability measure on `G ⧸ Γ`. If `f` is integrable and `Φ` is an a.e. strongly
measurable function on `G ⧸ Γ` with `Φ (g Γ) = ∑_{γ ∈ Γ} f (g γ)` for every `g`, then the mean of
`Φ` is `(μ 𝓕)⁻¹ • ∫ f dμ`. -/
@[to_additive integral_eq_inv_measureReal_smul_integral_of_hasSum /-- **The mean of a periodic
function over a compact quotient.** Let `μ` be a nonzero left and right invariant measure on a
locally compact additive group `G`, finite on compact sets, let `Γ` be a countable normal subgroup
and `𝓕` a fundamental domain for the action of `Γ` by right addition, and let `ν` be the additive
Haar probability measure on `G ⧸ Γ`. If `f` is integrable and `Φ` is an a.e. strongly measurable
function on `G ⧸ Γ` with `Φ (g + Γ) = ∑_{γ ∈ Γ} f (g + γ)` for every `g`, then the mean of `Φ`
is `(μ 𝓕)⁻¹ • ∫ f dμ`. -/]
theorem integral_eq_inv_measureReal_smul_integral_of_hasSum [μ.IsMulRightInvariant]
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μ) (hμ : μ ≠ 0) (ν : Measure (G ⧸ Γ)) [ν.IsHaarMeasure]
    [IsProbabilityMeasure ν] {f : G → E} (hf : Integrable f μ) {Φ : G ⧸ Γ → E}
    (hΦ : AEStronglyMeasurable Φ ν) (hsum : ∀ g : G, HasSum (fun γ : Γ ↦ f (g * γ)) (Φ g)) :
    ∫ q, Φ q ∂ν = (μ.real 𝓕)⁻¹ • ∫ x, f x ∂μ := by
  -- `Φ` is the automorphization of `f`
  have hΦf : QuotientGroup.automorphize f = Φ := funext <| QuotientGroup.mk_surjective.forall.2
    fun g ↦ by
      -- `Subgroup.equivOp Γ` sends `γ : Γ` to `op γ : Γ.op`, which acts on `g` as `g * γ`
      have h : HasSum (fun γ : Γ.op ↦ f (γ • g)) (Φ g) :=
        (Subgroup.equivOp Γ).symm.hasSum_iff.mpr (hsum g)
      rw [QuotientGroup.automorphize_mk, h.tsum_eq]
  have : CompactSpace (G ⧸ Γ) := ν.compactSpace_of_isMulLeftInvariant_of_isFiniteMeasure
  have h𝓕₀ : μ.real 𝓕 ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨h𝓕.measure_ne_zero hμ, h𝓕.measure_lt_top_of_compactSpace_quotientGroup.ne⟩
  rw [h𝓕.integral_eq_measureReal_smul_integral_automorphize ν hf (hΦf ▸ hΦ), hΦf,
    inv_smul_smul₀ h𝓕₀]

end MeasureTheory.IsFundamentalDomain

end CompactQuotient
