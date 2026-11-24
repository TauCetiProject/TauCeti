/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.Space
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import TauCeti.Analysis.BoundedVariation.Compactness
import TauCeti.Analysis.BoundedVariation.W1p
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov

/-!
# Global `L¹` compactness of BV functions and sets of finite perimeter on bounded Lipschitz domains

Local compactness in `L¹_loc(Ω)` (`TauCeti.Analysis.BoundedVariation.Compactness`) holds on every
open subset `Ω` of a finite-dimensional real inner product space, without any assumption on the
boundary of `Ω`. Global compactness in `L¹(Ω)` fails on arbitrary bounded open sets (for instance on
a countable union of disjoint open intervals accumulating at `0`), because variations can vanish
while values jump freely across components.

On a bounded Lipschitz domain `Ω`, however, the Rellich–Kondrachov theorem makes the Sobolev value
projection `W^{1,1}(Ω) → L¹(Ω)` a compact operator
(`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`), and strict `W^{1,1}`
approximation transfers compactness from `W^{1,1}(Ω)` to `BV(Ω)`
(`TauCeti.BV.isCompactOperator_toL1CLM_iff_isCompactOperator_valueL`). Combined with the
domain-independent consequences of `IsCompactOperator BV.toL1CLM` in
`TauCeti.Analysis.BoundedVariation.Compactness` and isometric transport in
`TauCeti.Analysis.BoundedVariation.Isometry`, this file proves global `L¹(Ω)` compactness for
bounded Lipschitz domains with respect to any additive Haar measure `μ`:

* for bounded `IsLipschitzDomainWith` domains in the model space `WithLp 2 (ℝ × E)`;
* for bounded open sets in any finite-dimensional real inner product space `F` whose affine
  isometric image in the model space is `IsLipschitzDomainWith`;
* intrinsically for any bounded `(Ω : Set F).IsLipschitzDomain E`, together with the resulting
  global sequential compactness, total boundedness, and perimeter-compactness corollaries; and
* concretely for open Euclidean balls.

## Main declarations

* `TauCeti.BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith`,
  `TauCeti.BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith_image`, and
  `TauCeti.BV.isCompactOperator_toL1CLM_of_isLipschitzDomain`: global `L¹` compactness of `BV` on
  bounded Lipschitz domains.
* `TauCeti.BV.exists_subseq_tendsto_toL1_of_isLipschitzDomain`,
  `TauCeti.totallyBounded_of_setLIntegral_le_of_totalVariationOn_le_of_isLipschitzDomain`,
  `TauCeti.isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le_of_isLipschitzDomain`,
  `TauCeti.exists_subseq_tendsto_setLIntegral_enorm_sub_of_isLipschitzDomain`, and
  `TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_isLipschitzDomain`: global compactness
  corollaries on bounded Lipschitz domains.
* `TauCeti.BV.isCompactOperator_toL1CLM_ball`: compactness of `BV.toL1CLM` on open Euclidean balls.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.23 and Remark 3.24.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2.3,
  Theorem 4.
* W. P. Ziemer, *Weakly Differentiable Functions*, Corollary 5.3.4.
-/

public section

namespace TauCeti

open Bornology Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology symmDiff

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure (WithLp 2 (ℝ × E))} [μ.IsAddHaarMeasure]
  {L : ℝ≥0}

/-- **Global `L¹` compactness of `BV` on bounded Lipschitz domains of the model space.** If
`Ω ⊆ WithLp 2 (ℝ × E)` is a bounded Lipschitz domain with constant `L` and `μ` is an additive Haar
measure, the inclusion `BV.toL1CLM : BV μ Ω →L[ℝ] _` is a compact operator. -/
theorem BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith
    {Ω : Opens (WithLp 2 (ℝ × E))}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    IsCompactOperator (BV.toL1CLM (μ := μ) (Ω := Ω)) := by
  rw [Measure.isAddLeftInvariant_eq_smul μ volume]
  exact BV.isCompactOperator_toL1CLM_smul_measure _
    (BV.isCompactOperator_toL1CLM_iff_isCompactOperator_valueL.mpr
      (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb))

end ModelSpace

section Intrinsic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens F}

/-- **Global `L¹` compactness of `BV` on isometric copies of bounded Lipschitz domains.** Let
`f : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)` be an affine isometry equivalence and `Ω ⊆ F` a bounded open set
whose image `f '' Ω` is a Lipschitz domain with constant `L`. Then `BV.toL1CLM` on `Ω` is a
compact operator for every additive Haar measure `μ` on `F`. No inner-product,
finite-dimensionality, or measurability instances are assumed on `E`, as
`f.linearIsometryEquiv.symm` embeds `E` linearly and isometrically into `F`. -/
theorem BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith_image {L : ℝ≥0}
    (f : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hΩ : (f '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) :
    IsCompactOperator (BV.toL1CLM (μ := μ) (Ω := Ω)) := by
  rw [Measure.isAddLeftInvariant_eq_smul μ volume]
  exact BV.isCompactOperator_toL1CLM_smul_measure _
    (BV.isCompactOperator_toL1CLM_iff_isCompactOperator_valueL.mpr
      (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_image f hΩ hb))

/-- **Global `L¹` compactness of `BV` on bounded Lipschitz domains.** Let `F` be a
finite-dimensional real inner product space, `μ` an additive Haar measure on `F`, and `Ω ⊆ F` a
bounded open set satisfying the intrinsic Lipschitz-domain condition `(Ω : Set F).IsLipschitzDomain
E` for some normed tangential model space `E`. Then `BV.toL1CLM : BV μ Ω →L[ℝ] _` is a compact
operator.

No inner-product, finite-dimensionality, or measurability instances are assumed on `E`: when
`frontier Ω` is empty `closure Ω ⊆ Ω` is already compact, and when `frontier Ω` is nonempty any
boundary chart embeds `E` linearly and isometrically into `F`. -/
theorem BV.isCompactOperator_toL1CLM_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    IsCompactOperator (BV.toL1CLM (μ := μ) (Ω := Ω)) :=
  BV.isCompactOperator_toL1CLM_iff_isCompactOperator_valueL.mpr
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb)

/-- **Sequential `L¹` compactness for bounded sequences in `BV` on a bounded Lipschitz domain.** -/
theorem BV.exists_subseq_tendsto_toL1_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {u : ℕ → BV μ Ω} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : BV μ Ω) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => (u (φ k)).toL1) atTop (𝓝 v.toL1) ∧
      totalVariationOn μ Ω v ≤ liminf (fun k => totalVariationOn μ Ω (u (φ k))) atTop ∧
      ‖v‖ ≤ R :=
  BV.exists_subseq_tendsto_toL1_of_isCompactOperator
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hu

/-- **Global total boundedness in `L¹(Ω)` on a bounded Lipschitz domain.** A family `S` of
functions on a bounded Lipschitz domain `Ω` with `∫_Ω |u| ≤ M` and `|Du|(Ω) ≤ M` (`M < ∞`) gives a
totally bounded subset of `L¹(Ω)`. -/
theorem totallyBounded_of_setLIntegral_le_of_totalVariationOn_le_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {S : Set (F → ℝ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M)
    (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    TotallyBounded {f : Lp ℝ 1 (μ.restrict (Ω : Set F)) |
      ∃ u ∈ S, f =ᵐ[μ.restrict (Ω : Set F)] u} :=
  totallyBounded_of_isCompactOperator_toL1CLM
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hM hbdd hvar

/-- **Global relative compactness in `L¹(Ω)` on a bounded Lipschitz domain.** -/
theorem isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {S : Set (F → ℝ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M)
    (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    IsCompact (closure {f : Lp ℝ 1 (μ.restrict (Ω : Set F)) |
      ∃ u ∈ S, f =ᵐ[μ.restrict (Ω : Set F)] u}) :=
  isCompact_closure_of_isCompactOperator_toL1CLM
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hM hbdd hvar

/-- **Global `L¹(Ω)` sequential compactness of unbundled BV sequences on a bounded Lipschitz
domain.** -/
theorem exists_subseq_tendsto_setLIntegral_enorm_sub_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {u : ℕ → F → ℝ} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hmeas : ∀ n, AEStronglyMeasurable (u n) (μ.restrict (Ω : Set F)))
    (hbdd : ∀ n, ∫⁻ x in Ω, ‖u n x‖ₑ ∂μ ≤ M)
    (hvar : ∀ n, totalVariationOn μ Ω (u n) ≤ M) :
    ∃ v : F → ℝ, MemBV μ Ω v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => ∫⁻ x in Ω, ‖u (φ j) x - v x‖ₑ ∂μ) atTop (𝓝 0) ∧
      totalVariationOn μ Ω v ≤ liminf (fun j => totalVariationOn μ Ω (u (φ j))) atTop :=
  exists_subseq_tendsto_setLIntegral_enorm_sub_of_isCompactOperator_toL1CLM
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hM hmeas hbdd hvar

/-- **Global compactness for sets of bounded perimeter on a bounded Lipschitz domain.** Every
sequence of null-measurable sets with uniformly bounded perimeter in a bounded Lipschitz domain `Ω`
has a subsequence converging globally in measure on `Ω` to a measurable set `t` with
`perimeter μ Ω t ≤ liminf_j perimeter μ Ω (s (φ j))`. -/
theorem exists_subseq_tendsto_measure_symmDiff_inter_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {s : ℕ → Set F} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hs : ∀ n, NullMeasurableSet (s n) (μ.restrict (Ω : Set F)))
    (hP : ∀ n, perimeter μ Ω (s n) ≤ M) :
    ∃ t : Set F, MeasurableSet t ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => μ ((s (φ j) ∆ t) ∩ Ω)) atTop (𝓝 0) ∧
      perimeter μ Ω t ≤ liminf (fun j => perimeter μ Ω (s (φ j))) atTop :=
  exists_subseq_tendsto_measure_symmDiff_inter_of_isCompactOperator_toL1CLM
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hb.measure_lt_top.ne hM hs hP

end Intrinsic

section Ball

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure]

/-- **Global `L¹` compactness of `BV` on an open Euclidean ball.** On any open ball
`Metric.ball c r` of a finite-dimensional real inner product space `F` equipped with an additive
Haar measure `μ`, `BV.toL1CLM` is a compact operator. -/
theorem BV.isCompactOperator_toL1CLM_ball (c : F) (r : ℝ) :
    IsCompactOperator (BV.toL1CLM (μ := μ) (Ω := ⟨ball c r, isOpen_ball⟩)) := by
  rcases le_or_gt r 0 with hr | hr
  · exact BV.isCompactOperator_toL1CLM_iff_isCompactOperator_valueL.mpr
      (W1p.isCompactOperator_valueL_of_frontier_eq_empty isBounded_ball
        (by simp [ball_eq_empty.mpr hr]))
  rcases subsingleton_or_nontrivial F with hsub | _
  · exact BV.isCompactOperator_toL1CLM_iff_isCompactOperator_valueL.mpr
      (W1p.isCompactOperator_valueL_of_frontier_eq_empty isBounded_ball
        (by simp [Subsingleton.eq_univ_of_nonempty (nonempty_ball.mpr hr)]))
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  let ν : F := ‖v‖⁻¹ • v
  have hν : ‖ν‖ = 1 := by simp [ν, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ) := (ℝ ∙ ν).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.toSpanUnitSingleton ν hν).symm
      (LinearIsometryEquiv.refl ℝ (ℝ ∙ ν)ᗮ))
  have hball : (e.toAffineIsometryEquiv ''
      (⟨ball c r, isOpen_ball⟩ : Opens F)).IsLipschitzDomainWith 1 := by
    rw [Opens.coe_mk, LinearIsometryEquiv.coe_toAffineIsometryEquiv, e.image_ball]
    exact isLipschitzDomainWith_ball (e c) hr one_pos
  exact BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith_image e.toAffineIsometryEquiv hball
    isBounded_ball

end Ball

end TauCeti
