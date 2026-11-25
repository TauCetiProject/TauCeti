/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.Convergence
public import TauCeti.Geometry.MeasureTheory.Varifold.FirstVariation
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Stationary varifolds and the total first variation in a Euclidean space

Let `E` be a finite-dimensional real inner product space, `W ⊆ E` open and `V` a `k`-varifold on
`W`, a Radon measure on `W × G(E, k)`, with first variation `δV` (`Euclidean.firstVariation`).

* `V` is **stationary** in `W` when `δV(X) = 0` for every `C¹` vector field `X` with compact
  support in `W` (`Euclidean.IsStationary`).
* `V` has **locally bounded first variation** in `W` when for each compact `K ⊆ W` there is `C`
  with `|δV(X)| ≤ C` for every such `X` supported in `K` with `|X| ≤ 1`
  (`Euclidean.HasLocallyBoundedFirstVariation`).
* The **total first variation** of a set `U` is
  `‖δV‖(U) = sup {δV(X) : X of class C¹ with compact support in U ∩ W, |X| ≤ 1} ∈ [0, ∞]`
  (`Euclidean.firstVariationMass`). It is defined for every varifold.

These are Simon, *Lectures on Geometric Measure Theory*, 39.3, and §4.3 of the Varifolds roadmap
in Euclidean space. The identification of `‖δV‖` with the total variation measure of the
extension of `δV` to continuous vector fields needs the Riesz representation for vector fields and
is not proved here.

## Main results

* `Euclidean.abs_firstVariation_le_mul_firstVariationMass`: `|δV(X)| ≤ c ‖δV‖(U)` when `X` is
  supported in `U` with `|X| ≤ c`.
* `Euclidean.isStationary_iff_firstVariationMass_eq_zero`: `V` is stationary in `W` if and only if
  `‖δV‖(W) = 0`.
* `Euclidean.hasLocallyBoundedFirstVariation_iff`: `V` has locally bounded first variation if and
  only if `‖δV‖(U) < ∞` for every open `U` with compact closure in `W`.
* `Euclidean.firstVariationMass_add_le`, `Euclidean.firstVariationMass_smul`:
  `‖δ(V + V')‖ ≤ ‖δV‖ + ‖δV'‖` and `‖δ(cV)‖ = c ‖δV‖`.
* `Euclidean.firstVariationMass_le_liminf`: lower semicontinuity of `‖δV‖(U)` under varifold
  convergence (Simon, 40.7(1)), and its consequences
  `Euclidean.hasLocallyBoundedFirstVariation_of_varifoldTendsto` and
  `Euclidean.IsStationary.of_varifoldTendsto`: limits of stationary varifolds are stationary.

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. 95 (1972), Section 4.
* L. Simon, *Lectures on Geometric Measure Theory*, §39 and §40.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped Distributions Topology NNReal ENNReal

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ} {W : Opens E}
  {V V₁ V₂ : Measure (W × grassmannian ℝ E k)} {U U' : Set E}

/-- A varifold `V` on an open set `W` of a Euclidean space is **stationary** in `W` when its first
variation `δV(X)` vanishes for every `C¹` vector field `X` with compact support in `W` (Simon,
*Lectures on Geometric Measure Theory*, 39.3). -/
def IsStationary (V : Measure (W × grassmannian ℝ E k)) : Prop :=
  firstVariation V = 0

/-- A varifold `V` on an open set `W` of a Euclidean space has **locally bounded first variation**
in `W` when for each compact `K ⊆ W` there is `C` with `|δV(X)| ≤ C` for every `C¹` vector field
`X` supported in `K` with `|X| ≤ 1` pointwise (Simon, *Lectures on Geometric Measure Theory*,
39.3). -/
def HasLocallyBoundedFirstVariation (V : Measure (W × grassmannian ℝ E k)) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ W → ∃ C : ℝ, ∀ X : 𝓓^{1}(W, E), tsupport X ⊆ K →
    (∀ x, ‖X x‖ ≤ 1) → |firstVariation V X| ≤ C

/-- The **total first variation** `‖δV‖(U) = sup {δV(X) : X ∈ C¹_c(U ∩ W), |X| ≤ 1}` of a set `U`,
in `[0, ∞]`. It is defined for every varifold; on open sets it is the total variation measure of
`δV` when `V` has locally bounded first variation. -/
def firstVariationMass (V : Measure (W × grassmannian ℝ E k)) (U : Set E) : ℝ≥0∞ :=
  ⨆ (X : 𝓓^{1}(W, E)) (_ : tsupport X ⊆ U) (_ : ∀ x, ‖X x‖ ≤ 1),
    ENNReal.ofReal (firstVariation V X)

/-- Unfolding lemma for `Euclidean.IsStationary`. -/
theorem isStationary_iff : IsStationary V ↔ ∀ X : 𝓓^{1}(W, E), firstVariation V X = 0 :=
  (ContinuousLinearMap.ext_iff)

/-- Unfolding lemma for `Euclidean.firstVariationMass`. -/
theorem firstVariationMass_def (V : Measure (W × grassmannian ℝ E k)) (U : Set E) :
    firstVariationMass V U = ⨆ (X : 𝓓^{1}(W, E)) (_ : tsupport X ⊆ U) (_ : ∀ x, ‖X x‖ ≤ 1),
      ENNReal.ofReal (firstVariation V X) :=
  (rfl)

/-- Every admissible vector field bounds the total first variation from below. -/
theorem ofReal_firstVariation_le_firstVariationMass {X : 𝓓^{1}(W, E)} (hXU : tsupport X ⊆ U)
    (hX : ∀ x, ‖X x‖ ≤ 1) : ENNReal.ofReal (firstVariation V X) ≤ firstVariationMass V U :=
  le_iSup₂_of_le X hXU (le_iSup_of_le hX le_rfl)

/-- The total first variation is monotone in the set. -/
theorem firstVariationMass_mono (h : U ⊆ U') : firstVariationMass V U ≤ firstVariationMass V U' :=
  iSup_mono fun _ ↦ iSup_mono' fun hXU ↦ ⟨hXU.trans h, le_rfl⟩

/-- The total first variation of a set `U` only sees `U ∩ W`. -/
theorem firstVariationMass_inter_opens (V : Measure (W × grassmannian ℝ E k)) (U : Set E) :
    firstVariationMass V (U ∩ W) = firstVariationMass V U :=
  le_antisymm (firstVariationMass_mono inter_subset_left) <|
    iSup_mono fun X ↦ iSup_mono' fun hXU ↦ ⟨subset_inter hXU X.tsupport_subset, le_rfl⟩

/-- The total first variation of the empty set is `0`. -/
@[simp]
theorem firstVariationMass_empty (V : Measure (W × grassmannian ℝ E k)) :
    firstVariationMass V ∅ = 0 := by
  refine nonpos_iff_eq_zero.1 (iSup₂_le fun X hX ↦ iSup_le fun _ ↦ ?_)
  have hX0 : X = 0 := by
    ext x
    exact image_eq_zero_of_notMem_tsupport fun hx ↦ hX hx
  simp [hX0]

/-- **The bound by the total first variation.** If `X` is supported in `U` and `|X| ≤ c`, then
`|δV(X)| ≤ c ‖δV‖(U)` (with `‖δV‖(U)` read as a real number, so the bound is only useful when
`‖δV‖(U) < ∞`). -/
theorem abs_firstVariation_le_mul_firstVariationMass (hU : firstVariationMass V U ≠ ∞)
    {X : 𝓓^{1}(W, E)} (hXU : tsupport X ⊆ U) {c : ℝ} (hX : ∀ x, ‖X x‖ ≤ c) :
    |firstVariation V X| ≤ c * (firstVariationMass V U).toReal := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (hX 0)
  rcases hc.eq_or_lt with rfl | hc
  · have hX0 : X = 0 := by
      ext x
      exact norm_le_zero_iff.1 (hX x)
    simp [hX0]
  -- Normalise `X` to `Y = c⁻¹ X` with `|Y| ≤ 1`, and test with `Y` and `-Y`.
  set Y : 𝓓^{1}(W, E) := c⁻¹ • X
  have hY (x : E) : ‖Y x‖ ≤ 1 := by
    rw [show Y x = c⁻¹ • X x from rfl, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
    exact (inv_mul_le_one₀ hc).2 (hX x)
  have hYU : tsupport Y ⊆ U := (tsupport_smul_subset_right _ _).trans hXU
  have hnY : tsupport (-Y) ⊆ U := by
    rw [show ((-Y : 𝓓^{1}(W, E)) : E → E) = -(Y : E → E) from rfl, tsupport_neg]
    exact hYU
  have h₁ := (ENNReal.ofReal_le_iff_le_toReal hU).1
    (ofReal_firstVariation_le_firstVariationMass hYU hY)
  have h₂ := (ENNReal.ofReal_le_iff_le_toReal hU).1
    (ofReal_firstVariation_le_firstVariationMass (V := V) hnY fun x ↦ by
      simpa [show (-Y : 𝓓^{1}(W, E)) x = -Y x from rfl] using hY x)
  rw [map_neg] at h₂
  have hXY : X = c • Y := by simp [Y, smul_smul, hc.ne']
  rw [hXY, map_smul, smul_eq_mul, abs_mul, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, h₁⟩) hc.le

/-- **Stationarity is the vanishing of the total first variation.** -/
theorem isStationary_iff_firstVariationMass_eq_zero :
    IsStationary V ↔ firstVariationMass V W = 0 := by
  refine ⟨fun h ↦ nonpos_iff_eq_zero.1 (iSup₂_le fun X _ ↦ iSup_le fun _ ↦ ?_), fun h ↦ ?_⟩
  · simp [isStationary_iff.1 h X]
  refine isStationary_iff.2 fun X ↦ ?_
  obtain ⟨c, hc⟩ := (map_continuous X).bounded_above_of_compact_support X.hasCompactSupport
  have := abs_firstVariation_le_mul_firstVariationMass (h ▸ ENNReal.zero_ne_top)
    X.tsupport_subset hc
  rw [h, ENNReal.toReal_zero, mul_zero] at this
  exact abs_nonpos_iff.1 this

/-- A stationary varifold has total first variation `0` on every set. -/
theorem IsStationary.firstVariationMass_eq_zero (h : IsStationary V) (U : Set E) :
    firstVariationMass V U = 0 :=
  nonpos_iff_eq_zero.1 <| (firstVariationMass_inter_opens V U).symm.trans_le
    (firstVariationMass_mono inter_subset_right) |>.trans_eq
      (isStationary_iff_firstVariationMass_eq_zero.1 h)

/-- **Local boundedness through the total first variation.** A varifold has locally bounded first
variation in `W` if and only if `‖δV‖(U) < ∞` for every open `U` with compact closure in `W`. -/
theorem hasLocallyBoundedFirstVariation_iff :
    HasLocallyBoundedFirstVariation V ↔ ∀ U : Set E, IsOpen U → IsCompact (closure U) →
      closure U ⊆ W → firstVariationMass V U ≠ ∞ := by
  refine ⟨fun h U _ hUc hUW ↦ ?_, fun h K hK hKW ↦ ?_⟩
  · obtain ⟨C, hC⟩ := h _ hUc hUW
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C))
      (iSup₂_le fun X hXU ↦ iSup_le fun hX ↦ ENNReal.ofReal_le_ofReal ?_)
    exact (le_abs_self _).trans (hC X (hXU.trans subset_closure) hX)
  · obtain ⟨U, hU, hKU, hUW, hUc⟩ :=
      exists_open_between_and_isCompact_closure hK W.isOpen hKW
    exact ⟨(firstVariationMass V U).toReal, fun X hXK hX ↦ by
      simpa using abs_firstVariation_le_mul_firstVariationMass (h U hU hUc hUW)
        (hXK.trans hKU) hX⟩

/-- A stationary varifold has locally bounded first variation. -/
theorem IsStationary.hasLocallyBoundedFirstVariation (h : IsStationary V) :
    HasLocallyBoundedFirstVariation V :=
  fun _ _ _ ↦ ⟨0, fun X _ _ ↦ by simp [isStationary_iff.1 h X]⟩

/-- A measure that is not finite on compact sets has first variation `0` by convention, so it is
stationary. -/
theorem isStationary_of_not_isFiniteMeasureOnCompacts (hV : ¬IsFiniteMeasureOnCompacts V) :
    IsStationary V :=
  firstVariation_of_not_isFiniteMeasureOnCompacts hV

omit [BorelSpace E] in
/-- A sum of measures is finite on compact sets only if both summands are. -/
private theorem isFiniteMeasureOnCompacts_and_of_add
    (h : IsFiniteMeasureOnCompacts (V₁ + V₂)) :
    IsFiniteMeasureOnCompacts V₁ ∧ IsFiniteMeasureOnCompacts V₂ :=
  ⟨⟨fun _ hK ↦ (Measure.le_add_right le_rfl _).trans_lt (h.lt_top_of_isCompact hK)⟩,
    ⟨fun _ hK ↦ (Measure.le_add_left le_rfl _).trans_lt (h.lt_top_of_isCompact hK)⟩⟩

/-- **Subadditivity in the varifold.** `‖δ(V₁ + V₂)‖(U) ≤ ‖δV₁‖(U) + ‖δV₂‖(U)`. -/
theorem firstVariationMass_add_le (U : Set E) :
    firstVariationMass (V₁ + V₂) U ≤ firstVariationMass V₁ U + firstVariationMass V₂ U := by
  by_cases h : IsFiniteMeasureOnCompacts (V₁ + V₂)
  · obtain ⟨_, _⟩ := isFiniteMeasureOnCompacts_and_of_add h
    refine iSup₂_le fun X hXU ↦ iSup_le fun hX ↦ ?_
    rw [firstVariation_add_measure, add_apply]
    exact ENNReal.ofReal_add_le.trans (add_le_add
      (ofReal_firstVariation_le_firstVariationMass hXU hX)
      (ofReal_firstVariation_le_firstVariationMass hXU hX))
  · simp [(isStationary_of_not_isFiniteMeasureOnCompacts h).firstVariationMass_eq_zero U]

/-- **Homogeneity in the varifold.** `‖δ(cV)‖(U) = c ‖δV‖(U)` for `c ≥ 0`. -/
theorem firstVariationMass_smul (c : ℝ≥0) (V : Measure (W × grassmannian ℝ E k)) (U : Set E) :
    firstVariationMass (c • V) U = c * firstVariationMass V U := by
  simp only [firstVariationMass_def, firstVariation_smul_measure, smul_apply,
    smul_eq_mul, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.mul_iSup]

/-- **Lower semicontinuity of the total first variation** (Simon, *Lectures on Geometric Measure
Theory*, 40.7(1)). If `V_j → V` as varifolds, then `‖δV‖(U) ≤ lim inf_j ‖δV_j‖(U)` for every
set `U`. -/
theorem firstVariationMass_le_liminf {V : ℕ → Measure (W × grassmannian ℝ E k)}
    {V₀ : Measure (W × grassmannian ℝ E k)} [∀ j, IsFiniteMeasureOnCompacts (V j)]
    (h : TauCeti.VarifoldTendsto V V₀) (U : Set E) :
    firstVariationMass V₀ U ≤ liminf (fun j ↦ firstVariationMass (V j) U) atTop := by
  by_cases hV₀ : IsFiniteMeasureOnCompacts V₀
  swap
  · simp [(isStationary_of_not_isFiniteMeasureOnCompacts hV₀).firstVariationMass_eq_zero U]
  refine iSup₂_le fun X hXU ↦ iSup_le fun hX ↦ ?_
  have hlim : Tendsto (fun j ↦ ENNReal.ofReal (firstVariation (V j) X)) atTop
      (𝓝 (ENNReal.ofReal (firstVariation V₀ X))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_firstVariation (TauCeti.varifoldTendsto_iff.1 h) X)
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun j ↦
    ofReal_firstVariation_le_firstVariationMass hXU hX)

/-- **Local bounds pass to varifold limits.** If `V_j → V` and `lim inf_j ‖δV_j‖(U) < ∞` for every
open `U` with compact closure in `W`, then `V` has locally bounded first variation in `W`. -/
theorem hasLocallyBoundedFirstVariation_of_varifoldTendsto
    {V : ℕ → Measure (W × grassmannian ℝ E k)} {V₀ : Measure (W × grassmannian ℝ E k)}
    [∀ j, IsFiniteMeasureOnCompacts (V j)] (h : TauCeti.VarifoldTendsto V V₀)
    (hV : ∀ U : Set E, IsOpen U → IsCompact (closure U) → closure U ⊆ W →
      liminf (fun j ↦ firstVariationMass (V j) U) atTop ≠ ∞) :
    HasLocallyBoundedFirstVariation V₀ :=
  hasLocallyBoundedFirstVariation_iff.2 fun U hU hUc hUW ↦
    ne_top_of_le_ne_top (hV U hU hUc hUW) (firstVariationMass_le_liminf h U)

/-- **Limits of stationary varifolds are stationary.** -/
theorem IsStationary.of_varifoldTendsto {V : ℕ → Measure (W × grassmannian ℝ E k)}
    {V₀ : Measure (W × grassmannian ℝ E k)} [∀ j, IsFiniteMeasureOnCompacts (V j)]
    (h : TauCeti.VarifoldTendsto V V₀) (hV : ∀ j, IsStationary (V j)) : IsStationary V₀ := by
  by_cases hV₀ : IsFiniteMeasureOnCompacts V₀
  swap
  · exact isStationary_of_not_isFiniteMeasureOnCompacts hV₀
  exact isStationary_iff.2 fun X ↦ tendsto_nhds_unique
    (tendsto_firstVariation (TauCeti.varifoldTendsto_iff.1 h) X)
    (by simp [isStationary_iff.1 (hV _) X])

/-- A varifold of `0`-planes is stationary. -/
theorem isStationary_zero_dim (V : Measure (W × grassmannian ℝ E 0)) : IsStationary V :=
  firstVariation_zero_dim V

/-- The zero varifold is stationary. -/
theorem isStationary_zero : IsStationary (0 : Measure (W × grassmannian ℝ E k)) :=
  firstVariation_zero_measure

/-- Sums of stationary varifolds are stationary. -/
theorem IsStationary.add (h₁ : IsStationary V₁) (h₂ : IsStationary V₂) :
    IsStationary (V₁ + V₂) := by
  by_cases h : IsFiniteMeasureOnCompacts (V₁ + V₂)
  · obtain ⟨_, _⟩ := isFiniteMeasureOnCompacts_and_of_add h
    rw [IsStationary, firstVariation_add_measure, h₁, h₂, add_zero]
  · exact isStationary_of_not_isFiniteMeasureOnCompacts h

/-- Nonnegative multiples of stationary varifolds are stationary. -/
theorem IsStationary.smul (h : IsStationary V) (c : ℝ≥0) : IsStationary (c • V) := by
  rw [IsStationary, firstVariation_smul_measure, h, smul_zero]

end Euclidean
