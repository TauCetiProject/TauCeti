/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Holder.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Inclusions between the Hölder spaces `C^{k,α}(M)` of different exponents

Let `A` be a compact chart atlas of a manifold `M`. For `β ≤ α`, every element of
`A.CkHolderSpace k α F` lies in `A.CkHolderSpace k β F`: on each piece of the atlas the `k`th
coordinate derivative is bounded by the `C^{k,α}` norm, so its values differ by at most twice that
norm, which is its Hölder bound of exponent `0`; interpolating with its `α`-Hölder bound
(Mathlib's `HolderWith.of_le_of_le`) makes it `β`-Hölder with constant `max (2 ‖f‖) [D^k f]_α`.
The inclusion is a continuous linear map of norm at most `2 N + 1`, for `N` the number of pieces
(`TauCeti.CompactChartAtlas.CkHolderSpace.norm_inclusionL_le`). This is the piecewise form of
the Euclidean inclusion `TauCeti.HolderSpace.inclusionL`.

## Main definitions

* `TauCeti.CompactChartAtlas.CkHolderSpace.inclusionL`: the inclusion
  `C^{k,α}(M, F) → C^{k,β}(M, F)` for `β ≤ α`.

## Main results

* `TauCeti.CompactChartAtlas.CkHolderSpace.holderWith_restrict_chartIteratedFDeriv_of_le`: the `k`th
  coordinate derivative of an element of `C^{k,α}(M, F)` is `β`-Hölder on each piece.
* `TauCeti.CompactChartAtlas.CkHolderSpace.norm_inclusionL_le`: the inclusion has norm at most
  `2 N + 1`.
* `TauCeti.CompactChartAtlas.CkHolderSpace.inclusionL_injective`: the inclusion is injective.

## References

* M. Taylor, *Partial Differential Equations III*, Chapter 13, for Hölder spaces on compact
  manifolds defined through finitely many charts.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 6.33, for the Euclidean inclusions.
-/

public section

open Set
open scoped Manifold NNReal

namespace TauCeti.CompactChartAtlas.CkHolderSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {A : CompactChartAtlas I M} {k : ℕ} {α β : ℝ≥0}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsManifold I k M]

/-- For `β ≤ α`, the `k`th coordinate derivative of an element `f` of `C^{k,α}(M, F)` is
`β`-Hölder on each piece of the atlas, with constant `max (2 ‖f‖) [D^k f]_α`: nearby points are
controlled by the `α`-Hölder bound and distant ones by the bound `‖f‖` on the derivative. -/
theorem holderWith_restrict_chartIteratedFDeriv_of_le (hβα : β ≤ α) (f : A.CkHolderSpace k α F)
    (i : A.ι) :
    HolderWith (max (2 * ‖f‖₊) (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
        (toContMDiffMap A k α F f))) β
      ⇑((ContMDiffMap.chartIteratedFDeriv (toContMDiffMap A k α F f) (A.center i) k
        le_rfl).restrict (A.piece i)) := by
  rw [ContMDiffMap.chartHolderNorm_def]
  exact (holderWith_zero_of_nnnorm_le fun z ↦ NNReal.coe_le_coe.1
    (norm_chartIteratedFDeriv_le f i le_rfl z.property)).of_le_of_le
      (ContMDiffMap.memChartHolder_iff.1 (memChartHolder f i)).holderWith zero_le hβα

/-- For `β ≤ α`, the `β`-Hölder seminorm of the `k`th coordinate derivative of an element `f` of
`C^{k,α}(M, F)` on a piece is at most `2 ‖f‖ + [D^k f]_α`. -/
private theorem chartHolderNorm_le_of_le (hβα : β ≤ α) (f : A.CkHolderSpace k α F) (i : A.ι) :
    (ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl β
        (toContMDiffMap A k α F f) : ℝ) ≤
      2 * ‖f‖ + ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) k le_rfl α
        (toContMDiffMap A k α F f) := by
  have h := NNReal.coe_le_coe.2
    (holderWith_restrict_chartIteratedFDeriv_of_le hβα f i).nnholderNorm_le
  push_cast at h
  rw [ContMDiffMap.chartHolderNorm_def]
  exact h.trans (max_le_add_of_nonneg (by positivity) (NNReal.coe_nonneg _))

variable (A k F) in
/-- **The inclusion of Hölder spaces on a compact manifold.** For `β ≤ α`, every element of
`C^{k,α}(M, F)` lies in `C^{k,β}(M, F)`, and the inclusion is a continuous linear map of norm at
most `2 N + 1`, for `N` the number of pieces of the atlas
(`TauCeti.CompactChartAtlas.CkHolderSpace.norm_inclusionL_le`). -/
noncomputable def inclusionL (hβα : β ≤ α) : A.CkHolderSpace k α F →L[𝕜] A.CkHolderSpace k β F :=
  LinearMap.mkContinuous
    { toFun f := mk (toContMDiffMap A k α F f) fun i ↦
        ContMDiffMap.memChartHolder_iff.2 ⟨_, holderWith_restrict_chartIteratedFDeriv_of_le hβα f i⟩
      map_add' _ _ := ext fun _ ↦ by simp
      map_smul' _ _ := ext fun _ ↦ by simp }
    (2 * Fintype.card A.ι + 1) fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, norm_def, toContMDiffMap_mk]
      have hf := norm_def f
      have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ chartHolderNorm_le_of_le hβα f i
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
      linarith

@[simp]
theorem coe_inclusionL (hβα : β ≤ α) (f : A.CkHolderSpace k α F) :
    ⇑(inclusionL A k F hβα f) = f := by
  simp [inclusionL]

@[simp]
theorem toContMDiffMap_inclusionL (hβα : β ≤ α) (f : A.CkHolderSpace k α F) :
    toContMDiffMap A k β F (inclusionL A k F hβα f) = toContMDiffMap A k α F f := by
  simp [inclusionL]

/-- The inclusion of Hölder spaces has norm at most `2 N + 1`, for `N` the number of pieces of the
atlas. -/
theorem norm_inclusionL_le (hβα : β ≤ α) :
    ‖inclusionL A k F hβα‖ ≤ 2 * Fintype.card A.ι + 1 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The inclusion of Hölder spaces is injective. -/
theorem inclusionL_injective (hβα : β ≤ α) : Function.Injective (inclusionL A k F hβα) :=
  fun f g h ↦ ext fun y ↦ by
    simpa using congrArg (fun g : A.CkHolderSpace k β F ↦ g y) h

/-- The inclusion for equal exponents is the identity. -/
@[simp]
theorem inclusionL_refl : inclusionL A k F (le_refl α) = ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.ext fun _ ↦ ext fun _ ↦ by simp

/-- Inclusions of Hölder spaces compose. -/
theorem inclusionL_comp_inclusionL {γ : ℝ≥0} (hγβ : γ ≤ β) (hβα : β ≤ α) :
    (inclusionL A k F hγβ).comp (inclusionL A k F hβα) = inclusionL A k F (hγβ.trans hβα) :=
  ContinuousLinearMap.ext fun _ ↦ ext fun _ ↦ by simp

end TauCeti.CompactChartAtlas.CkHolderSpace
