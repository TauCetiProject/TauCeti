/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Holder.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Topology.MetricSpace.Holder

/-!
# Inclusions between the Hölder spaces `C^{k,α}(M)`: lower exponent and lower order

Let `A` be a compact chart atlas of a manifold `M`. For `β ≤ α`, every element of
`A.CkHolderSpace k α F` lies in `A.CkHolderSpace k β F`: on each piece of the atlas the `k`th
coordinate derivative is bounded by the `C^{k,α}` norm, so its values differ by at most twice that
norm, which is its Hölder bound of exponent `0`; interpolating with its `α`-Hölder bound
(Mathlib's `HolderWith.of_le_of_le`) makes it `β`-Hölder with constant `max (2 ‖f‖) [D^k f]_α`.
The inclusion is a continuous linear map of norm at most `2 N + 1`, for `N` the number of pieces
(`TauCeti.CompactChartAtlas.CkHolderSpace.norm_inclusionL_le`). This is the piecewise form of
the Euclidean inclusion `TauCeti.HolderSpace.inclusionL`.

One derivative pays for any exponent at most one: over `ℝ` or `ℂ` and for `β ≤ 1`, every element of
`A.CkHolderSpace (k + 1) α F` lies in `A.CkHolderSpace k β F`, whatever `α`. In a chart, the `k`th
coordinate derivative of a `C^{k+1}` map is `C^1` on the extended chart target, whose intersection
with a small ball is convex, so it is locally Lipschitz
(`ContMDiffMap.locallyLipschitz_chartIteratedFDeriv`); on the compact pieces it is then Lipschitz,
by a Lebesgue-number argument, and so `β`-Hölder. The pieces need not be convex. Both spaces are
Banach when the model space is locally compact and `F` complete, and evaluation at points is
continuous on both, so the closed graph theorem makes the inclusion continuous
(`TauCeti.CompactChartAtlas.CkHolderSpace.inclusionSuccL`).

## Main definitions

* `TauCeti.CompactChartAtlas.CkHolderSpace.inclusionL`: the inclusion
  `C^{k,α}(M, F) → C^{k,β}(M, F)` for `β ≤ α`.
* `TauCeti.CompactChartAtlas.CkHolderSpace.inclusionSuccL`: the inclusion
  `C^{k+1,α}(M, F) → C^{k,β}(M, F)` for `β ≤ 1`.

## Main results

* `TauCeti.CompactChartAtlas.CkHolderSpace.holderWith_restrict_chartIteratedFDeriv_of_le`: the `k`th
  coordinate derivative of an element of `C^{k,α}(M, F)` is `β`-Hölder on each piece.
* `TauCeti.CompactChartAtlas.CkHolderSpace.norm_inclusionL_le`: the inclusion has norm at most
  `2 N + 1`.
* `TauCeti.CompactChartAtlas.CkHolderSpace.inclusionL_injective`: the inclusion is injective.
* `ContMDiffMap.memChartHolder_of_contMDiff_of_isCompact`: the `k`th coordinate derivative of a
  `C^{k+1}` map is `β`-Hölder on every compact subset of a chart target, for `β ≤ 1`.

## References

* M. Taylor, *Partial Differential Equations III*, Chapter 13, for Hölder spaces on compact
  manifolds defined through finitely many charts.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 6.33, for the Euclidean inclusions.
-/

public section

open Set Filter Topology
open scoped Manifold NNReal

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M] {k : ℕ}

/-- Over `ℝ` or `ℂ`, the `k`th coordinate derivative of a `C^{k+1}` map is locally Lipschitz on
the extended chart target: near each point the target is a convex set, the intersection of a ball
with the range of the model, on which this derivative is `C^1`. -/
theorem locallyLipschitz_chartIteratedFDeriv [IsManifold I (k + 1 : ℕ) M]
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (hf : ContMDiff I 𝓘(𝕜, F) (k + 1 : ℕ) f) (x : M) (hk : k ≤ n) :
    LocallyLipschitz (chartIteratedFDeriv f x k hk) := by
  let := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ (E [×k]→L[𝕜] F) := NormedSpace.restrictScalars ℝ 𝕜 _
  have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 (E [×k]→L[𝕜] F) := .restrictScalars ℝ 𝕜 _
  set T := (extChartAt I x).target
  have hT : UniqueDiffOn 𝕜 T := uniqueDiffOn_extChartAt_target x
  have hf' : ContDiffOn 𝕜 (k + 1 : ℕ) (f ∘ (extChartAt I x).symm) T :=
    contDiffOn_comp_extend_symm (⟨f, hf⟩ : C^(k + 1 : ℕ)⟮I, M; 𝓘(𝕜, F), F⟯)
      (IsManifold.chart_mem_maximalAtlas x)
  set g := iteratedFDerivWithin 𝕜 k (f ∘ (extChartAt I x).symm) T
  -- The `k`th derivative is `C^1` on the target.
  have hg : ContDiffOn 𝕜 1 g T := fun z hz ↦
    (hf' z hz).iteratedFDerivWithin_right hT (by rw [add_comm]; norm_cast) hz
  intro z
  obtain ⟨s, hsT, hs, hsn⟩ :=
    TauCeti.exists_convex_subset_mem_nhdsWithin_extChartAt_target z.property
  obtain ⟨L, t, ht, hL⟩ := ((hg.mono hsT).restrict_scalars ℝ).locallyLipschitzOn hs
    (mem_of_mem_nhdsWithin z.property hsn)
  refine ⟨L, Subtype.val ⁻¹' t, preimage_coe_mem_nhds_subtype.2 (nhdsWithin_le_of_mem hsn ht),
    fun a ha b hb ↦ ?_⟩
  rw [chartIteratedFDeriv_self_target_apply, chartIteratedFDeriv_self_target_apply,
    Subtype.edist_eq]
  exact hL ha hb

/-- **Hölder bounds from one more derivative.** Over `ℝ` or `ℂ` and for `β ≤ 1`, the
`k`th coordinate derivative of a `C^{k+1}` map is `β`-Hölder on every compact subset of a chart
target. The compact set need not be convex. -/
theorem memChartHolder_of_contMDiff_of_isCompact [IsManifold I (k + 1 : ℕ) M] {β : ℝ≥0}
    (hβ : β ≤ 1) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (hf : ContMDiff I 𝓘(𝕜, F) (k + 1 : ℕ) f) (x : M)
    {K : Set (extChartAt I x).target} (hK : IsCompact K) (hk : k ≤ n) :
    MemChartHolder x K k hk β f := by
  obtain ⟨C, hC⟩ := ((locallyLipschitz_chartIteratedFDeriv f hf x hk).locallyLipschitzOn
    (s := univ)).exists_holderOnWith_of_isCompact hβ hK (subset_univ K)
  exact .of_holderOnWith hC

end ContMDiffMap

namespace TauCeti.CompactChartAtlas.CkHolderSpace

section Exponent

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

end Exponent

section Succ

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {A : CompactChartAtlas I M} {k : ℕ} {α β : ℝ≥0}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsManifold I k M]
  [IsManifold I (k + 1 : ℕ) M]

omit [IsRCLikeNormedField 𝕜] [IsManifold I k M] in
/-- The underlying `C^k` map of an element of `C^{k+1,α}(M, F)`. -/
private noncomputable def toContMDiffMapSucc (f : A.CkHolderSpace (k + 1) α F) :
    C^k⟮I, M; 𝓘(𝕜, F), F⟯ :=
  ⟨f, (toContMDiffMap A (k + 1) α F f).contMDiff.of_le (by exact_mod_cast k.le_succ)⟩

omit [IsRCLikeNormedField 𝕜] [IsManifold I k M] in
private theorem coe_toContMDiffMapSucc (f : A.CkHolderSpace (k + 1) α F) :
    ⇑(toContMDiffMapSucc f) = f :=
  rfl

variable (A k α F) in
/-- For `β ≤ 1`, the inclusion `C^{k+1,α}(M, F) → C^{k,β}(M, F)`, as a linear map. -/
noncomputable def inclusionSuccLinearMap (hβ : β ≤ 1) :
    A.CkHolderSpace (k + 1) α F →ₗ[𝕜] A.CkHolderSpace k β F where
  toFun f := mk (toContMDiffMapSucc f) fun i ↦
    ContMDiffMap.memChartHolder_of_contMDiff_of_isCompact hβ (toContMDiffMapSucc f)
      (by simpa [coe_toContMDiffMapSucc] using (toContMDiffMap A (k + 1) α F f).contMDiff) _
      (A.piece i).isCompact le_rfl
  map_add' _ _ := ext fun _ ↦ by simp [coe_toContMDiffMapSucc]
  map_smul' _ _ := ext fun _ ↦ by simp [coe_toContMDiffMapSucc]

@[simp]
theorem coe_inclusionSuccLinearMap (hβ : β ≤ 1) (f : A.CkHolderSpace (k + 1) α F) :
    ⇑(inclusionSuccLinearMap A k α F hβ f) = f := by
  ext y
  simp [inclusionSuccLinearMap, coe_toContMDiffMapSucc]

variable [LocallyCompactSpace E] [CompleteSpace F]

/-- When the model space is locally compact and `F` is complete, the inclusion
`C^{k+1,α}(M, F) → C^{k,β}(M, F)` is continuous, by the closed graph theorem. -/
theorem continuous_inclusionSuccLinearMap (hβ : β ≤ 1) :
    Continuous (inclusionSuccLinearMap A k α F hβ) :=
  continuous_of_coe_eq _ (coe_inclusionSuccLinearMap hβ)

variable (A k α F) in
/-- **Lowering the order of a Hölder space.** Over `ℝ` or `ℂ`, when the model space is locally
compact and `F` is complete, every element of `C^{k+1,α}(M, F)` lies in `C^{k,β}(M, F)` for each
`β ≤ 1`, whatever `α`, and the inclusion is a continuous linear map. -/
noncomputable def inclusionSuccL (hβ : β ≤ 1) :
    A.CkHolderSpace (k + 1) α F →L[𝕜] A.CkHolderSpace k β F :=
  ⟨inclusionSuccLinearMap A k α F hβ, continuous_inclusionSuccLinearMap hβ⟩

@[simp]
theorem coe_inclusionSuccL (hβ : β ≤ 1) (f : A.CkHolderSpace (k + 1) α F) :
    ⇑(inclusionSuccL A k α F hβ f) = f :=
  coe_inclusionSuccLinearMap hβ f

/-- The inclusion `C^{k+1,α}(M, F) → C^{k,β}(M, F)` is injective. -/
theorem inclusionSuccL_injective (hβ : β ≤ 1) :
    Function.Injective (inclusionSuccL A k α F hβ) :=
  fun f g h ↦ ext fun y ↦ by
    simpa using congrArg (fun g : A.CkHolderSpace k β F ↦ g y) h

/-- The order-lowering inclusion followed by an exponent inclusion is again an order-lowering
inclusion. -/
theorem inclusionL_comp_inclusionSuccL {γ : ℝ≥0} (hγβ : γ ≤ β) (hβ : β ≤ 1) :
    (inclusionL A k F hγβ).comp (inclusionSuccL A k α F hβ) =
      inclusionSuccL A k α F (hγβ.trans hβ) :=
  ContinuousLinearMap.ext fun _ ↦ ext fun _ ↦ by simp

/-- An exponent inclusion followed by the order-lowering inclusion is the order-lowering
inclusion. -/
theorem inclusionSuccL_comp_inclusionL {γ : ℝ≥0} (hγα : γ ≤ α) (hβ : β ≤ 1) :
    (inclusionSuccL A k γ F hβ).comp (inclusionL A (k + 1) F hγα) =
      inclusionSuccL A k α F hβ :=
  ContinuousLinearMap.ext fun _ ↦ ext fun _ ↦ by simp

end Succ

end TauCeti.CompactChartAtlas.CkHolderSpace
