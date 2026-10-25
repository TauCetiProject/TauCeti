/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compact chart seminorms of smooth sections

A `C^n` section has a `C^n` fibre-coordinate representative in each simultaneous base chart
and bundle trivialization. The suprema of the norms of its derivatives through order `n` on
compact subsets of these domains are seminorms. They control coordinate derivatives uniformly,
and their common kernel is zero. These are the local building blocks of the compact smooth
section topology.

We work on manifolds without boundary, so the coordinate domains are open. No compactness,
finite-dimensionality, countability, fibre norm or background connection on the bundle is
required. Only the model fibre is normed. The topology, a countable defining family,
completeness and changes of atlas or connection are not constructed here.

The compact derivative seminorm convention is that of Trèves, *Topological Vector Spaces,
Distributions and Kernels*, Chapter 10. The coordinate construction uses Mathlib's
`Bundle.Trivialization.contMDiffOn_iff` and its native `ContMDiffSection` carrier.
-/

public section

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace ContMDiffSection

section Domain

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

variable (I F V) in
/-- The open coordinate domain where both the base chart and the bundle trivialization at `x`
are valid. Taking the interior avoids assigning meaning to coordinates outside the charts. -/
def chartDomain (x : M) : Set E :=
  (extChartAt I x).target ∩
    interior ((extChartAt I x).symm ⁻¹' (trivializationAt F V x).baseSet)

omit [I.Boundaryless] in
/-- Membership in a simultaneous chart domain. -/
@[simp]
theorem mem_chartDomain_iff (x : M) (z : E) :
    z ∈ chartDomain I F V x ↔ z ∈ (extChartAt I x).target ∧
      z ∈ interior ((extChartAt I x).symm ⁻¹' (trivializationAt F V x).baseSet) :=
  Iff.rfl

/-- The simultaneous coordinate domain is open. -/
theorem isOpen_chartDomain (x : M) : IsOpen (chartDomain I F V x) :=
  (isOpen_extChartAt_target x).inter isOpen_interior

/-- The simultaneous coordinate domain contains the coordinate of its centre. -/
theorem mem_chartDomain (x : M) : extChartAt I x x ∈ chartDomain I F V x := by
  refine ⟨mem_extChartAt_target x, mem_interior_iff_mem_nhds.2 ?_⟩
  have h := ((continuousOn_extChartAt_symm (I := I) x) _ (mem_extChartAt_target x)).continuousAt
    (extChartAt_target_mem_nhds (I := I) x)
  apply h.preimage_mem_nhds
  simpa only [extChartAt_to_inv] using
    (trivializationAt F V x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x)

end Domain

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]

/-- The fibre coordinates of a `C^n` section, extended by zero outside the trivialization's
base set. Only their values on `chartDomain` enter the derivative seminorms. -/
def chartCoordinates (x : M) : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] (E → F) where
  toFun s z := (trivializationAt F V x).linearMapAt 𝕜 ((extChartAt I x).symm z)
    (s ((extChartAt I x).symm z))
  map_add' s t := by
    ext z
    exact map_add ((trivializationAt F V x).linearMapAt 𝕜 _) _ _
  map_smul' c s := by
    ext z
    exact map_smul ((trivializationAt F V x).linearMapAt 𝕜 _) _ _

omit [I.Boundaryless] [IsManifold I n M] [ContMDiffVectorBundle n F V I] in
/-- On the simultaneous domain the coordinates agree with the native trivialization. -/
theorem chartCoordinates_apply (s : Cₛ^n⟮I; F, V⟯) (x : M) {z : E}
    (hz : z ∈ chartDomain I F V x) :
    chartCoordinates x s z =
      (trivializationAt F V x ⟨(extChartAt I x).symm z, s ((extChartAt I x).symm z)⟩).2 := by
  exact congrFun ((trivializationAt F V x).coe_linearMapAt_of_mem (R := 𝕜)
    (interior_subset (s := (extChartAt I x).symm ⁻¹'
      (trivializationAt F V x).baseSet) hz.2)) _

omit [IsManifold I n M] [ContMDiffVectorBundle n F V I] in
/-- Fibre coordinates recover the section at the centre of the chart. -/
@[simp]
theorem chartCoordinates_apply_self (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    chartCoordinates x s (I (chartAt H x x)) = (trivializationAt F V x ⟨x, s x⟩).2 := by
  have h := chartCoordinates_apply s x (mem_chartDomain (I := I) x)
  rw [extChartAt_to_inv] at h
  simpa only [extChartAt_coe, Function.comp_apply] using h

omit [I.Boundaryless] in
/-- The fibre-coordinate representative of a `C^n` section is `C^n` on its domain. -/
theorem contDiffOn_chartCoordinates (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    ContDiffOn 𝕜 n (chartCoordinates x s) (chartDomain I F V x) := by
  have hs := ((trivializationAt F V x).contMDiffOn_iff
    (f := fun y ↦ TotalSpace.mk' F y (s y))
    (s := (trivializationAt F V x).baseSet)
    (by intro y hy; exact (trivializationAt F V x).mem_source.2 hy)).1
    s.contMDiff.contMDiffOn
  have h := (hs.2.comp
    ((contMDiffOn_extChartAt_symm x).mono inter_subset_left)
    (fun z hz ↦ interior_subset hz.2)).contDiffOn
  exact h.congr fun z hz ↦ chartCoordinates_apply s x hz

/-- The coordinate derivative of order `m`, restricted to a compact subset of the simultaneous
chart domain. Its dependence on the section is linear. -/
def chartDerivative (x : M) (m : ℕ) (hm : m ≤ n) (K : Compacts E)
    (hK : (K : Set E) ⊆ chartDomain I F V x) :
    Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] C(K, E [×m]→L[𝕜] F) where
  toFun s := ⟨fun z ↦ iteratedFDerivWithin 𝕜 m (chartCoordinates x s)
      (chartDomain I F V x) z,
    ((contDiffOn_chartCoordinates s x).continuousOn_iteratedFDerivWithin hm
      (isOpen_chartDomain x).uniqueDiffOn).mono hK |>.domRestrict⟩
  map_add' s t := by
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, map_add]
    exact iteratedFDerivWithin_add_apply
      ((contDiffOn_chartCoordinates s x).of_le hm z (hK z.2))
      ((contDiffOn_chartCoordinates t x).of_le hm z (hK z.2))
      (isOpen_chartDomain x).uniqueDiffOn (hK z.2)
  map_smul' c s := by
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply, map_smul]
    exact iteratedFDerivWithin_const_smul_apply
      ((contDiffOn_chartCoordinates s x).of_le hm z (hK z.2))
      (isOpen_chartDomain x).uniqueDiffOn (hK z.2)

/-- Evaluation of the compact coordinate derivative. -/
@[simp]
theorem chartDerivative_apply (s : Cₛ^n⟮I; F, V⟯) (x : M) (m : ℕ) (hm : m ≤ n) (K : Compacts E)
    (hK : (K : Set E) ⊆ chartDomain I F V x) (z : K) :
    chartDerivative x m hm K hK s z =
      iteratedFDerivWithin 𝕜 m (chartCoordinates x s) (chartDomain I F V x) z :=
  (rfl)

/-- The supremum of the norm of a coordinate derivative over a compact chart subset. -/
def chartSeminorm (x : M) (m : ℕ) (hm : m ≤ n) (K : Compacts E)
    (hK : (K : Set E) ⊆ chartDomain I F V x) : Seminorm 𝕜 Cₛ^n⟮I; F, V⟯ :=
  (normSeminorm 𝕜 C(K, E [×m]→L[𝕜] F)).comp (chartDerivative x m hm K hK)

/-- The chart seminorm is the sup norm of the compact coordinate derivative. -/
@[simp]
theorem chartSeminorm_apply (s : Cₛ^n⟮I; F, V⟯) (x : M) (m : ℕ) (hm : m ≤ n) (K : Compacts E)
    (hK : (K : Set E) ⊆ chartDomain I F V x) :
    chartSeminorm x m hm K hK s = ‖chartDerivative x m hm K hK s‖ :=
  (rfl)

/-- A chart seminorm bounds the derivative at every point of its compact set. -/
theorem norm_chartDerivative_le (s : Cₛ^n⟮I; F, V⟯) (x : M) (m : ℕ) (hm : m ≤ n) (K : Compacts E)
    (hK : (K : Set E) ⊆ chartDomain I F V x) (z : K) :
    ‖chartDerivative x m hm K hK s z‖ ≤ chartSeminorm x m hm K hK s :=
  (chartDerivative x m hm K hK s).norm_coe_le_norm z

/-- A nonnegative upper bound on the chart seminorm is equivalent to the uniform bound on all
coordinate derivatives in the compact set. The nonnegativity also handles the empty set. -/
theorem chartSeminorm_le_iff (s : Cₛ^n⟮I; F, V⟯) (x : M) (m : ℕ) (hm : m ≤ n) (K : Compacts E)
    (hK : (K : Set E) ⊆ chartDomain I F V x) {r : ℝ} (hr : 0 ≤ r) :
    chartSeminorm x m hm K hK s ≤ r ↔ ∀ z : K, ‖chartDerivative x m hm K hK s z‖ ≤ r :=
  ContinuousMap.norm_le _ hr

/-- The compact chart seminorms separate sections: already their order-zero part has trivial
common kernel. -/
theorem eq_zero_iff_chartSeminorm_zero (s : Cₛ^n⟮I; F, V⟯) :
    s = 0 ↔ ∀ (x : M) (K : Compacts E) (hK : (K : Set E) ⊆ chartDomain I F V x),
      chartSeminorm x 0 (by simp) K hK s = 0 := by
  constructor
  · rintro rfl x K hK
    exact map_zero _
  · intro h
    ext x
    let K : Compacts E := ⟨{extChartAt I x x}, isCompact_singleton⟩
    have hK : (K : Set E) ⊆ chartDomain I F V x :=
      singleton_subset_iff.2 (mem_chartDomain x)
    let z : K := ⟨extChartAt I x x, mem_singleton _⟩
    have hz : chartDerivative x 0 (by simp) K hK s z = 0 := by
      apply norm_le_zero_iff.1
      exact (norm_chartDerivative_le s x 0 (by simp) K hK z).trans_eq (h x K hK)
    have hv := congrArg (fun A : E [×0]→L[𝕜] F ↦ A 0) hz
    have hcoord : (trivializationAt F V x ⟨x, s x⟩).2 = 0 := by
      simpa only [chartDerivative_apply, iteratedFDerivWithin_zero_apply, z,
        extChartAt_coe, Function.comp_apply, chartCoordinates_apply_self, zero_apply] using hv
    exact ((trivializationAt F V x).linearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F V x)).map_eq_zero_iff.1 hcoord

end ContMDiffSection
