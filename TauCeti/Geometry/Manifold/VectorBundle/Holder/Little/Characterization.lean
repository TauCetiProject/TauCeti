/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Holder.Little.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Holder.Little.Cutoff
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.ChartSection
import TauCeti.Geometry.Manifold.VectorBundle.Holder.ExtendByZero

/-!
# The little Hölder space of sections is characterized chartwise

Let `V → M` be a smooth real vector bundle with Banach model fibre `F` over a Hausdorff smooth
manifold without boundary modelled on a finite-dimensional real normed space `E`, and let `A` be a
finite bundle atlas. For `α < 1`, an element of the Hölder space `C^{k,α}(V)` lies in the little
Hölder space `h^{k,α}(V)`, the closure of the smooth sections, exactly when each of its chart
readings lies in the little Hölder space `h^{k,α}(A.image i)` of the chart image: when the `k`-th
derivative of every chart reading has `α`-Hölder difference quotients tending to zero at small
scales (`TauCeti.HolderSection.mem_littleHolder_iff_forall_mem_littleHolder_component`). By the
independence of `h^{k,α}(V)` from the atlas (`TauCeti.HolderSection.littleHolder_map_atlasEquiv`),
the vanishing of the small-scale modulus in the charts of one atlas forces it in the charts of
every other.

## The argument

Membership implies the chart condition by
`TauCeti.HolderSection.mem_littleHolder_component_of_mem_littleHolder`. For the converse, write
`w = ∑ᵢ ρᵢ w` for a smooth partition of unity `ρ` subordinate to the chart domains. The chart-`i`
reading of `ρᵢ w` is `χ wᵢ`, where `χ` is `ρᵢ` read in chart `i` and extended by zero, a smooth
function with compact support in the chart image
(`TauCeti.FiniteBundleAtlas.exists_contDiff_eqOn_comp_chart_symm`). Multiplication by `χ` maps
the little Hölder space of the chart image into the whole-space little Hölder space
(`TauCeti.CkHolderSpaceOn.cutoffSMulL_mem_littleHolder`), whose compactly supported elements are
limits of smooth maps supported in any neighbourhood of their support
(`CkHolderSpace.exists_mem_smoothBoundedDerivatives_hasCompactSupport_tsupport_subset_norm_sub_lt`).
These smooth maps are the chart-`i` readings of smooth sections supported in a fixed compact
subset `L` of the chart domain. Extension by zero from chart `i`
(`TauCeti.HolderSection.extendByZeroL`) is continuous, so these smooth sections converge to
`ρᵢ w` in `C^{k,α}(V)`.

## Main results

* `TauCeti.HolderSection.mem_littleHolder_iff_forall_mem_littleHolder_component`: for `α < 1`,
  an element of `C^{k,α}(V)` lies in `h^{k,α}(V)` exactly when its chart readings have vanishing
  small-scale `α`-Hölder modulus of their `k`-th derivatives.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13.
* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Birkhäuser
  (1995), Chapter 0, for little Hölder spaces as closures of smooth functions.
-/

public section

noncomputable section

open Bundle Set Metric
open scoped Manifold NNReal ContDiff Topology

universe u

namespace TauCeti

namespace HolderSection

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] {A : FiniteBundleAtlas E M F V} {k : ℕ} {α : ℝ≥0}

/-- **Little Hölder functions in one chart extend to little Hölder sections.** For `α < 1`, let
`K'` be a compact subset of the image of chart `i`, and let `g` be a compactly supported element of
the whole-space little Hölder space `h^{k,α}(E)` supported in the interior of `K'`. The extension by
zero from chart `i` of the restriction of `g` to the chart image lies in `h^{k,α}(V)`: it is the
limit of the extensions by zero of smooth approximants of `g`, which are smooth sections. -/
private theorem extendByZeroL_restrictOnL_mem_littleHolder (hα : α < 1)
    (hn : (k : WithTop ℕ∞) + 1 ≤ ∞) {i : Fin A.n} {K' : Set E} (hK'i : K' ⊆ A.image i)
    (hL : IsClosed ((A.chart i).symm '' K')) (hLi : (A.chart i).symm '' K' ⊆ A.dom i)
    {g : CkHolderSpace k α E F} (hg : g ∈ CkHolderSpace.littleHolder k α E F)
    (hgc : HasCompactSupport g) (hgK : tsupport g ⊆ interior K') :
    extendByZeroL hα.le hn hL hLi
      ⟨_, restrictOnL_mem_chartZeroOff (hgK.trans interior_subset)⟩ ∈ littleHolder A k α := by
  set S := extendByZeroL hα.le hn hL hLi
  set T : Set (chartZeroOff A k α i ((A.chart i).symm '' K')) :=
    S ⁻¹' (smoothSections A k α : Set (HolderSection A k α))
  have hT : (⟨_, restrictOnL_mem_chartZeroOff (hgK.trans interior_subset)⟩ :
      chartZeroOff A k α i ((A.chart i).symm '' K')) ∈ closure T := by
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    obtain ⟨g', hg', hg'c, hg'K', hgg'⟩ :=
      g.exists_mem_smoothBoundedDerivatives_hasCompactSupport_tsupport_subset_norm_sub_lt hg
        hgc isOpen_interior hgK hε
    refine ⟨⟨_, restrictOnL_mem_chartZeroOff (hg'K'.trans interior_subset)⟩, ?_, ?_⟩
    · -- The extension by zero of the restriction of `g'` is a smooth section.
      obtain ⟨ξ, hξ, hξg', hξL⟩ := A.exists_contMDiff_eqOn_coord
        (CkHolderSpace.mem_smoothBoundedDerivatives_iff.1 hg').1 hg'c
        (hg'K'.trans (interior_subset.trans hK'i))
      have hξdom (x : M) (hx : x ∉ A.dom i) : ξ x = 0 := by
        by_contra hξx
        obtain ⟨y, hy, rfl⟩ := hξL (subset_closure hξx)
        exact hx (hLi ⟨y, interior_subset (hg'K' hy), rfl⟩)
      rw [mem_preimage, SetLike.mem_coe, mem_smoothSections_iff,
        toSection_extendByZeroL_eq hα.le hn hL hLi hξdom fun y ↦ by
          rw [CkHolderSpace.restrictOnL_apply]
          exact (hξg' y.property).symm]
      exact hξ
    · rw [Subtype.dist_eq, dist_eq_norm, ← map_sub]
      exact ((CkHolderSpace.restrictOnL (A.image i)).le_of_opNorm_le
        (CkHolderSpace.norm_restrictOnL_le_one (A.image i)) _).trans_lt (by rwa [one_mul])
  rw [← SetLike.mem_coe, coe_littleHolder]
  exact map_mem_closure S.continuous hT (mapsTo_preimage _ _)

/-- **Pieces of a little Hölder section.** For `α < 1`, let `w ∈ C^{k,α}(V)` have chart-`i`
reading in the little Hölder space of the chart image, and let `ρ` be a smooth function supported in
the domain of chart `i`. Then `ρ w` is an element of the little Hölder space `h^{k,α}(V)`. -/
private theorem exists_mem_littleHolder_toSection_eq_smul (hα : α < 1) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ) {i : Fin A.n} (hρi : tsupport ρ ⊆ A.dom i)
    (w : HolderSection A k α)
    (hw : (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i ∈
      CkHolderSpaceOn.littleHolder k α (A.image i) F) :
    ∃ v ∈ littleHolder A k α, toSection v = fun x ↦ ρ x • toSection w x := by
  -- The cutoff `χ`: `ρ` read in chart `i`, supported in the compact set `K ⊆ A.image i`.
  set K := A.chart i '' tsupport ρ
  have hK : IsCompact K := A.isCompact_chart_image_of_isClosed (isClosed_tsupport ρ) hρi
  have hKi : K ⊆ A.image i := by
    rintro _ ⟨x, hx, rfl⟩
    exact A.mem_image.2 ⟨x, hρi hx, rfl⟩
  obtain ⟨χ, hχ, hχK, hχi⟩ := A.exists_contDiff_eqOn_comp_chart_symm hρ hρi
  have hχK' : tsupport χ ⊆ K :=
    closure_minimal (fun y hy ↦ by_contra fun h ↦ hy (hχK y h)) hK.isClosed
  obtain ⟨C, -, hC⟩ := (HasCompactSupport.intro hK hχK).exists_bound_iteratedFDeriv_of_contDiff
    (n := k + 1) (hχ.of_le (by exact_mod_cast le_top))
  have hχb : ∀ j ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ j χ y‖ ≤ C.toNNReal :=
    fun j hj y ↦ (hC j hj y).trans (Real.le_coe_toNNReal C)
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open (A.image i).isOpen hKi
  have hχΩ : thickening (δ.toNNReal : ℝ) (tsupport χ) ⊆ A.image i := by
    rw [Real.coe_toNNReal _ hδ.le]
    exact (thickening_subset_of_subset δ hχK').trans hδK
  -- `g = χ wᵢ` is a compactly supported element of the whole-space little Hölder space, and
  -- its restriction to the chart image is the chart-`i` reading of `ρ w`.
  set wᵢ := (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i
  set g := CkHolderSpaceOn.cutoffSMulL (hχ.of_le (by exact_mod_cast le_top))
    (Real.toNNReal_pos.2 hδ) hχΩ hα.le hχb wᵢ
  have hgK : tsupport g ⊆ K := (CkHolderSpaceOn.tsupport_cutoffSMulL_subset _ _ _ _ _ _).trans hχK'
  -- A compact `K'` between `K` and the chart image, and its preimage in the chart domain.
  obtain ⟨K', hK', hKK', hK'i⟩ := exists_compact_between hK (A.image i).isOpen hKi
  have hn : (k : WithTop ℕ∞) + 1 ≤ ∞ := by exact_mod_cast le_top
  have hL : IsClosed ((A.chart i).symm '' K') :=
    (hK'.image_of_continuousOn ((A.continuousOn_chart_symm i).mono hK'i)).isClosed
  have hLi : (A.chart i).symm '' K' ⊆ A.dom i := by
    rintro _ ⟨y, hy, rfl⟩
    exact A.symm_mem_dom (hK'i hy)
  refine ⟨_, extendByZeroL_restrictOnL_mem_littleHolder hα hn hK'i hL hLi
    (CkHolderSpaceOn.cutoffSMulL_mem_littleHolder _ _ hχΩ hα hχb hw)
    (HasCompactSupport.intro hK fun y hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hy (hgK h))
    (hgK.trans hKK'), toSection_extendByZeroL_eq hα.le hn hL hLi (fun x hx ↦ ?_) fun y ↦ ?_⟩
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hρi h), zero_smul]
  · rw [CkHolderSpace.restrictOnL_apply, CkHolderSpaceOn.cutoffSMulL_apply_coe,
      hχi y.property, A.coord_fun_smul i _ _ y.property, coord_toSection]

/-- **The little Hölder space of sections is characterized by vanishing small-scale modulus in the
charts.** For `α < 1`, an element of `C^{k,α}(V)` lies in the little Hölder space `h^{k,α}(V)`,
the closure of the smooth sections, exactly when each of its chart readings lies in the little
Hölder space of the chart image: the `k`-th derivative of every chart reading has `α`-Hölder
difference quotients tending to zero at small scales. -/
theorem mem_littleHolder_iff_forall_mem_littleHolder_component (hα : α < 1)
    {w : HolderSection A k α} :
    w ∈ littleHolder A k α ↔ ∀ i, (w : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i ∈
      CkHolderSpaceOn.littleHolder k α (A.image i) F := by
  refine ⟨fun hw i ↦ mem_littleHolder_component_of_mem_littleHolder hα hw i, fun hw ↦ ?_⟩
  have := A.compactSpace
  -- Decompose `w` by a smooth partition of unity subordinate to the chart domains.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ A.dom
    A.isOpen_dom (by simp [A.iUnion_dom])
  choose v hv hvw using fun i ↦
    exists_mem_littleHolder_toSection_eq_smul hα (ρ i).contMDiff (hρ i) w (hw i)
  have hsum : w = ∑ i, v i := by
    refine ext (funext fun x ↦ ?_)
    rw [map_sum, Finset.sum_apply]
    simp only [hvw]
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one (mem_univ x), one_smul]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ ↦ hv i

end HolderSection

end TauCeti
