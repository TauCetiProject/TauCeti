/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Extending compatible almost complex structures from a closed region

A compatible almost complex structure prescribed smoothly on an open neighbourhood of a
closed set extends to the whole manifold, agreeing with a chosen background structure outside
that neighbourhood. The local field is a total function, but its regularity and compatibility
are required only on the given open set; its values elsewhere have no effect.

The construction cuts off the local field in the Cayley chart of the background structure,
not by averaging almost complex structures. The convexity of the compatible Cayley ball
preserves compatibility. A cutoff whose topological support lies in the open set makes the
result smooth even where the prescribed field is not defined smoothly.
The coordinate smoothness argument uses the pointwise tangent-bundle Cayley formula lemma in
`TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath`, requiring regularity only
on the open region where the local field is used.

The cutoff interpolation is defined pointwise for structures along any map `f : N → M`, so the
same construction serves parametrized families of structures on `M`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.cutoffInterp`: Cayley interpolation from a compatible
  background towards prescribed structures, with a given weight, along a map `f : N → M`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_cutoffInterp`: it is smooth along a smooth
  `f` for a smooth weight with topological support where the prescribed structures are smooth.
* `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eq_of_cutoff`: extend using a specified
  smooth cutoff with topological support in the prescribed open set.
* `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eqOn`: extend from an arbitrary closed
  set in a Hausdorff sigma-compact manifold, constructing the cutoff with
  `IsClosed.exists_contMDiff_tsupport_subset_eq_one_iff`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Sections 2.5 and 4.1 (compatible Cayley charts and relative extension).
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Cutoff interpolation along a smooth map -/

namespace SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} (hσn : σ.IsNondegenerate) {N : Type*} {f : N → M} {W : Set N}
  {K₀ K₁ : ∀ n : N, AlmostComplexStructure (TangentSpace I (f n))}
  (hK₀ : ∀ n, (hσn.symplecticFormAt (f n)).Compatible (K₀ n))
  (hK₁ : ∀ n ∈ W, (hσn.symplecticFormAt (f n)).Compatible (K₁ n))
  (ρ : N → ℝ) (hρ : ∀ n, ρ n ∈ Icc 0 1)

open Classical in
/-- Cutoff interpolation of structures along a map `f : N → M`: over `W`, the compatible Cayley
interpolation from the background `K₀ n` towards the prescribed `K₁ n` with weight `ρ n`;
elsewhere, `K₀ n`. -/
def cutoffInterp (n : N) : AlmostComplexStructure (TangentSpace I (f n)) :=
  if h : n ∈ W then (hK₀ n).cayleyInterp (V := E) (hK₁ n h) (hρ n) else K₀ n

/-- Over `W`, cutoff interpolation is the compatible Cayley interpolation. -/
theorem cutoffInterp_of_mem {n : N} (h : n ∈ W) :
    cutoffInterp hσn hK₀ hK₁ ρ hρ n = (hK₀ n).cayleyInterp (V := E) (hK₁ n h) (hρ n) :=
  dite_eq_left h

/-- Outside `W`, cutoff interpolation is the background structure. -/
@[simp]
theorem cutoffInterp_of_notMem {n : N} (h : n ∉ W) :
    cutoffInterp hσn hK₀ hK₁ ρ hρ n = K₀ n :=
  dite_eq_right h

/-- Cutoff interpolation is compatible everywhere. -/
theorem compatible_cutoffInterp (n : N) :
    (hσn.symplecticFormAt (f n)).Compatible (cutoffInterp hσn hK₀ hK₁ ρ hρ n) := by
  by_cases h : n ∈ W
  · rw [cutoffInterp_of_mem hσn hK₀ hK₁ ρ hρ h]
    exact (hK₀ n).compatible_cayleyInterp (V := E) (hK₁ n h) (hρ n)
  · rw [cutoffInterp_of_notMem hσn hK₀ hK₁ ρ hρ h]
    exact hK₀ n

/-- Where the weight vanishes, cutoff interpolation is the background structure. -/
@[simp]
theorem cutoffInterp_of_eq_zero {n : N} (h : ρ n = 0) :
    cutoffInterp hσn hK₀ hK₁ ρ hρ n = K₀ n := by
  by_cases hW : n ∈ W
  · rw [cutoffInterp_of_mem hσn hK₀ hK₁ ρ hρ hW]
    simp only [h]
    exact (hK₀ n).cayleyInterp_zero (V := E) (hK₁ n hW)
  · exact cutoffInterp_of_notMem hσn hK₀ hK₁ ρ hρ hW

/-- Over `W`, where the weight is one, cutoff interpolation is the prescribed structure. -/
@[simp]
theorem cutoffInterp_of_eq_one {n : N} (hW : n ∈ W) (h : ρ n = 1) :
    cutoffInterp hσn hK₀ hK₁ ρ hρ n = K₁ n := by
  rw [cutoffInterp_of_mem hσn hK₀ hK₁ ρ hρ hW]
  simp only [h]
  exact (hK₀ n).cayleyInterp_one (V := E) (hK₁ n hW)

/-- Where the prescribed structure is the background one, or outside `W`, cutoff interpolation is
the background structure. -/
@[simp]
theorem cutoffInterp_of_eq {n : N} (h : n ∈ W → K₁ n = K₀ n) :
    cutoffInterp hσn hK₀ hK₁ ρ hρ n = K₀ n := by
  by_cases hW : n ∈ W
  · rw [cutoffInterp_of_mem hσn hK₀ hK₁ ρ hρ hW]
    generalize hK₁ n hW = h₁
    revert h₁
    rw [h hW]
    exact fun h₁ => (hK₀ n).cayleyInterp_self (V := E) h₁ (hρ n)
  · exact cutoffInterp_of_notMem hσn hK₀ hK₁ ρ hρ hW

/-- Over `W`, cutoff interpolation is the Cayley path expression in the operators of `K₀` and
`K₁`. -/
theorem toContinuousLinearMap_cutoffInterp {n : N} (h : n ∈ W) :
    LinearMap.toContinuousLinearMap (cutoffInterp hσn hK₀ hK₁ ρ hρ n).toLinearMap =
      cayleyPathFormula (ρ n) (LinearMap.toContinuousLinearMap (K₀ n).toLinearMap)
        (LinearMap.toContinuousLinearMap (K₁ n).toLinearMap) := by
  rw [cutoffInterp_of_mem hσn hK₀ hK₁ ρ hρ h]
  exact (hK₀ n).toContinuousLinearMap_cayleyInterp (V := E) (hK₁ n h) (hρ n)
    (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)

/-- **Smoothness of cutoff interpolation.** Along a smooth map `f : N → M`, let the background
be smooth everywhere and the prescribed structures smooth on an open set `W`. For a smooth weight
with topological support in `W`, the cutoff interpolation is smooth as a section of the tangent
endomorphism bundle along `f`. -/
theorem contMDiff_cutoffInterp {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    (hf : ContMDiff IN I ∞ f) (hW : IsOpen W)
    (hK₀s : ContMDiff IN (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun n ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f n) (LinearMap.toContinuousLinearMap (K₀ n).toLinearMap)))
    (hK₁s : ContMDiffOn IN (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun n ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f n) (LinearMap.toContinuousLinearMap (K₁ n).toLinearMap)) W)
    (hsρ : ContMDiff IN 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ W) :
    ContMDiff IN (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun n ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f n) (LinearMap.toContinuousLinearMap (cutoffInterp hσn hK₀ hK₁ ρ hρ n).toLinearMap)) := by
  intro n₀
  by_cases h₀ : n₀ ∈ W
  · -- Over the open set `W` the interpolation is the Cayley path expression.
    have hu₁ := SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E)
      (hK₀ n₀).tames (hK₁ n₀ h₀).tames
      (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)
    have hu₂ := SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E)
      (hK₀ n₀) (hK₁ n₀ h₀).tames (b := ρ n₀)
      (by simpa only [abs_of_nonneg (hρ n₀).1] using (hρ n₀).2)
      (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)
    refine (ContMDiffAt.cayleyPathFormula_hom_bundle (hf n₀) (hsρ n₀) (hK₀s n₀)
      ((hK₁s n₀ h₀).contMDiffAt (hW.mem_nhds h₀)) hu₁ hu₂).congr_of_eventuallyEq ?_
    filter_upwards [hW.mem_nhds h₀] with n hn
    exact congrArg (fun L : E →L[ℝ] E ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f n) L)
      (toContinuousLinearMap_cutoffInterp hσn hK₀ hK₁ ρ hρ hn)
  · -- Away from the support of the weight the interpolation is the background.
    have hz : ∀ᶠ n in 𝓝 n₀, ρ n = 0 :=
      notMem_tsupport_iff_eventuallyEq.mp fun h ↦ h₀ (hsupp h)
    refine (hK₀s n₀).congr_of_eventuallyEq ?_
    filter_upwards [hz] with n hn
    rw [cutoffInterp_of_eq_zero hσn hK₀ hK₁ ρ hρ hn]

end SmoothTwoForm.IsNondegenerate

/-! ### Extension from a closed region -/

namespace SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) {U : Set M} (K : M → AlmostComplexStructure E)
  (hK : ∀ x ∈ U, (h₀.isNondegenerate.symplecticFormAt x).Compatible (K x))
  (ρ : M → ℝ) (hρ : ∀ x, ρ x ∈ Icc 0 1)

include h₀ hK hρ in
/-- A smooth cutoff supported inside the region where a local field is smooth and compatible
extends it to a global compatible structure. Where the cutoff is one the local field is
unchanged; where it is zero, or where the local field is the background structure, the background
structure is unchanged. -/
theorem exists_compatible_eq_of_cutoff (hU : IsOpen U)
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (K x).toLinearMap)) U)
    (hsρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      (∀ x, ρ x = 1 → J.almostComplexStructureAt x = K x) ∧
      (∀ x, ρ x = 0 → J.almostComplexStructureAt x = J₀.almostComplexStructureAt x) ∧
      (∀ x, (x ∈ U → K x = J₀.almostComplexStructureAt x) →
        J.almostComplexStructureAt x = J₀.almostComplexStructureAt x) := by
  -- Cutoff interpolation along the identity, with background `J₀`.
  let L := h₀.isNondegenerate.cutoffInterp (f := id) h₀.compatibleAt hK ρ hρ
  have hJ₀s : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (J₀.almostComplexStructureAt x).toLinearMap)) := by
    refine J₀.toEndomorphism.contMDiff.congr fun x ↦ ?_
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    -- Converting a continuous linear map to a linear map and back is definitionally the
    -- original map; here it is read on `TangentSpace I x = E`.
    congr 1
  let J : SmoothAlmostComplexStructure I M :=
    { toEndomorphism := ⟨fun x ↦ LinearMap.toContinuousLinearMap (L x).toLinearMap,
        h₀.isNondegenerate.contMDiff_cutoffInterp (f := id) h₀.compatibleAt hK ρ hρ contMDiff_id
          hU hJ₀s hs hsρ hsupp⟩
      square_neg := fun x ↦ by
        ext v
        exact (L x).apply_apply v }
  have hJ (x : M) : J.almostComplexStructureAt x = L x := by
    apply AlmostComplexStructure.toLinearMap_injective
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    exact LinearMap.coe_toContinuousLinearMap _
  refine ⟨J, h₀.isNondegenerate.compatible_iff.mpr (fun x ↦ ?_), ?_, ?_, ?_⟩
  · rw [hJ]
    exact h₀.isNondegenerate.compatible_cutoffInterp (f := id) h₀.compatibleAt hK ρ hρ x
  · intro x hx
    have hxU : x ∈ U := hsupp (subset_tsupport ρ (by simp [Function.mem_support, hx]))
    rw [hJ]
    exact h₀.isNondegenerate.cutoffInterp_of_eq_one (f := id) h₀.compatibleAt hK ρ hρ hxU hx
  · intro x hx
    rw [hJ]
    exact h₀.isNondegenerate.cutoffInterp_of_eq_zero (f := id) h₀.compatibleAt hK ρ hρ hx
  · intro x hx
    rw [hJ]
    exact h₀.isNondegenerate.cutoffInterp_of_eq (f := id) h₀.compatibleAt hK ρ hρ hx

include h₀ hK in
/-- Extend a compatible field prescribed smoothly near a closed set, retaining a chosen
background compatible structure outside that neighbourhood. No closedness of the two-form or
compactness of the prescribed set is required. The local field is tested for smoothness as a
section of the tangent endomorphism bundle, not in a global trivialization. Wherever the local
field is the background structure, so is the extension. -/
theorem exists_compatible_eqOn [T2Space M] [SigmaCompactSpace M]
    (hU : IsOpen U) {A : Set M} (hA : IsClosed A) (hAU : A ⊆ U)
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (K x).toLinearMap)) U) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      (∀ x ∈ A, J.almostComplexStructureAt x = K x) ∧
      (∀ x ∉ U, J.almostComplexStructureAt x = J₀.almostComplexStructureAt x) ∧
      (∀ x, (x ∈ U → K x = J₀.almostComplexStructureAt x) →
        J.almostComplexStructureAt x = J₀.almostComplexStructureAt x) := by
  obtain ⟨ρ, hsρ, hρ, ht, hone⟩ := hA.exists_contMDiff_tsupport_subset_eq_one_iff (I := I) hU hAU
  obtain ⟨J, hJ, hlocal, hbase, hagree⟩ := h₀.exists_compatible_eq_of_cutoff K hK ρ hρ hU hs hsρ ht
  refine ⟨J, hJ, fun x hx ↦ hlocal x ((hone x).mp hx), fun x hx ↦ hbase x ?_, hagree⟩
  exact Function.notMem_support.mp (fun h ↦ hx (ht (subset_tsupport ρ h)))

end SmoothTwoForm.Compatible
end TauCeti
