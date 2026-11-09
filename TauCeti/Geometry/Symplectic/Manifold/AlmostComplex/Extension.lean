/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath
import Mathlib.Geometry.Manifold.PartitionOfUnity

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

## Main results

* `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eq_of_cutoff`: extend using a specified
  smooth cutoff with topological support in the prescribed open set.
* `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eqOn`: extend from an arbitrary closed
  set in a Hausdorff sigma-compact manifold, constructing the cutoff automatically.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Sections 2.5 and 4.1 (compatible Cayley charts and relative extension).
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace TauCeti
namespace SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) {U : Set M} (K : M → AlmostComplexStructure E)
  (hK : ∀ x ∈ U, (h₀.isNondegenerate.symplecticFormAt x).Compatible (K x))
  (ρ : M → ℝ) (hρ : ∀ x, ρ x ∈ Icc 0 1)

open Classical in
private def cutoffField (x : M) : AlmostComplexStructure E :=
  if hx : x ∈ U then
    (h₀.compatibleAt x).cayleyInterp (V := E) (hK x hx) (hρ x)
  else J₀.almostComplexStructureAt x

private theorem cutoffField_of_mem {x : M} (hx : x ∈ U) :
    cutoffField h₀ K hK ρ hρ x =
      (h₀.compatibleAt x).cayleyInterp (V := E) (hK x hx) (hρ x) :=
  dite_eq_left hx

private theorem cutoffField_of_notMem {x : M} (hx : x ∉ U) :
    cutoffField h₀ K hK ρ hρ x = J₀.almostComplexStructureAt x :=
  dite_eq_right hx

private theorem compatible_cutoffField (x : M) :
    (h₀.isNondegenerate.symplecticFormAt x).Compatible
      (cutoffField (E := E) h₀ K hK ρ hρ x) := by
  by_cases hx : x ∈ U
  · rw [cutoffField_of_mem h₀ K hK ρ hρ hx]
    exact (h₀.compatibleAt x).compatible_cayleyInterp (V := E) (hK x hx) (hρ x)
  · rw [cutoffField_of_notMem h₀ K hK ρ hρ hx]
    exact h₀.compatibleAt x

private theorem cutoffField_eq_background {x : M} (hx : ρ x = 0) :
    cutoffField h₀ K hK ρ hρ x = J₀.almostComplexStructureAt x := by
  by_cases hxU : x ∈ U
  · rw [cutoffField_of_mem h₀ K hK ρ hρ hxU]
    simpa only [hx] using
      (h₀.compatibleAt x).cayleyInterp_zero (V := E) (hK x hxU)
  · exact cutoffField_of_notMem h₀ K hK ρ hρ hxU

private theorem cutoffField_eq_local {x : M} (hxU : x ∈ U) (hx : ρ x = 1) :
    cutoffField h₀ K hK ρ hρ x = K x := by
  rw [cutoffField_of_mem h₀ K hK ρ hρ hxU]
  simpa only [hx] using
    (h₀.compatibleAt x).cayleyInterp_one (V := E) (hK x hxU)

private theorem cutoffField_formula {x : M} (hx : x ∈ U) :
    LinearMap.toContinuousLinearMap (cutoffField h₀ K hK ρ hρ x).toLinearMap =
      cayleyPathFormula (ρ x) (J₀.toEndomorphism x)
        (LinearMap.toContinuousLinearMap (K x).toLinearMap) := by
  rw [cutoffField_of_mem h₀ K hK ρ hρ hx]
  exact (h₀.compatibleAt x).toContinuousLinearMap_cayleyInterp (V := E) (hK x hx) (hρ x)
    (J₀.almostComplexStructureAt_toLinearMap x).symm
    (LinearMap.coe_toContinuousLinearMap _)

private theorem contMDiffAt_cutoffField_of_mem (hU : IsOpen U)
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (K x).toLinearMap)) U)
    (hsρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (x₀ : M) (hx : x₀ ∈ U) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (cutoffField h₀ K hK ρ hρ x).toLinearMap)) x₀ := by
  have hs' := ContMDiffAt.cayleyPathFormula_hom_bundle contMDiffAt_id (hsρ x₀)
    (J₀.toEndomorphism.contMDiff x₀) ((hs x₀ hx).contMDiffAt (hU.mem_nhds hx))
    (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E)
      (h₀.compatibleAt x₀).tames (hK x₀ hx).tames
      (J₀.almostComplexStructureAt_toLinearMap x₀).symm
      (LinearMap.coe_toContinuousLinearMap _))
    (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E)
      (h₀.compatibleAt x₀) (hK x₀ hx).tames
      (by simpa only [abs_of_nonneg (hρ x₀).1] using (hρ x₀).2)
      (J₀.almostComplexStructureAt_toLinearMap x₀).symm
      (LinearMap.coe_toContinuousLinearMap _))
  refine hs'.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx] with x hxU
  exact congrArg (fun L : E →L[ℝ] E ↦ TotalSpace.mk'
    (E →L[ℝ] E) (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x L)
    (cutoffField_formula h₀ K hK ρ hρ hxU)

private theorem contMDiffAt_cutoffField (hU : IsOpen U)
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (K x).toLinearMap)) U)
    (hsρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (cutoffField h₀ K hK ρ hρ x).toLinearMap)) x₀ := by
  by_cases hx : x₀ ∈ U
  · exact contMDiffAt_cutoffField_of_mem h₀ K hK ρ hρ hU hs hsρ x₀ hx
  · have hz : ∀ᶠ x in 𝓝 x₀, ρ x = 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hsupp h))
    refine (J₀.toEndomorphism.contMDiff x₀).congr_of_eventuallyEq ?_
    filter_upwards [hz] with x hx
    rw [cutoffField_eq_background h₀ K hK ρ hρ hx,
      SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    -- Converting a continuous linear map to a linear map and back is definitionally the
    -- original map; here it is read on `TangentSpace I x = E`.
    congr 1

include h₀ hK hρ in
/-- A smooth cutoff supported inside the region where a local field is smooth and compatible
extends it to a global compatible structure. Where the cutoff is one the local field is
unchanged; where it is zero the background structure is unchanged. -/
theorem exists_compatible_eq_of_cutoff (hU : IsOpen U)
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (K x).toLinearMap)) U)
    (hsρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      (∀ x, ρ x = 1 → J.almostComplexStructureAt x = K x) ∧
      (∀ x, ρ x = 0 → J.almostComplexStructureAt x = J₀.almostComplexStructureAt x) := by
  let J : SmoothAlmostComplexStructure I M :=
    { toEndomorphism := ⟨fun x ↦ LinearMap.toContinuousLinearMap
        (cutoffField h₀ K hK ρ hρ x).toLinearMap,
        contMDiffAt_cutoffField h₀ K hK ρ hρ hU hs hsρ hsupp⟩
      square_neg := fun x ↦ by
        ext v
        exact (cutoffField h₀ K hK ρ hρ x).apply_apply v }
  have hJ (x : M) : J.almostComplexStructureAt x = cutoffField (E := E) h₀ K hK ρ hρ x := by
    apply AlmostComplexStructure.toLinearMap_injective
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    exact LinearMap.coe_toContinuousLinearMap _
  refine ⟨J, h₀.isNondegenerate.compatible_iff.mpr (fun x ↦ ?_), ?_, ?_⟩
  · rw [hJ]
    exact compatible_cutoffField h₀ K hK ρ hρ x
  · intro x hx
    have hxU : x ∈ U := hsupp (subset_tsupport ρ (by simp [Function.mem_support, hx]))
    rw [hJ, cutoffField_eq_local h₀ K hK ρ hρ hxU hx]
  · intro x hx
    rw [hJ, cutoffField_eq_background h₀ K hK ρ hρ hx]

include h₀ hK in
/-- Extend a compatible field prescribed smoothly near a closed set, retaining a chosen
background compatible structure outside that neighbourhood. No closedness of the two-form or
compactness of the prescribed set is required. The local field is tested for smoothness as a
section of the tangent endomorphism bundle, not in a global trivialization. -/
theorem exists_compatible_eqOn [T2Space M] [SigmaCompactSpace M]
    (hU : IsOpen U) {A : Set M} (hA : IsClosed A) (hAU : A ⊆ U)
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (K x).toLinearMap)) U) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      (∀ x ∈ A, J.almostComplexStructureAt x = K x) ∧
      (∀ x ∉ U, J.almostComplexStructureAt x = J₀.almostComplexStructureAt x) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  obtain ⟨ρ, hsρ, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff I hV hA hAV
  have hρ : ∀ x, ρ x ∈ Icc 0 1 := fun x ↦ hrange (mem_range_self x)
  have ht : tsupport ρ ⊆ U := by
    rw [tsupport, hsupp]
    exact hVU
  obtain ⟨J, hJ, hlocal, hbase⟩ := h₀.exists_compatible_eq_of_cutoff K hK ρ hρ hU hs hsρ ht
  refine ⟨J, hJ, fun x hx ↦ hlocal x ((hone x).mp hx), fun x hx ↦ hbase x ?_⟩
  exact Function.notMem_support.mp (fun h ↦ hx (ht (subset_tsupport ρ h)))

end SmoothTwoForm.Compatible
end TauCeti
