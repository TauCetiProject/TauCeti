/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Cayley.Smooth
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
The coordinate smoothness argument follows the tangent-bundle Cayley path construction in
`TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath`, but requires regularity only
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

private def cutoffField (x : M) : AlmostComplexStructure E := by
  classical
  exact if hx : x ∈ U then
    ((h₀.compatibleAt x).cayleyEquiv.symm
      ⟨ρ x • (J₀.almostComplexStructureAt x).cayley (K x),
        (h₀.compatibleAt x).smul_cayley_mem_cayleyBall (hK x hx).tames (hρ x)⟩).val
  else J₀.almostComplexStructureAt x

private theorem cayley_cutoffField {x : M} (hx : x ∈ U) :
    (J₀.almostComplexStructureAt x).cayley (cutoffField (E := E) h₀ K hK ρ hρ x) =
      ρ x • (J₀.almostComplexStructureAt x).cayley (K x) := by
  erw [cutoffField, dite_eq_left hx]
  have h := congrArg Subtype.val ((h₀.compatibleAt x).cayleyEquiv.apply_symm_apply
    ⟨ρ x • (J₀.almostComplexStructureAt x).cayley (K x),
      (h₀.compatibleAt x).smul_cayley_mem_cayleyBall (hK x hx).tames (hρ x)⟩)
  rw [SymplecticForm.Compatible.cayleyEquiv_apply_coe] at h
  exact h

private theorem compatible_cutoffField (x : M) :
    (h₀.isNondegenerate.symplecticFormAt x).Compatible
      (cutoffField (E := E) h₀ K hK ρ hρ x) := by
  by_cases hx : x ∈ U
  · have ht : (h₀.isNondegenerate.symplecticFormAt x).Tames
        (cutoffField (E := E) h₀ K hK ρ hρ x) := by
      erw [cutoffField, dite_eq_left hx]
      exact Subtype.property _
    rw [← (h₀.compatibleAt x).cayley_mem_compatibleCayleyBall_iff ht,
      cayley_cutoffField h₀ K hK ρ hρ hx]
    exact (h₀.compatibleAt x).smul_cayley_mem_compatibleCayleyBall (hK x hx) (hρ x)
  · erw [cutoffField, dite_eq_right hx]
    exact h₀.compatibleAt x

private theorem cutoffField_eq_background {x : M} (hx : ρ x = 0) :
    cutoffField h₀ K hK ρ hρ x = J₀.almostComplexStructureAt x := by
  by_cases hxU : x ∈ U
  · apply (h₀.compatibleAt x).eq_of_cayley_eq
      (compatible_cutoffField h₀ K hK ρ hρ x).tames (h₀.compatibleAt x).tames
    simp [cayley_cutoffField h₀ K hK ρ hρ hxU, hx]
  · erw [cutoffField, dite_eq_right hxU]

private theorem cutoffField_eq_local {x : M} (hxU : x ∈ U) (hx : ρ x = 1) :
    cutoffField h₀ K hK ρ hρ x = K x := by
  apply (h₀.compatibleAt x).eq_of_cayley_eq
    (compatible_cutoffField h₀ K hK ρ hρ x).tames (hK x hxU).tames
  simp [cayley_cutoffField h₀ K hK ρ hρ hxU, hx]

private theorem cutoffField_formula {x : M} (hx : x ∈ U) :
    LinearMap.toContinuousLinearMap (cutoffField h₀ K hK ρ hρ x).toLinearMap =
      cayleyPathFormula (ρ x) (J₀.toEndomorphism x)
        (LinearMap.toContinuousLinearMap (K x).toLinearMap) := by
  erw [cutoffField, dite_eq_left hx]
  exact SymplecticForm.Compatible.toContinuousLinearMap_cayleyEquiv_symm_smul_cayley
    (V := E) (h₀.compatibleAt x)
    (hK x hx).tames (hρ x) (J₀.almostComplexStructureAt_toLinearMap x).symm
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
  -- Work in the tangent frame at `x₀`. Both Cayley inverse denominators are units.
  rw [contMDiffAt_hom_bundle]
  constructor
  · exact contMDiffAt_id
  · let e := trivializationAt E (TangentSpace I) x₀
    let coord : (x : M) → (TangentSpace I x →L[ℝ] TangentSpace I x) → E →L[ℝ] E :=
      fun x A ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        x₀ x x₀ x A
    have hconj {x : M} (hx : x ∈ e.baseSet) (A : TangentSpace I x →L[ℝ] TangentSpace I x) :
        coord x A = (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv A := by
      simp only [coord, e, ContinuousLinearMap.inCoordinates_eq hx hx,
        ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
    have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hinner : ContMDiffAt I 𝓘(ℝ, ℝ × (E →L[ℝ] E) × (E →L[ℝ] E)) ∞
        (fun x ↦ (ρ x, coord x (J₀.toEndomorphism x),
          coord x (LinearMap.toContinuousLinearMap (K x).toLinearMap))) x₀ :=
      (hsρ x₀).prodMk_space
        (((contMDiffAt_hom_bundle _).1 (J₀.toEndomorphism.contMDiff x₀)).2.prodMk_space
          ((contMDiffAt_hom_bundle _).1 ((hs x₀ hx).contMDiffAt (hU.mem_nhds hx))).2)
    -- Both inverse denominators are units, and conjugation into a tangent frame preserves
    -- the Cayley expression. This gives smoothness without differentiating a moving frame.
    let φ := (e.continuousLinearEquivAt ℝ x₀ hx₀).conjContinuousAlgEquiv
    have hu₁ : IsUnit (1 - coord x₀ (J₀.toEndomorphism x₀) *
        coord x₀ (LinearMap.toContinuousLinearMap (K x₀).toLinearMap)) := by
      rw [hconj hx₀, hconj hx₀, ← map_mul, ← map_one φ, ← map_sub]
      exact (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E)
        (h₀.compatibleAt x₀).tames
        (hK x₀ hx).tames (J₀.almostComplexStructureAt_toLinearMap x₀).symm
        (LinearMap.coe_toContinuousLinearMap _)).map φ
    have hu₂ : IsUnit (1 - ρ x₀ • cayleyFormula (coord x₀ (J₀.toEndomorphism x₀))
        (coord x₀ (LinearMap.toContinuousLinearMap (K x₀).toLinearMap))) := by
      rw [hconj hx₀, hconj hx₀, ← map_cayleyFormula, ← map_smul, ← map_one φ, ← map_sub]
      exact (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E)
        (h₀.compatibleAt x₀) (hK x₀ hx).tames
        (hρ x₀) (J₀.almostComplexStructureAt_toLinearMap x₀).symm
        (LinearMap.coe_toContinuousLinearMap _)).map φ
    refine ((contDiffAt_cayleyPathFormula hu₁ hu₂).comp_contMDiffAt
      (f := fun x ↦ (ρ x, coord x (J₀.toEndomorphism x),
        coord x (LinearMap.toContinuousLinearMap (K x).toLinearMap)))
      hinner).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx, e.open_baseSet.mem_nhds hx₀] with x hxU hxe
    erw [Function.comp_apply, cutoffField_formula h₀ K hK ρ hρ hxU]
    rw [hconj hxe, hconj hxe]
    exact (hconj hxe _).trans (map_cayleyPathFormula _ _ _ _)

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
