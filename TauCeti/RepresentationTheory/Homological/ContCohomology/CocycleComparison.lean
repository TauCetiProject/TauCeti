/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CochainComparison

/-!
# Explicit and canonical continuous two-cocycles

`cocycleEquiv2` identifies continuous inhomogeneous two-cocycles with the cycles of Mathlib's
homogeneous complex. The forward formula is `g • c (g⁻¹ * h, h⁻¹ * k)`; the inverse evaluates
at `(1, g, g * h)`. The comparison is natural in compatible pairs and identifies the explicit
coboundaries with canonical boundaries, providing the cycle-level input to the comparison of
second cohomology.

This is an additive equivalence, with no assertion about the pointwise topology on explicit
cocycles. The group is locally compact: the inverse cochain comparison uses Mathlib's
`ContinuousMap.uncurry`. Coefficients are discrete with a jointly continuous action.

The formulas follow Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, second edition,
Chapter I §2. The passage from the concrete kernel to canonical cycles uses Mathlib's
`TopModuleCat.isLimitKer` and `HomologicalComplex.cyclesIsKernel`.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Continuous two-cocycles in inhomogeneous coordinates are the cycles of the canonical
homogeneous cochain complex. -/
noncomputable def cocycleEquiv2 :
    Z2 G M ≃+ _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2 :=
  ({ toFun c := ⟨cochainEquiv2 G M ⟨c.val, Z2_le_C2 G M c.property⟩,
        (d_cochainEquiv2_eq_zero_iff G M _).mpr c.property⟩
     invFun c := ⟨((cochainEquiv2 G M).symm c.val).val,
        (d_cochainEquiv2_eq_zero_iff G M _).mp (by
          rw [AddEquiv.apply_symm_apply]
          exact c.property)⟩
     left_inv c := by
       apply Subtype.ext
       exact congrArg (fun b : C2 G M => b.val)
         ((cochainEquiv2 G M).symm_apply_apply ⟨c.val, Z2_le_C2 G M c.property⟩)
     right_inv c := by
       apply Subtype.ext
       exact (cochainEquiv2 G M).apply_symm_apply c.val
     map_add' c d := by
       apply Subtype.ext
       exact (cochainEquiv2 G M).map_add
         ⟨c.val, Z2_le_C2 G M c.property⟩ ⟨d.val, Z2_le_C2 G M d.property⟩ } :
      Z2 G M ≃+ TopModuleCat.ker
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 2 3)).trans
    (Limits.IsLimit.conePointUniqueUpToIso (TopModuleCat.isLimitKer _)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).cyclesIsKernel 2 3
        (by simp))).toContinuousLinearEquiv.toAddEquiv

/-- The inclusion of a compared cocycle is the existing cochain comparison. -/
@[simp]
theorem iCycles_cocycleEquiv2 (c : Z2 G M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).sc 2).iCycles.hom
        (cocycleEquiv2 G M c) =
      cochainEquiv2 G M ⟨c.val, Z2_le_C2 G M c.property⟩ := by
  exact ConcreteCategory.congr_hom
    (Limits.IsLimit.conePointUniqueUpToIso_hom_comp (TopModuleCat.isLimitKer _)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).cyclesIsKernel 2 3 (by simp))
      Limits.WalkingParallelPair.zero) _

/-- The inverse cocycle comparison reads the canonical cocycle at `(1, g, g * h)`. -/
@[simp]
theorem cocycleEquiv2_symm_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2) (g h : G) :
    ((cocycleEquiv2 G M).symm c).val (g, h) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 2 c).val 1 g (g * h) := by
  obtain ⟨c, rfl⟩ := (cocycleEquiv2 G M).surjective c
  -- Read the short-complex inclusion as the inclusion of the homogeneous complex.
  have e : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 2
      (cocycleEquiv2 G M c) =
      cochainEquiv2 G M ⟨c.val, Z2_le_C2 G M c.property⟩ := iCycles_cocycleEquiv2 G M c
  rw [AddEquiv.symm_apply_apply, e, cochainEquiv2_apply]
  simp

/-- The comparison sends the explicit coboundary of a continuous one-cochain to its canonical
boundary, with the same primitive under the degree-one cochain comparison. -/
theorem cocycleEquiv2_d1 (c : C1 G M) :
    cocycleEquiv2 G M
        ⟨d1 G M c.val, B2_le_Z2 G M
          (mem_B2_iff.mpr ⟨c.val, mem_C1_iff.mp c.property, rfl⟩)⟩ =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).toCycles 1 2
        (cochainEquiv1 G M c) := by
  apply (cocycleEquiv2 G M).symm.injective
  apply Subtype.ext
  funext ⟨g, h⟩
  rw [AddEquiv.symm_apply_apply, cocycleEquiv2_symm_apply]
  have e := ConcreteCategory.congr_hom
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).toCycles_i 1 2)
    (cochainEquiv1 G M c)
  simp only [ConcreteCategory.comp_apply] at e
  rw [e, d_cochainEquiv1]
  simp

/-- A continuous two-cocycle is an explicit coboundary exactly when its canonical image is a
boundary. -/
theorem mem_B2_iff_cocycleEquiv2_mem_range (c : Z2 G M) :
    c.val ∈ B2 G M ↔ cocycleEquiv2 G M c ∈ Set.range
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).toCycles 1 2) := by
  constructor
  · intro hc
    obtain ⟨b, hb, he⟩ := mem_B2_iff.mp hc
    refine ⟨cochainEquiv1 G M ⟨b, mem_C1_iff.mpr hb⟩, ?_⟩
    rw [← cocycleEquiv2_d1]
    exact congrArg (cocycleEquiv2 G M) (Subtype.ext he)
  · rintro ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := (cochainEquiv1 G M).surjective b
    rw [← cocycleEquiv2_d1] at hb
    exact mem_B2_iff.mpr ⟨b.val, mem_C1_iff.mp b.property,
      congrArg Subtype.val ((cocycleEquiv2 G M).injective hb)⟩

/-- The two-cocycle comparison is natural in compatible pairs of group and coefficient maps. -/
theorem cocycleEquiv2_naturality
    (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction H N] [ContinuousSMul H N]
    (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z2 G M) :
    _root_.ContinuousCohomology.cocyclesMap φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m)) 2
        (cocycleEquiv2 G M c) =
      cocycleEquiv2 H N
        (cocyclesMap2 G M H N φ f continuous_of_discreteTopology hf c) := by
  apply (cocycleEquiv2 H N).symm.injective
  apply Subtype.ext
  funext ⟨h, k⟩
  rw [cocycleEquiv2_symm_apply, AddEquiv.symm_apply_apply]
  have e := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (_root_.ContinuousCohomology.cochainsMap φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m))) 2)
    (cocycleEquiv2 G M c)
  simp only [ConcreteCategory.comp_apply] at e
  -- `cyclesMap_i` uses the homological-complex spelling of the same inclusion.
  have hc : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 2
      (cocycleEquiv2 G M c) =
      cochainEquiv2 G M ⟨c.val, Z2_le_C2 G M c.property⟩ := iCycles_cocycleEquiv2 G M c
  rw [hc] at e
  rw [e, cochainEquiv2_naturality G M H N φ f hf]
  simp [cocyclesMap2_apply]

end TauCeti.ContCohomology
