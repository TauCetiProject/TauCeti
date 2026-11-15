/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Simple-root coefficients in the numbered simply connected root datum

In the pinned datum `TauCeti.DynkinType.simplyConnectedRootDatum`, simple roots are numbered by
`Fin t.rank` in the Bourbaki order and the simple root `i` is row `i` of the Cartan matrix. This
file renumbers the columns of `RootPairing.Base.rootCoefficients` and the reflections
`RootPairing.Base.coefficientReflection` by that order, so that they become statements about
`t.cartanMatrix` alone: reflecting at `i` is `Matrix.columnReflection`, evaluation of a column in
the root lattice is the product `c ᵥ* t.cartanMatrix`, and the root columns are recovered as the
orbits of the coordinate columns. These are simple-root coordinates, not the fundamental-weight
coordinates of the character lattice of the datum.

## Main definitions

* `TauCeti.DynkinType.simpleRootCoefficients`: the numbered column of a root.

## Main results

* `TauCeti.DynkinType.columnReflection_comp_simpleSupportEquiv`: the numbered reflection is the
  reflection of the base, relabelled.
* `TauCeti.DynkinType.reflection_vecMul_cartanMatrix`: `c ↦ c ᵥ* t.cartanMatrix` intertwines the
  numbered reflection with the actual reflection.
* `TauCeti.DynkinType.simpleRootCoefficients_eq_iff`: the characterization of the numbered column.
* `TauCeti.DynkinType.columnReflection_simpleRootCoefficients`: the numbered reflection computes the
  numbered column of the reflected root.
* `TauCeti.DynkinType.iUnion_orbit_single_eq_range_simpleRootCoefficients`: the root columns are the
  orbits of the coordinate columns.
* `TauCeti.DynkinType.iUnion_orbit_single_inter_Ici_eq_image_isPos`: the nonnegative ones are the
  columns of the positive roots.
-/

public noncomputable section

open Function Set Matrix

namespace TauCeti.DynkinType

variable (t : DynkinType) (ht : t.Valid)

/-- The Cartan matrix of the numbered base is the Bourbaki-numbered Cartan matrix. -/
theorem cartanMatrix_simplyConnectedBase_apply (i j : Fin t.rank) :
    (t.simplyConnectedBase ht).cartanMatrix (t.simpleSupportEquivSimplyConnectedBase ht i)
        (t.simpleSupportEquivSimplyConnectedBase ht j) =
      t.cartanMatrix i j := by
  simp [RootPairing.Base.cartanMatrixIn_def, pairingIn_simpleIndex]

/-- The numbered reflection on columns is the reflection of the numbered base, relabelled. -/
theorem columnReflection_comp_simpleSupportEquiv (i : Fin t.rank)
    (c : (t.simplyConnectedBase ht).support → ℤ) :
    t.cartanMatrix.columnReflection t.cartanMatrix_apply_same i
        (c ∘ t.simpleSupportEquivSimplyConnectedBase ht) =
      (t.simplyConnectedBase ht).coefficientReflection
          (t.simpleSupportEquivSimplyConnectedBase ht i) c ∘
        t.simpleSupportEquivSimplyConnectedBase ht :=
  Matrix.columnReflection_comp_equiv _ _ _ _
    (fun i j ↦ (t.cartanMatrix_simplyConnectedBase_apply ht i j).symm) i c

/-- Evaluating a numbered column on the simple roots is the product with the Cartan matrix, since
the simple roots are its rows. -/
theorem sum_smul_root_simpleIndex (c : Fin t.rank → ℤ) :
    ∑ i, c i • (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) =
      c ᵥ* t.cartanMatrix := by
  rw [Matrix.vecMul_eq_sum]
  simp

/-- Evaluation of a column in the root lattice is, in the numbering, the product with the Cartan
matrix. -/
theorem coe_toWeightBasisInt_equivFun_symm_comp_symm (c : Fin t.rank → ℤ) :
    (((t.simplyConnectedBase ht).toWeightBasisInt.equivFun.symm
        (c ∘ (t.simpleSupportEquivSimplyConnectedBase ht).symm) :
          (t.simplyConnectedRootDatum ht).rootSpan ℤ) : Fin t.rank → ℤ) =
      c ᵥ* t.cartanMatrix := by
  rw [RootPairing.Base.coe_toWeightBasisInt_equivFun_symm,
    ← (t.simpleSupportEquivSimplyConnectedBase ht).sum_comp]
  simpa using t.sum_smul_root_simpleIndex ht c

/-- **The product with the Cartan matrix intertwines the numbered reflection on columns with the
actual reflection.** -/
theorem reflection_vecMul_cartanMatrix (i : Fin t.rank) (c : Fin t.rank → ℤ) :
    (t.simplyConnectedRootDatum ht).reflection (t.simpleIndex ht i) (c ᵥ* t.cartanMatrix) =
      t.cartanMatrix.columnReflection t.cartanMatrix_apply_same i c ᵥ* t.cartanMatrix := by
  simp only [← sum_smul_root_simpleIndex t ht, Matrix.sum_columnReflection_smul,
    RootPairing.reflection_sum_zsmul_root, pairingIn_simpleIndex]

/-! ### The numbered column of a root -/

/-- The column of simple-root coefficients of a root of the pinned datum, in the Bourbaki numbering
of the simple roots. -/
def simpleRootCoefficients (k : Fin t.numRoots) : Fin t.rank → ℤ :=
  (t.simplyConnectedBase ht).rootCoefficients k ∘ t.simpleSupportEquivSimplyConnectedBase ht

/-- The numbered column of a root is the only column whose product with the Cartan matrix is that
root. -/
theorem simpleRootCoefficients_eq_iff {k : Fin t.numRoots} {c : Fin t.rank → ℤ} :
    t.simpleRootCoefficients ht k = c ↔
      c ᵥ* t.cartanMatrix = (t.simplyConnectedRootDatum ht).root k := by
  rw [simpleRootCoefficients, ← Equiv.eq_comp_symm, RootPairing.Base.rootCoefficients_eq_iff,
    ← (t.simpleSupportEquivSimplyConnectedBase ht).sum_comp, ← sum_smul_root_simpleIndex t ht]
  simp

/-- The product of the numbered column of a root with the Cartan matrix is the root. -/
@[simp]
theorem vecMul_simpleRootCoefficients (k : Fin t.numRoots) :
    t.simpleRootCoefficients ht k ᵥ* t.cartanMatrix =
      (t.simplyConnectedRootDatum ht).root k :=
  (t.simpleRootCoefficients_eq_iff ht).mp rfl

/-- Distinct roots have distinct numbered columns. -/
theorem simpleRootCoefficients_injective : Injective (t.simpleRootCoefficients ht) := fun k l hkl ↦
  (t.simplyConnectedRootDatum ht).root.injective <| by
    rw [← vecMul_simpleRootCoefficients, hkl, vecMul_simpleRootCoefficients]

/-- The numbered column of a simple root is the corresponding coordinate column. -/
@[simp]
theorem simpleRootCoefficients_simpleIndex (i : Fin t.rank) :
    t.simpleRootCoefficients ht (t.simpleIndex ht i) = Pi.single i 1 :=
  (t.simpleRootCoefficients_eq_iff ht).mpr <| by
    rw [← sum_smul_root_simpleIndex t ht]
    simp [Pi.single_apply, ite_smul]

/-- **The numbered reflection on columns computes the numbered column of the reflected root.** -/
theorem columnReflection_simpleRootCoefficients (i : Fin t.rank) (k : Fin t.numRoots) :
    t.cartanMatrix.columnReflection t.cartanMatrix_apply_same i (t.simpleRootCoefficients ht k) =
      t.simpleRootCoefficients ht
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) k) :=
  ((t.simpleRootCoefficients_eq_iff ht).mpr <| by
    rw [← reflection_vecMul_cartanMatrix, vecMul_simpleRootCoefficients,
      RootPairing.root_reflectionPerm]).symm

/-- A root of the pinned datum is positive exactly when its numbered column is nonnegative. -/
theorem zero_le_simpleRootCoefficients_iff {k : Fin t.numRoots} :
    0 ≤ t.simpleRootCoefficients ht k ↔ (t.simplyConnectedBase ht).IsPos k := by
  rw [← RootPairing.Base.zero_le_rootCoefficients_iff, simpleRootCoefficients]
  exact ⟨fun h j ↦ by simpa using h ((t.simpleSupportEquivSimplyConnectedBase ht).symm j),
    fun h i ↦ h _⟩

/-- **The union of the orbits of the coordinate columns is the set of numbered root columns**,
including those of negative roots. -/
theorem iUnion_orbit_single_eq_range_simpleRootCoefficients :
    ⋃ i : Fin t.rank,
        MulAction.orbit (t.cartanMatrix.columnReflectionGroup t.cartanMatrix_apply_same)
          (Pi.single i 1 : Fin t.rank → ℤ) =
      range (t.simpleRootCoefficients ht) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  refine subset_antisymm (iUnion_subset fun i ↦ ?_) ?_
  · refine Matrix.orbit_columnReflectionGroup_subset ?_
      ⟨_, t.simpleRootCoefficients_simpleIndex ht i⟩
    rintro i _ ⟨k, rfl⟩
    exact ⟨_, (t.columnReflection_simpleRootCoefficients ht i k).symm⟩
  · rintro _ ⟨k, rfl⟩
    have hk : (t.simplyConnectedBase ht).rootCoefficients k ∈ _ :=
      (t.simplyConnectedBase ht).iUnion_orbit_single_eq_range_rootCoefficients.ge ⟨k, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hk
    refine mem_iUnion.mpr ⟨(t.simpleSupportEquivSimplyConnectedBase ht).symm j, ?_⟩
    have h := Matrix.comp_equiv_mem_orbit _ _ t.cartanMatrix_apply_same
      (t.simpleSupportEquivSimplyConnectedBase ht)
      (fun i j ↦ (t.cartanMatrix_simplyConnectedBase_apply ht i j).symm) hj
    have hs : (Pi.single j 1 : _ → ℤ) ∘ t.simpleSupportEquivSimplyConnectedBase ht =
        Pi.single ((t.simpleSupportEquivSimplyConnectedBase ht).symm j) 1 := by
      ext i
      simp [Pi.single_apply, Equiv.eq_symm_apply]
    rwa [hs] at h

/-- **The nonnegative numbered columns in the orbits of the coordinate columns are the columns of
the positive roots.** -/
theorem iUnion_orbit_single_inter_Ici_eq_image_isPos :
    (⋃ i : Fin t.rank,
        MulAction.orbit (t.cartanMatrix.columnReflectionGroup t.cartanMatrix_apply_same)
          (Pi.single i 1 : Fin t.rank → ℤ)) ∩ Ici 0 =
      t.simpleRootCoefficients ht '' {k | (t.simplyConnectedBase ht).IsPos k} := by
  rw [t.iUnion_orbit_single_eq_range_simpleRootCoefficients ht, ← image_preimage_eq_range_inter]
  congr 1
  ext k
  exact t.zero_le_simpleRootCoefficients_iff ht

end TauCeti.DynkinType

end
