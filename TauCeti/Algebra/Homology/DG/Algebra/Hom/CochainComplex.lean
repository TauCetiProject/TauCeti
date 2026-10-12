/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.CochainComplex

/-!
# The cochain map of a differential graded algebra morphism

A DG algebra morphism is, in particular, a map of cochain complexes. This interface connects
the internal direct-sum grading used for algebra multiplication to Mathlib's cochain-complex API.
The map on degree `n` is the restriction of the algebra morphism to homogeneous degree `n`.
It supplies the Hom-complex map for the one-object DG functor of a DG algebra morphism.

## References

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uB uC uExtra

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

namespace DGAlgHom

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {hC : IsDGAlgebra 𝒞 dC}

private theorem toLinearMap_isHomogeneous (f : DGAlgHom hA hB) :
    LinearMap.IsHomogeneous f.toGradedAlgHom.toAlgHom.toLinearMap 𝒜 ℬ 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ by
    simpa [AlgHom.toLinearMap_apply] using f.toGradedAlgHom.map_mem ha

/-- A DG algebra morphism, viewed as a map of the underlying cochain complexes. -/
noncomputable def toCochainMap (f : DGAlgHom hA hB) :
    hA.toCochainComplex.{uR, uA, max uB uExtra} ⟶
      hB.toCochainComplex.{uR, uB, max uA uExtra} :=
  gradedCochainComplexMap f.toGradedAlgHom.toAlgHom.toLinearMap
    f.toLinearMap_isHomogeneous (fun _ x ↦ by simp)

/-- The cochain map acts on homogeneous elements by the DG algebra morphism. -/
@[simp]
theorem toCochainMap_f_apply (f : DGAlgHom hA hB) (n : ℤ) (x : 𝒜 n) :
    (eqToHom (gradedCochainComplexLift_X.{uR, uB, max uA uExtra} n)
      ((f.toCochainMap.f n)
        (eqToHom (gradedCochainComplexLift_X.{uR, uA, max uB uExtra} n).symm
          (ULift.up x)))).down.val = f x := by
  simpa [toCochainMap, AlgHom.toLinearMap_apply] using
    gradedCochainComplexMap_f_apply (hdeg := LinearMap.isHomogeneous_def.mpr
      fun _ _ ha ↦ hA.map_mem ha) (hsq := fun _ y ↦ hA.sq_zero y)
      (hdegN := LinearMap.isHomogeneous_def.mpr fun _ _ hb ↦ hB.map_mem hb)
      (hsqN := fun _ y ↦ hB.sq_zero y)
      f.toGradedAlgHom.toAlgHom.toLinearMap f.toLinearMap_isHomogeneous
      (fun _ y ↦ by simp) n x

/-- The identity DG algebra morphism induces the identity cochain map. -/
@[simp]
theorem toCochainMap_id (hA : IsDGAlgebra 𝒜 dA) :
    (DGAlgHom.id hA).toCochainMap = 𝟙 hA.toCochainComplex := by
  have hlin : (DGAlgHom.id hA).toGradedAlgHom.toAlgHom.toLinearMap =
      (LinearMap.id : A →ₗ[R] A) := by
    ext x
    simp
  calc
    (DGAlgHom.id hA).toCochainMap =
        gradedCochainComplexMap (hdeg := LinearMap.isHomogeneous_def.mpr
          fun _ _ ha ↦ hA.map_mem ha) (hsq := fun _ y ↦ hA.sq_zero y)
          (hdegN := LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ hA.map_mem ha)
          (hsqN := fun _ y ↦ hA.sq_zero y) (LinearMap.id : A →ₗ[R] A)
          (LinearMap.isHomogeneous_id 𝒜) (fun _ _ ↦ rfl) := by
            exact gradedCochainComplexMap_congr hlin _ _ _ _
    _ = 𝟙 hA.toCochainComplex := gradedCochainComplexMap_id

/-- Composition of DG algebra morphisms induces composition of cochain maps. -/
theorem toCochainMap_comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    (g.comp f).toCochainMap.{uR, uA, uC, max uB uExtra} =
      f.toCochainMap.{uR, uA, uB, max uC uExtra} ≫
        g.toCochainMap.{uR, uB, uC, max uA uExtra} := by
  have hlin : (g.comp f).toGradedAlgHom.toAlgHom.toLinearMap =
      g.toGradedAlgHom.toAlgHom.toLinearMap.comp
        f.toGradedAlgHom.toAlgHom.toLinearMap := by
    ext x
    simp
  have hgf : LinearMap.IsHomogeneous
      (g.toGradedAlgHom.toAlgHom.toLinearMap.comp
        f.toGradedAlgHom.toAlgHom.toLinearMap) 𝒜 𝒞 0 := by
    rw [← hlin]
    exact (g.comp f).toLinearMap_isHomogeneous
  have hcommgf (p : ℤ) (x : 𝒜 p) :
      dC ((g.toGradedAlgHom.toAlgHom.toLinearMap.comp
        f.toGradedAlgHom.toAlgHom.toLinearMap) x) =
      (g.toGradedAlgHom.toAlgHom.toLinearMap.comp
        f.toGradedAlgHom.toAlgHom.toLinearMap) (dA x) := by
    simp
  calc
    (g.comp f).toCochainMap.{uR, uA, uC, max uB uExtra} = gradedCochainComplexMap
        (g.toGradedAlgHom.toAlgHom.toLinearMap.comp
          f.toGradedAlgHom.toAlgHom.toLinearMap) hgf hcommgf := by
        exact gradedCochainComplexMap_congr hlin _ _ _ _
    _ = f.toCochainMap.{uR, uA, uB, max uC uExtra} ≫ g.toCochainMap.{uR, uB, uC, max uA uExtra} :=
      gradedCochainComplexMap_comp _ _ _ _ _ _

end DGAlgHom

end TauCeti
