/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CentralSimple.Bimodule
public import TauCeti.Algebra.Homology.DG.Bimodule.Category
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.Algebra.TensorProduct.Module

/-!
# The differential graded bimodule of a DG algebra morphism

A morphism `f : A ⟶ B` of differential graded algebras makes `B` into an `(A, B)`-DG
bimodule: `A` acts on the left through `f`, while `B` acts on the right by multiplication.
The grading and differential are those of `B`.  This is the bimodule customarily denoted
`{}_f B`; tensoring a right DG `A`-module with it is extension of scalars along `f`.

The carrier reuses `TauCeti.Bimodule f`, which keeps the action belonging to `f` separate from
other actions on the underlying type `B`.  Its enveloping-algebra action is restricted to the two
factors, and the grading and differential are transported along `TauCeti.Bimodule.of`.

## Main definitions

* `TauCeti.DGAlgHom.bimoduleGrading`: the transported grading on `{}_f B`.
* `TauCeti.DGAlgHom.bimoduleDifferential`: the transported differential on `{}_f B`.
* `TauCeti.DGAlgHom.toBimodule`: `{}_f B` as a bundled DG bimodule.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

open MulOpposite
open scoped TensorProduct

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {Aₙ : ℤ → Submodule R A} {Bₙ : ℤ → Submodule R B}
  [GradedAlgebra Aₙ] [GradedAlgebra Bₙ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra Aₙ dA} {hB : IsDGAlgebra Bₙ dB}

namespace DGAlgHom

variable (f : DGAlgHom hA hB)

noncomputable instance bimoduleModuleLeft :
    Module A (Bimodule f.toGradedAlgHom.toAlgHom) :=
  Algebra.TensorProduct.moduleLeft (k := R) (A := A) (B := Bᵐᵒᵖ)
    (Bimodule f.toGradedAlgHom.toAlgHom)

noncomputable instance bimoduleModuleRight :
    Module Bᵐᵒᵖ (Bimodule f.toGradedAlgHom.toAlgHom) :=
  Algebra.TensorProduct.moduleRight (k := R) (A := A) (B := Bᵐᵒᵖ)
    (Bimodule f.toGradedAlgHom.toAlgHom)

noncomputable instance bimoduleScalarTowerLeft :
    IsScalarTower R A (Bimodule f.toGradedAlgHom.toAlgHom) :=
  Algebra.TensorProduct.moduleLeftIsScalarTower
    (k := R) (A := A) (B := Bᵐᵒᵖ) (Bimodule f.toGradedAlgHom.toAlgHom)

noncomputable instance bimoduleScalarTowerRight :
    IsScalarTower R Bᵐᵒᵖ (Bimodule f.toGradedAlgHom.toAlgHom) :=
  Algebra.TensorProduct.moduleRightIsScalarTower
    (k := R) (A := A) (B := Bᵐᵒᵖ) (Bimodule f.toGradedAlgHom.toAlgHom)

noncomputable instance bimoduleSMulCommClass :
    SMulCommClass A Bᵐᵒᵖ (Bimodule f.toGradedAlgHom.toAlgHom) :=
  Algebra.TensorProduct.moduleSMulCommClass
    (k := R) (A := A) (B := Bᵐᵒᵖ) (Bimodule f.toGradedAlgHom.toAlgHom)

/-! ### Grading and differential -/

/-- The grading on `{}_f B`, transported from the target DG algebra. -/
noncomputable def bimoduleGrading (p : ℤ) :
    Submodule R (Bimodule f.toGradedAlgHom.toAlgHom) :=
  ((InternalGrading.ofDecomposition Bₙ).map
    (Bimodule.of f.toGradedAlgHom.toAlgHom)).piece p

/-- Membership in the transported grading is membership in the target-algebra grading. -/
@[simp]
theorem mem_bimoduleGrading_iff {p : ℤ}
    {b : Bimodule f.toGradedAlgHom.toAlgHom} :
    b ∈ f.bimoduleGrading p ↔ (Bimodule.of f.toGradedAlgHom.toAlgHom).symm b ∈ Bₙ p := by
  simpa only [bimoduleGrading, InternalGrading.ofDecomposition_piece] using
    (InternalGrading.ofDecomposition Bₙ).mem_map_piece_iff
      (Bimodule.of f.toGradedAlgHom.toAlgHom) p b

/-- The transported grading of `{}_f B` is a direct-sum decomposition. -/
noncomputable instance bimoduleGradingDecomposition : DirectSum.Decomposition f.bimoduleGrading :=
  inferInstanceAs (DirectSum.Decomposition
    (((InternalGrading.ofDecomposition Bₙ).map
      (Bimodule.of f.toGradedAlgHom.toAlgHom)).piece))

/-- The differential on `{}_f B`, transported from the target DG algebra. -/
noncomputable def bimoduleDifferential :
    Bimodule f.toGradedAlgHom.toAlgHom →ₗ[R] Bimodule f.toGradedAlgHom.toAlgHom :=
  (Bimodule.of f.toGradedAlgHom.toAlgHom).toLinearMap ∘ₗ dB ∘ₗ
    (Bimodule.of f.toGradedAlgHom.toAlgHom).symm.toLinearMap

/-- The differential on `{}_f B` is the target differential on underlying elements. -/
@[simp]
theorem bimoduleDifferential_bimoduleOf (b : B) :
    f.bimoduleDifferential (Bimodule.of f.toGradedAlgHom.toAlgHom b) =
      Bimodule.of f.toGradedAlgHom.toAlgHom (dB b) := by
  simp [bimoduleDifferential]

/-- Reading the differential on `{}_f B` gives the target differential. -/
@[simp]
theorem bimoduleOf_symm_bimoduleDifferential
    (b : Bimodule f.toGradedAlgHom.toAlgHom) :
    (Bimodule.of f.toGradedAlgHom.toAlgHom).symm (f.bimoduleDifferential b) =
      dB ((Bimodule.of f.toGradedAlgHom.toAlgHom).symm b) := by
  simp [bimoduleDifferential]

/-- The left action of `A` on `{}_f B` respects the transported grading. -/
noncomputable instance bimoduleGradedSMulLeft : SetLike.GradedSMul Aₙ f.bimoduleGrading where
  smul_mem {p q a b} ha hb := by
    rw [mem_bimoduleGrading_iff] at hb ⊢
    rw [← (Bimodule.of f.toGradedAlgHom.toAlgHom).apply_symm_apply b,
      Algebra.TensorProduct.smul_moduleLeft, Bimodule.smul_of]
    simp only [unop_one, mul_one,
      (Bimodule.of f.toGradedAlgHom.toAlgHom).symm_apply_apply]
    exact SetLike.GradedMul.mul_mem (Graded.map_mem f ha) hb

/-- The right action of `B` on `{}_f B` respects the transported grading. -/
noncomputable instance bimoduleGradedSMulRight : SetLike.GradedSMul
    (InternalGrading.ofDecomposition Bₙ).opposite.piece f.bimoduleGrading where
  smul_mem {p q b x} hb hx := by
    rw [mem_bimoduleGrading_iff] at hx ⊢
    rw [← (Bimodule.of f.toGradedAlgHom.toAlgHom).apply_symm_apply x,
      Algebra.TensorProduct.smul_moduleRight, Bimodule.symm_smul]
    simp only [map_one, one_mul, (Bimodule.of f.toGradedAlgHom.toAlgHom).symm_apply_apply]
    have hb' : b.unop ∈ Bₙ p := by
      simpa only [InternalGrading.ofDecomposition_piece] using
        ((InternalGrading.ofDecomposition Bₙ).mem_opposite_piece_iff p b).mp hb
    simpa only [vadd_eq_add, add_comm q p] using SetLike.GradedMul.mul_mem hx hb'

/-- A DG algebra morphism makes its target into the DG bimodule `{}_f B`. -/
theorem isDGBimodule :
    IsDGBimodule hA hB f.bimoduleGrading f.bimoduleDifferential where
  isHomogeneous := by
    rw [LinearMap.isHomogeneous_def]
    intro p b hb
    rw [mem_bimoduleGrading_iff] at hb ⊢
    rw [← (Bimodule.of f.toGradedAlgHom.toAlgHom).apply_symm_apply b,
      bimoduleDifferential_bimoduleOf,
      (Bimodule.of f.toGradedAlgHom.toAlgHom).symm_apply_apply]
    exact hB.isDGLeftModule.isHomogeneous.map_mem hb
  sq_zero b := by
    rw [← (Bimodule.of f.toGradedAlgHom.toAlgHom).apply_symm_apply b,
      bimoduleDifferential_bimoduleOf, bimoduleDifferential_bimoduleOf, hB.sq_zero, map_zero]
  leibniz {p a} ha b := by
    apply (Bimodule.of f.toGradedAlgHom.toAlgHom).symm.injective
    simp only [bimoduleOf_symm_bimoduleDifferential, map_add, Units.smul_def, map_zsmul,
      Algebra.TensorProduct.smul_moduleLeft, Bimodule.symm_smul, unop_one, mul_one]
    change dB (f a * (Bimodule.of f.toGradedAlgHom.toAlgHom).symm b) =
      f (dA a) * (Bimodule.of f.toGradedAlgHom.toAlgHom).symm b +
        p.negOnePow •
          (f a * dB ((Bimodule.of f.toGradedAlgHom.toAlgHom).symm b))
    simpa only [f.map_d] using hB.leibniz (Graded.map_mem f ha)
      ((Bimodule.of f.toGradedAlgHom.toAlgHom).symm b)
  leibniz_right {q b} hb c := by
    have hb' := (mem_bimoduleGrading_iff (f := f)).mp hb
    apply (Bimodule.of f.toGradedAlgHom.toAlgHom).symm.injective
    simpa only [bimoduleOf_symm_bimoduleDifferential, map_add, Units.smul_def, map_zsmul,
      Algebra.TensorProduct.smul_moduleRight, Bimodule.symm_smul, map_one, one_mul, unop_op] using
      hB.leibniz hb' c

/-- The target of a DG algebra morphism as its canonical `(A, B)`-DG bimodule `{}_f B`. -/
-- Expose the carrier so the characteristic grading and differential equations reduce.
@[expose]
noncomputable def toBimodule : DGBimoduleCat hA hB :=
  DGBimoduleCat.of f.isDGBimodule

@[simp]
theorem toBimodule_carrier :
    f.toBimodule.carrier = Bimodule f.toGradedAlgHom.toAlgHom := (rfl)

@[simp]
theorem toBimodule_grading : f.toBimodule.grading = f.bimoduleGrading := (rfl)

@[simp]
theorem toBimodule_differential : f.toBimodule.differential = f.bimoduleDifferential := (rfl)

end DGAlgHom

end TauCeti
