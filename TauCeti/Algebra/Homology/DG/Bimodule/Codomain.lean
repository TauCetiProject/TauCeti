/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Bimodule.Defs

/-!
# The codomain of a DG algebra morphism as a DG bimodule

A morphism `f : A ⟶ B` of differential graded algebras makes `B` into a DG `(A, B)`-bimodule:
`A` acts on the left through `f`, by `a · x = f(a) x`, and `B` acts on the right by
multiplication.  The grading and the differential are those of `B`, and the two Leibniz rules
are the Leibniz rule of `B` together with the fact that `f` commutes with the differentials.
For `f` the identity this is the regular bimodule `TauCeti.IsDGAlgebra.isDGBimodule`.

This bimodule is the coefficient bimodule of extension of scalars along `f`: tensoring a right
DG `A`-module with it over `A` gives a right DG `B`-module.

To avoid a global `A`-module instance on `B` depending on `f`, the carrier is the wrapper
`TauCeti.DGAlgHom.CodomainBimodule f`, in the same way as
`TauCeti.DGRightModule.RestrictScalars` wraps a restricted right module.

## Main definitions

* `TauCeti.DGAlgHom.CodomainBimodule`: the carrier of `B`, viewed as an `(A, B)`-bimodule
  through `f`.
* `TauCeti.DGAlgHom.codomainBimoduleGrading`: its grading, transported from `B`.
* `TauCeti.DGAlgHom.codomainBimoduleDifferential`: its differential, transported from `B`.
* `TauCeti.DGAlgHom.isDGBimodule_codomainBimodule`: the DG `(A, B)`-bimodule structure.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

open MulOpposite

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGAlgHom

/-- The codomain `B` of a DG algebra morphism `f : A ⟶ B`, viewed as an `(A, B)`-bimodule:
`a : A` acts on the left by multiplication with `f a`, and `B` acts on the right by
multiplication.

The wrapper keeps the left `A`-module instance local to the chosen morphism `f`. -/
structure CodomainBimodule (_f : DGAlgHom hA hB) where
  /-- The element of `B` underlying an element of the bimodule. -/
  val : B

namespace CodomainBimodule

variable {f : DGAlgHom hA hB}

/-- Elements of the codomain bimodule are equal when their underlying elements are equal. -/
@[ext]
theorem ext {x y : CodomainBimodule f} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

variable (f)

instance : AddCommGroup (CodomainBimodule f) :=
  Equiv.addCommGroup
    { toFun := CodomainBimodule.val, invFun := CodomainBimodule.mk
      left_inv _ := rfl, right_inv _ := rfl }

instance : Module R (CodomainBimodule f) :=
  AddEquiv.module R
    { toFun := CodomainBimodule.val, invFun := CodomainBimodule.mk
      left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl }

/-- The left action: `a : A` acts by left multiplication with `f a`. -/
instance : Module A (CodomainBimodule f) :=
  letI : Module A B := Module.compHom B f.toGradedAlgHom.toAlgHom.toRingHom
  AddEquiv.module A
    { toFun := CodomainBimodule.val, invFun := CodomainBimodule.mk
      left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl }

/-- The right action: `B` acts by right multiplication. -/
instance : Module Bᵐᵒᵖ (CodomainBimodule f) :=
  AddEquiv.module Bᵐᵒᵖ
    { toFun := CodomainBimodule.val, invFun := CodomainBimodule.mk
      left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl }

/-- The identity `R`-linear equivalence from the codomain bimodule to `B`. -/
def linearEquiv : CodomainBimodule f ≃ₗ[R] B where
  toFun := CodomainBimodule.val
  invFun := CodomainBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem val_zero : (0 : CodomainBimodule f).val = 0 := rfl

@[simp]
theorem val_add (x y : CodomainBimodule f) : (x + y).val = x.val + y.val := rfl

@[simp]
theorem val_neg (x : CodomainBimodule f) : (-x).val = -x.val := rfl

@[simp]
theorem val_zsmul (n : ℤ) (x : CodomainBimodule f) : (n • x).val = n • x.val := rfl

@[simp]
theorem val_smul (r : R) (x : CodomainBimodule f) : (r • x).val = r • x.val := rfl

/-- On underlying elements, the left action of `a : A` is multiplication by `f a`. -/
@[simp]
theorem val_smul_left (a : A) (x : CodomainBimodule f) : (a • x).val = f a * x.val := rfl

/-- On underlying elements, the right action of `b : Bᵐᵒᵖ` is the right action on `B`. -/
@[simp]
theorem val_smul_right (b : Bᵐᵒᵖ) (x : CodomainBimodule f) : (b • x).val = b • x.val := rfl

@[simp]
theorem linearEquiv_apply (x : CodomainBimodule f) : linearEquiv f x = x.val := by rfl

@[simp]
theorem linearEquiv_symm_apply (x : B) : (linearEquiv f).symm x = CodomainBimodule.mk x := by rfl

instance : IsScalarTower R A (CodomainBimodule f) where
  smul_assoc r a x := by
    apply CodomainBimodule.ext
    simp only [val_smul_left, val_smul, map_smul, smul_mul_assoc]

instance : IsScalarTower R Bᵐᵒᵖ (CodomainBimodule f) where
  smul_assoc r b x := by
    apply CodomainBimodule.ext
    simp only [val_smul_right, val_smul, smul_assoc]

instance : SMulCommClass A Bᵐᵒᵖ (CodomainBimodule f) where
  smul_comm a b x := by
    apply CodomainBimodule.ext
    simp only [val_smul_left, val_smul_right, smul_eq_mul_unop, mul_assoc]

end CodomainBimodule

variable (f : DGAlgHom hA hB)

/-- The grading of the codomain bimodule: the grading of `B`. -/
noncomputable def codomainBimoduleGrading (q : ℤ) : Submodule R (CodomainBimodule f) :=
  ((InternalGrading.ofDecomposition ℬ).map (CodomainBimodule.linearEquiv f).symm).piece q

@[simp]
theorem mem_codomainBimoduleGrading_iff {q : ℤ} {x : CodomainBimodule f} :
    x ∈ codomainBimoduleGrading f q ↔ x.val ∈ ℬ q := by
  simpa only [codomainBimoduleGrading, LinearEquiv.symm_symm,
    InternalGrading.ofDecomposition_piece, CodomainBimodule.linearEquiv_apply] using
      (InternalGrading.ofDecomposition ℬ).mem_map_piece_iff
        (CodomainBimodule.linearEquiv f).symm q x

/- The grading is by definition a transported grading `InternalGrading.map`, which already
carries a decomposition; we read the instance off that definition. -/
/-- The transported grading of the codomain bimodule is a direct-sum decomposition. -/
noncomputable instance : DirectSum.Decomposition (codomainBimoduleGrading f) :=
  inferInstanceAs (DirectSum.Decomposition
    (((InternalGrading.ofDecomposition ℬ).map (CodomainBimodule.linearEquiv f).symm).piece))

/-- The left action through `f` adds degrees, because `f` is graded. -/
instance : SetLike.GradedSMul 𝒜 (codomainBimoduleGrading f) where
  smul_mem {i j a x} ha hx := by
    rw [mem_codomainBimoduleGrading_iff] at hx ⊢
    rw [CodomainBimodule.val_smul_left, vadd_eq_add]
    exact SetLike.GradedMul.mul_mem (Graded.map_mem f ha) hx

/-- The right action by multiplication adds degrees. -/
instance : SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece
    (codomainBimoduleGrading f) where
  smul_mem {i j b x} hb hx := by
    rw [mem_codomainBimoduleGrading_iff] at hx ⊢
    rw [CodomainBimodule.val_smul_right]
    exact SetLike.GradedSMul.smul_mem hb hx

/-- The differential of the codomain bimodule: the differential of `B`. -/
def codomainBimoduleDifferential : CodomainBimodule f →ₗ[R] CodomainBimodule f :=
  (CodomainBimodule.linearEquiv f).symm.toLinearMap ∘ₗ dB ∘ₗ
    (CodomainBimodule.linearEquiv f).toLinearMap

@[simp]
theorem val_codomainBimoduleDifferential (x : CodomainBimodule f) :
    (codomainBimoduleDifferential f x).val = dB x.val := by rfl

/-- **The codomain of a DG algebra morphism is a DG bimodule.**  For `f : A ⟶ B`, the algebra
`B` is a DG `(A, B)`-bimodule with left action through `f` and right action by multiplication. -/
theorem isDGBimodule_codomainBimodule :
    IsDGBimodule hA hB (codomainBimoduleGrading f) (codomainBimoduleDifferential f) where
  isHomogeneous := by
    rw [LinearMap.isHomogeneous_def]
    intro q x hx
    rw [mem_codomainBimoduleGrading_iff] at hx ⊢
    exact hB.map_mem hx
  sq_zero x := by
    apply CodomainBimodule.ext
    simp only [val_codomainBimoduleDifferential, hB.sq_zero, CodomainBimodule.val_zero]
  leibniz {p a} ha x := by
    apply CodomainBimodule.ext
    simp only [val_codomainBimoduleDifferential, CodomainBimodule.val_smul_left,
      CodomainBimodule.val_add, Units.smul_def, CodomainBimodule.val_zsmul, ← f.map_d]
    simpa only [Units.smul_def] using hB.leibniz (Graded.map_mem f ha) x.val
  leibniz_right {q x} hx b := by
    apply CodomainBimodule.ext
    simp only [val_codomainBimoduleDifferential, CodomainBimodule.val_smul_right,
      CodomainBimodule.val_add, Units.smul_def, CodomainBimodule.val_zsmul]
    simpa only [Units.smul_def] using
      hB.isDGRightModule.leibniz ((mem_codomainBimoduleGrading_iff f).mp hx) b

end DGAlgHom

end TauCeti
