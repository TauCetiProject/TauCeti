/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar extension of exterior algebras

The exterior algebra commutes with extension of scalars over arbitrary commutative rings,
including in characteristic two. The inverse comparison sends `a ⊗ ι(m)` to `ι(a ⊗ m)`.
This supplies the ambient algebra comparison for scalar extension of exterior powers.

The construction follows Mathlib's `CliffordAlgebra.equivBaseChange` (Eric Wieser), but
uses the alternating relations directly: unlike the Clifford-algebra comparison, it does
not require that two be invertible. No flatness or freeness assumption is needed.
-/

public section

open scoped TensorProduct

open ExteriorAlgebra

namespace TauCeti

variable {R : Type*} (A : Type*) {M : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- The map induced by the canonical inclusion of the module into its scalar extension. -/
private def ofBaseChangeAux :
    ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra A (A ⊗[R] M) :=
  lift R
    ⟨((ι A).restrictScalars R).comp (TensorProduct.mk R A M 1),
      fun _ ↦ ι_sq_zero _⟩

private theorem ofBaseChangeAux_ι (m : M) :
    ofBaseChangeAux A (ι R m) =
      ι A (1 ⊗ₜ[R] m) :=
  lift_ι_apply _ _ _ _

/-- The scalar-linear extension of the map on exterior generators. -/
private def ofBaseChange :
    A ⊗[R] ExteriorAlgebra R M →ₐ[A] ExteriorAlgebra A (A ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (ofBaseChangeAux A)
    (by intro a x; exact Algebra.commutes a _)

private theorem ofBaseChange_tmul_ι (a : A) (m : M) :
    ofBaseChange A (a ⊗ₜ[R] ι R m) =
      ι A (a ⊗ₜ[R] m) := by
  calc
    _ = algebraMap A _ a * ofBaseChangeAux A (ι R m) := rfl
    _ = _ := by
      simp only [ofBaseChangeAux_ι, ← Algebra.smul_def, ← map_smul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem baseChange_ι_sq_zero (x : A ⊗[R] M) :
    ((ι R).baseChange A x) *
      ((ι R).baseChange A x) = 0 := by
  have hanti (x y : A ⊗[R] M) :
      ((ι R).baseChange A x) *
          ((ι R).baseChange A y) +
        ((ι R).baseChange A y) *
          ((ι R).baseChange A x) = 0 := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
        simp only [map_add, add_mul, mul_add]
        rw [add_add_add_comm, hx, hy, add_zero]
    | tmul a m =>
      induction y using TensorProduct.inductionOn with
      | add x y hx hy =>
          simp only [map_add, add_mul, mul_add]
          rw [add_add_add_comm, hx, hy, add_zero]
      | tmul b n =>
        simp only [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
        rw [mul_comm b a, ← TensorProduct.tmul_add, ι_add_mul_swap,
          TensorProduct.tmul_zero]
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
      simp only [map_add, add_mul, mul_add]
      rw [hx, hy, zero_add, add_zero, hanti y x]

/-- The exterior-algebra map induced by the scalar-extended square-zero generators. -/
private def toBaseChange :
    ExteriorAlgebra A (A ⊗[R] M) →ₐ[A] A ⊗[R] ExteriorAlgebra R M :=
  lift A
    ⟨(ι R).baseChange A, baseChange_ι_sq_zero A⟩

private theorem toBaseChange_ι (x : A ⊗[R] M) :
    toBaseChange A (ι A x) =
      (ι R).baseChange A x :=
  lift_ι_apply _ _ _ _

/-- Scalar extension commutes with exterior algebras, without restrictions on characteristic. -/
noncomputable def exteriorAlgebraEquivBaseChange :
    ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M :=
  AlgEquiv.ofAlgHom (toBaseChange A) (ofBaseChange A)
    (by
      apply Algebra.TensorProduct.ext
      · ext
      · apply hom_ext
        ext m
        simp [ofBaseChange_tmul_ι, toBaseChange_ι])
    (by
      apply hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro a m
      simp [toBaseChange_ι, ofBaseChange_tmul_ι])

/-- The comparison carries an exterior generator to the scalar extension of that generator. -/
@[simp]
theorem exteriorAlgebraEquivBaseChange_ι (x : A ⊗[R] M) :
    exteriorAlgebraEquivBaseChange A (ι A x) =
      (ι R).baseChange A x :=
  toBaseChange_ι A x

/-- The inverse comparison on a scalar multiple of an exterior generator. -/
@[simp]
theorem exteriorAlgebraEquivBaseChange_symm_tmul_ι (a : A) (m : M) :
    (exteriorAlgebraEquivBaseChange A).symm (a ⊗ₜ[R] ι R m) =
      ι A (a ⊗ₜ[R] m) :=
  ofBaseChange_tmul_ι A a m

/-- On wedges of pure tensors the scalar coefficients multiply. -/
@[simp]
theorem exteriorAlgebraEquivBaseChange_ιMulti_tmul {n : ℕ} (a : Fin n → A) (m : Fin n → M) :
    exteriorAlgebraEquivBaseChange A (ιMulti A n (fun i ↦ a i ⊗ₜ[R] m i)) =
      (∏ i, a i) ⊗ₜ[R] ιMulti R n m := by
  induction n with
  | zero => simp [ιMulti_zero_apply, Algebra.TensorProduct.one_def]
  | succ n ih =>
      simp only [ιMulti_succ_apply, map_mul, exteriorAlgebraEquivBaseChange_ι,
        LinearMap.baseChange_tmul, Matrix.vecTail, Function.comp_def, ih,
        Algebra.TensorProduct.tmul_mul_tmul, Fin.prod_univ_succ]

/-- Scalar extension of exterior algebras is natural in the module. -/
@[simp]
theorem exteriorAlgebraEquivBaseChange_map {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x : ExteriorAlgebra A (A ⊗[R] M)) :
    exteriorAlgebraEquivBaseChange A (map (f.baseChange A) x) =
      Algebra.TensorProduct.map (AlgHom.id A A) (map f)
        (exteriorAlgebraEquivBaseChange A x) := by
  have h : (exteriorAlgebraEquivBaseChange A).toAlgHom.comp
      (map (f.baseChange A)) =
      (Algebra.TensorProduct.map (AlgHom.id A A) (map f)).comp
        (exteriorAlgebraEquivBaseChange A).toAlgHom := by
    apply hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simp [exteriorAlgebraEquivBaseChange_ι]
  exact AlgHom.congr_fun h x

end TauCeti
