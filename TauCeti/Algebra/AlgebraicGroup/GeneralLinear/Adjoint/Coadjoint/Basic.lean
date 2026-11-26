/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Comodule
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The coadjoint representation of the general linear group

Let `𝔤 = 𝔤𝔩ₙ` be the Lie algebra of `GLₙ` over a commutative ring `k`, identified with the
`n × n` matrices by `TauCeti.GeneralLinear.cotangentDualMatrixEquiv`. Through the trace pairing, a
matrix `Y` with entries in a `k`-algebra `A` is read as the `A`-valued covector `X ↦ tr (Y X)` on
`𝔤` (`TauCeti.GeneralLinear.traceCovector`), and every covector arises this way: the generic matrix
`TauCeti.GeneralLinear.coadjointGenericMatrix`, with entries in the polynomial functions `Sym 𝔤` on
`𝔤*`, evaluates at a covector to its matrix. Over a field, the coadjoint action of a point
`G ∈ GLₙ(A)` is conjugation, `Y ↦ G⁻¹ Y G`.

## Main declarations

* `TauCeti.GeneralLinear.traceCovector`: the covector `X ↦ tr (Y X)` of a matrix `Y`.
* `TauCeti.GeneralLinear.coadjointGenericMatrix`: the generic covector as a matrix, with
  `TauCeti.GeneralLinear.map_lift_traceCovector_coadjointGenericMatrix` and
  `TauCeti.GeneralLinear.traceCovector_map_lift_coadjointGenericMatrix` saying that the trace
  pairing identifies covectors with matrices.
* `TauCeti.GeneralLinear.liftBaseChange_traceCovector_endOfPoint` and
  `TauCeti.GeneralLinear.translate_traceCovector`: the coadjoint action of a point `G` is
  conjugation `Y ↦ G⁻¹ Y G`.
* `TauCeti.GeneralLinear.lift_traceCovector_charpoly_coeff_coadjointGenericMatrix`: the
  characteristic coefficients of the generic matrix evaluate to those of `Y` at the covector of
  `Y`.
-/

public section

open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ}

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))

section TraceCovector

variable {A : Type*} [CommSemiring A] [Algebra k A]

variable (k) in
/-- The covector `X ↦ tr (Y X)` on the Lie algebra `𝔤𝔩ₙ` with values in `A` attached to a matrix
`Y` with entries in `A` by the trace pairing. -/
noncomputable def traceCovector (Y : Matrix (Fin n) (Fin n) A) : 𝔤 →ₗ[k] A where
  toFun x := (Y * (cotangentDualMatrixEquiv x).map (algebraMap k A)).trace
  map_add' x y := by
    rw [map_add, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.trace_add]
  map_smul' c x := by
    rw [map_smul, RingHom.id_apply, Matrix.map_smul' _ _ _ fun _ _ ↦ map_mul _ _ _,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Algebra.smul_def]

/-- The trace covector of `Y` pairs `Y` with the matrix of a vector of `𝔤𝔩ₙ`. -/
@[simp]
theorem traceCovector_apply (Y : Matrix (Fin n) (Fin n) A) (x : 𝔤) :
    traceCovector k Y x = (Y * (cotangentDualMatrixEquiv x).map (algebraMap k A)).trace :=
  (rfl)

/-- The trace pairing is linear in the matrix. -/
theorem traceCovector_smul (a : A) (Y : Matrix (Fin n) (Fin n) A) :
    traceCovector k (a • Y) = a • traceCovector k Y := by
  ext x
  simp [Matrix.trace_smul]

/-- The trace covector of a matrix with entries in `k`, viewed over `A`, is the trace covector over
`k` followed by the structure map. -/
theorem traceCovector_map_algebraMap (Y : Matrix (Fin n) (Fin n) k) :
    traceCovector k (Y.map (algebraMap k A)) = Algebra.linearMap k A ∘ₗ traceCovector k Y := by
  ext x
  simp only [traceCovector_apply, LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
    Matrix.trace, Matrix.diag, map_sum, Matrix.mul_apply, map_mul, Matrix.map_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

variable (k n) in
/-- The generic covector on `𝔤𝔩ₙ` as a matrix in the trace pairing: the matrix with entries in the
polynomial functions `Sym 𝔤` on `𝔤*` whose entry `(i, j)` is the matrix unit `E_ji ∈ 𝔤`, a linear
function on `𝔤*`. Evaluating it at a covector gives the matrix of that covector. -/
noncomputable def coadjointGenericMatrix : Matrix (Fin n) (Fin n) (SymmetricAlgebra k 𝔤) :=
  Matrix.of fun i j ↦ SymmetricAlgebra.ι k 𝔤 (cotangentDualMatrixEquiv.symm (Matrix.single j i 1))

/-- The entries of the generic matrix are the matrix units, as linear functions on `𝔤*`. -/
theorem coadjointGenericMatrix_apply (i j : Fin n) :
    coadjointGenericMatrix k n i j =
      SymmetricAlgebra.ι k 𝔤 (cotangentDualMatrixEquiv.symm (Matrix.single j i 1)) :=
  (rfl)

/-- **The trace pairing is nondegenerate.** Evaluating the generic matrix at the trace covector of
`Y` gives back `Y`. -/
@[simp]
theorem map_lift_traceCovector_coadjointGenericMatrix (Y : Matrix (Fin n) (Fin n) A) :
    (coadjointGenericMatrix k n).map (SymmetricAlgebra.lift (traceCovector k Y)) = Y := by
  ext i j
  simp [coadjointGenericMatrix_apply, Matrix.trace_mul_single]

/-- **Every covector comes from a matrix.** A covector on `𝔤𝔩ₙ` with values in `A` is the trace
covector of its matrix, the evaluation of the generic matrix at it. -/
@[simp]
theorem traceCovector_map_lift_coadjointGenericMatrix (ψ : 𝔤 →ₗ[k] A) :
    traceCovector k ((coadjointGenericMatrix k n).map (SymmetricAlgebra.lift ψ)) = ψ := by
  ext x
  conv_rhs => rw [← cotangentDualMatrixEquiv.symm_apply_apply x,
    Matrix.matrix_eq_sum_single (cotangentDualMatrixEquiv x)]
  simp only [map_sum, traceCovector_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.map_apply, coadjointGenericMatrix_apply, SymmetricAlgebra.lift_ι_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have hs : Matrix.single j i (cotangentDualMatrixEquiv x j i) =
      cotangentDualMatrixEquiv x j i • Matrix.single j i (1 : k) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, Algebra.smul_def, mul_comm]

/-- The characteristic coefficients of the generic matrix below the leading one vanish at the
origin. -/
theorem algebraMapInv_charpoly_coeff_coadjointGenericMatrix {i : ℕ} (hi : i < n) :
    SymmetricAlgebra.algebraMapInv ((coadjointGenericMatrix k n).charpoly.coeff i) = 0 := by
  have h0 : (SymmetricAlgebra.algebraMapInv : SymmetricAlgebra k 𝔤 →ₐ[k] k) =
      SymmetricAlgebra.lift (traceCovector k (0 : Matrix (Fin n) (Fin n) k)) :=
    SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ by simp [SymmetricAlgebra.algebraMapInv_ι])
  rw [h0, ← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, ← Matrix.charpoly_map,
    AlgHom.coe_toRingHom, map_lift_traceCovector_coadjointGenericMatrix, Matrix.charpoly_zero,
    Fintype.card_fin, Polynomial.coeff_X_pow]
  simp [hi.ne]

end TraceCovector

section ScalarExtension

variable {A : Type*} [CommRing A] [Algebra k A]

/-- The scalar extension of the trace covector of `Y` evaluates the trace of `Y` against the matrix
of an `A`-valued tangent vector. -/
theorem liftBaseChange_traceCovector (Y : Matrix (Fin n) (Fin n) A) (w : A ⊗[k] 𝔤) :
    LinearMap.liftBaseChange A (traceCovector k Y) w =
      (Y * tangentMatrix n (Derivation.tangentScalarExtensionEquiv (R := k)
        (A := coordinateHopfAlgebra k n) (B := A) w)).trace := by
  induction w using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.liftBaseChange_tmul, tangentMatrix_tangentScalarExtensionEquiv_tmul,
      traceCovector_apply, Matrix.mul_smul, Matrix.trace_smul]
  | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw', Matrix.mul_add, Matrix.trace_add]

/-- The value of the characteristic coefficients of the generic matrix at the trace covector of `Y`
are the characteristic coefficients of `Y`. -/
theorem lift_traceCovector_charpoly_coeff_coadjointGenericMatrix (Y : Matrix (Fin n) (Fin n) A)
    (i : ℕ) :
    SymmetricAlgebra.lift (traceCovector k Y) ((coadjointGenericMatrix k n).charpoly.coeff i) =
      Y.charpoly.coeff i := by
  conv_rhs => rw [← map_lift_traceCovector_coadjointGenericMatrix (k := k) Y]
  rw [← AlgHom.coe_toRingHom, Matrix.charpoly_map, Polynomial.coeff_map]

end ScalarExtension

end CommRing

section Conjugation

variable {k : Type u} [Field k] {n : ℕ} {A : Type*} [CommRing A] [Algebra k A]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))

attribute [local instance] Derivation.adjointComodule

/-- **The coadjoint action of `GLₙ` is conjugation.** In the trace pairing, the point `G ∈ GLₙ(A)`
translates the covector of `Y` to the covector of `G⁻¹ Y G`. -/
theorem liftBaseChange_traceCovector_endOfPoint
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A))
    (Y : Matrix (Fin n) (Fin n) A) (x : 𝔤) :
    LinearMap.liftBaseChange A (traceCovector k Y)
        (Comodule.endOfPoint 𝔤 g.ofConv (1 ⊗ₜ[k] x)) =
      traceCovector k ((((pointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A) * Y * (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A)) x := by
  rw [liftBaseChange_traceCovector, tangentMatrix_adjointComodule_endOfPoint,
    tangentMatrix_tangentScalarExtensionEquiv_one_tmul, traceCovector_apply, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

/-- The translate of the trace covector of `Y` by the coadjoint action of `G ∈ GLₙ(A)` is the trace
covector of `G⁻¹ Y G`. -/
theorem translate_traceCovector (G : Matrix.GeneralLinearGroup (Fin n) A)
    (Y : Matrix (Fin n) (Fin n) A) :
    (LinearMap.liftBaseChange A (traceCovector k Y)).restrictScalars k ∘ₗ
        (Comodule.endOfPoint 𝔤 ((pointsMulEquiv n).symm G).ofConv).restrictScalars k ∘ₗ
          TensorProduct.mk k A 𝔤 1 =
      traceCovector k (((G⁻¹ : Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A) * Y * (G : Matrix (Fin n) (Fin n) A)) := by
  ext x
  simpa using liftBaseChange_traceCovector_endOfPoint ((pointsMulEquiv n).symm G) Y x

end Conjugation

end TauCeti.GeneralLinear
