/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Transposition into the opposite ring

Transposing an invertible matrix and passing its coefficients to the opposite ring reverses
products. On algebraic `K₁`, the same operation induces a homomorphism because the target is
abelian. Its value on a finite matrix is the class of the transpose with opposite coefficients.
-/

public section

noncomputable section

open Matrix MulOpposite

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R S : Type*} [Semiring R] [Semiring S]

/-- Transposition of invertible matrices into the opposite coefficient ring, as an
anti-isomorphism. This is the unit-group form of `RingEquiv.mopMatrix`. -/
def transposeOpEquiv : GL n R ≃* (GL n Rᵐᵒᵖ)ᵐᵒᵖ :=
  (MulEquiv.opOp (GL n R)).trans <|
    MulEquiv.op (((Units.mapEquiv
      (RingEquiv.mopMatrix (m := n) (α := R)).toMulEquiv).trans Units.opEquiv).symm)

/-- The entries of the transpose over the opposite ring are the opposite entries of the
original matrix, with row and column exchanged. -/
@[simp]
theorem coe_unop_transposeOpEquiv (g : GL n R) :
    ((transposeOpEquiv g).unop : Matrix n n Rᵐᵒᵖ) = (g : Matrix n n R)ᵀ.map op :=
  (rfl)

/-- Transpose into the opposite ring commutes with entrywise scalar change. -/
@[simp]
theorem unop_transposeOpEquiv_map (f : R →+* S) (g : GL n R) :
    (transposeOpEquiv (Units.map (MonoidHom.ofClass (f.mapMatrix (m := n))) g)).unop =
      Units.map (MonoidHom.ofClass (f.op.mapMatrix (m := n))) (transposeOpEquiv g).unop := by
  apply Units.ext
  ext i j
  simp [RingHom.mapMatrix_apply]

end Matrix.GeneralLinearGroup

namespace TauCeti

open Matrix.GeneralLinearGroup

variable {R S : Type*} [Ring R] [Ring S]

/-- Transpose into the opposite ring preserves identity stabilization. -/
@[simp]
theorem unop_transposeOpEquiv_stabilizeGL {m n : ℕ} (h : m ≤ n) (g : GL (Fin m) R) :
    (transposeOpEquiv (stabilizeGL R h g)).unop =
      stabilizeGL Rᵐᵒᵖ h (transposeOpEquiv g).unop := by
  apply Units.ext
  ext i j
  simp only [coe_unop_transposeOpEquiv, Matrix.map_apply, Matrix.transpose_apply,
    coe_stabilizeGL_apply]
  split_ifs <;> simp_all [Matrix.one_apply, eq_comm, apply_ite op]

namespace AlgebraicK1

/-- Transposing matrices into the opposite ring induces a homomorphism of algebraic `K₁`.
The value on a finite representative is its transpose with opposite coefficients. -/
def transposeOp : AlgebraicK1 R →* AlgebraicK1 Rᵐᵒᵖ :=
  lift (fun n ↦
    { toFun := fun g ↦ mk Rᵐᵒᵖ n (transposeOpEquiv g).unop
      map_one' := by simp
      map_mul' := fun g h ↦ by rw [map_mul, MulOpposite.unop_mul, map_mul, mul_comm] })
    (fun _ _ h g ↦ by simp [unop_transposeOpEquiv_stabilizeGL h g])

/-- Transposition on algebraic `K₁` sends a finite representative to the class of its transpose
over the opposite coefficient ring. -/
@[simp]
theorem transposeOp_mk (n : ℕ) (g : GL (Fin n) R) :
    transposeOp (mk R n g) = mk Rᵐᵒᵖ n (transposeOpEquiv g).unop :=
  lift_mk _ _ _ _

/-- The transpose homomorphism on algebraic `K₁` is natural in the coefficient ring. -/
@[simp]
theorem transposeOp_map (f : R →+* S) (x : AlgebraicK1 R) :
    transposeOp (map f x) = map f.op (transposeOp x) := by
  obtain ⟨n, g, rfl⟩ := exists_mk x
  simp

end AlgebraicK1
end TauCeti
