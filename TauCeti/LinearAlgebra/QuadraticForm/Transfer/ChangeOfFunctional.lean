/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.TensorProduct
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic

/-!
# Change of functional for Scharlau transfer

Composing a transfer functional with multiplication by `a` has the same effect as tensoring
the form with the quadratic line `⟨a⟩` before transfer. The isometry is induced by the
canonical left unitor `L ⊗[L] V ≃ V`.

This identifies the transfers obtained from different nonzero functionals on a finite field
extension: the functionals differ by multiplication by a unique unit, and the corresponding
transfers differ by tensoring with its quadratic line.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section

open scoped TensorProduct

namespace QuadraticForm

variable {R M : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M]

/-- The tensor product of the quadratic line `⟨a⟩` with `Q` is isometric to `a • Q`.
The underlying linear equivalence is the canonical left unitor. -/
def tensorLIdSMul (a : R) (Q : QuadraticForm R M) :
    (QuadraticForm.tmul (a • QuadraticMap.sq (R := R)) Q).IsometryEquiv (a • Q) where
  toLinearEquiv := TensorProduct.lid R M
  map_app' x := by
    calc
      (a • Q) (TensorProduct.lid R M x) = a • Q (TensorProduct.lid R M x) := by
        rw [smul_apply]
      _ = a • QuadraticForm.tmul (QuadraticMap.sq (R := R)) Q x := by
        rw [tmul_tensorLId_apply]
      _ = QuadraticForm.tmul (a • QuadraticMap.sq (R := R)) Q x := by
        rw [QuadraticForm.smul_tmul, smul_apply]

/-- The isometry from `⟨a⟩ ⊗ Q` to `a • Q` acts by the canonical left unitor. -/
@[simp]
theorem tensorLIdSMul_apply (a : R) (Q : QuadraticForm R M) (x : R ⊗[R] M) :
    tensorLIdSMul a Q x = TensorProduct.lid R M x := (rfl)

/-- The inverse isometry sends a vector to the pure tensor with left factor `1`. -/
@[simp]
theorem tensorLIdSMul_symm_apply (a : R) (Q : QuadraticForm R M) (x : M) :
    (tensorLIdSMul a Q).symm x = 1 ⊗ₜ[R] x := (rfl)

end QuadraticForm

namespace QuadraticMap

variable {K L V : Type*} [CommRing K] [CommRing L] [Algebra K L]
  [Invertible (2 : L)] [AddCommGroup V] [Module L V] [Module K V]
  [IsScalarTower K L V]

/-- **Change of functional for Scharlau transfer.** Transfer of `Q` along the functional
`x ↦ s (a * x)` is isometric to transfer along `s` after tensoring `Q` with `⟨a⟩`.
The statement also holds for `a = 0`; applications comparing nonzero functionals take `a` to
be the unique unit relating them. -/
def IsometryEquiv.scharlauTransferCompMul (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) :
    (Q.scharlauTransfer (s.comp (LinearMap.mul K L a))).IsometryEquiv
      ((QuadraticForm.tmul (a • QuadraticMap.sq (R := L)) Q).scharlauTransfer s) where
  toLinearEquiv := (TensorProduct.lid L V).symm.restrictScalars K
  map_app' v := by
    simp [QuadraticForm.tensorDistrib_tmul, smul_eq_mul]

/-- The change-of-functional isometry sends `v` to `1 ⊗ v`. -/
@[simp]
theorem IsometryEquiv.scharlauTransferCompMul_apply (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) (v : V) :
    IsometryEquiv.scharlauTransferCompMul Q s a v = 1 ⊗ₜ[L] v := (rfl)

end QuadraticMap
