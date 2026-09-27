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
      ((QuadraticForm.tmul (a • QuadraticMap.sq (R := L)) Q).scharlauTransfer s) :=
  let e := (QuadraticForm.tensorLIdSMul a Q).symm.scharlauTransfer s
  { toLinearEquiv := e.toLinearEquiv
    map_app' := fun v => by
      rw [scharlauTransfer_comp_mul]
      exact e.map_app v }

/-- The change-of-functional isometry sends `v` to `1 ⊗ v`. -/
@[simp]
theorem IsometryEquiv.scharlauTransferCompMul_apply (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) (v : V) :
    IsometryEquiv.scharlauTransferCompMul Q s a v = 1 ⊗ₜ[L] v := by
  change (QuadraticForm.tensorLIdSMul a Q).symm.scharlauTransfer s v = _
  simp

/-- The inverse change-of-functional isometry acts by the canonical left unitor. -/
@[simp]
theorem IsometryEquiv.scharlauTransferCompMul_symm_apply (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) (x : L ⊗[L] V) :
    (IsometryEquiv.scharlauTransferCompMul Q s a).symm x = TensorProduct.lid L V x := by
  rw [IsometryEquiv.symm_apply_eq]
  rw [IsometryEquiv.scharlauTransferCompMul_apply]
  simpa only [TensorProduct.lid_symm_apply] using
    (TensorProduct.lid L V).symm_apply_apply x |>.symm

end QuadraticMap
