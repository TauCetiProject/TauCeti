/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Changing the functional in Scharlau transfer

Multiplying the input of a transfer functional by `a` has the same effect as tensoring the
original form with the quadratic line `⟨a⟩` before transfer. The identification uses the
canonical equivalence `L ⊗[L] V ≃ₗ[L] V`, so it works for every scalar `a`, including zero.
For a finite field extension, every pair of nonzero functionals differs in this way by a unit.

This change-of-functional formula controls the dependence on the functional when transfer is
descended to Witt classes.

## Main definitions

* `QuadraticForm.scharlauTransferCompMul`: the change-of-functional isometry, together with its
  forward and inverse application rules.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section

open scoped TensorProduct

namespace QuadraticForm

variable {K L V : Type*} [CommSemiring K] [CommRing L] [Algebra K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [Invertible (2 : L)]

/-- **Change of functional for Scharlau transfer.** Transfer of `Q` along the functional
`x ↦ s (a * x)` is isometric to transfer along `s` after tensoring `Q` with `⟨a⟩`.
The statement also holds for `a = 0`; applications comparing nonzero functionals take `a` to
be the unique unit relating them. -/
def scharlauTransferCompMul (Q : QuadraticForm L V) (s : L →ₗ[K] K) (a : L) :
    (Q.scharlauTransfer (s.comp (LinearMap.mul K L a))).IsometryEquiv
      ((QuadraticForm.tmul (a • (QuadraticMap.sq : QuadraticForm L L)) Q).scharlauTransfer s) :=
  let e := (QuadraticMap.rankOneTensorIsometry Q a).symm.scharlauTransfer s
  { toLinearEquiv := e.toLinearEquiv
    map_app' := fun v => by
      rw [QuadraticMap.scharlauTransfer_comp_mul]
      exact e.map_app v }

/-- The change-of-functional isometry sends `v` to `1 ⊗ v`. -/
@[simp]
theorem scharlauTransferCompMul_apply (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) (v : V) :
    scharlauTransferCompMul Q s a v = 1 ⊗ₜ[L] v := by
  unfold scharlauTransferCompMul
  -- The definition rebuilds the transferred rank-one isometry only to replace its source form
  -- along `scharlauTransfer_comp_mul`; its underlying linear equivalence is copied unchanged.
  change ((QuadraticMap.rankOneTensorIsometry Q a).symm.scharlauTransfer s) v = _
  rw [QuadraticMap.IsometryEquiv.scharlauTransfer_apply,
    QuadraticMap.rankOneTensorIsometry_symm_apply]

/-- The inverse change-of-functional isometry acts by the canonical left unitor. -/
@[simp]
theorem scharlauTransferCompMul_symm_apply (Q : QuadraticForm L V)
    (s : L →ₗ[K] K) (a : L) (x : L ⊗[L] V) :
    (scharlauTransferCompMul Q s a).symm x = TensorProduct.lid L V x := by
  rw [QuadraticMap.IsometryEquiv.symm_apply_eq, scharlauTransferCompMul_apply]
  simpa only [TensorProduct.lid_symm_apply] using
    (TensorProduct.lid L V).symm_apply_apply x |>.symm

end QuadraticForm

namespace QuadraticMap

section Field

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [Invertible (2 : L)]

/-- Any two nonzero functionals on a finite field extension give transfers related by tensoring
the original form with a one-dimensional form of unit coefficient. -/
theorem exists_unit_scharlauTransfer_equivalent_rankOneTensor [FiniteDimensional K L]
    (Q : QuadraticForm L V) (s t : L →ₗ[K] K) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ a : Lˣ, (Q.scharlauTransfer t).Equivalent
      ((QuadraticForm.tmul ((a : L) • (QuadraticMap.sq : QuadraticForm L L)) Q).scharlauTransfer
        s) := by
  obtain ⟨a, ha⟩ := Q.exists_unit_scharlauTransfer_eq s t hs ht
  refine ⟨a, ?_⟩
  rw [ha]
  exact ⟨(rankOneTensorIsometry Q a).symm.scharlauTransfer s⟩

end Field

end QuadraticMap
