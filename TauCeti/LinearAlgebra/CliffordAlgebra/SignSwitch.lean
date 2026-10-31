/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Sign-switch equivalence for Clifford algebras

For a quadratic form `P` over a commutative ring, adjoining one positive line `⟨1⟩` makes the
Clifford algebras of `P` and `-P` isomorphic: `Cl(P ⊕ ⟨1⟩) ≃ₐ Cl(-P ⊕ ⟨1⟩)`. Writing `e` for the
generator of the adjoined line, the isomorphism sends `ι (m, r)` to `e * ι (m, 0) + r • e`.

## Main results

* `CliffordAlgebra.signSwitchEquiv`: the sign-switch algebra equivalence;
* `CliffordAlgebra.signSwitchEquiv_ι`: its equation on generators;
* `CliffordAlgebra.signSwitchEquiv_symm_apply_ι`: the inverse generator equation.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
variable (P P' : QuadraticForm R N)

private def signSwitchGenerator : N × R →ₗ[R] CliffordAlgebra (P'.prod QuadraticMap.sq) :=
  (LinearMap.mulLeft R (ι _ (0, 1)) ∘ₗ ι _ ∘ₗ LinearMap.inl R N R).coprod
    (LinearMap.toSpanSingleton R _ (ι _ (0, 1)))

private theorem signSwitchGenerator_apply (x : N × R) :
    signSwitchGenerator P' x = ι _ (0, 1) * ι _ (x.1, 0) + x.2 • ι _ (0, 1) :=
  rfl

private theorem signSwitchGenerator_sq (h : P' = -P) (x : N × R) :
    signSwitchGenerator P' x * signSwitchGenerator P' x =
      algebraMap R _ (P.prod QuadraticMap.sq x) := by
  rw [signSwitchGenerator_apply]
  set e := ι (P'.prod QuadraticMap.sq) (0, 1)
  set v := ι (P'.prod QuadraticMap.sq) (x.1, 0)
  have he : e * e = 1 := by rw [ι_sq_scalar]; simp
  have hv : v * v = algebraMap R _ (-P x.1) := by rw [ι_sq_scalar]; simp [h]
  have hve : v * e = -(e * v) := eq_neg_of_add_eq_zero_left <| by
    rw [ι_mul_ι_add_swap]; simp [polar]
  have he' (w) : e * (e * w) = w := by rw [← mul_assoc, he, one_mul]
  have hve' (w) : v * (e * w) = -(e * (v * w)) := by rw [← mul_assoc, hve, neg_mul, mul_assoc]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc, hve, hve', mul_neg, he,
    he', hv, smul_neg, smul_add]
  simp [Algebra.smul_def, prod_apply]

private def signSwitchTo (h : P' = -P) :
    CliffordAlgebra (P.prod QuadraticMap.sq) →ₐ[R] CliffordAlgebra (P'.prod QuadraticMap.sq) :=
  lift _ ⟨signSwitchGenerator P', signSwitchGenerator_sq P P' h⟩

private theorem signSwitchTo_ι (h : P' = -P) (x : N × R) :
    signSwitchTo P P' h (ι _ x) = signSwitchGenerator P' x :=
  lift_ι_apply _ _ x

private theorem signSwitchTo_comp_signSwitchTo (h : P' = -P) (h' : P = -P') :
    (signSwitchTo P' P h').comp (signSwitchTo P P' h) = AlgHom.id R _ := by
  ext m <;> simp [signSwitchTo_ι, signSwitchGenerator_apply, Prod.mk_zero_zero, ← mul_assoc]

/-- Adjoining a positive line to a quadratic form or to its negation gives equivalent Clifford
algebras: `Cl(P ⊕ ⟨1⟩) ≃ₐ[R] Cl(-P ⊕ ⟨1⟩)`. -/
def signSwitchEquiv :
    CliffordAlgebra (P.prod QuadraticMap.sq) ≃ₐ[R] CliffordAlgebra ((-P).prod QuadraticMap.sq) :=
  AlgEquiv.ofAlgHom (signSwitchTo P (-P) rfl) (signSwitchTo (-P) P (neg_neg P).symm)
    (signSwitchTo_comp_signSwitchTo (-P) P (neg_neg P).symm rfl)
    (signSwitchTo_comp_signSwitchTo P (-P) rfl (neg_neg P).symm)

/-- The sign-switch equivalence sends `ι (m, r)` to `e * ι (m, 0) + r • e`, where `e = ι (0, 1)`
generates the adjoined positive line. -/
@[simp]
theorem signSwitchEquiv_ι (x : N × R) :
    signSwitchEquiv P (ι _ x) = ι _ (0, 1) * ι _ (x.1, 0) + x.2 • ι _ (0, 1) := by
  rw [signSwitchEquiv, AlgEquiv.ofAlgHom_apply, signSwitchTo_ι, signSwitchGenerator_apply]

/-- The inverse sign-switch equivalence is given by the same formula on generators. -/
@[simp]
theorem signSwitchEquiv_symm_apply_ι (x : N × R) :
    (signSwitchEquiv P).symm (ι _ x) = ι _ (0, 1) * ι _ (x.1, 0) + x.2 • ι _ (0, 1) := by
  rw [signSwitchEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply, signSwitchTo_ι,
    signSwitchGenerator_apply]

end CliffordAlgebra
