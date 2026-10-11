/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.SpecialLinear
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.QuaternionProduct

import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Center
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# The four-dimensional Spin group over a square-closed field

For a nondegenerate four-dimensional quadratic space over a field of characteristic different from
two in which every element is a square, the Spin group is noncanonically isomorphic to a product of
two copies of `SL₂`. In particular, this applies over a separably closed field.

The even Clifford center is a split quadratic algebra because its discriminant has a square root.
The resulting quaternion-product model identifies Spin with two quaternion norm-one groups. Each
quaternion algebra splits because its first parameter is a square, and its norm-one group is `SL₂`.

The equivalence is stated as `Nonempty`: its construction chooses an orthogonal basis, a splitting
of the even Clifford center, a quaternion presentation, and a matrix splitting of that quaternion
algebra.

## Main result

* The `_of_forall_isSquare` variant identifies a regular four-dimensional Spin group with
  `SL₂ × SL₂` when every field element is a square.
* `TauCeti.nonempty_spinGroup_mulEquiv_specialLinearGroup_prod_of_finrank_eq_four` identifies a
  regular four-dimensional Spin group with `SL₂ × SL₂` over a separably closed field.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
-/

public section

namespace TauCeti

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nondegenerate four-dimensional quadratic space over a field in which every element is a
square has Spin group noncanonically isomorphic to `SL₂ × SL₂`. -/
theorem nonempty_spinGroup_mulEquiv_specialLinearGroup_prod_of_finrank_eq_four_of_forall_isSquare
    [NeZero (2 : K)] (hsq : ∀ x : K, IsSquare x) (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4) :
    Nonempty (spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  obtain ⟨l, hl, hlen, hspan, hQl⟩ := hQ.exists_list_pairwise_isOrtho
  have hlen4 : l.length = 4 := by rw [hlen, hV]
  have hE : Nonempty (Subalgebra.center K (CliffordAlgebra.even Q) ≃ₐ[K] K × K) :=
    (CliffordAlgebra.nonempty_center_even_algEquiv_prod_iff_isSquare_discriminant
      hl (by rw [hlen4]; decide)
      (by intro h; rw [h] at hlen4; simp at hlen4) hspan hQl).mpr (hsq _)
  obtain ⟨a, b, ⟨eSpin⟩⟩ :=
    CliffordAlgebra.exists_spinGroupEquivQuaternionUnitaryProd_of_finrank_eq_four
      Q hQ hV hE
  obtain ⟨eQuat⟩ :=
    QuaternionAlgebra.nonempty_unitaryEquivSpecialLinear_of_isSquare a b (hsq a)
  exact ⟨eSpin.trans (eQuat.prodCongr eQuat)⟩

/-- A nondegenerate four-dimensional quadratic space over a separably closed field of
characteristic different from two has Spin group noncanonically isomorphic to `SL₂ × SL₂`. -/
theorem nonempty_spinGroup_mulEquiv_specialLinearGroup_prod_of_finrank_eq_four
    [NeZero (2 : K)] [IsSepClosed K] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 4) :
    Nonempty (spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  apply
    nonempty_spinGroup_mulEquiv_specialLinearGroup_prod_of_finrank_eq_four_of_forall_isSquare
      (Q := Q) (fun x ↦ ?_) hQ hV
  obtain ⟨s, hs⟩ := IsSepClosed.isSquare x
  exact ⟨s, by simpa [pow_two] using hs⟩

end TauCeti

end
