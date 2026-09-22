/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

/-!
# Quaternion algebras attached to binary quadratic forms

The Clifford algebra of the diagonal binary form `⟨a, b⟩` is the quaternion algebra
`ℍ[R,a,b]`. Consequently, an isometry between two binary diagonal forms induces an algebra
equivalence between the corresponding quaternion algebras. This is the binary quaternion lemma
used to prove that Hasse invariants are independent of a diagonalization.

The result is stated over a commutative ring: Mathlib's Clifford-algebra construction and its
quaternion equivalence require neither a field nor invertibility of two.

## Main result

* `TauCeti.QuaternionAlgebra.nonempty_algEquiv_of_equivalent_binary`: equivalent binary
  diagonal forms have isomorphic quaternion algebras.

## Reference

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, §2.11.
-/

public section

open QuadraticMap
open scoped Quaternion

namespace TauCeti.QuaternionAlgebra

universe u

variable {R : Type u} [CommRing R]

/-- **The binary quaternion lemma.** If the diagonal binary forms `⟨a, b⟩` and `⟨c, d⟩`
are equivalent, then the quaternion algebras `ℍ[R,a,b]` and `ℍ[R,c,d]` are isomorphic as
`R`-algebras.

This follows by functoriality of Clifford algebras under isometries and Mathlib's identification
of the Clifford algebra of a binary diagonal form with the corresponding quaternion algebra. -/
theorem nonempty_algEquiv_of_equivalent_binary (a b c d : R)
    (h : (weightedSumSquares R ![a, b]).Equivalent
      (weightedSumSquares R ![c, d])) :
    Nonempty (ℍ[R,(a : R),(b : R)] ≃ₐ[R] ℍ[R,(c : R),(d : R)]) := by
  obtain ⟨e⟩ := h
  let toCliffordQ (x y : R) :
      (weightedSumSquares R ![x, y]).IsometryEquiv (CliffordAlgebraQuaternion.Q x y) :=
    ⟨LinearEquiv.finTwoArrow R R, fun v ↦ by
      simp [weightedSumSquares_apply, CliffordAlgebraQuaternion.Q_apply]⟩
  exact ⟨CliffordAlgebraQuaternion.equiv.symm |>.trans
    (CliffordAlgebra.equivOfIsometry
      ((toCliffordQ a b).symm.trans (e.trans (toCliffordQ c d)))) |>.trans
    CliffordAlgebraQuaternion.equiv⟩

end TauCeti.QuaternionAlgebra
