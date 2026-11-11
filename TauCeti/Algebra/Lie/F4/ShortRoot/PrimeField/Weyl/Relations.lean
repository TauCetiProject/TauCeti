/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Weyl.Basic
public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Relations

/-!
# Braid relations in the F₄ carrier generated over 𝔽₂

The pinned Weyl words in the short-root F₄ carrier generated over 𝔽₂ satisfy the
Bourbaki braid relations, including the four-letter relation between nodes 1 and 2.
This permits braid moves in the words used to conjugate numbered root subgroups.
The relations hold over every commutative 𝔽₂-algebra, including nonreduced algebras.

The matrix comparison with the integral representatives transfers
`TauCeti.F4ShortRoot.weylWordPoint_braid`. No identification of the prime-field generated
carrier with the reduction of the integral carrier, or with the pinned simply connected
group scheme, is asserted.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

/-- The Weyl representatives in the prime-field generated carrier satisfy every F₄
braid relation over every commutative 𝔽₂-algebra. -/
theorem weylWordPoint_braid (i j : Fin 4) (A : Type*) [CommRing A] [Algebra (ZMod 2) A] :
    weylWordPoint (CoxeterSystem.braidWord CoxeterMatrix.F₄ i j) A =
      weylWordPoint (CoxeterSystem.braidWord CoxeterMatrix.F₄ j i) A := by
  apply Subtype.ext
  rw [coe_weylWordPoint, coe_weylWordPoint]
  exact congrArg Subtype.val (F4ShortRoot.weylWordPoint_braid i j A)

end TauCeti.F4ShortRoot.PrimeField
