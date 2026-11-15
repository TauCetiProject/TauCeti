/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Etale.Weakly
import TauCeti.RingTheory.Henselization.IndEtale
import TauCeti.RingTheory.Ideal.Pure

/-!
# Checks for diagonal flatness of ind-étale algebras

These checks exercise the new weak-étaleness instance on henselizations, including a
nonreduced base and a henselization which is the zero ring. A nonflat quotient of the
integers tests the kernel criterion used in the diagonal-flatness argument.
-/

open scoped TensorProduct

universe u

-- The actual diagonal, not only the structure map, is flat.
example (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [TauCeti.Algebra.IndEtale R S] :
    (Algebra.TensorProduct.lmul' R (S := S)).Flat :=
  Algebra.WeaklyEtale.flat_lmul' R S

-- Henselization needs neither Noetherianity nor finite generation of its defining ideal.
example (R : Type u) [CommRing R] (I : Ideal R) :
    Algebra.WeaklyEtale R (TauCeti.Henselization.algebra I) := inferInstance

-- A nonreduced base is allowed.
example : Algebra.WeaklyEtale (ZMod 4)
    (TauCeti.Henselization.algebra (Ideal.span {(2 : ZMod 4)})) := inferInstance

-- The henselization along the unit ideal is the zero ring; its diagonal is still flat.
example (R : Type u) [CommRing R] :
    (Algebra.TensorProduct.lmul' R
      (S := TauCeti.Henselization.algebra (⊤ : Ideal R))).Flat :=
  Algebra.WeaklyEtale.flat_lmul' R _

-- A surjective algebra map need not satisfy the elementwise kernel criterion.
example : ¬ (Int.castRingHom (ZMod 2)).Flat := by
  intro h
  obtain ⟨y, hy, h2⟩ :=
    (RingHom.flat_iff_forall_exists_eq_mul_of_surjective _ (ZMod.intCast_surjective)).mp h
      2 (by decide)
  have : y = 1 := by omega
  subst y
  exact one_ne_zero hy
