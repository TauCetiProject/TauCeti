/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Semisimplification
import TauCeti.RepresentationTheory.Augmentation.Semisimple
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Irreducible

/-!
# Examples: the semisimplification of a representation

* An irreducible representation is equivalent to its semisimplification, and the
  semisimplification of the zero representation is zero.
* The semisimplification is idempotent, and a representation with an irreducible subrepresentation
  `W` and irreducible quotient `V/W` has semisimplification `W ⊕ V/W`.
* In characteristic `p`, the regular representation of the cyclic group of order `p` (for `p = 2`
  the action of `ℤ/2` on `𝔽₂²` by `(1 1; 0 1)` in the basis `e₀ + e₁, e₁`) has the
  characteristic polynomials of its semisimplification but is not equivalent to it.
-/

open Representation

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

-- An irreducible representation is equivalent to its semisimplification.
example (ρ : Representation k G V) [ρ.IsIrreducible] : Nonempty (ρ.semisimplification.Equiv ρ) :=
  ρ.nonempty_equiv_semisimplification_iff.mpr inferInstance

-- The semisimplification of the zero representation is zero.
example (ρ : Representation k G PUnit) :
    Subsingleton (TauCeti.semisimplification k[G] ρ.asModule) := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton PUnit)
  infer_instance

-- The semisimplification is idempotent: `(V^ss)^ss ≅ V^ss`.
example (ρ : Representation k G V) :
    Nonempty (ρ.semisimplification.semisimplification.Equiv ρ.semisimplification) :=
  ρ.nonempty_equiv_semisimplification_semisimplification

-- With `W` and `V/W` irreducible, `V^ss ≅ W ⊕ V/W`: the two-step composition series is read off
-- `V^ss ≅ W^ss ⊕ (V/W)^ss`.
example (ρ : Representation k G V) (W : Subrepresentation ρ) [W.toRepresentation.IsIrreducible]
    [W.quotient.IsIrreducible] :
    Nonempty (ρ.semisimplification.Equiv (W.toRepresentation.prod W.quotient)) := by
  obtain ⟨e⟩ := W.nonempty_equiv_semisimplification_prod_quotient
  obtain ⟨e₁⟩ := W.toRepresentation.nonempty_equiv_semisimplification_of_isIrreducible
  obtain ⟨e₂⟩ := W.quotient.nonempty_equiv_semisimplification_of_isIrreducible
  exact ⟨TauCeti.Representation.equivOfAsModuleLinearEquiv
    (TauCeti.Representation.asModuleLinearEquivOfEquiv e ≪≫ₗ
      prodAsModuleEquiv _ _ ≪≫ₗ
      (TauCeti.Representation.asModuleLinearEquivOfEquiv e₁).prodCongr
        (TauCeti.Representation.asModuleLinearEquivOfEquiv e₂) ≪≫ₗ
      (prodAsModuleEquiv _ _).symm)⟩

section Cyclic

variable (p : ℕ) [Fact p.Prime]

-- The regular representation of `ℤ/p` over `𝔽_p` has the characteristic polynomials of its
-- semisimplification ...
example (g : Multiplicative (ZMod p)) :
    ((leftRegular (ZMod p) (Multiplicative (ZMod p))).semisimplification g).charpoly =
      (leftRegular (ZMod p) (Multiplicative (ZMod p)) g).charpoly :=
  charpoly_semisimplification_apply _ g

-- ... but is not equivalent to it, as it is not semisimple.
example : IsEmpty ((leftRegular (ZMod p) (Multiplicative (ZMod p))).semisimplification.Equiv
    (leftRegular (ZMod p) (Multiplicative (ZMod p)))) :=
  not_nonempty_iff.mp fun h ↦ not_isSemisimpleRepresentation_leftRegular (by simp)
    ((nonempty_equiv_semisimplification_iff _).mp h)

end Cyclic
