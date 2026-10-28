/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
-- The existence of a base, the rigidity theorem and the independence of the Cartan type from the
-- base are used in proofs only.
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.LinearAlgebra.RootSystem.Isomorphism
import TauCeti.LinearAlgebra.RootSystem.Weyl.CartanType

/-!
# The Cartan-Killing classification of rational root systems

Every irreducible reduced crystallographic finite root system over `ℚ` is isomorphic to the model
root system `TauCeti.DynkinType.rationalRootSystem t` of exactly one valid Dynkin type `t`
(`RootPairing.existsUnique_nonempty_equiv_rationalRootSystem`). So `t ↦ t.rationalRootSystem` is a
bijection from the valid Dynkin types onto the isomorphism classes of such root systems.

The three ingredients are all available. The combinatorial classification attaches a valid Dynkin
type to every base (`TauCeti.classifiedDynkinType`), and that type does not depend on the base
(`TauCeti.HasCartanType.of_base`). The model root systems realize every valid type
(`TauCeti.DynkinType.hasCartanType_rationalRootSystem`). Rigidity turns equal types into an
isomorphism (`TauCeti.nonempty_equiv_of_hasCartanType`). A base to start from exists over any field
of characteristic zero (`RootPairing.nonempty_base`).

## Main results

* `RootPairing.Base.nonempty_equiv_rationalRootSystem_iff`: a rational root system is isomorphic to
  the model of a valid type `t` exactly when `t` is the Dynkin type of one, hence of every, base.
* `RootPairing.existsUnique_nonempty_equiv_rationalRootSystem`: **the Cartan-Killing
  classification**, every irreducible reduced crystallographic finite root system over `ℚ` is
  isomorphic to the model root system of a unique valid Dynkin type.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III,
  §11 and §12.
-/

public section

namespace TauCeti

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  {P : RootPairing ι ℚ M N} [Finite ι] [Nonempty ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]

/-- **A rational root system is isomorphic to the model of its Dynkin type, and to no other.** The
Dynkin type may be read off any base. -/
theorem _root_.RootPairing.Base.nonempty_equiv_rationalRootSystem_iff (b : P.Base)
    {t : DynkinType} (ht : t.Valid) :
    Nonempty (P.Equiv (t.rationalRootSystem ht)) ↔ t = classifiedDynkinType b := by
  refine ⟨fun ⟨e⟩ ↦ ?_, ?_⟩
  · exact (hasCartanType_iff_eq_classifiedDynkinType b ht).mp
      (((DynkinType.hasCartanType_rationalRootSystem t ht).map e.symm).of_base b)
  · rintro rfl
    exact nonempty_equiv_of_hasCartanType b _ _ (hasCartanType_classifiedDynkinType b)
      (DynkinType.hasCartanType_rationalRootSystem _ ht)

variable (P) in
/-- **The Cartan-Killing classification.** Every irreducible reduced crystallographic finite root
system over `ℚ` is isomorphic to the model root system `TauCeti.DynkinType.rationalRootSystem t` of
a unique valid Dynkin type `t`. -/
theorem _root_.RootPairing.existsUnique_nonempty_equiv_rationalRootSystem :
    ∃! t : DynkinType, ∃ ht : t.Valid, Nonempty (P.Equiv (t.rationalRootSystem ht)) := by
  obtain ⟨b⟩ := RootPairing.nonempty_base P
  exact ⟨classifiedDynkinType b, ⟨valid_classifiedDynkinType b,
    (b.nonempty_equiv_rationalRootSystem_iff _).mpr rfl⟩,
    fun t ⟨ht, he⟩ ↦ (b.nonempty_equiv_rationalRootSystem_iff ht).mp he⟩

end TauCeti
