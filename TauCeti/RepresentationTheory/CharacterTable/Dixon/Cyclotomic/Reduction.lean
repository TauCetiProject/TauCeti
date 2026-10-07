/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Checker
public import TauCeti.RingTheory.Cyclotomic.Lift

/-!
# Distinct central-character rows after cyclotomic reduction

An exact cyclotomic character-table certificate has distinct central rows after reduction at
any primitive root modulo a prime not dividing the group order. This holds at every conjugate
root, so aligning the modular rows for cyclotomic lifting requires no additional injectivity
hypothesis on the certificate.

The underlying result is `TauCeti.ClassData.IsExactCharacterTableSpec.map_central_injective`:
exact orthogonality prevents central rows from merging in a ring without zero divisors in which
the group order is nonzero. The reduction need not preserve the certificate's conjugation operation.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik **10** (1967),
  446--450.
-/

public section

namespace TauCeti.ClassData.IsCyclotomicCharacterTableSpec

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {d : ClassData G} {e p : ℕ} [NeZero e] [Fact p.Prime]
variable {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
variable {degree : Fin d.numClasses → ℕ}

/-- The central rows of an exact cyclotomic certificate remain distinct at every conjugate
primitive root modulo a prime in which the group order is nonzero. -/
theorem conjugateResidueRow_injective
    (h : d.IsCyclotomicCharacterTableSpec e omega table degree)
    {α : ZMod p} (hα : IsPrimitiveRoot α e) (hG : (Fintype.card G : ZMod p) ≠ 0)
    (j : Fin e.totient) :
    Function.Injective fun i k ↦ Cyclotomic.conjugateResidues α (omega i k) j := by
  simpa only [Cyclotomic.reduceRingHom_apply, Cyclotomic.conjugateResidues_apply] using
    h.map_central_injective
      (Cyclotomic.reduceRingHom p (Cyclotomic.conjugateRoot e α j)
        (Cyclotomic.isPrimitiveRoot_conjugateRoot hα j)) hG

end TauCeti.ClassData.IsCyclotomicCharacterTableSpec
