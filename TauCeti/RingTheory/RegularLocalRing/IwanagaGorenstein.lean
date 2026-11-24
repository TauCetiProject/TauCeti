/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IwanagaGorenstein
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Regular rings of finite Krull dimension are Iwanaga–Gorenstein

Every commutative Noetherian regular ring `R` of finite Krull dimension has global dimension bounded
by `ringKrullDim R` (`ModuleCat.projectiveDimension_le_ringKrullDim`), hence is Iwanaga–Gorenstein
(`of_isRegularRing_of_ringKrullDim_lt_top`, `of_isRegularRing_of_krullDimLE`). In particular, every
regular local ring is Iwanaga–Gorenstein.

## References

* Yasuo Iwanaga, *On rings with finite self-injective dimension*, Comm. Algebra **7** (1979).
* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* H. Matsumura, *Commutative Ring Theory*, Section 19, Theorem 19.2.
-/

public section

namespace TauCeti.IsIwanagaGorenstein

universe u

/-- **Regular rings of finite Krull dimension are Iwanaga–Gorenstein.** -/
theorem of_isRegularRing_of_ringKrullDim_lt_top (R : Type u) [CommRing R] [IsRegularRing R]
    (h : ringKrullDim R < ⊤) : IsIwanagaGorenstein R :=
  of_globalDimension_lt_top R <|
    ((globalDimension_le_iff R _).mpr ModuleCat.projectiveDimension_le_ringKrullDim).trans_lt h

/-- A commutative regular ring with `[Ring.KrullDimLE d R]` is Iwanaga–Gorenstein. -/
theorem of_isRegularRing_of_krullDimLE (R : Type u) [CommRing R] [IsRegularRing R] (d : ℕ)
    [Ring.KrullDimLE d R] : IsIwanagaGorenstein R :=
  of_isRegularRing_of_ringKrullDim_lt_top R <|
    (Order.KrullDimLE.krullDim_le (n := d) (α := PrimeSpectrum R)).trans_lt
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))

/-- Regular local rings are Iwanaga–Gorenstein. -/
instance (R : Type u) [CommRing R] [IsRegularLocalRing R] : IsIwanagaGorenstein R :=
  of_globalDimension_lt_top R IsRegularLocalRing.globalDimension_lt_top

end TauCeti.IsIwanagaGorenstein
