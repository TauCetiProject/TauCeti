/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import TauCeti.LinearAlgebra.RootSystem.RankTwo

/-!
# The pinned root systems outside G₂

The Cartan integers of the pinned rational systems of simply-laced types and types B, C,
and F₄ have absolute value at most two. These instances make the root-string bounds outside
G₂ available for collecting positive root subgroups and for punctured-positive normalization.
The proof uses `hasCartanType_G2_of_isG2` and uniqueness of valid Cartan types to exclude G₂.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plates I–VIII.
-/

public section

namespace TauCeti.DynkinType

/-- The pinned rational root system of every Dynkin type other than G₂ has no triple
root strings. -/
theorem isNotG2_rationalRootSystem_of_ne_G2 {t : DynkinType} {ht : t.Valid}
    (h : t ≠ G2) : (t.rationalRootSystem ht).IsNotG2 :=
  (t.rationalRootSystem ht).not_isG2_iff_isNotG2.mp fun hG2 =>
    h ((hasCartanType_rationalRootSystem t ht).eq_of_valid
      (hasCartanType_G2_of_isG2 hG2 (t.rationalBase ht)) ht valid_G2)

/-- A simply-laced pinned rational root system is not G₂. -/
theorem isNotG2_rationalRootSystem_of_isSimplyLaced
    {t : DynkinType} {ht : t.Valid} (hs : t.IsSimplyLaced) :
    (t.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 (by rintro rfl; exact not_isSimplyLaced_G2 hs)

/-- The Cartan integers of the rational type-B system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemB (n : ℕ) (hn : (B n).Valid) :
    ((B n).rationalRootSystem hn).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 nofun

/-- The Cartan integers of the rational type-C system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemC (n : ℕ) (hn : (C n).Valid) :
    ((C n).rationalRootSystem hn).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 nofun

/-- The Cartan integers of the rational F₄ system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemF4 (ht : F4.Valid) :
    (F4.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 nofun

/-- The rational type-A root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemA (n : ℕ) (ht : (A n).Valid) :
    ((A n).rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 nofun

/-- The rational type-D root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemD (n : ℕ) (ht : (D n).Valid) :
    ((D n).rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 nofun

/-- The rational E₆ root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemE6 (ht : E6.Valid) :
    (E6.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 nofun

/-- The rational E₇ root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemE7 (ht : E7.Valid) :
    (E7.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 nofun

/-- The rational E₈ root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemE8 (ht : E8.Valid) :
    (E8.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_ne_G2 nofun

end TauCeti.DynkinType
