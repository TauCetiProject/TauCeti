/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import TauCeti.LinearAlgebra.RootSystem.RankTwo
import TauCeti.LinearAlgebra.RootSystem.Finite.PositiveCombinations

/-!
# The pinned root systems outside G₂

The pinned rational root system is not G₂ when its Dynkin type is not G₂, and its Cartan
integers then have absolute value at most two. Instances for simply-laced types and types
B, C, and F₄ make these root-string bounds available for collecting positive root subgroups
and for punctured-positive normalization. The proof uses `hasCartanType_G2_of_isG2` and
uniqueness of valid Cartan types to exclude G₂.
In particular, outside G₂ no root string has length four:
`TauCeti.DynkinType.three_nsmul_add_notMem_range_root`.

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

/-- The pinned rational root system has no triple root strings exactly when its Dynkin
type is not `G₂`. -/
@[simp] theorem isNotG2_rationalRootSystem_iff {t : DynkinType} {ht : t.Valid} :
    (t.rationalRootSystem ht).IsNotG2 ↔ t ≠ G2 := by
  refine ⟨fun h hG2 => ?_, isNotG2_rationalRootSystem_of_ne_G2⟩
  subst t
  exact ((RootPairing.not_isG2_iff_isNotG2 (G2.rationalRootSystem ht)).mpr h)
    (isG2_of_hasCartanType_G2 (G2.hasCartanType_rationalRootSystem ht))

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

/-- **No root strings of length four outside G₂.** If the pinned rational root system has no
triple root strings, then `3a + c` is not a root of the integral datum, for any roots `a` and `c`.
For linearly independent roots this is the bound on root strings; otherwise `c = ±a` and
`3a + c` is `4a` or `2a`, which are not roots of the reduced datum. -/
theorem three_nsmul_add_notMem_range_root {t : DynkinType} {ht : t.Valid}
    [(t.rationalRootSystem ht).IsNotG2] (a c : Fin t.numRoots) :
    3 • (t.simplyConnectedRootDatum ht).root a + (t.simplyConnectedRootDatum ht).root c ∉
      Set.range (t.simplyConnectedRootDatum ht).root := by
  by_cases hli : LinearIndependent ℚ
      ![(t.rationalRootSystem ht).root a, (t.rationalRootSystem ht).root c]
  · rintro ⟨d, hd⟩
    have hdQ := (t.root_rationalRootSystem_eq_nsmul_add_iff ht a c d 3).mpr hd
    have hcoeff := (t.rationalRootSystem ht).coefficients_of_pos_nsmul_add_pos_nsmul_mem hli
      (by decide : 0 < 3) (by decide : 0 < 1)
      (by simpa only [one_nsmul] using Set.mem_range.mpr ⟨d, hdQ⟩)
    omega
  · -- Dependent roots of the reduced rational system are equal or opposite, and so are the
    -- integral roots they come from.
    have := t.isReduced_simplyConnectedRootDatum ht
    have hint {μ ν : Fin t.rank → ℤ} (h : (fun k => (μ k : ℚ)) = fun k => (ν k : ℚ)) : μ = ν :=
      funext fun k => by exact_mod_cast congrFun h k
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := t.rationalRootSystem ht) a c hli with h | h
    · have hac : (t.simplyConnectedRootDatum ht).root a = (t.simplyConnectedRootDatum ht).root c :=
        hint (funext fun k => by simpa using congrFun h k)
      rw [← hac, ← succ_nsmul]
      exact RootPairing.nsmul_notMem_range_root _ (n := 4)
    · have hac : (t.simplyConnectedRootDatum ht).root c =
          -(t.simplyConnectedRootDatum ht).root a :=
        hint (funext fun k => by have h' := congrFun h k; simp at h' ⊢; linarith)
      rw [hac, ← sub_eq_add_neg, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, add_sub_cancel_right]
      exact RootPairing.nsmul_notMem_range_root _ (n := 2)

end TauCeti.DynkinType
