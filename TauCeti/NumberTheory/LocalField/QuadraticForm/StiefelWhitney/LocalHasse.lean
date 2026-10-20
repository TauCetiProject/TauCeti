/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Hasse
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Brauer

/-!
# The second Stiefel–Whitney class and the local Hasse invariant

Let `K` be a nonarchimedean local field in which `2` is invertible, for instance a finite
extension of `ℚ₂`. The second Stiefel–Whitney class of a regular form over `K` is determined by
its local Hasse invariant `∏_{i<j} (aᵢ, aⱼ)_K`. So every identity between second Stiefel–Whitney
classes over `K` is an identity between signs, which can be evaluated with the Hilbert symbol.

Over a general field `w₂` corresponds to the Brauer-valued Hasse invariant, a sum of quaternion
classes. Over a local field a quaternion algebra is determined by its Hilbert symbol, so this
Brauer-valued invariant carries exactly the information of the local sign-valued one.

## Main results

* `TauCeti.sw2Class_eq_iff_localHasse_eq`: two regular form classes have the same `w₂` exactly
  when their local Hasse invariants agree.
* `TauCeti.sw2Class_eq_cup_kummerClass_iff_localHasse_eq`: `w₂(q) = (a) ∪ (b)` if and only if
  the local Hasse invariant of `q` is `(a, b)_K`.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), XIV §2, Proposition 5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, GSM 67 (2005), Chapter V, §3 and
  Chapter VI, §2.
-/

public section

namespace TauCeti

open _root_.ContinuousCohomology RegularFormClass

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- **The second Stiefel–Whitney class over a local field is the local Hasse invariant**: two
regular form classes over `K` have the same `w₂` exactly when their local Hasse invariants agree.
No equality of ranks or discriminants is required. -/
theorem sw2Class_eq_iff_localHasse_eq (q r : RegularFormClass K) :
    sw2Class q = sw2Class r ↔ localHasse q = localHasse r := by
  rw [sw2Class_eq_iff_hasseInvariant_eq, ← quaternionSubgroupSignEquiv_apply_hasseInvariant,
    ← quaternionSubgroupSignEquiv_apply_hasseInvariant, EmbeddingLike.apply_eq_iff_eq,
    Subtype.mk.injEq]

/-- The second Stiefel–Whitney class of a regular form class over a local field vanishes exactly
when its local Hasse invariant is `1`. -/
theorem sw2Class_eq_zero_iff_localHasse_eq_one (q : RegularFormClass K) :
    sw2Class q = 0 ↔ localHasse q = 1 := by
  simpa only [sw2Class_zero, localHasse_zero] using sw2Class_eq_iff_localHasse_eq q 0

/-- The second Stiefel–Whitney class of a regular form class over a local field is the Kummer cup
`(a) ∪ (b)` exactly when its local Hasse invariant is the Hilbert symbol `(a, b)_K`. -/
theorem sw2Class_eq_cup_kummerClass_iff_localHasse_eq (q : RegularFormClass K) (a b : Kˣ) :
    sw2Class q =
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) ↔
      localHasse q = hilbertSymbol a b := by
  rw [← sw2Class_mk_binary, ← localHasse_mk_binary, sw2Class_eq_iff_localHasse_eq]

end TauCeti
