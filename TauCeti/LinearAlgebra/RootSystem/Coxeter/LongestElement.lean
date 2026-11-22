/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.LongestElement
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.Opposition.Basic

/-!
# The longest element in the Weyl Coxeter system

This file connects the longest element `TauCeti.longestElement` of a finite Weyl group to its
Coxeter structure `TauCeti.weylCoxeterSystem`:

* `RootPairing.length_weylCoxeterSystem_longestElement` identifies the Coxeter length of the
  longest element with the number of positive roots.
* `RootPairing.isLongest_longestElement`: the longest element complements lengths,
  `ℓ (w * w₀) + ℓ w = ℓ w₀`, so it reverses the Bruhat order of the Weyl group and of its
  parabolic quotients (`TauCeti.GroupTheory.Coxeter.LongestElement`).
* `TauCeti.conj_longestElement_simple`: conjugating a simple reflection by `w₀` applies the
  opposition involution `TauCeti.oppositionPerm`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI, §1, no. 6.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, §2.2 and Theorem 3.3.1.
-/

public section

open TauCeti

namespace RootPairing

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- The longest element has Coxeter length equal to the number of positive roots. -/
theorem length_weylCoxeterSystem_longestElement :
    (weylCoxeterSystem P b).length (longestElement P b) = (posRoots P b).ncard := by
  rw [length_weylCoxeterSystem_eq, ncard_inversions_longestElement]

/-- **The longest element of the Weyl group is a longest element of the Weyl Coxeter system**:
`ℓ (w * w₀) + ℓ w = ℓ w₀` for every `w`. -/
theorem isLongest_longestElement :
    (weylCoxeterSystem P b).IsLongest (longestElement P b) := by
  simp only [CoxeterSystem.isLongest_iff, length_weylCoxeterSystem_eq, inversions_longestElement]
  exact ncard_inversions_mul_longestElement_add_ncard_inversions P b

end RootPairing

namespace TauCeti

open RootPairing

/-- **Conjugating a simple reflection by `w₀` applies the opposition involution.** -/
theorem conj_longestElement_simple {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
    {b : P.Base} [Finite ι] [P.IsCrystallographic] [P.IsReduced] (i : b.support) :
    longestElement P b * (weylCoxeterSystem P b).simple i * longestElement P b =
      (weylCoxeterSystem P b).simple (oppositionPerm P b i) := by
  rw [weylCoxeterSystem_simple, weylCoxeterSystem_simple, coe_oppositionPerm]
  have hconj : longestElement P b * weylGroup.ofIdx P ↑i * longestElement P b =
      longestElement P b * weylGroup.ofIdx P ↑i * (longestElement P b)⁻¹ :=
    congrArg (_ * ·) (longestElement_inv P b).symm
  rw [hconj, ← weylGroup.ofIdx_weylGroupToPerm_eq_conj]
  let := P.indexNeg
  have hneg : opposition P b ↑i = -(P.weylGroupToPerm (longestElement P b) ↑i) := by
    rw [RootPairing.indexNeg_neg, ← P.root_eq_neg_iff, root_opposition, P.weylGroup_apply_root]
  rw [hneg, weylGroup.ofIdx_neg]

end TauCeti
