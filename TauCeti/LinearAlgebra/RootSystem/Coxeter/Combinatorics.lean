/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Poincare
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.LongestElement

/-!
# Length and subwords in the Weyl group

This file relates the combinatorics of the native Weyl Coxeter system to roots and actual
simple reflections. Its Poincaré polynomial counts Weyl elements by their number of inversions,
and its Bruhat subword criterion uses `TauCeti.wordProd`, the product of the reflections in the
specified simple roots. In particular, the criterion applies to every reduced expression, not
just to a chosen expression.

* `RootPairing.coeff_poincarePolynomial_weylCoxeterSystem` counts elements with a given number
  of inversions. Finiteness of the Weyl group follows from the base; spanning is not needed.
* `RootPairing.bruhatLE_wordProd_iff_exists_sublist` expresses Bruhat comparison using any word
  whose inversion count equals its number of letters.
* `RootPairing.bruhatLE_wordProd_iff_exists_reduced_sublist` additionally makes the subword
  reduced, with its length equal to the inversion count of the lower element.
* `RootPairing.length_weylCoxeterSystem_longestElement` identifies the length of the longest
  element with the number of positive roots.

The length and reducedness comparisons come from `TauCeti.length_weylCoxeterSystem_eq` and
`TauCeti.isReduced_weylCoxeterSystem_iff`. The longest element here is the existing
`TauCeti.longestElement`, whose definition assumes a spanning root system; the polynomial and
subword results do not make that assumption.

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

/-- The coefficient of degree `k` in the Poincaré polynomial of the Weyl Coxeter system counts
Weyl elements that send exactly `k` positive roots to negative roots. -/
theorem coeff_poincarePolynomial_weylCoxeterSystem (k : ℕ) :
    letI := P.finite_weylGroup_of_base b
    (poincarePolynomial (weylCoxeterSystem P b)).coeff k =
      (Nat.card {w : P.weylGroup // (inversions P b w).ncard = k} : ℤ) := by
  simp only [coeff_poincarePolynomial, length_weylCoxeterSystem_eq]

/-- For any reduced expression in the actual simple root reflections, the elements below its
product in Bruhat order are exactly the products of its subwords. Reducedness is expressed
intrinsically by equality of the inversion count and the number of letters. -/
theorem bruhatLE_wordProd_iff_exists_sublist {u : P.weylGroup} {l : List b.support}
    (hl : (inversions P b (wordProd P b l)).ncard = l.length) :
    (weylCoxeterSystem P b).BruhatLE u (wordProd P b l) ↔
      ∃ s : List b.support, s.Sublist l ∧ wordProd P b s = u := by
  simpa only [weylCoxeterSystem_wordProd] using
    (weylCoxeterSystem P b).bruhatLE_iff_exists_sublist_wordProd_eq
      ((isReduced_weylCoxeterSystem_iff P b l).mpr hl)

/-- The subword in the Bruhat criterion can itself be taken reduced: its number of letters is
the number of inversions of the lower element. The upper reduced expression is arbitrary. -/
theorem bruhatLE_wordProd_iff_exists_reduced_sublist {u : P.weylGroup} {l : List b.support}
    (hl : (inversions P b (wordProd P b l)).ncard = l.length) :
    (weylCoxeterSystem P b).BruhatLE u (wordProd P b l) ↔
      ∃ s : List b.support, s.Sublist l ∧ wordProd P b s = u ∧
        s.length = (inversions P b u).ncard := by
  constructor
  · intro h
    simpa only [weylCoxeterSystem_wordProd, length_weylCoxeterSystem_eq] using
      h.exists_sublist_wordProd_eq_length_eq l (weylCoxeterSystem_wordProd P b l)
  · rintro ⟨s, hs, hsu, -⟩
    exact (P.bruhatLE_wordProd_iff_exists_sublist b hl).mpr ⟨s, hs, hsu⟩

/-- The longest element has Coxeter length equal to the number of positive roots. -/
theorem length_weylCoxeterSystem_longestElement [P.IsRootSystem] :
    (weylCoxeterSystem P b).length (longestElement P b) = (posRoots P b).ncard := by
  rw [length_weylCoxeterSystem_eq, ncard_inversions_longestElement]

end RootPairing
