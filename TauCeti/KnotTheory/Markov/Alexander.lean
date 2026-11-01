/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Alexander
public import TauCeti.KnotTheory.Burau.Normalization
public import TauCeti.KnotTheory.Markov.Basic
import TauCeti.KnotTheory.Burau.Skein
import TauCeti.KnotTheory.Markov.Skein

/-!
# The Seifert and Burau routes to the Alexander polynomial of a closed braid agree

There are two classical ways to compute the Conway-normalized Alexander polynomial of the closure of
a braid, written in the square root `s` of the Alexander variable `t`.

* **From a Seifert surface.** Seifert's algorithm on the closure of a braid word `w` gives the
  canonical Seifert surface, with Seifert matrix `V = TauCeti.BraidWord.seifertMatrix w`, and the
  polynomial is `det(s V - s⁻¹ Vᵀ)` (`Matrix.seifertConwayDeterminant`). This requires the surface
  to be connected, which happens exactly when every level `0, …, n - 2` carries a letter of `w`.
  Otherwise the closure is a split link and the polynomial is `0`. This is
  `TauCeti.BraidWord.seifertAlexander w`, defined in
  `TauCeti.KnotTheory.BraidWord.SeifertMatrix.Alexander`.
* **From the Burau representation.** The corner minor of `burau β - 1`, evaluated at `t = s²` and
  multiplied by the exact Markov normalization `(-1)^p s^(-e-p)`, for `p + 1` strands and exponent
  sum `e` (`TauCeti.MarkovBraid.normalizedBurauAlexander`).

The Seifert route does not depend on the word representing a braid: Artin relations, cyclic
rotation and stabilization change the Seifert matrix by relabellings and unimodular congruences,
and free cancellation by an elementary enlargement, or by a zero row and column when it joins two
components of the canonical surface. So it defines `TauCeti.MarkovBraid.seifertAlexander` on
braids, constant on Markov equivalence classes (`TauCeti.MarkovEquiv.seifertAlexander_eq`). Both
routes satisfy the Conway skein relation `Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`, vanish on braids with an
uncrossed strand, whose closures are split, and take the value `1` on the trivial braid on one
strand, whose closure is the unknot. A Markov invariant with these three properties is determined
(`TauCeti.MarkovBraid.eq_of_skein`), so the two routes agree for every braid and every unit `s` of
every commutative ring
(`TauCeti.MarkovBraid.normalizedBurauAlexander_eq_eval₂_seifertAlexander`).

## Main definitions

* `TauCeti.MarkovBraid.seifertAlexander`: the Seifert-matrix Alexander polynomial of the closure
  of a braid, read from any word representing it.

## Main results

* `TauCeti.MarkovEquiv.seifertAlexander_eq`: it is a Markov invariant.
* `TauCeti.MarkovBraid.seifertAlexander_skein`: it satisfies the Conway skein relation.
* `TauCeti.MarkovBraid.normalizedBurauAlexander_eq_eval₂_seifertAlexander`: **the Seifert-matrix
  and Burau routes to the Alexander polynomial of a closed braid agree.**

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices) and Chapter 8, Theorem 8.6 (the Conway-normalized skein characterization).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 3 (the Burau representation and the Alexander polynomial of a closed braid).
-/

public section

namespace TauCeti

open BraidGroup BraidWord KnotTheory LaurentPolynomial Matrix

namespace MarkovBraid

variable {n : ℕ}

/-- The **Seifert-matrix Alexander polynomial** of the closure of a braid, in the square root `s`
of the Alexander variable: the polynomial `TauCeti.BraidWord.seifertAlexander` of any word
representing the braid (`TauCeti.MarkovBraid.seifertAlexander_eq_of_toBraid_eq`). It agrees with
the normalized Burau invariant
(`TauCeti.MarkovBraid.normalizedBurauAlexander_eq_eval₂_seifertAlexander`). -/
noncomputable def seifertAlexander (β : MarkovBraid) : ℤ[T;T⁻¹] :=
  β.liftWord fun _ w ↦ w.seifertAlexander

/-- The Seifert-matrix Alexander polynomial of a braid is computed by any word representing it. -/
theorem seifertAlexander_eq_of_toBraid_eq {β : MarkovBraid}
    {w : BraidWord (β.predStrands + 1)} (hw : w.toBraid = β.braid) :
    β.seifertAlexander = w.seifertAlexander :=
  liftWord_eq_of_toBraid_eq BraidWord.seifertAlexander_eq_of_toBraid_eq hw

/-- The Seifert-matrix Alexander polynomial of the braid represented by a word is that of the
word. -/
@[simp]
theorem seifertAlexander_mk (w : BraidWord (n + 1)) :
    seifertAlexander ⟨n, w.toBraid⟩ = w.seifertAlexander :=
  liftWord_mk BraidWord.seifertAlexander_eq_of_toBraid_eq w

/-- The trivial braid on one strand closes to the unknot, of Seifert-matrix Alexander
polynomial `1`. -/
@[simp]
theorem seifertAlexander_one_strand : seifertAlexander ⟨0, 1⟩ = 1 := by
  rw [seifertAlexander_eq_of_toBraid_eq (β := ⟨0, 1⟩) (w := []) toBraid_nil,
    seifertAlexander_nil_one]

/-- Adding an uncrossed strand makes the Seifert-matrix Alexander polynomial vanish: the closure
becomes split. -/
@[simp]
theorem seifertAlexander_strandIncl (b : BraidGroup (n + 1)) :
    seifertAlexander ⟨n + 1, strandIncl b⟩ = 0 := by
  obtain ⟨w, rfl⟩ := toBraid_surjective b
  rw [← toBraid_strandIncl, seifertAlexander_mk, BraidWord.seifertAlexander_strandIncl]

/-- **The Conway skein relation for the Seifert-matrix Alexander polynomial of a closed braid.**
Changing one crossing of a braid from positive to negative, and smoothing it, give the three
closures of a skein triple, and `Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`. -/
theorem seifertAlexander_skein (b c : BraidGroup (n + 1)) (i : Fin n) :
    seifertAlexander ⟨n, b * sigma (n := n + 1) i * c⟩ -
        seifertAlexander ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ =
      (T (-1) - T 1) * seifertAlexander ⟨n, b * c⟩ := by
  obtain ⟨u, rfl⟩ := toBraid_surjective b
  obtain ⟨v, rfl⟩ := toBraid_surjective c
  have hw (ε : ℤˣ) : toBraid (u ++ ((i, ε) :: v : BraidWord (n + 1))) =
      u.toBraid * sigma (n := n + 1) i ^ (ε : ℤ) * v.toBraid := by
    rw [toBraid_append, toBraid_cons, mul_assoc]
  rw [seifertAlexander_eq_of_toBraid_eq (β := ⟨n, _⟩) ((hw 1).trans (by simp)),
    seifertAlexander_eq_of_toBraid_eq (β := ⟨n, _⟩) ((hw (-1)).trans (by simp)),
    ← toBraid_append, seifertAlexander_mk, BraidWord.seifertAlexander_skein]

end MarkovBraid

/-- A single Markov move does not change the Seifert-matrix Alexander polynomial. -/
theorem IsMarkovMove.seifertAlexander_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ) :
    β.seifertAlexander = γ.seifertAlexander :=
  h.liftWord_eq BraidWord.seifertAlexander_eq_of_toBraid_eq BraidWord.seifertAlexander_rotate
    BraidWord.seifertAlexander_stabilize

/-- **The Seifert-matrix Alexander polynomial is a Markov invariant.** By Markov's theorem, it is
an invariant of the oriented link obtained by closing the braid. -/
theorem MarkovEquiv.seifertAlexander_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ) :
    β.seifertAlexander = γ.seifertAlexander :=
  h.liftWord_eq BraidWord.seifertAlexander_eq_of_toBraid_eq BraidWord.seifertAlexander_rotate
    BraidWord.seifertAlexander_stabilize

namespace MarkovBraid

/-- **The Seifert-matrix and Burau routes to the Alexander polynomial of a closed braid agree.**
For every braid `β` and every unit `s` of a commutative ring, the normalized Burau invariant at `s`
is the Seifert-matrix Alexander polynomial evaluated at `s`. -/
theorem normalizedBurauAlexander_eq_eval₂_seifertAlexander {R : Type*} [CommRing R]
    (β : MarkovBraid) (s : Rˣ) :
    β.normalizedBurauAlexander s = eval₂ (Int.castRingHom R) s β.seifertAlexander := by
  refine congrFun (eq_of_skein (R := R) (M := R) 1 (((s⁻¹ : Rˣ) : R) - s) 0
    (F := fun β ↦ β.normalizedBurauAlexander s)
    (G := fun β ↦ eval₂ (Int.castRingHom R) s β.seifertAlexander)
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq s)
    (fun _ _ h ↦ by rw [h.seifertAlexander_eq]) (fun n c i ↦ ?_) (fun n c i ↦ ?_)
    (fun n b ↦ by simp) (fun n b ↦ by simp) (by simp)) β
  · simpa using normalizedBurauAlexander_skein 1 c i s
  · have h := congrArg (eval₂ (Int.castRingHom R) s) (seifertAlexander_skein 1 c i)
    simp only [one_mul, map_sub, map_mul, eval₂_T, _root_.zpow_neg_one, zpow_one] at h
    simpa using h

end MarkovBraid

end TauCeti
