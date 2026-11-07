/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Length

/-!
# Positive combinations of two roots in G₂

The factors in a Chevalley commutator are indexed by roots `mα + nβ` with both coefficients
positive. For the pinned integral G₂ datum, this file determines that entire support for every
independent pair, not only for a pair of simple roots. The support is empty, a singleton, a
three-element set for two short roots with short sum, or one of two four-element sets for a
short–long pair. In particular the mixed term has coefficients `(3, 2)` in the short–long
orientation and `(2, 3)` in the reverse orientation.

`g2PositiveRootSupport` records these sets using the existing root, length and pairing tables.
`g2_mem_positiveRootSupport_iff` identifies them with the actual positive combinations for
arbitrary natural coefficients. Thus the finite sets can index a product without overlooking
higher root terms. No group commutator identity is asserted here.

The proof uses the two coordinate determinants to recover the coefficients of an independent
pair and checks the resulting finite root-table calculations in the kernel.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate IX, for the coordinates.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open Set

/-- The positive coefficient pairs occurring between two independent roots of the pinned G₂
root datum. The first coordinate multiplies the first root. An absent root sum gives empty
support; a short–long pair has four terms, two short roots with short sum have three, and the
remaining root sums give one term. Correctness for independent roots is
`g2_mem_positiveRootSupport_iff`. -/
def g2PositiveRootSupport (i j : Fin 12) : Finset (ℕ × ℕ) :=
  if g2Root i + g2Root j ∈ range g2Root then
    if g2Length i = 1 ∧ g2Length j = 3 then {(1, 1), (2, 1), (3, 1), (3, 2)}
    else if g2Length i = 3 ∧ g2Length j = 1 then {(1, 1), (1, 2), (1, 3), (2, 3)}
    else if g2Length i = 1 ∧ g2Length j = 1 ∧
        g2SimplyConnectedRootDatum.pairing i j = -1 then {(1, 1), (2, 1), (1, 2)}
    else {(1, 1)}
  else ∅

/-- The support in terms of the root sum, lengths and Cartan pairing. -/
theorem g2PositiveRootSupport_def (i j : Fin 12) :
    g2PositiveRootSupport i j =
      if g2Root i + g2Root j ∈ range g2Root then
        if g2Length i = 1 ∧ g2Length j = 3 then {(1, 1), (2, 1), (3, 1), (3, 2)}
        else if g2Length i = 3 ∧ g2Length j = 1 then {(1, 1), (1, 2), (1, 3), (2, 3)}
        else if g2Length i = 1 ∧ g2Length j = 1 ∧
            g2SimplyConnectedRootDatum.pairing i j = -1 then {(1, 1), (2, 1), (1, 2)}
        else {(1, 1)}
      else ∅ := (rfl)

/-- The support is empty exactly when the sum of the two roots is not a root. -/
@[simp]
theorem g2PositiveRootSupport_eq_empty_iff (i j : Fin 12) :
    g2PositiveRootSupport i j = ∅ ↔ g2Root i + g2Root j ∉ range g2Root := by
  rw [g2PositiveRootSupport_def]
  split_ifs <;> simp_all

/-- Reversing the root pair exchanges the two coefficients of every term. -/
theorem g2PositiveRootSupport_swap (i j : Fin 12) :
    g2PositiveRootSupport j i =
      (g2PositiveRootSupport i j).map (Equiv.prodComm ℕ ℕ).toEmbedding := by
  simp only [g2PositiveRootSupport_def, g2Length_apply,
    g2SimplyConnectedRootDatum_pairing, Set.mem_range, g2Root_apply, g2Coroot_apply]
  revert i j
  decide +kernel

-- These determinants are specific to the existing two-coordinate root table.
private def g2RootDet (i j : Fin 12) : ℤ :=
  g2Root i 0 * g2Root j 1 - g2Root i 1 * g2Root j 0

private theorem g2RootDet_ne_zero (i j : Fin 12)
    (h : LinearIndependent ℤ ![g2Root i, g2Root j]) : g2RootDet i j ≠ 0 := by
  rw [← g2SimplyConnectedRootDatum_root] at h
  have hi := (RootPairing.IsReduced.linearIndependent_iff
    (P := g2SimplyConnectedRootDatum) (i := i) (j := j)).1 h
  have table : ∀ i j : Fin 12, i ≠ j → g2Root i ≠ -g2Root j → g2RootDet i j ≠ 0 := by
    simp only [g2RootDet, g2Root_apply]
    intro i
    fin_cases i <;> decide +kernel
  rw [g2SimplyConnectedRootDatum_root] at hi
  exact table i j hi.1 hi.2

private theorem g2PositiveRootSupport_sound_table (i j : Fin 12) (m n : Fin 4) :
    (m.val, n.val) ∈ g2PositiveRootSupport i j →
      0 < m.val ∧ 0 < n.val ∧ m.val • g2Root i + n.val • g2Root j ∈ range g2Root := by
  simp only [g2PositiveRootSupport, g2Length_apply, g2SimplyConnectedRootDatum_pairing,
    Set.mem_range, g2Root_apply, g2Coroot_apply]
  revert i j m n
  decide +kernel

private theorem g2PositiveRootSupport_bound (i j : Fin 12) (m n : ℕ)
    (hc : (m, n) ∈ g2PositiveRootSupport i j) : m < 4 ∧ n < 4 := by
  unfold g2PositiveRootSupport at hc
  split_ifs at hc <;> simp_all only [Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty, Prod.mk.injEq] <;> omega

private theorem g2PositiveRootSupport_complete_table (i j k : Fin 12) :
    g2RootDet i j ≠ 0 →
    g2RootDet i j ∣ g2RootDet k j → g2RootDet i j ∣ g2RootDet i k →
    0 < g2RootDet k j / g2RootDet i j → 0 < g2RootDet i k / g2RootDet i j →
    ((g2RootDet k j / g2RootDet i j).toNat,
      (g2RootDet i k / g2RootDet i j).toNat) ∈ g2PositiveRootSupport i j := by
  simp only [g2PositiveRootSupport, g2RootDet, g2Length_apply,
    g2SimplyConnectedRootDatum_pairing, Set.mem_range, g2Root_apply, g2Coroot_apply]
  revert i j k
  decide +kernel

/-- The displayed finite support is exactly the set of strictly positive combinations of an
independent pair that are roots. Both orientations, including their mixed highest-root term,
are included. Coefficients are unrestricted natural numbers. -/
theorem g2_mem_positiveRootSupport_iff (i j : Fin 12)
    (h : LinearIndependent ℤ ![g2Root i, g2Root j]) (m n : ℕ) :
    (m, n) ∈ g2PositiveRootSupport i j ↔
      0 < m ∧ 0 < n ∧ m • g2Root i + n • g2Root j ∈ range g2Root := by
  constructor
  · intro hc
    obtain ⟨hm, hn⟩ := g2PositiveRootSupport_bound i j m n hc
    exact g2PositiveRootSupport_sound_table i j ⟨m, hm⟩ ⟨n, hn⟩ hc
  rintro ⟨hm, hn, k, hk⟩
  have hd := g2RootDet_ne_zero i j h
  have h0 := congrFun hk 0
  have h1 := congrFun hk 1
  simp only [Pi.add_apply, Pi.smul_apply] at h0 h1
  have ha : g2RootDet k j = (m : ℤ) * g2RootDet i j := by
    unfold g2RootDet
    rw [h0, h1]
    ring
  have hb : g2RootDet i k = (n : ℤ) * g2RootDet i j := by
    unfold g2RootDet
    rw [h0, h1]
    ring
  have ht := g2PositiveRootSupport_complete_table i j k hd
  simpa [ha, hb, hd, hm, hn] using ht

end TauCeti.DynkinType
