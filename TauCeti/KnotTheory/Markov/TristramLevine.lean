/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Markov.Basic
public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Basic
import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Equivalence

/-!
# The Tristram–Levine signature of a closed braid

Seifert's algorithm turns a braid word `w` into a Seifert surface for its closure, whose Seifert
matrix in a basis of loops is `TauCeti.BraidWord.seifertMatrix w`. This file shows that the
Tristram–Levine signatures `σ_ω` of that matrix depend only on the Markov equivalence class of the
braid `w` represents, so they are invariants of the oriented link obtained by closing it (by
Markov's theorem, which is not formalized here).

Two words representing the same braid have the same signatures
(`TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_eq_of_toBraid_eq`), since Artin
relations and free cancellation change the matrix by a congruence, an elementary enlargement, or a
zero row and column. This defines `TauCeti.MarkovBraid.tristramLevineSignature` on braids. Since
inserting `σᵢ σᵢ⁻¹` on every unused level gives a word whose canonical surface is connected, the
value is the signature of a connected Seifert surface of the closure. Conjugation `c b c⁻¹` is a
cyclic rotation of a word followed by a free cancellation
(`TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_rotate`), and stabilization only relabels
the loops (`TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_stabilize`), so the signature is
constant on Markov equivalence classes (`TauCeti.MarkovEquiv.tristramLevineSignature_eq`).

Unlike the Alexander polynomial, which is symmetric under `t ↦ t⁻¹`, the signature can tell a
knot from its mirror image: mirroring negates it, so it separates the two whenever it is nonzero.
The braid `σ₀³` closes to the right-handed trefoil, of signature `-2`, and `σ₀⁻³` to the
left-handed one, of signature `2`, so the two braids are not Markov equivalent
(`TauCeti.not_markovEquiv_sigma_pow_three_sigma_inv_pow_three`). Informally, by Markov's theorem,
the trefoil is not isotopic to its mirror image.

## Main definitions

* `TauCeti.MarkovBraid.tristramLevineSignature β ω`: the Tristram–Levine signature at `ω` of the
  Seifert matrix of any braid word representing `β`.

## Main results

* `TauCeti.MarkovBraid.tristramLevineSignature_eq_of_toBraid_eq`: the signature of a braid is that
  of the Seifert matrix of any word representing it.
* `TauCeti.IsMarkovMove.tristramLevineSignature_eq` and
  `TauCeti.MarkovEquiv.tristramLevineSignature_eq`: **the Tristram–Levine signature is a Markov
  invariant**.
* `TauCeti.MarkovBraid.tristramLevineSignature_sigma_pow_three_neg_one` and
  `TauCeti.MarkovBraid.tristramLevineSignature_sigma_inv_pow_three_neg_one`: the right- and
  left-handed trefoils have signatures `-2` and `2`.
* `TauCeti.not_markovEquiv_sigma_pow_three_sigma_inv_pow_three`: so `σ₀³` and `σ₀⁻³` are not
  Markov equivalent.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices) and Chapter 8 (the signature, and S-equivalence).
* A. G. Tristram, *Some cobordism invariants for links*, Proc. Cambridge Philos. Soc. 66 (1969),
  251–264.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2 (Markov's theorem).
-/

public section

namespace TauCeti

open BraidGroup BraidWord KnotTheory

namespace MarkovBraid

/-- The **Tristram–Levine signature** at `ω` of the closure of a braid: the signature of the
Hermitian form `(1 - ω) V + (1 - conj ω) Vᵀ`, where `V` is the Seifert matrix of the canonical
Seifert surface of the closure of a word representing the braid. It does not depend on the word
(`TauCeti.MarkovBraid.tristramLevineSignature_eq_of_toBraid_eq`). -/
noncomputable def tristramLevineSignature (β : MarkovBraid) (ω : ℂ) : ℤ :=
  KnotTheory.tristramLevineSignature
    ((toBraid_surjective β.braid).choose.seifertMatrix.map ((↑) : ℤ → ℝ)) ω

/-- The Tristram–Levine signature of a braid is computed by any word representing it. -/
theorem tristramLevineSignature_eq_of_toBraid_eq {β : MarkovBraid}
    {w : BraidWord (β.predStrands + 1)} (hw : w.toBraid = β.braid) (ω : ℂ) :
    β.tristramLevineSignature ω =
      KnotTheory.tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω :=
  tristramLevineSignature_seifertMatrix_eq_of_toBraid_eq
    ((toBraid_surjective β.braid).choose_spec.trans hw.symm) ω

/-- The Tristram–Levine signature of the braid represented by a word is that of the word's Seifert
matrix. -/
@[simp]
theorem tristramLevineSignature_mk {n : ℕ} (w : BraidWord (n + 1)) (ω : ℂ) :
    tristramLevineSignature ⟨n, w.toBraid⟩ ω =
      KnotTheory.tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω :=
  tristramLevineSignature_eq_of_toBraid_eq (β := ⟨n, w.toBraid⟩) rfl ω

end MarkovBraid

/-- A single Markov move does not change the Tristram–Levine signature. -/
theorem IsMarkovMove.tristramLevineSignature_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ)
    (ω : ℂ) : β.tristramLevineSignature ω = γ.tristramLevineSignature ω := by
  cases h with
  | conj b c =>
    -- Conjugation by a word `u` is undone by rotating `u` to the end of the word.
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    obtain ⟨u, rfl⟩ := toBraid_surjective c
    let uInv : BraidWord _ := u.reverse.map fun x ↦ (x.1, -x.2)
    have huInv : uInv.toBraid = u.toBraid⁻¹ := toBraid_reverse_map_neg u
    have hrot := tristramLevineSignature_seifertMatrix_rotate (u ++ (w ++ uInv)) u.length ω
    rw [List.rotate_append_length_eq] at hrot
    rw [MarkovBraid.tristramLevineSignature_mk,
      MarkovBraid.tristramLevineSignature_eq_of_toBraid_eq (w := u ++ (w ++ uInv))
        (by rw [toBraid_append, toBraid_append, huInv, mul_assoc]), ← hrot]
    exact tristramLevineSignature_seifertMatrix_eq_of_toBraid_eq
      (by rw [toBraid_append, toBraid_append, huInv, inv_mul_cancel_right]) ω
  | stabilize b =>
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    rw [MarkovBraid.tristramLevineSignature_eq_of_toBraid_eq (w := w.stabilize 1) (by simp),
      tristramLevineSignature_seifertMatrix_stabilize, MarkovBraid.tristramLevineSignature_mk]
  | stabilizeInv b =>
    obtain ⟨w, rfl⟩ := toBraid_surjective b
    rw [MarkovBraid.tristramLevineSignature_eq_of_toBraid_eq (w := w.stabilize (-1)) (by simp),
      tristramLevineSignature_seifertMatrix_stabilize, MarkovBraid.tristramLevineSignature_mk]

/-- **The Tristram–Levine signature is a Markov invariant.** Markov-equivalent braids have the same
Tristram–Levine signature at every `ω`; by Markov's theorem, it is an invariant of the oriented
link obtained by closing the braid. -/
theorem MarkovEquiv.tristramLevineSignature_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (ω : ℂ) : β.tristramLevineSignature ω = γ.tristramLevineSignature ω :=
  h.induction (fun hmove ↦ hmove.tristramLevineSignature_eq ω) (fun _ ↦ rfl)
    (fun _ ih ↦ ih.symm) (fun _ _ ih ih' ↦ ih.trans ih')

/-! ### The right- and left-handed trefoils -/

namespace MarkovBraid

/-- **The right-handed trefoil has signature `-2`.** The braid `σ₀³` closes to the right-handed
trefoil, and its Seifert matrix has classical signature `-2`. -/
theorem tristramLevineSignature_sigma_pow_three_neg_one :
    tristramLevineSignature ⟨1, sigma 0 ^ 3⟩ (-1) = -2 := by
  have hw : toBraid (n := 2) [(0, 1), (0, 1), (0, 1)] = sigma 0 ^ 3 := by
    rw [toBraid_cons, toBraid_cons, toBraid_cons, toBraid_nil]
    simp [pow_succ, mul_assoc]
  rw [tristramLevineSignature_eq_of_toBraid_eq hw, KnotTheory.tristramLevineSignature_neg_one,
    signature_seifertMatrix_trefoil]

/-- **The left-handed trefoil has signature `2`.** The braid `σ₀⁻³` closes to the left-handed
trefoil, the mirror image of the closure of `σ₀³`. -/
theorem tristramLevineSignature_sigma_inv_pow_three_neg_one :
    tristramLevineSignature ⟨1, (sigma 0)⁻¹ ^ 3⟩ (-1) = 2 := by
  have hw : toBraid (n := 2) [(0, -1), (0, -1), (0, -1)] = (sigma 0)⁻¹ ^ 3 := by
    rw [toBraid_cons, toBraid_cons, toBraid_cons, toBraid_nil]
    simp [pow_succ, mul_assoc]
  rw [tristramLevineSignature_eq_of_toBraid_eq hw, KnotTheory.tristramLevineSignature_neg_one,
    signature_seifertMatrix_mirrorTrefoil]

end MarkovBraid

/-- **The trefoil braid is not Markov equivalent to its mirror image.** The braids `σ₀³` and
`σ₀⁻³`, whose closures are the right- and left-handed trefoils, are not Markov equivalent: their
Tristram–Levine signatures at `ω = -1` are `-2` and `2`. The Alexander polynomial cannot separate
them, being the same for a knot and its mirror image. Informally, by Markov's theorem, the trefoil
is chiral. -/
theorem not_markovEquiv_sigma_pow_three_sigma_inv_pow_three :
    ¬ MarkovEquiv ⟨1, sigma 0 ^ 3⟩ ⟨1, (sigma 0)⁻¹ ^ 3⟩ := fun h ↦ by
  have := h.tristramLevineSignature_eq (-1)
  rw [MarkovBraid.tristramLevineSignature_sigma_pow_three_neg_one,
    MarkovBraid.tristramLevineSignature_sigma_inv_pow_three_neg_one] at this
  omega

end TauCeti
