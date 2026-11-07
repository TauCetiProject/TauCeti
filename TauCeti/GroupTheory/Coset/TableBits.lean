/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Bitwise
public import TauCeti.GroupTheory.Coset.TableFast

/-!
# Bit masks for coset-table deductions

Each letter has a natural-number mask whose bits record known edges.
`BitsAgree` relates this compact state to `KnownEdges`; `bitsAgree_foldl` proves
that the original indexed deduction and the bit-mask deduction stay in agreement.
The relator, subgroup, tree-edge and closure conditions of the checker are unchanged.
-/

public section

namespace TauCeti.CosetTable

variable {m k : ℕ} (T : TauCeti.CosetTable m k)

/-- One deduction with a natural-number bit mask for each letter.
The known-edge and closure tests are exactly those of `deduceFast`. -/
@[expose]
def deduceBits (bits : Vector ℕ m) (i : Fin k) : List (Fin m) → Vector ℕ m
  | [] => bits
  | t :: u =>
    if (T.edges u i).all (fun e ↦ bits[e.1].testBit e.2.val) &&
        T.act t (T.trace u i) = i then
      bits.set t.val (bits[t] ||| 2 ^ (T.trace u i).val)
    else bits

/-- The bit at a point in each letter's mask records precisely its known-edge flag. -/
@[expose]
def BitsAgree (fast : KnownEdges m k) (bits : Vector ℕ m) : Prop :=
  ∀ (t : Fin m) (i : Fin k), fast[t][i] = bits[t].testBit i.val

/-- Adding an edge preserves agreement between Boolean vectors and bit masks. -/
theorem bitsAgree_set {fast : KnownEdges m k} {bits : Vector ℕ m}
    (h : BitsAgree fast bits) (t : Fin m) (i : Fin k) :
    BitsAgree (fast.set t.val (fast[t].set i.val true))
      (bits.set t.val (bits[t] ||| 2 ^ i.val)) := by
  intro s j
  by_cases ht : t = s
  · subst s
    by_cases hi : i = j
    · subst j
      simp
    · have hij : i.val ≠ j.val := fun he ↦ hi (Fin.ext he)
      simpa [hij, Nat.testBit_two_pow] using h t j
  · have hts : t.val ≠ s.val := fun he ↦ ht (Fin.ext he)
    simpa [hts] using h s j

/-- A deduction preserves agreement, including when its guard fails. -/
theorem bitsAgree_deduce {fast : KnownEdges m k} {bits : Vector ℕ m}
    (h : BitsAgree fast bits) (i : Fin k) (r : List (Fin m)) :
    BitsAgree (T.deduceFast fast i r) (deduceBits T bits i r) := by
  cases r with
  | nil => exact h
  | cons t u =>
    have he : (T.edges u i).all (fun e ↦ fast[e.1][e.2]) =
        (T.edges u i).all (fun e ↦ bits[e.1].testBit e.2.val) := by
      congr 1
      funext e
      exact h e.1 e.2
    simp only [TauCeti.CosetTable.deduceFast, deduceBits, he]
    split_ifs
    · exact bitsAgree_set h t (T.trace u i)
    · exact h

/-- An entire deduction certificate preserves agreement of the two edge states. -/
theorem bitsAgree_foldl {fast : KnownEdges m k} {bits : Vector ℕ m}
    (h : BitsAgree fast bits) (cert : List (Fin k × List (Fin m))) :
    BitsAgree (cert.foldl (fun s c ↦ T.deduceFast s c.1 c.2) fast)
      (cert.foldl (fun s c ↦ deduceBits T s c.1 c.2) bits) := by
  induction cert generalizing fast bits with
  | nil => exact h
  | cons c cert ih =>
    exact ih (bitsAgree_deduce T h c.1 c.2)

end TauCeti.CosetTable
