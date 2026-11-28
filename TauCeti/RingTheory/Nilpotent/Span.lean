/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Abel

/-!
# Multiplicative generation along a nilpotent scalar

If `t` is nilpotent and `s` spans an associative algebra, the elements `1 + t • x`
are generated multiplicatively by `1 + (t * c) • b` for scalars `c` and `b ∈ s`.
In a truncated polynomial algebra this allows multiplicative identities on a spanning
set to be extended to arbitrary sums, one power of the variable at a time.
-/

public section

namespace Submonoid

/-- To contain every `1 + t • x` for a nilpotent scalar `t`, it suffices for a submonoid
to contain these elements for scalar multiples of a spanning set. -/
theorem one_add_smul_mem_of_isNilpotent_of_span_eq_top
    {S R : Type*} [CommRing S] [Semiring R] [Algebra S R] (M : Submonoid R)
    {t : S} (ht : IsNilpotent t) {s : Set R} (hs : Submodule.span S s = ⊤)
    (hgen : ∀ b ∈ s, ∀ c : S, 1 + (t * c) • b ∈ M) (x : R) : 1 + t • x ∈ M := by
  let : Ring R := Algebra.semiringToRing S
  obtain ⟨n, hn⟩ := ht
  have unit (k : ℕ) (a : R) : IsUnit (1 + t ^ (k + 1) • a) := by
    apply IsNilpotent.isUnit_one_add
    exact ⟨n, by rw [smul_pow, ← pow_mul, Nat.mul_comm, pow_mul, hn]; simp⟩
  suffices h : ∀ k ≤ n, ∀ a : R, 1 + t ^ (k + 1) • a ∈ M by
    simpa using h 0 (Nat.zero_le _) x
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self => simp [pow_succ, hn]
  | of_succ k _ ih =>
    intro a
    have ha : a ∈ Submodule.span S s := hs ▸ Submodule.mem_top
    induction ha using Submodule.closure_induction with
    | zero => simp
    | smul_mem c b hb => simpa [smul_smul, pow_succ', mul_assoc] using hgen b hb (t ^ k * c)
    | add a b _ _ ha hb =>
      -- The error in multiplying the two linear factors has order 2(k+1).
      -- Their product is a unit, so a factor of order k+2 corrects it.
      obtain ⟨u, hu⟩ := (unit k a).mul (unit k b)
      let e := t ^ k • (a * b)
      have herr : t ^ (k + 1 + 1) • e = (t ^ (k + 1) • a) * (t ^ (k + 1) • b) := by
        simp only [e, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add]
        congr 2
        omega
      have hfactor : (u : R) * (1 + t ^ (k + 1 + 1) • (↑u⁻¹ * (-e))) =
          1 + t ^ (k + 1) • (a + b) := by
        rw [mul_add, mul_smul_comm, ← mul_assoc, Units.mul_inv]
        simp only [mul_one, one_mul, smul_neg, herr, hu, add_mul, mul_add, smul_add]
        abel
      exact hfactor ▸ M.mul_mem (hu ▸ M.mul_mem ha hb) (ih _)

end Submonoid
