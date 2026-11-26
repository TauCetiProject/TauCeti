/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.ClassNumber.NormPair

/-!
# Prime pairs of prescribed product norm from logarithmic windows

For `K = ℚ(√−d)` with `d ≡ 3 (mod 4)`, a supply of primes congruent to `1`
modulo a multiple of `d` in sufficiently many disjoint logarithmic windows gives two distinct
primes whose product is `z * conj z` for some `z ∈ 𝓞 K`. The class-group selection is the one
used in `New.Parameters.exists_prime_pair_norm` of lsernau/grh-lean (`72fead1`).
-/

public section

open Polynomial
open scoped NumberField ComplexConjugate

namespace TauCeti.OneSidedBound

/-- Given a prime `≡ 1 (mod M)` in every logarithmic window of width `W` inside `[U,V]`,
select two such primes with logarithms in `[U,V]` whose product is `z * conj z` in `ℚ(√−d)`.
It suffices that `[U,V]` be strictly wider than `classNumber K + 1` such windows. -/
theorem exists_prime_pair_mul_conj_eq_of_log_windows {K : Type*} [Field K] [NumberField K]
    {d M : ℕ} (hd₄ : d % 4 = 3) (hdM : d ∣ M) {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = X ^ 2 - C (-(d : ℤ))) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (σ : K →+* ℂ) {U V W : ℝ} (hW : 0 ≤ W)
    (hwidth : U + ((NumberField.classNumber K : ℝ) + 1) * W < V)
    (hwindow : ∀ u ∈ Set.Icc U (V - W),
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD M] ∧ Real.log p ∈ Set.Icc u (u + W)) :
    ∃ p q : ℕ, p ≠ q ∧ (∀ n ∈ ({p, q} : Finset ℕ),
      n.Prime ∧ n ≡ 1 [MOD M] ∧ Real.log n ∈ Set.Icc U V) ∧
      ∃ z : 𝓞 K, σ z * conj (σ z) = (p : ℂ) * q := by
  classical
  let h := NumberField.classNumber K
  have hh : 0 < (h : ℝ) := by exact_mod_cast NumberField.classNumber_pos (K := K)
  let D := (V - U - W) / (h : ℝ)
  have hD : W < D := (lt_div_iff₀ hh).mpr (by dsimp only [h]; linarith)
  have hD₀ := hW.trans_lt hD
  have hDh : D * h = V - U - W := div_mul_cancel₀ _ hh.ne'
  let left (i : Fin (h + 1)) := U + (i.val : ℝ) * D
  have hleft (i : Fin (h + 1)) : left i ∈ Set.Icc U (V - W) := by
    refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
    have hi : (i.val : ℝ) ≤ h := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
    dsimp only [left]
    nlinarith [mul_le_mul_of_nonneg_right hi hD₀.le]
  choose p hprime hmod hlog using fun i ↦ hwindow (left i) (hleft i)
  have hsep {i j : Fin (h + 1)} (hij : i < j) : left i + W < left j := by
    have hij' : ((i.val : ℝ) + 1) ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij
    dsimp only [left]
    nlinarith [mul_le_mul_of_nonneg_right hij' hD₀.le]
  have hinj : Function.Injective p := by
    have hmono : StrictMono (fun i ↦ Real.log (p i)) := fun _ _ hij ↦
      (hlog _).2.trans_lt ((hsep hij).trans_le (hlog _).1)
    exact fun i j hpq ↦ hmono.injective (congrArg (fun n : ℕ ↦ Real.log n) hpq)
  let S := Finset.univ.image p
  have hS : NumberField.classNumber K < S.card := by
    simp [S, h, Finset.card_image_of_injective _ hinj]
  have hspec {n : ℕ} (hn : n ∈ S) :
      n.Prime ∧ n ≡ 1 [MOD M] ∧ Real.log n ∈ Set.Icc U V := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨hprime i, hmod i, (hleft i).1.trans (hlog i).1,
      (hlog i).2.trans (by linarith [(hleft i).2])⟩
  obtain ⟨a, ha, b, hb, hab, hz⟩ :=
    NumberField.exists_prime_pair_mul_conj_eq_of_classNumber_lt hd₄ hmin hgen σ S hS
      (fun n hn ↦ ⟨(hspec hn).1, (hspec hn).2.1.of_dvd hdM⟩)
  refine ⟨a, b, hab, fun n hn ↦ hspec ?_, hz⟩
  rcases Finset.mem_insert.mp hn with rfl | hn
  · exact ha
  · rwa [Finset.mem_singleton.mp hn]

end TauCeti.OneSidedBound
