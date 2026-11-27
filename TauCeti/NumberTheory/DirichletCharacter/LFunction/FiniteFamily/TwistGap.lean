/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.PowerLevel
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.TwoPrimeTwists
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# A shared real zero gap for quadratic Dirichlet twists

For a conductor dividing `2 ^ k * f * q * d`, with `q` and `d` distinct odd auxiliary
primes coprime to `f`, the real characters are accounted for by quadratic characters at
level `8 * f` and their three Legendre twists. Thus it suffices to check the gap for the
twists; the untwisted characters have a common gap fixed before choosing the primes or
the height `k` of the tower.

The family of twists checked here is that of Levent Alpöge's `UpperTheory.Top.RealBox`
(`Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean`).
-/

public section

open Set
open scoped ComplexOrder

namespace DirichletCharacter

/-- For quadratic characters with conductor dividing `2 ^ k * (f * q * d)`, a zero gap
of width `c` for the three Legendre twists of every quadratic character modulo `8 * f`
gives a zero gap of width `min δ c` for the entire family, where `δ` depends only on `f`.
The level of a character can be larger than its conductor; the comparison is at real points
strictly between zero and one, so changing the level does not affect nonvanishing. -/
theorem exists_pos_real_zero_gap_of_legendreTwists (f : ℕ) [NeZero f] :
    ∃ δ ∈ Ioc (0 : ℝ) (1 / 2),
      ∀ {q d : ℕ} [Fact q.Prime] [Fact d.Prime],
      (8 * f).Coprime q → (8 * f * q).Coprime d → ∀ c : ℝ,
      (∀ (ψ : DirichletCharacter ℂ (8 * f)), ψ.IsQuadratic → ∀ β ∈ Ioo (max (1 - c) 0) 1,
        (ψ.legendreTwist q).LFunction β ≠ 0 ∧ (ψ.legendreTwist d).LFunction β ≠ 0 ∧
          ((ψ.legendreTwist q).legendreTwist d).LFunction β ≠ 0) →
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ),
      χ.conductor ∣ 2 ^ k * (f * q * d) → χ.IsQuadratic →
      ∀ β ∈ Ioo (1 - min δ c) 1, χ.LFunction β ≠ 0 := by
  let B := 8 * f
  obtain ⟨r, hr, hbase⟩ := TauCeti.DirichletCharacter.exists_pos_real_zero_gap B
  let δ := min r (1 / 2)
  have hδ : δ ∈ Ioc (0 : ℝ) (1 / 2) := ⟨lt_min hr (by norm_num), min_le_right ..⟩
  refine ⟨δ, hδ, ?_⟩
  intro q d _ _ hfq hfqd c htwist N _ χ k hlevel hχ β hβ hz
  have hB : χ.conductor ∣ B * q * d :=
    (χ.conductor_dvd_lcm_eight_of_sq_eq_one hχ.sq_eq_one hlevel).trans
      (Nat.lcm_dvd ⟨f * q * d, by dsimp [B]; ring⟩ ⟨8, by dsimp [B]; ring⟩)
  have hβδ : β ∈ Ioo (1 - δ) 1 := ⟨by linarith [hβ.1, min_le_left δ c], hβ.2⟩
  have hpos : 0 < β := by linarith [hβδ.1, hδ.2]
  have hβc : β ∈ Ioo (max (1 - c) 0) 1 :=
    ⟨max_lt (by linarith [hβ.1, min_le_right δ c]) hpos, hβ.2⟩
  have hβ₀ : 0 < (β : ℂ).re := by simpa using hpos
  have hβ₁ : (β : ℂ) ≠ 1 := by exact_mod_cast hβ.2.ne
  have hlift {A D : ℕ} [NeZero A] [NeZero D] (ψ : DirichletCharacter ℂ A) (hAD : A ∣ D) :
      (ψ.changeLevel hAD).LFunction β = 0 ↔ ψ.LFunction β = 0 :=
    ψ.LFunction_changeLevel_eq_zero_iff hAD hβ₀.ne' (Or.inr hβ₁)
  have hz' := (hlift χ.primitiveCharacter hB).mpr
    ((χ.LFunction_primitiveCharacter_eq_zero_iff hβ₀ (Or.inr hβ₁)).mpr hz)
  obtain ⟨ψ, hψ, hcases⟩ := (χ.primitiveCharacter.changeLevel hB)
    |>.exists_eq_legendreTwists_of_isQuadratic
      ((MulChar.IsQuadratic.primitiveCharacter hχ).changeLevel hB) hfq hfqd
  obtain he | he | he | he := hcases <;> rw [he] at hz'
  · have hzψ := (hlift ψ _).mp hz'
    rcases eq_or_ne ψ 1 with rfl | hψ₁
    · have hζ := (hlift (1 : DirichletCharacter ℂ 1) (one_dvd B)).mp (by simpa using hzψ)
      rw [LFunction_modOne_eq] at hζ
      exact (TauCeti.riemannZeta_lt_zero hpos hβ.2).ne (by simp [hζ])
    · linarith [hbase B le_rfl ψ hψ₁ β hβ.2 hzψ, hβδ.1, min_le_left r (1 / 2)]
  · exact (htwist ψ hψ β hβc).1 ((hlift _ _).mp hz')
  · exact (htwist ψ hψ β hβc).2.1 ((hlift _ _).mp hz')
  · exact (htwist ψ hψ β hβc).2.2 hz'

end DirichletCharacter
