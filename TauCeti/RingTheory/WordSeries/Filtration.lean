/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WordSeries.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The degree filtration of word series

The `n`-th filtration ideal consists of series whose coefficients vanish on words of length
less than `n`. Multiplication adds filtration degrees, and the filtration is separated.
In particular, the `n`-th power of a series with zero constant coefficient vanishes in all
degrees below `n`. This is the finiteness property needed for formal substitution into such
series.
-/

public section

noncomputable section

namespace TauCeti.WordSeries

variable {ι R : Type*} [Semiring R]

/-- If the factors vanish below degrees `m` and `n`, their product vanishes below `m + n`. -/
theorem coeff_mul_eq_zero_of_length_lt {f g : WordSeries ι R} {m n : ℕ}
    (hf : ∀ w, w.toList.length < m → coeff w f = 0)
    (hg : ∀ w, w.toList.length < n → coeff w g = 0)
    {w : FreeMonoid ι} (hw : w.toList.length < m + n) : coeff w (f * g) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp := congrArg (fun v : FreeMonoid ι => v.toList.length)
    (Finset.mem_mulAntidiagonal.mp hp)
  simp only [FreeMonoid.toList_mul, List.length_append] at hp
  by_cases h : p.1.toList.length < m
  · simp [hf _ h]
  · have h' : p.2.toList.length < n := by omega
    simp [hg _ h']

/-- The ideal of series vanishing on all words of length less than `n`. -/
def filtration (n : ℕ) : Ideal (WordSeries ι R) where
  carrier := {f | ∀ w, w.toList.length < n → coeff w f = 0}
  zero_mem' := by simp
  add_mem' hf hg w hw := by simp [hf w hw, hg w hw]
  smul_mem' a f hf w hw := by
    exact coeff_mul_eq_zero_of_length_lt (m := 0) (n := n) (by simp) hf (by simpa using hw)

@[simp] theorem mem_filtration (f : WordSeries ι R) (n : ℕ) :
    f ∈ filtration n ↔ ∀ w, w.toList.length < n → coeff w f = 0 := Iff.rfl

/-- Multiplication adds filtration degrees. -/
theorem mul_mem_filtration {f g : WordSeries ι R} {m n : ℕ}
    (hf : f ∈ filtration m) (hg : g ∈ filtration n) : f * g ∈ filtration (m + n) :=
  fun _ hw => coeff_mul_eq_zero_of_length_lt hf hg hw

/-- The degree filtration is decreasing. -/
theorem filtration_antitone : Antitone (filtration (ι := ι) (R := R)) := by
  intro m n h f hf w hw
  exact hf w (hw.trans_le h)

@[simp] theorem filtration_zero : filtration (ι := ι) (R := R) 0 = ⊤ := by
  ext f
  simp

/-- The first filtration ideal is the augmentation ideal, the kernel of the constant
coefficient homomorphism. -/
theorem filtration_one : filtration (ι := ι) (R := R) 1 = RingHom.ker constantCoeff := by
  ext f
  simp only [mem_filtration, RingHom.mem_ker, constantCoeff_apply]
  constructor
  · intro hf
    exact hf 1 (by simp)
  · intro hf w hw
    have hw : w = 1 := by
      apply FreeMonoid.ext
      simpa using (List.length_eq_zero_iff.mp (by omega : w.toList.length = 0))
    simpa [hw] using hf

/-- A series lying in every filtration ideal is zero. -/
theorem eq_zero_of_mem_filtration {f : WordSeries ι R} (hf : ∀ n, f ∈ filtration n) : f = 0 := by
  ext w
  simpa using hf (w.toList.length + 1) w (Nat.lt_succ_self _)

/-- The degree filtration is separated. -/
@[simp] theorem iInf_filtration : (⨅ n, filtration (ι := ι) (R := R) n) = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  exact (Submodule.mem_bot _).2 (eq_zero_of_mem_filtration (by simpa using hf))

/-- Powers multiply filtration degrees. -/
theorem pow_mem_filtration {f : WordSeries ι R} {m : ℕ} (hf : f ∈ filtration m) (n : ℕ) :
    f ^ n ∈ filtration (n * m) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using mul_mem_filtration ih hf

/-- The `n`-th power of a series with zero constant coefficient has no terms below degree `n`.
This gives coefficientwise local finiteness for substitution by zero-constant series. -/
theorem coeff_pow_eq_zero_of_length_lt {f : WordSeries ι R} (hf : constantCoeff f = 0)
    {w : FreeMonoid ι} {n : ℕ} (hw : w.toList.length < n) : coeff w (f ^ n) = 0 := by
  have h : f ∈ filtration 1 := by rwa [filtration_one, RingHom.mem_ker]
  have hn := pow_mem_filtration h n
  exact hn w (by simpa using hw)

end TauCeti.WordSeries
