/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness for cofinal ideals and for powers of an ideal

For ideals `I` and `J` of a commutative ring `R` with `J ^ k ≤ I` for some `k`, every step
`I ^ m • ⊤` of the `I`-adic filtration of an `R`-module `M` contains a step of the `J`-adic one, so
an `I`-adically Hausdorff module is `J`-adically Hausdorff. If moreover `I ^ l ≤ J` for some `l`,
the two filtrations are cofinal in each other, and `I`-adic precompleteness and completeness
transfer to `J` as well: these properties depend only on the adic topology. The powers `J = I ^ n`
with `n ≠ 0` are the main instance of this, and precompleteness holds for `n = 0` too, since every
module is `⊤`-adically precomplete.

The main use is Hensel's lemma at `I ^ n`: an `I ^ n`-adically complete ring is Henselian at
`I ^ n` by Mathlib's `IsAdicComplete.henselianRing`, which lifts an approximate root modulo `I ^ n`
to a root congruent to it modulo `I ^ n`, and not merely modulo `I`.

## Main results

* `IsHausdorff.of_pow_le`, `IsHausdorff.of_le`: adic Hausdorffness for `I` implies the same for
  every `J` with `J ^ k ≤ I`, in particular for every `J ≤ I`.
* `IsPrecomplete.of_pow_le_of_pow_le`, `IsAdicComplete.of_pow_le_of_pow_le`: adic precompleteness
  and completeness for `I` imply the same for every `J` with `J ^ k ≤ I` and `I ^ l ≤ J`.
* `IsHausdorff.pow`, `IsAdicComplete.pow`: adic Hausdorffness and completeness for `I` imply the
  same for `I ^ n` when `n ≠ 0`.
* `IsPrecomplete.pow`: adic precompleteness for `I` implies precompleteness for every `I ^ n`.
-/

public section

variable {R : Type*} [CommRing R] {I J : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

/-- An `I`-adically Hausdorff module is `J`-adically Hausdorff for every `J` with `J ^ k ≤ I` for
some `k`. -/
theorem IsHausdorff.of_pow_le [IsHausdorff I M] {k : ℕ} (hJI : J ^ k ≤ I) : IsHausdorff J M where
  haus' x hx := IsHausdorff.haus' (I := I) x fun m ↦
    (hx (k * m)).mono (Submodule.smul_mono_left ((pow_mul J k m).le.trans
      (Ideal.pow_right_mono hJI m)))

/-- An `I`-adically Hausdorff module is `J`-adically Hausdorff for every `J ≤ I`. -/
theorem IsHausdorff.of_le [IsHausdorff I M] (h : J ≤ I) : IsHausdorff J M :=
  .of_pow_le (I := I) ((pow_one J).trans_le h)

/-- An `I`-adically precomplete module is `J`-adically precomplete for every `J` with `J ^ k ≤ I`
and `I ^ l ≤ J` for some `k` and `l`. -/
theorem IsPrecomplete.of_pow_le_of_pow_le [IsPrecomplete I M] {k l : ℕ} (hJI : J ^ k ≤ I)
    (hIJ : I ^ l ≤ J) : IsPrecomplete J M := by
  have pow_mul_le {A B : Ideal R} {a : ℕ} (h : A ^ a ≤ B) (m : ℕ) : A ^ ((a + 1) * m) ≤ B ^ m :=
    (pow_mul A (a + 1) m).le.trans
      (Ideal.pow_right_mono ((Ideal.pow_le_pow_right a.le_succ).trans h) m)
  refine ⟨fun f hf ↦ ?_⟩
  -- The subsequence `f ((k + 1) m)` is `I`-adically Cauchy, since `J ^ ((k + 1) m) ≤ I ^ m`. Its
  -- `I`-adic limit `L` is a `J`-adic limit of `f`: compare `f m` with `f ((k + 1) ((l + 1) m))`,
  -- which is congruent to `L` modulo `I ^ ((l + 1) m) ≤ J ^ m`.
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun m ↦ f ((k + 1) * m)) fun {m n} hmn ↦
    (hf (Nat.mul_le_mul_left _ hmn)).mono (Submodule.smul_mono_left (pow_mul_le hJI m))
  exact ⟨L, fun m ↦ (hf ((Nat.le_mul_of_pos_left m l.succ_pos).trans
    (Nat.le_mul_of_pos_left _ k.succ_pos))).trans
    ((hL ((l + 1) * m)).mono (Submodule.smul_mono_left (pow_mul_le hIJ m)))⟩

/-- An `I`-adically complete module is `J`-adically complete for every `J` with `J ^ k ≤ I` and
`I ^ l ≤ J` for some `k` and `l`. -/
theorem IsAdicComplete.of_pow_le_of_pow_le [IsAdicComplete I M] {k l : ℕ} (hJI : J ^ k ≤ I)
    (hIJ : I ^ l ≤ J) : IsAdicComplete J M where
  toIsHausdorff := .of_pow_le hJI
  toIsPrecomplete := .of_pow_le_of_pow_le hJI hIJ

/-- An `I`-adically Hausdorff module is `I ^ n`-adically Hausdorff for `n ≠ 0`. -/
theorem IsHausdorff.pow [IsHausdorff I M] {n : ℕ} (hn : n ≠ 0) : IsHausdorff (I ^ n) M :=
  .of_le (Ideal.pow_le_self hn)

/-- An `I`-adically precomplete module is `I ^ n`-adically precomplete for every `n`. -/
theorem IsPrecomplete.pow [IsPrecomplete I M] (n : ℕ) : IsPrecomplete (I ^ n) M := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top]
    exact IsPrecomplete.top M
  exact .of_pow_le_of_pow_le (I := I) ((pow_one _).trans_le (Ideal.pow_le_self hn)) le_rfl

/-- An `I`-adically complete module is `I ^ n`-adically complete for `n ≠ 0`. -/
theorem IsAdicComplete.pow [IsAdicComplete I M] {n : ℕ} (hn : n ≠ 0) :
    IsAdicComplete (I ^ n) M where
  toIsHausdorff := .pow hn
  toIsPrecomplete := .pow n
