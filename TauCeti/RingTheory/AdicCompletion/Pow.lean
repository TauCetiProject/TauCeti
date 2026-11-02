/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness for cofinal ideals and for powers of an ideal

For ideals `J ≤ I` of a commutative ring `R`, the `J`-adic filtration `J ^ m • ⊤` of an `R`-module
`M` is finer than the `I`-adic one, so an `I`-adically Hausdorff module is `J`-adically Hausdorff.
If moreover `I ^ k ≤ J` for some `k`, the two filtrations are cofinal in each other, and `I`-adic
precompleteness and completeness transfer to `J` as well. The powers `J = I ^ n` with `n ≠ 0` are
the main instance of this, and precompleteness holds for `n = 0` too, since every module is
`⊤`-adically precomplete.

The main use is Hensel's lemma at `I ^ n`: an `I ^ n`-adically complete ring is Henselian at
`I ^ n` by Mathlib's `IsAdicComplete.henselianRing`, which lifts an approximate root modulo `I ^ n`
to a root congruent to it modulo `I ^ n`, and not merely modulo `I`.

## Main results

* `IsHausdorff.of_le`: adic Hausdorffness for `I` implies the same for every `J ≤ I`.
* `IsPrecomplete.of_le_of_pow_le`, `IsAdicComplete.of_le_of_pow_le`: adic precompleteness and
  completeness for `I` imply the same for every `J` with `I ^ k ≤ J ≤ I`.
* `IsHausdorff.pow`, `IsAdicComplete.pow`: adic Hausdorffness and completeness for `I` imply the
  same for `I ^ n` when `n ≠ 0`.
* `IsPrecomplete.pow`: adic precompleteness for `I` implies precompleteness for every `I ^ n`.
* `IsHausdorff.of_pow`, `IsPrecomplete.of_pow`, `IsAdicComplete.of_pow`: the converses, for
  `n ≠ 0` in the last two.
-/

public section

variable {R : Type*} [CommRing R] {I J : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

/-- An `I`-adically Hausdorff module is `J`-adically Hausdorff for every `J ≤ I`. -/
theorem IsHausdorff.of_le [IsHausdorff I M] (h : J ≤ I) : IsHausdorff J M where
  haus' x hx := IsHausdorff.haus' x fun m ↦
    (hx m).mono (Submodule.smul_mono_left (Ideal.pow_right_mono h m))

/-- An `I`-adically precomplete module is `J`-adically precomplete for every `J` with
`I ^ k ≤ J ≤ I` for some `k`. -/
theorem IsPrecomplete.of_le_of_pow_le [IsPrecomplete I M] (hJI : J ≤ I) {k : ℕ}
    (hIJ : I ^ k ≤ J) : IsPrecomplete J M := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [pow_zero, Ideal.one_eq_top, top_le_iff] at hIJ
    rw [hIJ]
    exact IsPrecomplete.top M
  refine ⟨fun f hf ↦ ?_⟩
  -- A sequence that is Cauchy for the `J`-adic filtration is Cauchy for the `I`-adic one, so it
  -- has an `I`-adic limit `L`; the subsequence `f (k m)` shows that `L` is also the `J`-adic
  -- limit, since `I ^ (k m) ≤ J ^ m`.
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' f fun {m k} hmk ↦
    (hf hmk).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI m))
  refine ⟨L, fun m ↦ (hf (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hk))).trans ?_⟩
  exact (hL (k * m)).mono (Submodule.smul_mono_left ((pow_mul I k m).le.trans
    (Ideal.pow_right_mono hIJ m)))

/-- An `I`-adically complete module is `J`-adically complete for every `J` with `I ^ k ≤ J ≤ I`
for some `k`. -/
theorem IsAdicComplete.of_le_of_pow_le [IsAdicComplete I M] (hJI : J ≤ I) {k : ℕ}
    (hIJ : I ^ k ≤ J) : IsAdicComplete J M where
  toIsHausdorff := IsHausdorff.of_le hJI
  toIsPrecomplete := IsPrecomplete.of_le_of_pow_le hJI hIJ

/-- An `I`-adically Hausdorff module is `I ^ n`-adically Hausdorff for `n ≠ 0`. -/
theorem IsHausdorff.pow [IsHausdorff I M] {n : ℕ} (hn : n ≠ 0) : IsHausdorff (I ^ n) M :=
  .of_le (Ideal.pow_le_self hn)

/-- An `I`-adically precomplete module is `I ^ n`-adically precomplete for every `n`. -/
theorem IsPrecomplete.pow [IsPrecomplete I M] (n : ℕ) : IsPrecomplete (I ^ n) M := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top]
    exact IsPrecomplete.top M
  exact .of_le_of_pow_le (Ideal.pow_le_self hn) le_rfl

/-- An `I`-adically complete module is `I ^ n`-adically complete for `n ≠ 0`. -/
theorem IsAdicComplete.pow [IsAdicComplete I M] {n : ℕ} (hn : n ≠ 0) :
    IsAdicComplete (I ^ n) M :=
  .of_le_of_pow_le (Ideal.pow_le_self hn) le_rfl

/-- An `I ^ n`-adically Hausdorff module is `I`-adically Hausdorff. -/
theorem IsHausdorff.of_pow {n : ℕ} [IsHausdorff (I ^ n) M] : IsHausdorff I M where
  haus' x hx := IsHausdorff.haus' (I := I ^ n) x fun m ↦ by
    rw [← pow_mul]
    exact hx (n * m)

/-- An `I ^ n`-adically precomplete module is `I`-adically precomplete for `n ≠ 0`. -/
theorem IsPrecomplete.of_pow {n : ℕ} (hn : n ≠ 0) [IsPrecomplete (I ^ n) M] :
    IsPrecomplete I M := by
  refine ⟨fun f hf ↦ ?_⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I ^ n) (fun m ↦ f (n * m)) fun {m k} hmk ↦ by
    rw [← pow_mul]
    exact hf (Nat.mul_le_mul_left n hmk)
  refine ⟨L, fun m ↦ (hf (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn))).trans ?_⟩
  have hm := hL m
  rw [← pow_mul] at hm
  exact hm.mono (Submodule.smul_mono_left
    (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn))))

/-- An `I ^ n`-adically complete module is `I`-adically complete for `n ≠ 0`. -/
theorem IsAdicComplete.of_pow {n : ℕ} (hn : n ≠ 0) [IsAdicComplete (I ^ n) M] :
    IsAdicComplete I M where
  toIsHausdorff := .of_pow (n := n)
  toIsPrecomplete := .of_pow hn
