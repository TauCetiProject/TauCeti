/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.RingOfIntegers.BoundedConjugates
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Elements of a number field with bounded conjugates and finite part in a compact set

Let `K` be a number field of degree `d = [K : ℚ]` and `s` a compact set of finite adeles of `K`.
There is `c > 0` such that for every `r`, the elements of `K` whose finite part lies in `s` and
whose absolute values at the infinite places are at most `r` number at most `(⌊c r⌋₊ + 1) ^ d`.

The set `s` has a common denominator `b ∈ 𝓞 K`, so every such element is `a / b` for an algebraic
integer `a` with absolute values at most `r * max_w |b|_w`, and such integers are counted by
`NumberField.RingOfIntegers.ncard_le_floor_add_one_pow`.

## Main results

* `TauCeti.GlobalNumberFields.exists_encard_le_floor_mul_add_one_pow`: the count
  `(⌊c r⌋₊ + 1) ^ d`.

## References

* This is the one-coordinate step of the dyadic count
  `TauCeti.GlobalNumberFields.exists_encard_setOf_twoInf_zpow_mul_mem_le`, whose source is
  credited in `TauCeti.NumberTheory.NumberField.Global.Adeles.DyadicCount`; the proof here is
  written independently.
-/

public section

open IsDedekindDomain Module NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **Elements of a number field with bounded conjugates and finite part in a compact set.** For a
compact set `s` of finite adeles of `K` there is `c > 0` such that for every `r`, the elements of
`K` whose finite part lies in `s` and whose absolute value is at most `r` at every infinite place
number at most `(⌊c r⌋₊ + 1) ^ [K : ℚ]`. -/
theorem exists_encard_le_floor_mul_add_one_pow {s : Set 𝔸ᶠ[K]} (hs : IsCompact s) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ,
      {x : K | (∀ w : InfinitePlace K, w x ≤ r) ∧ algebraMap K 𝔸ᶠ[K] x ∈ s}.encard ≤
        ((⌊c * r⌋₊ + 1) ^ finrank ℚ K : ℕ) := by
  obtain ⟨b, hb0, hb⟩ :=
    FiniteAdeleRing.mul_nonZeroDivisor_mem_integralAdeles_of_isCompact (R := 𝓞 K) hs
  have hbK : (b : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero hb0)
  -- `M` bounds the absolute values of the common denominator `b` at every infinite place
  set M : ℝ := 1 + ∑ w : InfinitePlace K, w (b : K)
  have hM (w : InfinitePlace K) : w (b : K) ≤ M := by
    have := Finset.single_le_sum (fun w _ ↦ apply_nonneg w (b : K)) (Finset.mem_univ w)
    linarith
  have hM0 : 0 < M := by
    have := Finset.sum_nonneg fun (w : InfinitePlace K) (_ : w ∈ Finset.univ) ↦
      apply_nonneg w (b : K)
    linarith
  refine ⟨2 * M, mul_pos two_pos hM0, fun r ↦ ?_⟩
  rcases lt_or_ge r 0 with hr | hr
  · -- no element of `K` has a negative absolute value
    have hempty : {x : K | (∀ w : InfinitePlace K, w x ≤ r) ∧ algebraMap K 𝔸ᶠ[K] x ∈ s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx ↦
        (hr.trans_le (apply_nonneg (Classical.arbitrary (InfinitePlace K)) x)).not_ge (hx.1 _)
    simp [hempty]
  -- every such element is `a / b` with `a ∈ 𝓞 K` of absolute values at most `M * r`
  set T : Set (Unit → 𝓞 K) := {v | ∀ i (w : InfinitePlace K), w (v i : K) ≤ M * r}
  have hsub : {x : K | (∀ w : InfinitePlace K, w x ≤ r) ∧ algebraMap K 𝔸ᶠ[K] x ∈ s} ⊆
      (fun v : Unit → 𝓞 K ↦ (v () : K) / b) '' T := by
    rintro x ⟨hxw, hxs⟩
    have hint : algebraMap K 𝔸ᶠ[K] (x * algebraMap (𝓞 K) K b) ∈
        FiniteAdeleRing.integralAdeles (𝓞 K) K := by
      rw [map_mul, ← IsScalarTower.algebraMap_apply]
      exact hb _ hxs
    obtain ⟨a, ha⟩ := (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff _).mp hint
    refine ⟨fun _ ↦ a, fun _ w ↦ ?_, ?_⟩
    · calc w (a : K) = w x * w (b : K) := by rw [← map_mul, ← ha]
        _ ≤ r * M := mul_le_mul (hxw w) (hM w) (apply_nonneg _ _) hr
        _ = M * r := mul_comm _ _
    · dsimp only
      rw [div_eq_iff hbK, ← ha]
  have hT : T.Finite := RingOfIntegers.finite_of_forall_infinitePlace_le fun _ hv ↦ hv
  calc _ ≤ ((fun v : Unit → 𝓞 K ↦ (v () : K) / b) '' T).encard := Set.encard_le_encard hsub
    _ ≤ T.encard := Set.encard_image_le _ _
    _ = T.ncard := hT.cast_ncard_eq.symm
    _ ≤ ((⌊2 * M * r⌋₊ + 1) ^ finrank ℚ K : ℕ) := by
      have := RingOfIntegers.ncard_le_floor_add_one_pow (S := T) fun _ hv ↦ hv
      rw [Nat.card_unique, one_mul, ← mul_assoc] at this
      exact_mod_cast this

end TauCeti.GlobalNumberFields
