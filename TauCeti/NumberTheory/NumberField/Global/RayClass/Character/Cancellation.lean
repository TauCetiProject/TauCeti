/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Sum
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.DegreeOne
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.PartialSums

/-!
# Cancellation for the ideal weight of a ray class character

The ideal partial sums of the unitary weight `χ.toUnitaryIdealWeight` of a ray class character
`χ` of `𝔪` are the character sums `rayClassCharacterPartialSum 𝔪 χ`: the weight vanishes on the
ideals that are not prime to `𝔪` and is `χ` of the ray class on the others. For a nontrivial
character those sums are `O(x ^ (1 - 1 / [K : ℚ]))`, which is the cancellation hypothesis
`TauCeti.HasCancellation` of the Arithmetic Dirichlet Series library. Through
`TauCeti.differentiableOn_continuedLFunctionOfWeight` it continues the L-series of a nontrivial
ray class character holomorphically to `Re s > 1 - 1 / [K : ℚ]`, a half-plane containing the
line `Re s = 1`.

Furthermore, `χ.toMultiplicativeIdealWeight` is periodic of period `Ideal.absNorm 𝔪.finitePart` on
the principal ideals `(k : 𝓞 K)` for `k ≥ 1`, because shifting `k` by `Ideal.absNorm 𝔪.finitePart`
preserves both coprimality to `𝔪.support` and positivity at every real place of `𝔪.infinitePart`.
Combining `hasCancellation_toUnitaryIdealWeight` with
`TauCeti.HasCancellation.normTwist_of_periodic_span_natCast` therefore gives cancellation for every
purely imaginary norm twist of a nontrivial ray class character in every degree `[K : ℚ] ≥ 1`,
while the trivial character and its imaginary norm twists never cancel.

## Main results

* `TauCeti.GlobalNumberFields.idealClass_span_eq_of_sub_mem`: two principal ideals `(a)` and `(b)`
  prime to `𝔪` whose generators satisfy `b - a ∈ 𝔪.finitePart` and are positive at every real place
  of `𝔪.infinitePart` have the same ray class modulo `𝔪`.
* `TauCeti.GlobalNumberFields.RayClassCharacter.idealSummatory_toUnitaryIdealWeight`: the ideal
  partial sums of the weight are the character sums.
* `TauCeti.GlobalNumberFields.RayClassCharacter.hasCancellation_toUnitaryIdealWeight_iff` and
  `TauCeti.GlobalNumberFields.RayClassCharacter.hasCancellation_normTwist_toUnitaryIdealWeight_iff`:
  the weight of `χ`, and any purely imaginary norm twist of it, has cancellation if and only if
  `χ ≠ 1`.

## Implementation notes

The reindexing proof of `idealSummatory_toUnitaryIdealWeight` is adapted from the private lemma
`idealSummatory_restrictAway_galoisCharacterUnitaryWeight` formerly in
`TauCeti/NumberTheory/Chebotarev/GaloisCharacter/Cyclotomic/Cancellation.lean`, which now derives
its cancellation from `hasCancellation_toUnitaryIdealWeight` instead.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

section SpanCongruence

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

private theorem isPrimeTo_span_of_sub_mem {a b : 𝓞 K} (hb0 : b ≠ 0)
    (hsub : b - a ∈ 𝔪.finitePart) (ha : (Ideal.span {a}).IsPrimeTo 𝔪.support) :
    (Ideal.span {b}).IsPrimeTo 𝔪.support := by
  refine Ideal.isPrimeTo_iff.mpr ⟨mt Ideal.span_singleton_eq_bot.mp hb0, fun 𝔭 h𝔭 hdvd ↦ ?_⟩
  have h𝔭m : 𝔪.finitePart ≤ 𝔭.asIdeal := Ideal.dvd_iff_le.mp ((𝔪.mem_support_iff 𝔭).mp h𝔭)
  have hb_mem : b ∈ 𝔭.asIdeal := Ideal.dvd_iff_le.mp hdvd (Ideal.mem_span_singleton_self b)
  have ha_mem : a ∈ 𝔭.asIdeal := by
    simpa only [sub_sub_cancel] using 𝔭.asIdeal.sub_mem hb_mem (h𝔭m hsub)
  exact (Ideal.isPrimeTo_iff.mp ha).2 𝔭 h𝔭 (Ideal.dvd_span_singleton.mpr ha_mem)

/-- For nonzero `a b : 𝓞 K` congruent modulo `𝔪.finitePart`, `(b)` is prime to `𝔪.support` if and
only if `(a)` is. -/
theorem isPrimeTo_span_iff_of_sub_mem {a b : 𝓞 K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hsub : b - a ∈ 𝔪.finitePart) :
    (Ideal.span {b}).IsPrimeTo 𝔪.support ↔ (Ideal.span {a}).IsPrimeTo 𝔪.support :=
  ⟨isPrimeTo_span_of_sub_mem ha0 (by simpa only [neg_sub] using 𝔪.finitePart.neg_mem hsub),
    isPrimeTo_span_of_sub_mem hb0 hsub⟩

/-- **Congruent positive generators define the same ray class.** If `(a)` and `(b)` are prime to
`𝔪`, satisfy `b - a ∈ 𝔪.finitePart`, and are positive at every real place of `𝔪.infinitePart`, then
they represent the same class in `RayClassGroup 𝔪`. -/
theorem idealClass_span_eq_of_sub_mem {a b : 𝓞 K}
    (ha : Ideal.span {a} ∈ integralIdealsPrimeTo 𝔪)
    (hb : Ideal.span {b} ∈ integralIdealsPrimeTo 𝔪) (hsub : b - a ∈ 𝔪.finitePart)
    (ha_pos : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (a : K))
    (hb_pos : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (b : K)) :
    idealClass 𝔪 ⟨Ideal.span {b}, hb⟩ = idealClass 𝔪 ⟨Ideal.span {a}, ha⟩ := by
  let Ia : integralIdealsPrimeTo 𝔪 := ⟨Ideal.span {a}, ha⟩
  let Ib : integralIdealsPrimeTo 𝔪 := ⟨Ideal.span {b}, hb⟩
  obtain ⟨J, c, x, hxc, hx, hspan⟩ := exists_isCongrOne_span_eq_mul Ia
  obtain ⟨d, rfl⟩ : a ∣ c :=
    Ideal.span_singleton_le_span_singleton.mp (Ideal.dvd_iff_le.mp ⟨J, hspan⟩)
  have ha_bot : Ideal.span {a} ≠ ⊥ := (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp ha).1
  have hJspan : Ideal.span {d} = (J : Ideal (𝓞 K)) := mul_left_cancel₀ ha_bot
    (by rw [Ideal.span_singleton_mul_span_singleton, hspan])
  have hbd1 : b * d - 1 ∈ 𝔪.finitePart := by
    have heq : b * d - 1 = (b - a) * d + (a * d - 1) := by ring
    rw [heq]
    exact 𝔪.finitePart.add_mem (𝔪.finitePart.mul_mem_right d hsub)
      (sub_one_mem_of_isCongrOne hxc hx)
  have hb0 : (b : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr fun h ↦
    (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp hb).1 (by simp [h])
  have hd0 : (d : K) ≠ 0 := fun h ↦ x.ne_zero (by rw [hxc]; push_cast; simp [h])
  have hbd0 : ((b * d : 𝓞 K) : K) ≠ 0 := by push_cast; exact mul_ne_zero hb0 hd0
  have hy : IsCongrOne 𝔪 (Units.mk0 ((b * d : 𝓞 K) : K) hbd0) := by
    refine isCongrOne_of_sub_one_mem rfl hbd1 fun w hw ↦ ?_
    have hpos_ad : 0 < InfinitePlace.embedding_of_isReal w.2 (a : K) *
        InfinitePlace.embedding_of_isReal w.2 (d : K) := by
      simpa [hxc] using (isCongrOne_iff_mem_congruenceSubgroup_and_pos.mp hx).2 w hw
    have hd_pos : 0 < InfinitePlace.embedding_of_isReal w.2 (d : K) :=
      pos_of_mul_pos_right hpos_ad (ha_pos w hw).le
    simpa using mul_pos (hb_pos w hw) hd_pos
  have hspan_bd : Ideal.span {b * d} = (Ib : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)) := by
    rw [← Ideal.span_singleton_mul_span_singleton, hJspan]
  exact mul_right_cancel ((idealClass_mul_eq_one_of_span_eq_mul rfl hy hspan_bd).trans
    (idealClass_mul_eq_one_of_span_eq_mul hxc hx hspan).symm)

end SpanCongruence

namespace RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **The ideal partial sums of a ray class weight are the character sums.** Summing the unitary
weight of `χ` over the nonzero ideals of norm at most `x` gives the sum of `χ` over the integral
ideals prime to `𝔪` of norm at most `x`, since the weight vanishes on the other ideals. -/
theorem idealSummatory_toUnitaryIdealWeight (χ : RayClassCharacter 𝔪) (x : ℝ) :
    idealSummatory K χ.toUnitaryIdealWeight.toIdealArithmeticFunction x =
      rayClassCharacterPartialSum 𝔪 χ x := by
  classical
  have hmem (J : Ideal (𝓞 K)) : J ∈ integralIdealsPrimeTo 𝔪 ↔ J.IsPrimeTo 𝔪.support :=
    NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo
  let e : integralIdealsPrimeTo 𝔪 → (Ideal (𝓞 K))⁰ := fun I ↦
    ⟨I, mem_nonZeroDivisors_of_ne_zero ((hmem I).mp I.2).ne_bot⟩
  have hsum : rayClassCharacterPartialSum 𝔪 χ x =
      ∑ I ∈ normLE (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x,
        (χ.onIdeals I : ℂ) := by
    rw [rayClassCharacterPartialSum_def, ← finsum_mem_coe_finset, coe_normLE]
    exact finsum_set_coe_eq_finsum_mem (f := fun I ↦ (χ.onIdeals I : ℂ))
      {I : integralIdealsPrimeTo 𝔪 | Ideal.absNorm (I : Ideal (𝓞 K)) ≤ x}
  -- The ideals prime to `𝔪` embed into the nonzero ideals; off the image the weight is `0`.
  rw [hsum, idealSummatory_apply]
  refine (Finset.sum_of_injOn e (fun I _ J _ h ↦ Subtype.ext (by simpa [e] using h))
    (fun I hI ↦ by simpa [e] using hI) (fun J hJ hJe ↦ ?_) (fun I _ ↦ ?_)).symm
  · have hJ𝔪 : ¬ (J : Ideal (𝓞 K)).IsPrimeTo 𝔪.support :=
      fun hJ𝔪 ↦ hJe ⟨⟨J, (hmem J).mpr hJ𝔪⟩, by simpa using hJ, rfl⟩
    simp [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hJ𝔪]
  · simp [e, toMultiplicativeIdealWeight_apply_of_isPrimeTo χ ((hmem I).mp I.2)]

/-- The extended weight of `χ` takes the same value on principal ideals `(a)` and `(b)` whenever
`a ≠ 0`, `b ≠ 0`, `b - a ∈ 𝔪.finitePart`, and `a`, `b` are positive at every real place of
`𝔪.infinitePart`. -/
theorem toMultiplicativeIdealWeight_span_eq_of_sub_mem (χ : RayClassCharacter 𝔪) {a b : 𝓞 K}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hsub : b - a ∈ 𝔪.finitePart)
    (ha_pos : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (a : K))
    (hb_pos : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (b : K)) :
    χ.toMultiplicativeIdealWeight (Ideal.span {b}) =
      χ.toMultiplicativeIdealWeight (Ideal.span {a}) := by
  by_cases ha : (Ideal.span {a}).IsPrimeTo 𝔪.support
  · have hb : (Ideal.span {b}).IsPrimeTo 𝔪.support :=
      (isPrimeTo_span_iff_of_sub_mem ha0 hb0 hsub).mpr ha
    rw [toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hb,
      toMultiplicativeIdealWeight_apply_of_isPrimeTo χ ha, onIdeals_apply, onIdeals_apply,
      idealClass_span_eq_of_sub_mem _ _ hsub ha_pos hb_pos]
  · have hb : ¬ (Ideal.span {b}).IsPrimeTo 𝔪.support :=
      mt (isPrimeTo_span_iff_of_sub_mem ha0 hb0 hsub).mp ha
    rw [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hb,
      toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ ha]

/-- **Periodicity of a ray class weight on positive natural integers.** For `k ≥ 1`, shifting `k`
by `Ideal.absNorm 𝔪.finitePart` leaves `χ.toMultiplicativeIdealWeight (Ideal.span {(k : 𝓞 K)})`
unchanged. -/
theorem toMultiplicativeIdealWeight_span_natCast_add_absNorm (χ : RayClassCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) :
    χ.toMultiplicativeIdealWeight (Ideal.span {((k + Ideal.absNorm 𝔪.finitePart : ℕ) : 𝓞 K)}) =
      χ.toMultiplicativeIdealWeight (Ideal.span {(k : 𝓞 K)}) := by
  refine χ.toMultiplicativeIdealWeight_span_eq_of_sub_mem (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega)) ?_ (fun w _ ↦ ?_) (fun w _ ↦ ?_)
  · push_cast
    rw [add_sub_cancel_left]
    exact Ideal.absNorm_mem 𝔪.finitePart
  · simpa using (by exact_mod_cast hk : (0 : ℝ) < k)
  · simpa using (by exact_mod_cast (by omega : 0 < k + Ideal.absNorm 𝔪.finitePart) :
      (0 : ℝ) < (k + Ideal.absNorm 𝔪.finitePart : ℕ))

/-- **Cancellation for a nontrivial ray class character.** The unitary weight of a nontrivial
ray class character has ideal partial sums `O(x ^ (1 - 1 / [K : ℚ]))`. -/
theorem hasCancellation_toUnitaryIdealWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) :
    HasCancellation χ.toUnitaryIdealWeight := by
  simpa [hasCancellation_iff_isBigO, idealSummatory_toUnitaryIdealWeight] using
    isBigO_rayClassCharacterPartialSum 𝔪 χ hχ

/-- **Imaginary norm twists of a nontrivial ray class character have cancellation** in every
number-field degree `[K : ℚ] ≥ 1`. -/
theorem hasCancellation_normTwist_toUnitaryIdealWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    (z : ℂ) (hz : z.re = 0) :
    HasCancellation (UnitaryIdealWeight.normTwist z hz χ.toUnitaryIdealWeight) :=
  (hasCancellation_toUnitaryIdealWeight hχ).normTwist_of_periodic_span_natCast
    (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot)
    (fun _ hk ↦ by simpa using χ.toMultiplicativeIdealWeight_span_natCast_add_absNorm hk) z hz

/-- The unitary weight of the trivial ray class character never has cancellation. -/
theorem not_hasCancellation_one_toUnitaryIdealWeight :
    ¬ HasCancellation (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight :=
  not_hasCancellation_of_isTrivialOnGood (by
    rw [val_toUnitaryIdealWeight, toMultiplicativeIdealWeight_one]
    exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes 𝔪.support.finite_toSet)

/-- No purely imaginary norm twist of the trivial ray class character has cancellation. -/
theorem not_hasCancellation_normTwist_one_toUnitaryIdealWeight (z : ℂ) (hz : z.re = 0) :
    ¬ HasCancellation
      (UnitaryIdealWeight.normTwist z hz (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight) := by
  set u : ℝ := -z.im
  have hz_eq : -((u : ℂ) * Complex.I) = z := by
    apply Complex.ext <;> simp [u, hz]
  have htwist : (UnitaryIdealWeight.normTwist z hz
      (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight).1.IsNormTwistOnGood u := by
    rw [UnitaryIdealWeight.val_normTwist, val_toUnitaryIdealWeight,
      toMultiplicativeIdealWeight_one, ← hz_eq]
    exact MultiplicativeIdealWeight.isNormTwistOnGood_normTwist_ofBadPrimes
      𝔪.support.finite_toSet u
  exact not_hasCancellation_of_isNormTwistOnGood htwist

/-- The unitary weight of `χ` has cancellation if and only if `χ ≠ 1`. -/
@[simp]
theorem hasCancellation_toUnitaryIdealWeight_iff {χ : RayClassCharacter 𝔪} :
    HasCancellation χ.toUnitaryIdealWeight ↔ χ ≠ 1 :=
  ⟨fun h ↦ by rintro rfl; exact not_hasCancellation_one_toUnitaryIdealWeight h,
    hasCancellation_toUnitaryIdealWeight⟩

/-- Any purely imaginary norm twist of `χ.toUnitaryIdealWeight` has cancellation if and only if
`χ ≠ 1`. -/
@[simp]
theorem hasCancellation_normTwist_toUnitaryIdealWeight_iff {χ : RayClassCharacter 𝔪} (z : ℂ)
    (hz : z.re = 0) :
    HasCancellation (UnitaryIdealWeight.normTwist z hz χ.toUnitaryIdealWeight) ↔ χ ≠ 1 :=
  ⟨fun h ↦ by rintro rfl; exact not_hasCancellation_normTwist_one_toUnitaryIdealWeight z hz h,
    fun hχ ↦ hasCancellation_normTwist_toUnitaryIdealWeight hχ z hz⟩

/-- A nontrivial ray class character's weight is never a pure imaginary norm twist on its good
ideals. -/
theorem not_isNormTwistOnGood_toUnitaryIdealWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    (u : ℝ) : ¬ χ.toUnitaryIdealWeight.1.IsNormTwistOnGood u :=
  fun hu ↦ not_hasCancellation_of_isNormTwistOnGood hu (hasCancellation_toUnitaryIdealWeight hχ)

/-- Twisting a nontrivial ray class character's weight by `N(I) ^ (-z)` (`Re z = 0`) translates its
continued L-function by `z` across `Re s = 1`, in every degree `[K : ℚ] ≥ 1`. -/
theorem continuedLFunctionOfWeight_normTwist_toUnitaryIdealWeight {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) {z : ℂ} (hz : z.re = 0) {s : ℂ}
    (hs : 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re) :
    continuedLFunctionOfWeight (UnitaryIdealWeight.normTwist z hz χ.toUnitaryIdealWeight) s =
      continuedLFunctionOfWeight χ.toUnitaryIdealWeight (s + z) :=
  continuedLFunctionOfWeight_normTwist hz (hasCancellation_toUnitaryIdealWeight hχ)
    (hasCancellation_normTwist_toUnitaryIdealWeight hχ z hz) hs

end RayClassCharacter

end TauCeti.GlobalNumberFields
