/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.NumberTheory.NumberField.RingOfIntegers.BoundedConjugates
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Counting rational points in dyadic dilates of a compact set of adeles

Let `K` be a number field of degree `d = [K : ℚ]`, and let `2_∞` be the idele equal to `2` at the
infinite places and to `1` at the finite places (`TauCeti.GlobalNumberFields.twoInf`). For a
compact set `B ⊆ 𝔸_K ^ n` there is a constant `C` such that for every `x ∈ ℤ ^ n` the number of
`ξ ∈ K ^ n` with `(2_∞ ^ (-x i) * ξ i)_i ∈ B` is at most `C * 2 ^ (d * ∑ i, max (x i) 0)`. If `K`
has `f` infinite places then `d ≤ 2 f`, with equality when `K` is totally complex, so the count is
also at most `C * 4 ^ (f * ∑ i, max (x i) 0)`.

The proof goes through the one-coordinate count of
`TauCeti.GlobalNumberFields.exists_encard_le_floor_mul_add_one_pow`: a compact set `s` of finite
adeles has a common denominator `b ∈ 𝓞 K`, so every `ξ ∈ K` with finite part in `s` and absolute
values at most `r` at the infinite places is `a / b` for an algebraic integer `a` with absolute
values at most `r * max_w |b|_w`, and such integers are counted by
`NumberField.RingOfIntegers.ncard_le_floor_add_one_pow`. For the dyadic dilates, the infinite part
of `B` is bounded, so the `i`-th coordinate of a point has absolute values at most `R * 2 ^ x i`.

Counts of this shape bound the number of rational vectors in the translates of a fixed compact set
of adelic vectors by diagonal dyadic matrices, an input to the reduction theory of adelic groups.

## Main results

* `TauCeti.GlobalNumberFields.twoInf`: the idele `2_∞`, with `coe_twoInf`, `coe_twoInf_zpow` and
  `norm_fst_twoInf_zpow_mul_algebraMap_apply`.
* `TauCeti.GlobalNumberFields.exists_encard_le_floor_mul_add_one_pow`: elements of `K` with finite
  part in a compact set and absolute values at most `r` number at most `(⌊c r⌋ + 1) ^ d`.
* `TauCeti.GlobalNumberFields.exists_encard_setOf_twoInf_zpow_mul_mem_le`: the dyadic count
  `C * 2 ^ (d * ∑ i, max (x i) 0)`.
* `TauCeti.GlobalNumberFields.exists_encard_setOf_twoInf_zpow_mul_mem_le_four_pow`: the bound
  `C * 4 ^ (f * ∑ i, max (x i) 0)`, `f` the number of infinite places; for totally complex `K` it
  is the previous bound.

## References

* The statement is the third clause of the adelic Minkowski theorems in the formal proof of the
  folder `grh` of https://github.com/lsernau/grh-lean (Apache 2.0, Copyright 2026 Anthropic, PBC),
  `src/Lib/Adelic/Reduction/MinkowskiTheorems.lean` (`New.Core.encard_le_of_dyadic_box`); the
  proof here is written independently, through common denominators and the count of algebraic
  integers with bounded conjugates.
-/

public section

open IsDedekindDomain Module NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- The idele `2_∞` of a number field `K`: it is `2` at every infinite place and `1` at every
finite place. -/
noncomputable def twoInf : 𝔸[K]ˣ :=
  Units.map ((MonoidHom.inl _ _).comp (algebraMap K (InfiniteAdeleRing K)).toMonoidHom)
    (Units.mk0 (2 : K) two_ne_zero)

variable {K}

/-- The integral powers of `2_∞` are `2 ^ k` at the infinite places and `1` at the finite
places. -/
@[simp]
theorem coe_twoInf_zpow (k : ℤ) :
    ((twoInf K ^ k : 𝔸[K]ˣ) : 𝔸[K]) = (algebraMap K (InfiniteAdeleRing K) (2 ^ k), 1) := by
  rw [twoInf, ← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0,
    MonoidHom.comp_apply, MonoidHom.inl_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

/-- The idele `2_∞` is `2` at the infinite places and `1` at the finite places. -/
@[simp]
theorem coe_twoInf : ((twoInf K : 𝔸[K]ˣ) : 𝔸[K]) = (2, 1) := by
  rw [← zpow_one (twoInf K), coe_twoInf_zpow, zpow_one, map_ofNat]

/-- The inverses of the integral powers of `2_∞`, in the form `simp` reaches through
`zpow_neg`. -/
@[simp]
theorem coe_inv_twoInf_zpow (k : ℤ) :
    (((twoInf K ^ k)⁻¹ : 𝔸[K]ˣ) : 𝔸[K]) = (algebraMap K (InfiniteAdeleRing K) (2 ^ k)⁻¹, 1) := by
  rw [← zpow_neg, coe_twoInf_zpow, zpow_neg]

/-- Multiplying by a power of `2_∞` does not change the finite part of a diagonal adele. -/
theorem snd_twoInf_zpow_mul_algebraMap (k : ℤ) (x : K) :
    (((twoInf K ^ k : 𝔸[K]ˣ) : 𝔸[K]) * algebraMap K 𝔸[K] x).2 = algebraMap K 𝔸ᶠ[K] x := by
  rw [coe_twoInf_zpow, Prod.snd_mul, one_mul, AdeleRing.algebraMap_snd_def]

/-- Multiplying a diagonal adele by `2_∞ ^ k` multiplies its absolute value at every infinite
place by `2 ^ k`. -/
theorem norm_fst_twoInf_zpow_mul_algebraMap_apply (k : ℤ) (x : K) (w : InfinitePlace K) :
    ‖(((twoInf K ^ k : 𝔸[K]ˣ) : 𝔸[K]) * algebraMap K 𝔸[K] x).1 w‖ = 2 ^ k * w x := by
  rw [coe_twoInf_zpow, Prod.fst_mul, AdeleRing.algebraMap_fst_def, ← map_mul]
  -- the absolute value at `w` of the diagonal infinite adele of `z ∈ K` is `w z`
  have hnorm (z : K) : ‖algebraMap K (InfiniteAdeleRing K) z w‖ = w z := by
    simp [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe,
      InfinitePlace.coe_apply]
  have h2 : w 2 = 2 := by exact_mod_cast w.map_natCast 2
  rw [hnorm, map_mul, map_zpow₀, h2]

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

/-- A compact set of vectors of adeles has bounded absolute values at the infinite places. -/
private theorem exists_forall_norm_fst_apply_le {ι : Type*} [Finite ι] {B : Set (ι → 𝔸[K])}
    (hB : IsCompact B) :
    ∃ R : ℝ, ∀ b ∈ B, ∀ i (w : InfinitePlace K), ‖(b i).1 w‖ ≤ R := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR⟩ := (hB.image (f := fun b : ι → 𝔸[K] ↦ ∑ i, ∑ w, ‖(b i).1 w‖)
    (by fun_prop)).bddAbove
  refine ⟨R, fun b hb i w ↦ ?_⟩
  calc ‖(b i).1 w‖ ≤ ∑ w, ‖(b i).1 w‖ :=
        Finset.single_le_sum (fun w _ ↦ norm_nonneg _) (Finset.mem_univ w)
    _ ≤ ∑ i, ∑ w, ‖(b i).1 w‖ :=
        Finset.single_le_sum (f := fun i ↦ ∑ w, ‖(b i).1 w‖)
          (fun i _ ↦ Finset.sum_nonneg fun w _ ↦ norm_nonneg _) (Finset.mem_univ i)
    _ ≤ R := hR ⟨b, hb, rfl⟩

/-- **Rational points in dyadic dilates of a compact set of adeles.** Let `K` be a number field
and `B` a compact set of vectors of adeles of `K`. There is a constant `C` such that for every
`x ∈ ℤ ^ ι` the number of `ξ ∈ K ^ ι` with `(2_∞ ^ (-x i) * ξ i)_i ∈ B` is at most
`C * 2 ^ ([K : ℚ] * ∑ i, max (x i) 0)`. -/
theorem exists_encard_setOf_twoInf_zpow_mul_mem_le {ι : Type*} [Fintype ι]
    {B : Set (ι → 𝔸[K])} (hB : IsCompact B) :
    ∃ C : ℕ, ∀ x : ι → ℤ,
      {ξ : ι → K | (fun i ↦ ((twoInf K ^ (-x i) : 𝔸[K]ˣ) : 𝔸[K]) * algebraMap K 𝔸[K] (ξ i)) ∈
        B}.encard ≤ (C * 2 ^ (finrank ℚ K * ∑ i, (x i).toNat) : ℕ) := by
  -- the finite parts of the coordinates of `B` form compact sets
  choose c _ hc using fun i ↦
    exists_encard_le_floor_mul_add_one_pow (hB.image (f := fun b : ι → 𝔸[K] ↦ (b i).2)
      (by fun_prop))
  -- the infinite parts of the coordinates of `B` are bounded by some `R`
  obtain ⟨R, hR⟩ := exists_forall_norm_fst_apply_le hB
  refine ⟨∏ i, (⌊c i * R⌋₊ + 1) ^ finrank ℚ K, fun x ↦ ?_⟩
  -- the `i`-th coordinate of a point has finite part in the `i`-th projection of `B` and
  -- absolute values at most `R * 2 ^ x i`
  have hsub : {ξ : ι → K | (fun i ↦ ((twoInf K ^ (-x i) : 𝔸[K]ˣ) : 𝔸[K]) *
      algebraMap K 𝔸[K] (ξ i)) ∈ B} ⊆ Set.univ.pi fun i ↦
        {y : K | (∀ w : InfinitePlace K, w y ≤ R * 2 ^ x i) ∧
          algebraMap K 𝔸ᶠ[K] y ∈ (fun b : ι → 𝔸[K] ↦ (b i).2) '' B} := by
    intro ξ hξ i _
    refine ⟨fun w ↦ ?_, ⟨_, hξ, ?_⟩⟩
    · have h := hR _ hξ i w
      rw [norm_fst_twoInf_zpow_mul_algebraMap_apply, zpow_neg, inv_mul_le_iff₀ (by positivity),
        mul_comm] at h
      exact h
    · exact snd_twoInf_zpow_mul_algebraMap _ _
  calc _ ≤ (Set.univ.pi fun i ↦ {y : K | (∀ w : InfinitePlace K, w y ≤ R * 2 ^ x i) ∧
          algebraMap K 𝔸ᶠ[K] y ∈ (fun b : ι → 𝔸[K] ↦ (b i).2) '' B}).encard :=
        Set.encard_le_encard hsub
    _ = ∏ i, {y : K | (∀ w : InfinitePlace K, w y ≤ R * 2 ^ x i) ∧
          algebraMap K 𝔸ᶠ[K] y ∈ (fun b : ι → 𝔸[K] ↦ (b i).2) '' B}.encard :=
        Set.encard_pi_eq_prod_encard
    _ ≤ ∏ i, ((((⌊c i * R⌋₊ + 1) * 2 ^ (x i).toNat) ^ finrank ℚ K : ℕ) : ℕ∞) := by
      refine Finset.prod_le_prod fun i _ ↦ (hc i _).trans ?_
      rw [← mul_assoc]
      exact_mod_cast Nat.pow_le_pow_left (floor_mul_two_zpow_add_one_le (c i * R) (x i)) _
    _ = ((∏ i, (⌊c i * R⌋₊ + 1) ^ finrank ℚ K) * 2 ^ (finrank ℚ K * ∑ i, (x i).toNat) : ℕ) := by
      rw [← Nat.cast_prod]
      congr 1
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow_eq_pow_sum,
        ← pow_mul]
      rw [← Finset.sum_mul, mul_comm (∑ i, (x i).toNat)]

/-- **Rational points in dyadic dilates of a compact set of adeles, with `4` per infinite
place.** Let `K` be a number field with `f` infinite places and `B` a compact set of vectors of
adeles of `K`. There is a constant `C` such that for every `x ∈ ℤ ^ ι` the number of
`ξ ∈ K ^ ι` with `(2_∞ ^ (-x i) * ξ i)_i ∈ B` is at most `C * 4 ^ (f * ∑ i, max (x i) 0)`. This
is the bound of `exists_encard_setOf_twoInf_zpow_mul_mem_le` weakened through `[K : ℚ] ≤ 2 f`;
the two bounds coincide when `K` is totally complex. -/
theorem exists_encard_setOf_twoInf_zpow_mul_mem_le_four_pow {ι : Type*} [Fintype ι]
    {B : Set (ι → 𝔸[K])} (hB : IsCompact B) :
    ∃ C : ℕ, ∀ x : ι → ℤ,
      {ξ : ι → K | (fun i ↦ ((twoInf K ^ (-x i) : 𝔸[K]ˣ) : 𝔸[K]) * algebraMap K 𝔸[K] (ξ i)) ∈
        B}.encard ≤ (C * 4 ^ (Fintype.card (InfinitePlace K) * ∑ i, (x i).toNat) : ℕ) := by
  obtain ⟨C, hC⟩ := exists_encard_setOf_twoInf_zpow_mul_mem_le hB
  refine ⟨C, fun x ↦ (hC x).trans (Nat.cast_le.mpr (Nat.mul_le_mul_left C ?_))⟩
  -- `[K : ℚ] = r₁ + 2 r₂ ≤ 2 (r₁ + r₂)`
  have hd : finrank ℚ K ≤ 2 * Fintype.card (InfinitePlace K) := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    omega
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← mul_assoc]
  exact Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right _ hd)

end TauCeti.GlobalNumberFields
