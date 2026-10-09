/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
public import TauCeti.NumberTheory.NumberField.Global.Places.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Algebra.Order.Ring.Units
import TauCeti.GroupTheory.Index.NSmul

/-!
# Power classes at the places of a number field

Let `K` be a number field and `n ≥ 1`. At every place `v` of `K`, finite or infinite, the number
of `n`-th power classes of the completion is

`#(K_vˣ ⧸ (K_vˣ)ⁿ) · ‖n‖_v = n · #μ_n(K_v)`,

where `‖·‖_v` is the normalized absolute value `TauCeti.GlobalNumberFields.normalizedAbsValue` and
`μ_n(K_v)` is the group of `n`-th roots of unity of `K_v`. At a finite place this is the local count
`TauCeti.card_powerClasses_eq_mul_inv_normalizedAbsoluteValue`, once the norm of `K_v` is
identified with the normalized absolute value of `K_v` as a nonarchimedean local field. At a real
place it says `#(ℝˣ ⧸ (ℝˣ)ⁿ) = #μ_n(ℝ)`, and at a complex place every unit is an `n`-th power.

If `K` contains the `n`-th roots of unity, every factor `#μ_n(K_v)` is `n`. Let `S` be a finite
set of finite places containing those above the primes dividing `n`. Then `‖n‖_v = 1` at the finite
places outside `S`, so the product formula turns the local counts into the global identity

`∏_{v ∈ S} #(K_vˣ ⧸ (K_vˣ)ⁿ) · ∏_{w | ∞} #(K_wˣ ⧸ (K_wˣ)ⁿ) = n ^ (2 (#S + r₁ + r₂))`.

The left side is the index, in the `S`-ideles, of the subgroup of ideles that are `n`-th powers at
the places of `S` and at the infinite places and units elsewhere. That index is the local input to
the Kummer case of the second fundamental inequality and of the global existence theorem, where it
is compared with the index `n ^ (#S + r₁ + r₂)` of the `n`-th powers in the `S`-units.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.coe_normalizedAbsoluteValue_adicCompletion`: the norm of
  `K_v` is its normalized absolute value as a nonarchimedean local field.
* `TauCeti.card_powerClasses_real`: `#(ℝˣ ⧸ (ℝˣ)ⁿ) = #μ_n(ℝ)` for `n ≠ 0`.
* `TauCeti.card_powerClasses_of_isAlgClosed`: over an algebraically closed field every unit is an
  `n`-th power for `n ≠ 0`.
* `TauCeti.GlobalNumberFields.card_powerClasses_adicCompletion_mul_normalizedAbsValue` and
  `TauCeti.GlobalNumberFields.card_powerClasses_completion_mul_normalizedAbsValue`: the local count
  `#(K_vˣ ⧸ (K_vˣ)ⁿ) · ‖n‖_v = n · #μ_n(K_v)` at a finite and at an infinite place.
* `TauCeti.GlobalNumberFields.prod_card_powerClasses`: the product of the local counts over `S`
  and the infinite places is `n ^ (2 (#S + r₁ + r₂))` when `μ_n ⊆ K`.

## References

* J. S. Milne, *Class Field Theory*, VII, §5 (the second inequality in the Kummer case).
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter VII, §6.
-/

public section

open IsDedekindDomain NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- The norm of the completion `K_v` of a number field is its normalized absolute value as a
nonarchimedean local field: both send a nonzero `x` to `(N v) ^ (-v(x))`, the residue field of
`K_v` having `N v` elements. -/
theorem coe_normalizedAbsoluteValue_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) :
    (TauCeti.normalizedAbsoluteValue (v.adicCompletion K) x : ℝ) = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  -- The adic valuation of `x` is the inverse of its normalized valuation.
  have hv : Valued.v x = WithZero.exp
      (-(TauCeti.normalizedValuation (v.adicCompletion K) (Units.mk0 x hx)).toAdd) := by
    have h := v.normalizedValuationWithZero_adicCompletion (K := K) (Units.mk0 x hx)
    rw [TauCeti.normalizedValuationWithZero_coe, Units.val_mk0] at h
    rw [← inv_inv (Valued.v x), ← h, ← WithZero.coe_inv]
    rfl
  rw [TauCeti.normalizedAbsoluteValue_apply_ne_zero x hx, FinitePlace.norm_def, hv,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp,
    v.natCard_residueField_adicCompletion_eq_absNorm]
  simp

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

/-- **The `n`-th power classes of `ℝ`.** For `n ≠ 0`, the quotient `ℝˣ ⧸ (ℝˣ)ⁿ` has as many
elements as there are `n`-th roots of unity in `ℝ`: one for odd `n`, two for even `n`. -/
theorem card_powerClasses_real {n : ℕ} (hn : n ≠ 0) :
    Nat.card (ℝˣ ⧸ (powMonoidHom n : ℝˣ →* ℝˣ).range) = Nat.card (rootsOfUnity n ℝ) := by
  -- Compare with the positive units, a subgroup of index two on which `x ↦ xⁿ` is bijective.
  have h := Subgroup.index_range_pow_mul_card_ker (Units.posSubgroup ℝ) n
  have hker : (powMonoidHom n : Units.posSubgroup ℝ →* Units.posSubgroup ℝ).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (pow_left_injective hn)
  have hrange : (powMonoidHom n : Units.posSubgroup ℝ →* Units.posSubgroup ℝ).range = ⊤ := by
    refine MonoidHom.range_eq_top.2 fun x ↦ ?_
    have hx : (0 : ℝ) < ((x : ℝˣ) : ℝ) := (Units.mem_posSubgroup _).1 x.2
    have hy : (0 : ℝ) < ((x : ℝˣ) : ℝ) ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos hx _
    refine ⟨⟨Units.mk0 _ hy.ne', (Units.mem_posSubgroup _).2 hy⟩, ?_⟩
    ext
    simp [Real.rpow_inv_natCast_pow hx.le hn]
  have hG : (powMonoidHom n : ℝˣ →* ℝˣ).ker = rootsOfUnity n ℝ := by
    ext
    simp
  rw [hker, hrange, hG, Subgroup.index_top, Subgroup.card_bot, mul_one, mul_one] at h
  rw [← Subgroup.index_eq_card, h]

/-- **The `n`-th power classes of an algebraically closed field.** For `n ≠ 0`, every unit of an
algebraically closed field is an `n`-th power, so `Fˣ ⧸ (Fˣ)ⁿ` is trivial. -/
theorem card_powerClasses_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] {n : ℕ}
    (hn : n ≠ 0) : Nat.card (Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range) = 1 := by
  suffices h : (powMonoidHom n : Fˣ →* Fˣ).range = ⊤ by
    rw [← Subgroup.index_eq_card, h, Subgroup.index_top]
  refine MonoidHom.range_eq_top.2 fun x ↦ ?_
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) (Nat.pos_of_ne_zero hn)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by simpa [zero_pow hn] using hy.symm)
  exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩

namespace GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The power classes at a finite place.** For `n ≠ 0` and a finite place `v` of a number field
`K`, `#(K_vˣ ⧸ (K_vˣ)ⁿ) · ‖n‖_v = n · #μ_n(K_v)`. -/
theorem card_powerClasses_adicCompletion_mul_normalizedAbsValue (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : n ≠ 0) :
    (Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range) : ℝ) *
        normalizedAbsValue (.inl v) (n : K) =
      n * Nat.card (rootsOfUnity n (v.adicCompletion K)) := by
  have hn' : (n : v.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := congrArg ((↑) : ℚ≥0 → ℝ) (card_powerClasses_eq_mul_inv_normalizedAbsoluteValue hn')
  have h0 : (normalizedAbsoluteValue (v.adicCompletion K) (n : v.adicCompletion K) : ℝ) ≠ 0 := by
    simpa using hn'
  push_cast at h
  rw [normalizedAbsValue_inl, ← FinitePlace.norm_embedding, map_natCast,
    ← v.coe_normalizedAbsoluteValue_adicCompletion, h, mul_assoc, inv_mul_cancel₀ h0, mul_one]

/-- **The power classes at an infinite place.** For `n ≠ 0` and an infinite place `w` of a number
field `K`, `#(K_wˣ ⧸ (K_wˣ)ⁿ) · ‖n‖_w = n · #μ_n(K_w)`, where `‖n‖_w` is `n` at a real place and
`n ^ 2` at a complex place. -/
theorem card_powerClasses_completion_mul_normalizedAbsValue (w : InfinitePlace K) {n : ℕ}
    (hn : n ≠ 0) :
    (Nat.card (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* _).range) : ℝ) *
        normalizedAbsValue (.inr w) (n : K) =
      n * Nat.card (rootsOfUnity n w.Completion) := by
  have : NeZero n := ⟨hn⟩
  -- The number of power classes and of roots of unity only depend on the field up to isomorphism.
  have hcard {F : Type} [Field F] (e : w.Completion ≃+* F) :
      Nat.card (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* _).range) =
        Nat.card (Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card,
      ← Subgroup.index_map_equiv _ (Units.mapEquiv e.toMulEquiv),
      MulEquiv.map_range_powMonoidHom]
  have hroots {F : Type} [Field F] (e : w.Completion ≃+* F) :
      Nat.card (rootsOfUnity n w.Completion) = Nat.card (rootsOfUnity n F) :=
    Nat.card_congr (e.restrictRootsOfUnity n).toEquiv
  rw [normalizedAbsValue_inr, ← InfinitePlace.norm_embedding_eq, map_natCast, Complex.norm_natCast]
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    rw [hw.mult_eq_one, pow_one, hcard e, card_powerClasses_real hn, hroots e, mul_comm]
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    rw [hw.mult_eq_two, hcard e, card_powerClasses_of_isAlgClosed hn, hroots e,
      Complex.card_rootsOfUnity]
    push_cast
    ring

/-- **The product of the local power indices.** Let `K` be a number field containing the `n`-th
roots of unity and let `S` be a finite set of finite places of `K` containing every place above a
prime dividing `n`. Then the product of the numbers of `n`-th power classes of the completions of
`K` at the places of `S` and at the infinite places is `n ^ (2 (#S + r₁ + r₂))`, where
`r₁ + r₂` is the number of infinite places. -/
theorem prod_card_powerClasses (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S,
        Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range)) *
      ∏ w : InfinitePlace K,
        Nat.card (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* _).range) =
      n ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  have hn : n ≠ 0 := NeZero.ne n
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  -- Each completion contains the image of a primitive `n`-th root of unity of `K`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hfin (v : HeightOneSpectrum (𝓞 K)) : Nat.card (rootsOfUnity n (v.adicCompletion K)) = n :=
    (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective).card_rootsOfUnity
  have hinf (w : InfinitePlace K) : Nat.card (rootsOfUnity n w.Completion) = n :=
    (hζ.map_of_injective (algebraMap K w.Completion).injective).card_rootsOfUnity
  -- The normalized absolute value of `n` is `1` at the finite places outside `S`.
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      normalizedAbsValue (.inl v) (n : K)) ⊆ S := by
    intro v hv
    by_contra hvS
    refine hv ?_
    simpa using (normalizedAbsValue_inl_algebraMap_eq_one_iff v (n : 𝓞 K)).2
      fun h ↦ hvS (hS v h)
  -- The product formula, with the finite part restricted to `S`.
  have hformula : (∏ v ∈ S, normalizedAbsValue (.inl v) (n : K)) *
      ∏ w : InfinitePlace K, normalizedAbsValue (.inr w) (n : K) = 1 := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp, finprod_normalizedAbsValue_inl hnK]
    simp only [normalizedAbsValue_inr]
    have h0 : |(Algebra.norm ℚ) (n : K)| ≠ 0 := by simpa [Algebra.norm_eq_zero_iff] using hnK
    rw [InfinitePlace.prod_eq_abs_norm, ← Rat.cast_mul, inv_mul_cancel₀ h0, Rat.cast_one]
  -- At every place of `S` and every infinite place the local count is `n ^ 2`.
  have hfin' : ∏ v ∈ S, ((Nat.card ((v.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range) : ℝ) *
        normalizedAbsValue (.inl v) (n : K)) = ((n : ℝ) ^ 2) ^ S.card := by
    rw [Finset.prod_congr (g := fun _ ↦ (n : ℝ) ^ 2) rfl fun v _ ↦ by
      rw [card_powerClasses_adicCompletion_mul_normalizedAbsValue v hn, hfin, sq],
      Finset.prod_const]
  have hinf' : ∏ w : InfinitePlace K, ((Nat.card (w.Completionˣ ⧸
      (powMonoidHom n : w.Completionˣ →* _).range) : ℝ) *
        normalizedAbsValue (.inr w) (n : K)) = ((n : ℝ) ^ 2) ^ Fintype.card (InfinitePlace K) := by
    rw [Finset.prod_congr (g := fun _ ↦ (n : ℝ) ^ 2) rfl fun w _ ↦ by
      rw [card_powerClasses_completion_mul_normalizedAbsValue w hn, hinf, sq],
      Finset.prod_const, Finset.card_univ]
  have h := congrArg₂ (· * ·) hfin' hinf'
  simp only [Finset.prod_mul_distrib] at h
  rw [mul_mul_mul_comm, hformula, mul_one] at h
  exact_mod_cast h.trans (by ring : _ = (n : ℝ) ^ (2 * (S.card + Fintype.card (InfinitePlace K))))

end GlobalNumberFields

end TauCeti
