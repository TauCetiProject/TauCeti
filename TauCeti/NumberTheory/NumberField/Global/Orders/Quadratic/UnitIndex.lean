/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.IntAddMulOrder
public import TauCeti.NumberTheory.NumberField.Quadratic.Units

/-!
# The unit index of the order of conductor `f` in a quadratic field

Let `K` be a quadratic field and `O_f = ℤ + f 𝓞 K` its order of conductor `f`. The class number
formula for `O_f` involves the index `[(𝓞 K)ˣ : O_fˣ]` of the units of `O_f`, viewed inside the
units of `𝓞 K`. This file computes it for imaginary quadratic `K`.

The only roots of unity in `O_f` with `f ≥ 2` are `±1`. Indeed a root of unity `ζ ≠ ±1` of a
quadratic field satisfies `ζ² - t ζ + 1 = 0` with `t ∈ {-1, 0, 1}`. Writing `ζ = a + f y` with
`a ∈ ℤ` and `y ∈ 𝓞 K`, and `y² = T y - N` with `T`, `N` the trace and norm of `y`, the
irrationality of `ζ` forces `f ∣ 2a - t` and `f² N = a² - t a + 1`, whence
`f² (4 N - T²) = 4 - t² ∈ {3, 4}`. As `4 N - T² ≡ 0, 3 (mod 4)`, this leaves only `f = 1`.

Since every unit of an imaginary quadratic field is a root of unity, `O_fˣ = {±1}` for `f ≥ 2`,
and the unit index is `w_K / 2`. This gives the exceptional unit indices for `D = -3` and
`D = -4`:

```text
[(𝓞 K)ˣ : O_fˣ] = 1                       if f = 1,
[(𝓞 K)ˣ : O_fˣ] = 3, 2 or 1                if f ≥ 2 and D = -3, D = -4 or otherwise.
```

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.eq_one_or_neg_one_of_mem_torsion`: for `f ≠ 1`,
  the only roots of unity of a quadratic field lying in `ℤ + f 𝓞 K` are `±1`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.index_range_unitsMap_intAddMulOrder_one`: the
  maximal order `ℤ + 1 𝓞 K` has unit index `1`, in any number field.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.mem_range_unitsMap_intAddMulOrder_iff`: for
  imaginary quadratic `K` and `f ≠ 1`, the units of `ℤ + f 𝓞 K` are `±1`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.card_units_intAddMulOrder`: for imaginary
  quadratic `K` and `f ≠ 1`, the order `ℤ + f 𝓞 K` has exactly two units.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.index_range_unitsMap_intAddMulOrder`: the unit
  index `[(𝓞 K)ˣ : O_fˣ]` of an imaginary quadratic field of discriminant `D`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.24.
-/

public section
noncomputable section

open NumberField NumberField.Units Module

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]

/-- An algebraic integer `u` of a quadratic field with `u² - t u + 1 = 0` and `t² < 4` lies in
`ℤ + f 𝓞 K` only for `f = 1`. -/
private theorem eq_one_of_sq_sub_mul_add_one_eq_zero (hK : finrank ℚ K = 2) {f : ℕ} [NeZero f]
    {u : 𝓞 K} {t : ℤ} (ht : t ^ 2 < 4) (hu : u ^ 2 - t * u + 1 = 0)
    (huf : u ∈ (intAddMulOrder K f).toRingOfIntegers) : f = 1 := by
  have : Algebra.IsQuadraticExtension ℤ (𝓞 K) := ⟨by rw [RingOfIntegers.rank, hK]⟩
  obtain ⟨a, y, rfl⟩ := mem_toRingOfIntegers_intAddMulOrder.mp huf
  have hy := Algebra.IsQuadraticExtension.sq_eq_trace_smul_sub_norm ℤ y
  set T := Algebra.trace ℤ (𝓞 K) y
  set N := Algebra.norm ℤ y
  rw [zsmul_eq_mul, algebraMap_int_eq, eq_intCast] at hy
  -- Substituting `y² = T y - N` leaves a linear relation `α y + β = 0` over `ℤ`.
  set α : ℤ := f ^ 2 * T + f * (2 * a - t)
  set β : ℤ := a ^ 2 - t * a + 1 - f ^ 2 * N
  have hlin : (α : 𝓞 K) * y + β = 0 := by
    simp only [α, β]
    push_cast
    linear_combination hu - (f : 𝓞 K) ^ 2 * hy
  -- If `α ≠ 0` then `α (2 u - t)` is a rational integer whose square is `α² (t² - 4) < 0`.
  have hα : α = 0 := by
    by_contra hα
    have hsq : ((α * (2 * a - t) - 2 * f * β : ℤ) : 𝓞 K) ^ 2 =
        ((α ^ 2 * (t ^ 2 - 4) : ℤ) : 𝓞 K) := by
      push_cast
      linear_combination (4 * (α : 𝓞 K) ^ 2) * hu +
        (-4 * (f : 𝓞 K) * α * (2 * (a + f * y) - t) + 4 * (f : 𝓞 K) ^ 2 * (α * y + β)) * hlin
    have hsq' : (α * (2 * a - t) - 2 * f * β) ^ 2 = α ^ 2 * (t ^ 2 - 4) := by
      exact_mod_cast hsq
    have : α ^ 2 * (t ^ 2 - 4) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
    nlinarith [sq_nonneg (α * (2 * a - t) - 2 * f * β)]
  have hβ : β = 0 := by
    rw [hα, Int.cast_zero, zero_mul, zero_add] at hlin
    exact_mod_cast hlin
  have hf0 : (f : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne f
  have hc : 2 * a - t + f * T = 0 := by
    have h : (f : ℤ) * (2 * a - t + f * T) = 0 := by linear_combination hα
    exact (mul_eq_zero.mp h).resolve_left hf0
  have key : (f : ℤ) ^ 2 * (4 * N - T ^ 2) = 4 - t ^ 2 := by
    linear_combination (-4) * hβ + (2 * a - t - f * T) * hc
  have hf1 : (1 : ℤ) ≤ f := by have := NeZero.ne f; omega
  have hk : 0 < 4 * N - T ^ 2 := by
    by_contra hk
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (f : ℤ)) (not_lt.mp hk)]
  -- `4 N - T²` is not `1 (mod 4)`.
  have hk1 : 4 * N - T ^ 2 ≠ 1 := by
    intro h
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' T <;> rw [hm] at h <;> ring_nf at h <;> omega
  -- Hence `f² ≤ f² (4 N - T²) / 2 = (4 - t²) / 2 ≤ 2`.
  suffices (f : ℤ) = 1 by exact_mod_cast this
  by_contra hne
  have hf2 : (2 : ℤ) ≤ f := by omega
  have hk2 : 2 ≤ 4 * N - T ^ 2 := by omega
  nlinarith [mul_le_mul_of_nonneg_left hk2 (sq_nonneg (f : ℤ))]

/-- **The roots of unity in the order of conductor `f`.** For `f ≠ 1`, the only roots of unity
of a quadratic field lying in `ℤ + f 𝓞 K` are `±1`. -/
theorem eq_one_or_neg_one_of_mem_torsion (hK : finrank ℚ K = 2) {f : ℕ} [NeZero f]
    (hf : f ≠ 1) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hζf : (ζ : 𝓞 K) ∈ (intAddMulOrder K f).toRingOfIntegers) : ζ = 1 ∨ ζ = -1 := by
  set u : 𝓞 K := ↑ζ
  have hpow := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) (pow_torsionOrder_eq_one K hζ)
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hpow
  -- A root of unity of order `3`, `4` or `6` satisfies `u² - t u + 1 = 0` with `t ∈ {-1, 0, 1}`.
  have hroot : u = 1 ∨ u = -1 ∨ ∃ t : ℤ, t ^ 2 < 4 ∧ u ^ 2 - t * u + 1 = 0 := by
    rcases TauCeti.NumberField.Units.torsionOrder_eq_two_or_four_or_six hK.le with h | h | h <;>
      rw [h] at hpow
    · have : (u - 1) * (u + 1) = 0 := by linear_combination hpow
      rcases mul_eq_zero.mp this with h | h
      · exact .inl (sub_eq_zero.mp h)
      · exact .inr (.inl (eq_neg_of_add_eq_zero_left h))
    · have : ((u - 1) * (u + 1)) * (u ^ 2 - (0 : ℤ) * u + 1) = 0 := by
        push_cast; linear_combination hpow
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact .inl (sub_eq_zero.mp h)
        · exact .inr (.inl (eq_neg_of_add_eq_zero_left h))
      · exact .inr (.inr ⟨0, by norm_num, h⟩)
    · have : ((u - 1) * (u + 1)) *
          ((u ^ 2 - (1 : ℤ) * u + 1) * (u ^ 2 - (-1 : ℤ) * u + 1)) = 0 := by
        push_cast; linear_combination hpow
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact .inl (sub_eq_zero.mp h)
        · exact .inr (.inl (eq_neg_of_add_eq_zero_left h))
      · rcases mul_eq_zero.mp h with h | h
        · exact .inr (.inr ⟨1, by norm_num, h⟩)
        · exact .inr (.inr ⟨-1, by norm_num, h⟩)
  rcases hroot with h | h | ⟨t, ht, h⟩
  · exact .inl (Units.ext h)
  · exact .inr (Units.ext h)
  · exact absurd (eq_one_of_sq_sub_mul_add_one_eq_zero hK ht h hζf) hf

variable (K) in
/-- **The unit index of the maximal order.** Every unit of `𝓞 K` is a unit of `ℤ + 1 𝓞 K`, so
`[(𝓞 K)ˣ : O_1ˣ] = 1`. -/
theorem index_range_unitsMap_intAddMulOrder_one :
    (Units.map ((intAddMulOrder K 1).toRingOfIntegers.val :
      (intAddMulOrder K 1).toRingOfIntegers →* 𝓞 K)).range.index = 1 := by
  rw [Subgroup.index_eq_one, MonoidHom.range_eq_top]
  intro ε
  have hmem (x : 𝓞 K) : x ∈ (intAddMulOrder K 1).toRingOfIntegers :=
    mem_toRingOfIntegers_intAddMulOrder.mpr ⟨0, x, by simp⟩
  exact ⟨⟨⟨ε, hmem _⟩, ⟨_, hmem _⟩, Subtype.ext ε.mul_inv, Subtype.ext ε.inv_mul⟩,
    Units.ext rfl⟩

variable [IsTotallyComplex K]

/-- **The units of the order of conductor `f ≠ 1` in an imaginary quadratic field are `±1`.** -/
theorem mem_range_unitsMap_intAddMulOrder_iff (hK : finrank ℚ K = 2) {f : ℕ} [NeZero f]
    (hf : f ≠ 1) {ε : (𝓞 K)ˣ} :
    ε ∈ (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
      (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range ↔ ε = 1 ∨ ε = -1 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact eq_one_or_neg_one_of_mem_torsion hK hf
      (TauCeti.NumberField.Units.torsion_eq_top_of_isTotallyComplex hK ▸ Subgroup.mem_top _)
      (w : (intAddMulOrder K f).toRingOfIntegers).2
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact ⟨-1, Units.ext (by simp)⟩

/-- **The order of conductor `f ≠ 1` in an imaginary quadratic field has two units.** -/
theorem card_units_intAddMulOrder (hK : finrank ℚ K = 2) {f : ℕ} [NeZero f] (hf : f ≠ 1) :
    Nat.card (intAddMulOrder K f).toRingOfIntegersˣ = 2 := by
  set φ : (intAddMulOrder K f).toRingOfIntegersˣ →* (𝓞 K)ˣ :=
    Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
      (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)
  have hφ : Function.Injective φ := Units.map_injective Subtype.val_injective
  have hrange : (φ.range : Set (𝓞 K)ˣ) = {1, -1} := by
    ext ε
    exact mem_range_unitsMap_intAddMulOrder_iff hK hf
  have hne : (1 : (𝓞 K)ˣ) ≠ -1 := fun h ↦ by
    have := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) h
    rw [Units.val_one, Units.val_neg, Units.val_one, eq_neg_iff_add_eq_zero] at this
    norm_num at this
  rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, ← SetLike.coe_sort_coe, hrange,
    Nat.card_coe_set_eq, Set.ncard_pair hne]

/-- **The unit index of the order of conductor `f`.** In an imaginary quadratic field of
discriminant `D`, the index `[(𝓞 K)ˣ : O_fˣ]` of the units of `ℤ + f 𝓞 K` is `1` for `f = 1`,
and for `f ≥ 2` it is `2` if `D = -4`, `3` if `D = -3`, and `1` otherwise. -/
theorem index_range_unitsMap_intAddMulOrder (hK : finrank ℚ K = 2) (f : ℕ) [NeZero f] :
    (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
      (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index =
      if f = 1 then 1
      else if NumberField.discr K = -4 then 2 else if NumberField.discr K = -3 then 3 else 1 := by
  by_cases hf : f = 1
  · subst hf
    simpa using index_range_unitsMap_intAddMulOrder_one K
  -- `2 · [(𝓞 K)ˣ : O_fˣ] = w_K`.
  have h := (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
    (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.card_mul_index
  rw [← Nat.card_congr (MonoidHom.ofInjective
      (Units.map_injective Subtype.val_injective)).toEquiv, card_units_intAddMulOrder hK hf,
    TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at h
  simp only [hf, ↓reduceIte]
  split_ifs at h ⊢ <;> omega

end TauCeti.GlobalNumberFields.NumberFieldOrder
