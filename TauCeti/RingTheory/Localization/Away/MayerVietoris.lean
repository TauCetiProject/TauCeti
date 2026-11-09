/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The Mayer–Vietoris sequence of two coprime elements

Let `B` be a commutative ring and `u, v : B` coprime elements, so that the basic open subsets
`D(u)` and `D(v)` cover `Spec B`. Then the Mayer–Vietoris sequence

`0 → B → B[1/u] × B[1/v] → B[1/(uv)] → 0`,

with first map `b ↦ (b, b)` and second map `(x, y) ↦ x - y`, is exact. This is the Čech complex of
the structure sheaf for this cover, and its exactness at the last term says that this Čech
complex has no first cohomology. The localizations are arbitrary `IsLocalization.Away` models, and
the maps to `B[1/(uv)]` are any ring homomorphisms compatible with the maps from `B` (they are
unique, for instance `IsLocalization.Away.awayToAwayRight`).

## Main results

* `IsLocalization.Away.mayerVietoris_injective`: an element vanishing in `B[1/u]` and in `B[1/v]`
  vanishes.
* `IsLocalization.Away.mayerVietoris_exact`: elements of `B[1/u]` and `B[1/v]` with the same image
  in `B[1/(uv)]` come from a single element of `B`.
* `IsLocalization.Away.mayerVietoris_surjective`: every element of `B[1/(uv)]` is a difference of
  elements of `B[1/u]` and `B[1/v]`.

## References

* [Stacks Project, Lemma 10.24.1 (Tag 00EJ)](https://stacks.math.columbia.edu/tag/00EJ) for the
  sheaf property, and the proof of Lemma 15.93.1 (Tag 091Q) for this sequence.
-/

public section

namespace IsLocalization.Away

variable {B : Type*} [CommRing B] {u v : B} (huv : IsCoprime u v)
  {Bu Bv Buv : Type*} [CommRing Bu] [CommRing Bv] [CommRing Buv] [Algebra B Bu] [Algebra B Bv]
  [Algebra B Buv] [IsLocalization.Away u Bu] [IsLocalization.Away v Bv]
  [IsLocalization.Away (u * v) Buv]
include huv

/-- An element of `B` vanishing in `B[1/u]` and in `B[1/v]` vanishes, for coprime `u` and `v`. -/
theorem mayerVietoris_injective :
    Function.Injective fun b : B ↦ (algebraMap B Bu b, algebraMap B Bv b) := by
  refine (injective_iff_map_eq_zero ((algebraMap B Bu).prod (algebraMap B Bv))).2 fun b hb ↦ ?_
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers u) Bu b).1
    (congrArg Prod.fst hb)
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers v) Bv b).1
    (congrArg Prod.snd hb)
  obtain ⟨a, a', h⟩ := huv.pow (m := m) (n := n)
  simpa [hm, hn, add_mul, mul_assoc] using (congrArg (· * b) h).symm

variable {ρu : Bu →+* Buv} {ρv : Bv →+* Buv}
  (hρu : ∀ b, ρu (algebraMap B Bu b) = algebraMap B Buv b)
  (hρv : ∀ b, ρv (algebraMap B Bv b) = algebraMap B Buv b)
include hρu hρv

/-- Elements of `B[1/u]` and `B[1/v]` with the same image in `B[1/(uv)]` are the images of a single
element of `B`, for coprime `u` and `v`. -/
theorem mayerVietoris_exact :
    Function.Exact (fun b : B ↦ (algebraMap B Bu b, algebraMap B Bv b))
      (fun p : Bu × Bv ↦ ρu p.1 - ρv p.2) := by
  rintro ⟨x, y⟩
  simp only [Set.mem_range, sub_eq_zero]
  constructor
  · intro hxy
    obtain ⟨⟨a₁, _, m, rfl⟩, h₁⟩ := IsLocalization.surj (Submonoid.powers u) x
    obtain ⟨⟨a₂, _, n, rfl⟩, h₂⟩ := IsLocalization.surj (Submonoid.powers v) y
    dsimp only at h₁ h₂
    -- Compare the numerators in `B[1/(uv)]`.
    have e₁ : algebraMap B Buv a₁ = ρu x * algebraMap B Buv (u ^ m) := by
      rw [← hρu, ← h₁, map_mul, hρu]
    have e₂ : algebraMap B Buv a₂ = ρv y * algebraMap B Buv (v ^ n) := by
      rw [← hρv, ← h₂, map_mul, hρv]
    have : algebraMap B Buv (a₁ * v ^ n) = algebraMap B Buv (a₂ * u ^ m) := by
      rw [map_mul, map_mul, e₁, e₂, hxy]
      ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (u * v)) this
    dsimp only at hk
    -- Glue the two fractions with a partition of unity `α uᵐ⁺ᵏ + β vⁿ⁺ᵏ = 1`.
    obtain ⟨α, β, hαβ⟩ := huv.pow (m := m + k) (n := n + k)
    refine ⟨α * (a₁ * u ^ k) + β * (a₂ * v ^ k), Prod.ext ?_ ?_⟩
    · refine (IsLocalization.Away.algebraMap_pow_isUnit u (m + k)).mul_left_injective ?_
      dsimp only
      calc _ = algebraMap B Bu ((α * (a₁ * u ^ k) + β * (a₂ * v ^ k)) * u ^ (m + k)) := by
            simp
        _ = algebraMap B Bu (a₁ * u ^ k) :=
            congrArg _ (by linear_combination (a₁ * u ^ k) * hαβ - β * hk)
        _ = _ := by rw [map_mul, ← h₁, pow_add]; simp only [map_pow]; ring
    · refine (IsLocalization.Away.algebraMap_pow_isUnit v (n + k)).mul_left_injective ?_
      dsimp only
      calc _ = algebraMap B Bv ((α * (a₁ * u ^ k) + β * (a₂ * v ^ k)) * v ^ (n + k)) := by
            simp
        _ = algebraMap B Bv (a₂ * v ^ k) :=
            congrArg _ (by linear_combination (a₂ * v ^ k) * hαβ + α * hk)
        _ = _ := by rw [map_mul, ← h₂, pow_add]; simp only [map_pow]; ring
  · rintro ⟨b, hb⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb
    rw [hρu, hρv]

/-- Every element of `B[1/(uv)]` is a difference of the images of elements of `B[1/u]` and
`B[1/v]`, for coprime `u` and `v`. -/
theorem mayerVietoris_surjective :
    Function.Surjective fun p : Bu × Bv ↦ ρu p.1 - ρv p.2 := by
  intro z
  obtain ⟨⟨c, _, n, rfl⟩, hc⟩ := IsLocalization.surj (Submonoid.powers (u * v)) z
  dsimp only at hc
  obtain ⟨α, β, hαβ⟩ := huv.pow (m := n) (n := n)
  have eu : algebraMap B Buv u ^ n * ρu (IsLocalization.Away.invSelf u) ^ n = 1 := by
    rw [← mul_pow, ← hρu, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, one_pow]
  have ev : algebraMap B Buv v ^ n * ρv (IsLocalization.Away.invSelf v) ^ n = 1 := by
    rw [← mul_pow, ← hρv, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, one_pow]
  have hαβ' := congrArg (algebraMap B Buv) hαβ
  simp only [map_add, map_mul, map_pow, map_one] at hαβ' hc
  refine ⟨(algebraMap B Bu (β * c) * IsLocalization.Away.invSelf u ^ n,
    -(algebraMap B Bv (α * c) * IsLocalization.Away.invSelf v ^ n)), ?_⟩
  refine (IsLocalization.Away.algebraMap_pow_isUnit (S := Buv) (u * v) n).mul_left_injective ?_
  simp only [map_neg, sub_neg_eq_add, map_mul, map_pow, hρu, hρv, mul_pow]
  linear_combination (algebraMap B Buv β * algebraMap B Buv c * algebraMap B Buv v ^ n) * eu +
    (algebraMap B Buv α * algebraMap B Buv c * algebraMap B Buv u ^ n) * ev +
    algebraMap B Buv c * hαβ' - hc

end IsLocalization.Away
