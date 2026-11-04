/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Content
public import TauCeti.Algebra.Module.ZLattice.Level

/-!
# The Fricke partner of an even lattice

Let `L` be an even full lattice in a finite-dimensional real inner product space `E`, of rank `n`
and level `N = level L`. Its *Fricke partner* is the scaled dual lattice `√N • L^∨`. The Fricke
involution `τ ↦ -1 / (N τ)` exchanges the theta series of `L` and of `√N • L^∨`, which is why the
partner appears in the transformation law of `Θ_L` under the Fricke matrix `!![0, -1; N, 0]`.

This file proves that the Fricke partner is again an even lattice, that its determinant is
`Nⁿ / det L`, and computes its level. Since `(√N • L^∨)^∨ = (√N)⁻¹ • L`, an integer `K` is a
multiple of the level of the partner exactly when `N` divides `K ‖x‖² / 2` for every `x ∈ L`. So
the level is governed by the *content* `c_L` of `L`, the greatest common divisor of the half-norms
`‖x‖² / 2` of the vectors of `L` (`ZLattice.content`):
```text
level (√N • L^∨) = N / gcd (N, c_L).
```
In particular the level of the partner divides `N`, and it equals `N` exactly when no prime
dividing `N` divides every half-norm of `L`. Equality fails in general: the lattice `2 ℤ ⊆ ℝ` has
level `8` and content `2`, and its Fricke partner `√8 • ½ ℤ = √2 ℤ` has level `4`
(`ZLattice.level_sqrt_level_smul_dual_span_two`). Similarly `√2 • E₈` has level `2` and content
`2`, while its Fricke partner is `E₈`, of level `1`. More generally, in positive dimension an even
unimodular lattice `L` scaled by `√m` has level exactly `m` and Fricke partner `L`: the level
divides `m` because `(√m • L)^∨ = (√m)⁻¹ • L`, and it is at least `m` because the Fricke partner
`√N • (√m)⁻¹ • L`, being integral, has determinant `(N / m)ⁿ ≥ 1`.

The content and its basic API live in `TauCeti.Algebra.Module.ZLattice.Content`.

## Main statements

* `ZLattice.isEven_sqrt_level_smul_dual`: the Fricke partner `√N • L^∨` is even, for every `L`.
* `ZLattice.IsIntegral.det_sqrt_level_smul_dual`: for a full integral lattice of rank `n`,
  `det (√N • L^∨) = Nⁿ / det L`.
* `ZLattice.IsEven.level_sqrt_level_smul_dual`: for an even full lattice,
  `level (√N • L^∨) = N / gcd (N, c_L)`.
* `ZLattice.IsEven.level_sqrt_level_smul_dual_dvd`: the level of the Fricke partner divides `N`.
* `ZLattice.IsEven.level_sqrt_level_smul_dual_eq_level_iff`: it equals `N` exactly when `N` is
  coprime to the content.
* `ZLattice.IsEven.level_sqrt_smul_of_isUnimodular`,
  `ZLattice.IsEven.sqrt_level_smul_dual_sqrt_smul_of_isUnimodular`: in positive dimension, for an
  even unimodular `L` and `m > 0`, the lattice `√m • L` has level `m` and Fricke partner `L`.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 3.
* H. Iwaniec, *Topics in Classical Automorphic Forms*, AMS, 1997, Chapter 10.
-/

public section

open Module Submodule
open scoped Pointwise RealInnerProductSpace

namespace ZLattice

/-! ### The Fricke partner -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E}

variable (L) in
/-- The Fricke partner `√N • L^∨` of a lattice `L` of level `N` is even: for `x ∈ L^∨` the squared
norm `‖√N • x‖² = N ‖x‖²` is an even integer by the definition of the level. -/
theorem isEven_sqrt_level_smul_dual : IsEven (√(level L : ℝ) • dual L) :=
  (isEven_smul_iff _ _).mpr fun x hx ↦ by
    simpa [Real.sq_sqrt (Nat.cast_nonneg _)] using exists_level_mul_norm_sq_eq hx

/-- The Fricke partner `√N • L^∨` of a lattice `L` of level `N` is integral. -/
theorem isIntegral_sqrt_level_smul_dual : IsIntegral (√(level L : ℝ) • dual L) :=
  (isEven_sqrt_level_smul_dual L).isIntegral

section FiniteDimensional

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The Fricke partner of a full integral lattice `L` of level `N` and rank `n` has determinant
`det (√N • L^∨) = Nⁿ / det L`. -/
theorem IsIntegral.det_sqrt_level_smul_dual [MeasurableSpace E] [BorelSpace E]
    (h : IsIntegral L) :
    det (√(level L : ℝ) • dual L) = level L ^ finrank ℝ E / det L := by
  rw [det_sqrt_smul _ h.level_pos.ne', det_dual, div_eq_mul_inv]

/-- An integer `K` is a multiple of the level of the Fricke partner `√N • L^∨` of a full integral
lattice `L` of level `N` exactly when `N` divides `K ‖x‖² / 2` for every `x ∈ L`: the dual of the
partner is `(√N)⁻¹ • L`. -/
private theorem IsIntegral.level_sqrt_level_smul_dual_dvd_iff (h : IsIntegral L) {K : ℕ} :
    level (√(level L : ℝ) • dual L) ∣ K ↔
      ∀ x ∈ L, ∃ m : ℤ, (K : ℝ) * ‖x‖ ^ 2 = 2 * level L * m := by
  have hN : (0 : ℝ) < level L := Nat.cast_pos.mpr h.level_pos
  have hs : 0 < √(level L : ℝ) := Real.sqrt_pos.mpr hN
  rw [level_dvd_iff, dual_smul _ hs.ne', dual_dual]
  simp only [mem_smul_pointwise_iff_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, norm_smul, norm_inv, Real.norm_of_nonneg hs.le, mul_pow, inv_pow,
    Real.sq_sqrt hN.le]
  refine forall₂_congr fun x _ ↦ exists_congr fun m ↦ ?_
  constructor <;> intro hm
  · field_simp at hm
    linear_combination hm
  · field_simp
    linear_combination hm

/-- **The level of the Fricke partner.** For an even full lattice `L` of level `N` and content
`c_L` (the greatest common divisor of its half-norms `‖x‖² / 2`), the Fricke partner `√N • L^∨`
has level `N / gcd (N, c_L)`. -/
theorem IsEven.level_sqrt_level_smul_dual (h : IsEven L) :
    level (√(level L : ℝ) • dual L) = level L / Nat.gcd (level L) (content L) := by
  have hN := h.isIntegral.level_pos
  -- Both sides have the same multiples `K`: each is characterized by `N ∣ K c_L`.
  have key (K : ℕ) : level (√(level L : ℝ) • dual L) ∣ K ↔ level L ∣ K * content L := by
    rw [h.isIntegral.level_sqrt_level_smul_dual_dvd_iff, ← Int.natCast_dvd_natCast,
      Nat.cast_mul]
    refine ⟨fun hK ↦ dvd_mul_content fun x hx m hm ↦ ?_, fun hK x hx ↦ ?_⟩
    · obtain ⟨a, ha⟩ := hK x hx
      refine ⟨a, Int.cast_injective (α := ℝ) ?_⟩
      push_cast
      rw [hm] at ha
      linear_combination ha / 2
    · obtain ⟨m, hm⟩ := isEven_iff.mp h x hx
      obtain ⟨a, ha⟩ := hK.trans (mul_dvd_mul_left (K : ℤ) (content_dvd hx hm))
      have ha' : (K : ℝ) * m = level L * a := by exact_mod_cast ha
      refine ⟨a, ?_⟩
      rw [hm]
      linear_combination 2 * ha'
  refine Nat.dvd_antisymm ((key _).mpr ?_) ?_
  · calc level L = level L / Nat.gcd (level L) (content L) * Nat.gcd (level L) (content L) :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
      _ ∣ level L / Nat.gcd (level L) (content L) * content L :=
          Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_right _ _)
  · -- Cancel `c_L` from `level (√N • L^∨) * c_L ≡ 0 * c_L [MOD N]`.
    refine Nat.modEq_zero_iff_dvd.mp <| Nat.ModEq.cancel_right_div_gcd (c := content L) hN ?_
    rw [zero_mul]
    exact Nat.modEq_zero_iff_dvd.mpr ((key _).mp dvd_rfl)

/-- The level of the Fricke partner `√N • L^∨` of an even full lattice of level `N` divides `N`. -/
theorem IsEven.level_sqrt_level_smul_dual_dvd (h : IsEven L) :
    level (√(level L : ℝ) • dual L) ∣ level L := by
  rw [h.level_sqrt_level_smul_dual]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

/-- The Fricke partner `√N • L^∨` of an even full lattice of level `N` has level exactly `N` if and
only if `N` is coprime to the content of `L`, that is, no prime dividing `N` divides every
half-norm `‖x‖² / 2` of `L`. -/
theorem IsEven.level_sqrt_level_smul_dual_eq_level_iff (h : IsEven L) :
    level (√(level L : ℝ) • dual L) = level L ↔ (level L).Coprime (content L) := by
  rw [h.level_sqrt_level_smul_dual, Nat.div_eq_self, or_iff_right h.isIntegral.level_pos.ne',
    Nat.Coprime]

/-! ### Scaled even unimodular lattices -/

/-- **Scaled even unimodular lattices.** In positive dimension, scaling an even unimodular full
lattice `L` by `√m`, for a positive integer `m`, gives an even lattice of level exactly `m`.
For instance `√2 • E₈` has level `2`. -/
theorem IsEven.level_sqrt_smul_of_isUnimodular [Nontrivial E] (h : IsEven L)
    (hU : IsUnimodular L) {m : ℕ} (hm : m ≠ 0) : level (√(m : ℝ) • L) = m := by
  borelize E
  have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hs : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm₀
  have : NeZero √(m : ℝ) := ⟨hs.ne'⟩
  have hdual : dual (√(m : ℝ) • L) = (√(m : ℝ))⁻¹ • L := by rw [dual_smul _ hs.ne', hU.dual_eq]
  set N := level (√(m : ℝ) • L)
  -- `N ∣ m`: the dual `(√m)⁻¹ • L` has squared norms `‖y‖² / m` with `‖y‖² ∈ 2ℤ`.
  have hNm : N ∣ m := level_dvd_iff.mpr fun x hx ↦ by
    rw [hdual, mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, hk⟩ := isEven_iff.mp h y hy
    refine ⟨k, ?_⟩
    rw [norm_smul, mul_pow, norm_inv, Real.norm_of_nonneg hs.le, inv_pow, Real.sq_sqrt hm₀.le, hk]
    field_simp
  -- `m ≤ N`: the Fricke partner `√N • (√m)⁻¹ • L` is integral, so its determinant
  -- `(N / m)ⁿ det L = (N / m)ⁿ` is at least `1`.
  have hN₀ : (0 : ℝ) < N := Nat.cast_pos.mpr ((h.sqrt_smul m).isIntegral.level_pos)
  have hc : √(N : ℝ) * (√(m : ℝ))⁻¹ ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.mpr hN₀).ne' (inv_ne_zero hs.ne')
  have : NeZero (√(N : ℝ) * (√(m : ℝ))⁻¹) := ⟨hc⟩
  have hint : IsIntegral ((√(N : ℝ) * (√(m : ℝ))⁻¹) • L) := by
    simpa only [hdual, smul_smul] using isIntegral_sqrt_level_smul_dual (L := √(m : ℝ) • L)
  have hdet := hint.one_le_det
  rw [det_smul L hc, hU.det_eq_one, mul_one, pow_mul, mul_pow, inv_pow, Real.sq_sqrt hN₀.le,
    Real.sq_sqrt hm₀.le] at hdet
  have hmN : (m : ℝ) ≤ N := by
    by_contra hlt
    have hlt' : (N : ℝ) * (m : ℝ)⁻¹ < 1 := by
      rw [← div_eq_mul_inv, div_lt_one hm₀]
      exact not_le.mp hlt
    exact (pow_lt_one₀ (by positivity) hlt' finrank_pos.ne').not_ge hdet
  exact Nat.le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hNm) (by exact_mod_cast hmN)

/-- In positive dimension, the Fricke partner of `√m • L`, for an even unimodular full lattice `L`
and a positive integer `m`, is `L` itself: `√m • (√m • L)^∨ = L`. For instance the Fricke partner
of `√2 • E₈` is `E₈`, of level `1`. -/
theorem IsEven.sqrt_level_smul_dual_sqrt_smul_of_isUnimodular [Nontrivial E] (h : IsEven L)
    (hU : IsUnimodular L) {m : ℕ} (hm : m ≠ 0) :
    √(level (√(m : ℝ) • L) : ℝ) • dual (√(m : ℝ) • L) = L := by
  have hs : √(m : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
  rw [h.level_sqrt_smul_of_isUnimodular hU hm, dual_smul _ hs, hU.dual_eq, smul_smul,
    mul_inv_cancel₀ hs, one_smul]

end FiniteDimensional

/-! ### An example -/

/-- The Fricke partner of `2 ℤ ⊆ ℝ`, which has level `8`, is `√8 • ½ ℤ = √2 ℤ`, of level `4`: the
level of the Fricke partner of an even lattice can be a proper divisor of the level. This agrees
with `IsEven.level_sqrt_level_smul_dual`, since the content of `2 ℤ` is `2` (`content_span_two`)
and `8 / gcd (8, 2) = 4`. -/
theorem level_sqrt_level_smul_dual_span_two :
    level (√(level (span ℤ {2} : Submodule ℤ ℝ) : ℝ) • dual (span ℤ {2} : Submodule ℤ ℝ)) = 4 := by
  set b := OrthonormalBasis.singleton Unit ℝ
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
  have h8 : √(8 : ℝ) = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul' _ zero_le_two,
      Real.sqrt_sq zero_le_two]
  -- Write `2 ℤ` as `2 • ℤ b` for the orthonormal basis `b = (1)` of `ℝ`.
  have hL : (span ℤ {2} : Submodule ℤ ℝ) = (2 : ℝ) • span ℤ (Set.range b) := by
    simp [b, smul_span]
  have hlevel : level (span ℤ {2} : Submodule ℤ ℝ) = 8 := by
    simpa [hL, h4] using level_sqrt_smul_span_orthonormalBasis b (m := 4) (by norm_num)
  rw [hlevel, hL, dual_smul _ two_ne_zero, dual_span_orthonormalBasis, smul_smul]
  push_cast
  rw [h8, show 2 * √2 * (2 : ℝ)⁻¹ = √2 by ring]
  simpa [b, smul_span] using level_span_sqrt_two

end ZLattice
