/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.IntAddMulOrder
public import TauCeti.NumberTheory.NumberField.Quadratic.ComplexEmbedding
public import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Complex embeddings of imaginary quadratic orders

For an integer `D ≤ 0` with `D ≡ 0, 1 mod 4`, the distinguished complex embedding
`QuadraticAlgebra.complexEmbedding` of `ℚ(√D)` maps the half-integral generator `(D + ω) / 2` to
`complexGenerator D = (D + √(-D) · i) / 2` and transports `TauCeti.QuadraticOrder.toSubalgebra D` to
the subalgebra `complexOrder D ⊆ ℂ` with integral basis `1, (D + √(-D) · i) / 2`.

When `D < 0`, the complex embedding is injective (`QuadraticAlgebra.complexEmbedding_injective`), so
`toSubalgebra D` is `ℤ`-algebra isomorphic to `complexOrder D` (`equivComplexOrder`), and the
embedded subalgebra `complexOrder D ⊆ ℂ` uniquely determines the discriminant `D`
(`complexOrder_eq_iff`). For every positive conductor `f`, `complexOrder (f² D)` has the lattice
presentation `ℤ + ℤ · f complexGenerator D` (`mem_complexOrder_mul_sq_iff`) and, when `D` is a
fundamental discriminant, coincides with the image of `ℤ + f 𝓞 K` (`map_intAddMulOrder_eq`).

## Main definitions

* `TauCeti.QuadraticOrder.complexGenerator`: `(D + √(-D) · i) / 2 ∈ ℂ`, the image of `generator D`
  under `QuadraticAlgebra.complexEmbedding`.
* `TauCeti.QuadraticOrder.complexOrder`: the `ℤ`-subalgebra `ℤ[(D + √(-D) · i) / 2] ⊆ ℂ`.
* `TauCeti.QuadraticOrder.equivComplexOrder`: `toSubalgebra D ≃ₐ[ℤ] complexOrder D` for `D < 0`.

## Main results

* `QuadraticAlgebra.complexEmbedding_injective`: for `a < 0`, `QuadraticAlgebra.complexEmbedding`
  is injective.
* `TauCeti.QuadraticOrder.complexOrder_eq_iff`: for `D₁, D₂ < 0`,
  `complexOrder D₁ = complexOrder D₂` if and only if `D₁ = D₂`.
* `TauCeti.QuadraticOrder.mem_complexOrder_mul_sq_iff` and
  `TauCeti.QuadraticOrder.complexOrder_mul_sq_eq_adjoin`: `complexOrder (f² D)` equals
  `ℤ + ℤ · f complexGenerator D = ℤ[f complexGenerator D]`.
* `TauCeti.QuadraticOrder.map_intAddMulOrder_eq`: for a negative fundamental discriminant `D`, the
  complex image of `ℤ + f 𝓞 K` is `complexOrder (f² D)`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 and §10.
-/

public noncomputable section

open Complex QuadraticAlgebra

namespace QuadraticAlgebra

/-- For `a < 0`, the distinguished complex embedding of `ℚ(√a)` is injective. -/
theorem complexEmbedding_injective {a : ℚ} (ha : a < 0) :
    Function.Injective (complexEmbedding ha.le) := by
  intro x y hxy
  have hre : (x.re : ℝ) = (y.re : ℝ) := by
    simpa only [re_complexEmbedding] using congrArg Complex.re hxy
  have him : (x.im : ℝ) * √(-(a : ℝ)) = (y.im : ℝ) * √(-(a : ℝ)) := by
    simpa only [im_complexEmbedding] using congrArg Complex.im hxy
  have hsqrt : √(-(a : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (neg_pos.mpr (Rat.cast_lt_zero.mpr ha))).ne'
  ext
  · exact Rat.cast_injective hre
  · exact Rat.cast_injective (mul_right_cancel₀ hsqrt him)

end QuadraticAlgebra

namespace TauCeti.QuadraticOrder

/-- For `D ≡ 0, 1 mod 4` and any integer `f`, `f² D ≡ 0, 1 mod 4`. -/
theorem mul_sq_emod_four_eq_zero_or_one {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) (f : ℤ) :
    f ^ 2 * D % 4 = 0 ∨ f ^ 2 * D % 4 = 1 := by
  rw [Int.mul_emod, Int.sq_emod_four]
  rcases hD with hd | hd
  · simp [hd]
  · simp only [hd, mul_one]
    omega

/-- The half-integral generator `(D + √(-D) · i) / 2 ∈ ℂ` of the imaginary quadratic order of
discriminant `D`. -/
def complexGenerator (D : ℤ) : ℂ :=
  ((D : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2

/-- Definitional expansion of `complexGenerator`. -/
theorem complexGenerator_def (D : ℤ) :
    complexGenerator D = ((D : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2 := (rfl)

/-- Real part of `complexGenerator D`. -/
@[simp] theorem re_complexGenerator (D : ℤ) :
    (complexGenerator D).re = (D : ℝ) / 2 := by
  simp [complexGenerator]

/-- Imaginary part of `complexGenerator D`. -/
@[simp] theorem im_complexGenerator (D : ℤ) :
    (complexGenerator D).im = √(-(D : ℝ)) / 2 := by
  simp [complexGenerator]

/-- For `D < 0`, `complexGenerator D` lies strictly in the upper half-plane. -/
theorem im_complexGenerator_pos {D : ℤ} (hD0 : D < 0) :
    0 < (complexGenerator D).im := by
  rw [im_complexGenerator]
  exact half_pos (Real.sqrt_pos.mpr (neg_pos.mpr (Int.cast_lt_zero.mpr hD0)))

/-- The distinguished complex embedding sends `generator D = (D + ω) / 2` to
`complexGenerator D`. -/
@[simp] theorem complexEmbedding_generator {D : ℤ} (ha : (D : ℚ) ≤ 0) :
    complexEmbedding ha (generator D) = complexGenerator D := by
  rw [complexEmbedding_apply, generator_re, generator_im, complexGenerator_def]
  push_cast
  ring

/-- The complex generator satisfies `(complexGenerator D)² = (D - D²) / 4 + D · complexGenerator D`.
-/
theorem complexGenerator_mul_complexGenerator {D : ℤ} (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    complexGenerator D * complexGenerator D =
      (((D - D ^ 2) / 4 : ℤ) : ℂ) + D * complexGenerator D := by
  have h := congrArg (complexEmbedding (a := (D : ℚ)) (Int.cast_nonpos.mpr hD0))
    (generator_mul_generator D hD)
  simpa only [map_mul, map_add, map_zsmul, map_one, map_intCast, complexEmbedding_generator,
    zsmul_eq_mul, mul_one] using h

/-- **The embedded imaginary quadratic order of discriminant `D`** in `ℂ`: the image of
`toSubalgebra D hD` under the distinguished complex embedding of `ℚ(√D)`. -/
def complexOrder (D : ℤ) (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1) : Subalgebra ℤ ℂ :=
  (toSubalgebra D hD).map ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ)

/-- Definitional expansion of `complexOrder`. -/
theorem complexOrder_def (D : ℤ) (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    complexOrder D hD0 hD =
      (toSubalgebra D hD).map ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ) :=
  (rfl)

/-- Elements of `complexOrder D` are precisely the integral combinations
`m + k · complexGenerator D`. -/
theorem mem_complexOrder_iff (D : ℤ) (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1) {z : ℂ} :
    z ∈ complexOrder D hD0 hD ↔ ∃ m k : ℤ, z = m + k * complexGenerator D := by
  rw [complexOrder_def, Subalgebra.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨m, k, rfl⟩ := (mem_toSubalgebra_iff D hD w).mp hw
    refine ⟨m, k, ?_⟩
    simp [zsmul_eq_mul]
  · rintro ⟨m, k, rfl⟩
    refine ⟨m • 1 + k • generator D, (mem_toSubalgebra_iff D hD _).mpr ⟨m, k, rfl⟩, ?_⟩
    simp [zsmul_eq_mul]

/-- The generator `complexGenerator D` belongs to `complexOrder D`. -/
theorem complexGenerator_mem_complexOrder (D : ℤ) (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    complexGenerator D ∈ complexOrder D hD0 hD :=
  (mem_complexOrder_iff D hD0 hD).mpr ⟨0, 1, by simp⟩

/-- `complexOrder D` is generated over `ℤ` by `complexGenerator D`. -/
theorem complexOrder_eq_adjoin (D : ℤ) (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    complexOrder D hD0 hD = Algebra.adjoin ℤ {complexGenerator D} := by
  rw [complexOrder_def, toSubalgebra_eq_adjoin, AlgHom.map_adjoin, Set.image_singleton,
    AlgHom.restrictScalars_apply, complexEmbedding_generator]

/-- As a `ℤ`-submodule of `ℂ`, `complexOrder D` is spanned by `1` and `complexGenerator D`. -/
theorem complexOrder_toSubmodule (D : ℤ) (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    Subalgebra.toSubmodule (complexOrder D hD0 hD) =
      Submodule.span ℤ ({1, complexGenerator D} : Set ℂ) := by
  ext z
  rw [Subalgebra.mem_toSubmodule, mem_complexOrder_iff, Submodule.mem_span_pair]
  simp only [zsmul_eq_mul, mul_one]
  exact ⟨fun ⟨m, k, h⟩ ↦ ⟨m, k, h.symm⟩, fun ⟨m, k, h⟩ ↦ ⟨m, k, h.symm⟩⟩

/-- For `D < 0`, the distinguished complex embedding restricts to a `ℤ`-algebra isomorphism
`toSubalgebra D hD ≃ₐ[ℤ] complexOrder D hD0.le hD`. -/
def equivComplexOrder (D : ℤ) (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    toSubalgebra D hD ≃ₐ[ℤ] complexOrder D hD0.le hD :=
  (toSubalgebra D hD).equivMapOfInjective
    ((complexEmbedding (by exact_mod_cast hD0.le)).restrictScalars ℤ)
    (complexEmbedding_injective (by exact_mod_cast hD0))

/-- Evaluation of `equivComplexOrder` agrees with `QuadraticAlgebra.complexEmbedding`. -/
@[simp] theorem coe_equivComplexOrder_apply (D : ℤ) (hD0 : D < 0)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (z : toSubalgebra D hD) :
    (equivComplexOrder D hD0 hD z : ℂ) =
      complexEmbedding (by exact_mod_cast hD0.le) (z : QuadraticAlgebra ℚ (D : ℚ) 0) :=
  Subalgebra.coe_equivMapOfInjective_apply _ _ _ _

/-- Applying `QuadraticAlgebra.complexEmbedding` after `(equivComplexOrder D hD0 hD).symm` recovers
the complex element. -/
@[simp] theorem complexEmbedding_equivComplexOrder_symm (D : ℤ) (hD0 : D < 0)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (z : complexOrder D hD0.le hD) :
    complexEmbedding (by exact_mod_cast hD0.le)
        ((equivComplexOrder D hD0 hD).symm z : QuadraticAlgebra ℚ (D : ℚ) 0) = z := by
  rw [← coe_equivComplexOrder_apply D hD0 hD, AlgEquiv.apply_symm_apply]

/-- **Discriminant uniqueness for embedded imaginary quadratic orders**: for `D₁, D₂ < 0`,
`complexOrder D₁ = complexOrder D₂` in `ℂ` if and only if `D₁ = D₂`. -/
theorem complexOrder_eq_iff {D₁ D₂ : ℤ} (hD₁0 : D₁ < 0) (hD₁ : D₁ % 4 = 0 ∨ D₁ % 4 = 1)
    (hD₂0 : D₂ < 0) (hD₂ : D₂ % 4 = 0 ∨ D₂ % 4 = 1) :
    complexOrder D₁ hD₁0.le hD₁ = complexOrder D₂ hD₂0.le hD₂ ↔ D₁ = D₂ := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · have h₁₂ : complexGenerator D₁ ∈ complexOrder D₂ hD₂0.le hD₂ :=
      heq ▸ complexGenerator_mem_complexOrder D₁ hD₁0.le hD₁
    have h₂₁ : complexGenerator D₂ ∈ complexOrder D₁ hD₁0.le hD₁ :=
      heq.symm ▸ complexGenerator_mem_complexOrder D₂ hD₂0.le hD₂
    obtain ⟨m, k, hmk⟩ := (mem_complexOrder_iff D₂ hD₂0.le hD₂).mp h₁₂
    obtain ⟨n, l, hnl⟩ := (mem_complexOrder_iff D₁ hD₁0.le hD₁).mp h₂₁
    have him₁ : √(-(D₁ : ℝ)) / 2 = (k : ℝ) * (√(-(D₂ : ℝ)) / 2) := by
      simpa [im_complexGenerator] using congrArg Complex.im hmk
    have him₂ : √(-(D₂ : ℝ)) / 2 = (l : ℝ) * (√(-(D₁ : ℝ)) / 2) := by
      simpa [im_complexGenerator] using congrArg Complex.im hnl
    have hpos₁ : 0 < √(-(D₁ : ℝ)) / 2 := by
      simpa only [im_complexGenerator] using im_complexGenerator_pos hD₁0
    have hpos₂ : 0 < √(-(D₂ : ℝ)) / 2 := by
      simpa only [im_complexGenerator] using im_complexGenerator_pos hD₂0
    have hklR : ((k * l : ℤ) : ℝ) * (√(-(D₁ : ℝ)) / 2) = ((1 : ℤ) : ℝ) * (√(-(D₁ : ℝ)) / 2) := by
      push_cast
      linear_combination -him₁ - (k : ℝ) * him₂
    have hkl : k * l = 1 := Int.cast_injective (mul_right_cancel₀ hpos₁.ne' hklR)
    have hkpos : 0 < k := by
      have hkR : 0 < (k : ℝ) := pos_of_mul_pos_left (him₁ ▸ hpos₁) hpos₂.le
      exact_mod_cast hkR
    have hk : k = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hkl with rfl | rfl
      · rfl
      · omega
    have hsqrt : √(-(D₁ : ℝ)) = √(-(D₂ : ℝ)) := by
      rw [hk, Int.cast_one, one_mul] at him₁
      linarith
    have hsq := congrArg (fun x : ℝ ↦ x * x) hsqrt
    rw [Real.mul_self_sqrt (neg_nonneg.mpr (Int.cast_nonpos.mpr hD₁0.le)),
      Real.mul_self_sqrt (neg_nonneg.mpr (Int.cast_nonpos.mpr hD₂0.le)), neg_inj] at hsq
    exact Int.cast_injective hsq
  · rintro rfl
    rfl

/-- Relating `complexGenerator (f² D)` and `f · complexGenerator D`: their difference is the integer
`((f² - f) D) / 2`. -/
theorem complexGenerator_mul_sq (D : ℤ) (f : ℕ) :
    complexGenerator ((f : ℤ) ^ 2 * D) =
      (((((f : ℤ) ^ 2 - f) * D) / 2 : ℤ) : ℂ) + (f : ℂ) * complexGenerator D := by
  have heven : (2 : ℤ) ∣ ((f : ℤ) ^ 2 - f) * D := by
    have hf2 : (f : ℤ) ^ 2 - f = (f : ℤ) * ((f : ℤ) - 1) := by ring
    rw [hf2]
    exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp (Int.even_mul_pred_self f)) D
  obtain ⟨q, hq⟩ := heven
  have hdiv : (((f : ℤ) ^ 2 - f) * D) / 2 = q := by
    rw [hq, Int.mul_ediv_cancel_left _ two_ne_zero]
  have hsqrt : √(-((((f : ℤ) ^ 2 * D : ℤ) : ℝ))) = (f : ℝ) * √(-(D : ℝ)) := by
    have hcast : -((((f : ℤ) ^ 2 * D : ℤ) : ℝ)) = (f : ℝ) ^ 2 * (-(D : ℝ)) := by
      push_cast
      ring
    rw [hcast, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg f)]
  rw [hdiv, complexGenerator_def, complexGenerator_def, hsqrt]
  have hqC : (((f : ℤ) ^ 2 - f) * D : ℂ) = 2 * (q : ℂ) := by exact_mod_cast hq
  push_cast at hqC ⊢
  linear_combination hqC / 2

/-- **Complex lattice presentation of an order of conductor `f`**: for `D ≤ 0` with
`D ≡ 0, 1 mod 4` and any `f : ℕ`, the elements of `complexOrder (f² D)` are precisely
`m + k · (f · complexGenerator D)` for `m, k ∈ ℤ`. -/
theorem mem_complexOrder_mul_sq_iff {D : ℤ} (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (f : ℕ) {z : ℂ} :
    z ∈ complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0)
        (mul_sq_emod_four_eq_zero_or_one hD f) ↔
      ∃ m k : ℤ, z = m + k * ((f : ℂ) * complexGenerator D) := by
  rw [mem_complexOrder_iff, complexGenerator_mul_sq D f]
  set q : ℤ := (((f : ℤ) ^ 2 - f) * D) / 2
  constructor
  · rintro ⟨m, k, rfl⟩
    exact ⟨m + k * q, k, by push_cast; ring⟩
  · rintro ⟨m, k, rfl⟩
    exact ⟨m - k * q, k, by push_cast; ring⟩

/-- For `D ≤ 0` with `D ≡ 0, 1 mod 4` and any `f : ℕ`, `complexOrder (f² D)` is generated as a
`ℤ`-algebra by `f · complexGenerator D`. -/
theorem complexOrder_mul_sq_eq_adjoin {D : ℤ} (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (f : ℕ) :
    complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0)
        (mul_sq_emod_four_eq_zero_or_one hD f) =
      Algebra.adjoin ℤ {(f : ℂ) * complexGenerator D} := by
  apply le_antisymm
  · rw [complexOrder_eq_adjoin, Algebra.adjoin_le_iff, Set.singleton_subset_iff,
      complexGenerator_mul_sq D f]
    exact add_mem (Subalgebra.intCast_mem _ _) (Algebra.subset_adjoin rfl)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_complexOrder_mul_sq_iff hD0 hD f]
    exact ⟨0, 1, by simp⟩

/-- **The order `ℤ + f 𝓞 K` embeds onto `complexOrder (f² D)`**: for a negative fundamental
discriminant `D` and a positive conductor `f`, the image of `intAddMulOrder K f` under the
distinguished complex embedding of `K = ℚ(√D)` is `complexOrder (f² D) = ℤ + ℤ · f ω_D`. -/
theorem map_intAddMulOrder_eq {D : ℤ} (hD0 : D ≤ 0) [Fact (¬ IsSquare D)]
    (hfund : Int.IsFundamentalDiscr D) (f : ℕ) [NeZero f] :
    ((GlobalNumberFields.intAddMulOrder (QuadraticAlgebra ℚ (D : ℚ) 0) f).toSubalgebra).map
        ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ) =
      complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0)
        (mul_sq_emod_four_eq_zero_or_one hfund.1 f) := by
  have hmax : toSubalgebra D hfund.1 =
      integralClosure ℤ (QuadraticAlgebra ℚ (D : ℚ) 0) :=
    (toSubalgebra_eq_integralClosure_iff D hfund.1).mpr hfund
  ext z
  rw [Subalgebra.mem_map, mem_complexOrder_mul_sq_iff hD0 hfund.1 f]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, y, rfl⟩ := GlobalNumberFields.NumberFieldOrder.mem_intAddMulOrder.mp hx
    have hy : (y : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ toSubalgebra D hfund.1 :=
      hmax ▸ y.2
    obtain ⟨m, k, hmk⟩ := (mem_toSubalgebra_iff D hfund.1 _).mp hy
    refine ⟨a + f * m, k, ?_⟩
    simp only [AlgHom.restrictScalars_apply, hmk, map_add, map_intCast, map_mul, map_natCast,
      zsmul_eq_mul, mul_one, complexEmbedding_generator]
    push_cast
    ring
  · rintro ⟨m, k, rfl⟩
    have hw : k • generator D ∈ integralClosure ℤ (QuadraticAlgebra ℚ (D : ℚ) 0) := by
      rw [← hmax, mem_toSubalgebra_iff]
      exact ⟨0, k, by simp⟩
    refine ⟨m + f * (⟨k • generator D, hw⟩ :
        NumberField.RingOfIntegers (QuadraticAlgebra ℚ (D : ℚ) 0)),
      GlobalNumberFields.NumberFieldOrder.mem_intAddMulOrder.mpr ⟨m, ⟨k • generator D, hw⟩, rfl⟩,
      ?_⟩
    simp only [AlgHom.restrictScalars_apply, map_add, map_intCast, map_mul, map_natCast,
      zsmul_eq_mul, complexEmbedding_generator]
    ring

end TauCeti.QuadraticOrder
