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
`complexGenerator D = (D + √(-D) · i) / 2` and transports `TauCeti.QuadraticOrder.toSubalgebra D`
to the `ℤ`-subalgebra `complexOrder D = ℤ[complexGenerator D] ⊆ ℂ` (degenerating to `ℤ` at
`D = 0`).

When `D < 0` with `D ≡ 0, 1 mod 4`, `complexOrder D` is the embedded imaginary quadratic order of
discriminant `D` with integral basis `1, (D + √(-D) · i) / 2`: the complex embedding is injective
(`QuadraticAlgebra.complexEmbedding_injective`), so `toSubalgebra D` is `ℤ`-algebra isomorphic to
`complexOrder D` (`equivComplexOrder`), and for all `D₁, D₂ ≤ 0` with `D₁, D₂ ≡ 0, 1 mod 4` the
embedded subalgebra `complexOrder D ⊆ ℂ` uniquely determines `D` (`complexOrder_eq_iff`). For any
`f : ℕ`, `complexOrder (f² D)` equals the `ℤ`-span `ℤ + ℤ · f complexGenerator D` (the suborder of
index `f` in `complexOrder D` when `D < 0` and `f > 0`; `mem_complexOrder_sq_mul_iff`) and, when
`D` is a negative fundamental discriminant and `f > 0`, coincides with the complex image of the
order `ℤ + f 𝓞 K` of conductor `f`
(`map_toSubalgebra_intAddMulOrder_eq_complexOrder_of_isFundamentalDiscr`).

## Main definitions

* `TauCeti.QuadraticOrder.complexGenerator`: `(D + √(-D) · i) / 2 ∈ ℂ`, totalized for all `D : ℤ`
  and agreeing for `D ≤ 0` with the image of `generator D` under
  `QuadraticAlgebra.complexEmbedding`.
* `TauCeti.QuadraticOrder.complexOrder`: the `ℤ`-subalgebra `ℤ[complexGenerator D] ⊆ ℂ` for
  `D ≤ 0` with `D ≡ 0, 1 mod 4`.
* `TauCeti.QuadraticOrder.equivComplexOrder`: `toSubalgebra D ≃ₐ[ℤ] complexOrder D` for `D < 0`.

## Main results

* `TauCeti.QuadraticOrder.complexOrder_eq_bot_iff` and
  `TauCeti.QuadraticOrder.complexOrder_ne_bot`: `complexOrder D = ⊥` if and only if `D = 0`.
* `TauCeti.QuadraticOrder.complexOrder_eq_iff`: for `D₁, D₂ ≤ 0` with `D₁, D₂ ≡ 0, 1 mod 4`,
  `complexOrder D₁ = complexOrder D₂` if and only if `D₁ = D₂`.
* `TauCeti.QuadraticOrder.mem_complexOrder_sq_mul_iff` and
  `TauCeti.QuadraticOrder.complexOrder_sq_mul_eq_adjoin`: `complexOrder (f² D)` equals
  `ℤ + ℤ · f complexGenerator D = ℤ[f complexGenerator D]`.
* `TauCeti.QuadraticOrder.map_toSubalgebra_intAddMulOrder_eq_complexOrder_of_isFundamentalDiscr`:
  for a negative fundamental discriminant `D` and `f > 0`, the complex image of `ℤ + f 𝓞 K` is
  `complexOrder (f² D)`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 and §10.
-/

public noncomputable section

open Complex QuadraticAlgebra

namespace TauCeti.QuadraticOrder

/-- The complex expression `(D + √(-D) · i) / 2 ∈ ℂ`, totalized for all `D : ℤ`. When `D < 0` with
`D ≡ 0, 1 mod 4`, it is the half-integral generator of the embedded imaginary quadratic order of
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

/-- **The embedded quadratic `ℤ`-subalgebra `ℤ[complexGenerator D] ⊆ ℂ`** for `D ≤ 0` with
`D ≡ 0, 1 mod 4`: the image of `toSubalgebra D hD` under `QuadraticAlgebra.complexEmbedding`.
When `D < 0`, this is the imaginary quadratic order of discriminant `D` in `ℂ`; at `D = 0` it is
`ℤ` (`⊥`). -/
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
@[simp] theorem complexGenerator_mem_complexOrder (D : ℤ) (hD0 : D ≤ 0)
    (hD : D % 4 = 0 ∨ D % 4 = 1) :
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

/-- For `D < 0`, `complexOrder D` is strictly larger than `ℤ` (`⊥`). -/
theorem complexOrder_ne_bot {D : ℤ} (hD0 : D < 0) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    complexOrder D hD0.le hD ≠ ⊥ := by
  intro hbot
  have hmem : complexGenerator D ∈ (⊥ : Subalgebra ℤ ℂ) :=
    hbot ▸ complexGenerator_mem_complexOrder D hD0.le hD
  obtain ⟨m, hm⟩ := Algebra.mem_bot.mp hmem
  have him := congrArg Complex.im hm
  simp only [Algebra.algebraMap_eq_smul_one, zsmul_one, intCast_im] at him
  exact (im_complexGenerator_pos hD0).ne him

/-- `complexOrder D` equals `ℤ` (`⊥`) if and only if `D = 0`. -/
@[simp] theorem complexOrder_eq_bot_iff {D : ℤ} {hD0 : D ≤ 0} {hD : D % 4 = 0 ∨ D % 4 = 1} :
    complexOrder D hD0 hD = ⊥ ↔ D = 0 := by
  rcases hD0.lt_or_eq with hlt | rfl
  · exact ⟨fun h ↦ absurd h (complexOrder_ne_bot hlt hD), fun h ↦ absurd h hlt.ne⟩
  · simp [complexOrder_eq_adjoin, complexGenerator]

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

/-- **Discriminant uniqueness for embedded imaginary quadratic orders**: for `D₁, D₂ ≤ 0` with
`D₁, D₂ ≡ 0, 1 mod 4`, `complexOrder D₁ = complexOrder D₂` in `ℂ` if and only if `D₁ = D₂`. -/
@[simp] theorem complexOrder_eq_iff {D₁ D₂ : ℤ} {hD₁0 : D₁ ≤ 0}
    {hD₁ : D₁ % 4 = 0 ∨ D₁ % 4 = 1} {hD₂0 : D₂ ≤ 0} {hD₂ : D₂ % 4 = 0 ∨ D₂ % 4 = 1} :
    complexOrder D₁ hD₁0 hD₁ = complexOrder D₂ hD₂0 hD₂ ↔ D₁ = D₂ := by
  refine ⟨fun heq ↦ ?_, fun h ↦ by subst h; rfl⟩
  rcases hD₁0.lt_or_eq with h₁ | rfl
  · rcases hD₂0.lt_or_eq with h₂ | rfl
    · let e : toSubalgebra D₁ hD₁ ≃ₐ[ℤ] toSubalgebra D₂ hD₂ :=
        (equivComplexOrder D₁ h₁ hD₁).trans
          ((Subalgebra.equivOfEq _ _ heq).trans (equivComplexOrder D₂ h₂ hD₂).symm)
      calc
        D₁ = Algebra.discr ℤ (basis D₁ hD₁) := (discr_basis D₁ hD₁).symm
        _ = Algebra.discr ℤ ((basis D₁ hD₁).map e.toLinearEquiv) := by
          simpa only [Module.Basis.coe_map, AlgEquiv.coe_toLinearEquiv] using
            Algebra.discr_eq_discr_of_algEquiv (basis D₁ hD₁) e
        _ = Algebra.discr ℤ (basis D₂ hD₂) :=
          Algebra.discr_eq_discr (toSubalgebra D₂ hD₂) _ (basis D₂ hD₂)
        _ = D₂ := discr_basis D₂ hD₂
    · exact absurd (heq.trans (complexOrder_eq_bot_iff.mpr rfl)) (complexOrder_ne_bot h₁ hD₁)
  · exact (complexOrder_eq_bot_iff.mp (heq.symm.trans (complexOrder_eq_bot_iff.mpr rfl))).symm

/-- Relating `complexGenerator (f² D)` and `f · complexGenerator D`: their difference is the integer
`((f² - f) D) / 2`. -/
theorem complexGenerator_sq_mul (D : ℤ) (f : ℕ) :
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

/-- **Span presentation of `complexOrder (f² D)`**: for `D ≤ 0` with `D ≡ 0, 1 mod 4` and any
`f : ℕ`, the elements of `complexOrder (f² D)` are precisely `m + k · (f · complexGenerator D)` for
`m, k ∈ ℤ` (the suborder of index `f` in `complexOrder D` when `D < 0` and `f > 0`, and the order
of conductor `f` in `𝓞 K` when `D` is a negative fundamental discriminant). -/
theorem mem_complexOrder_sq_mul_iff {D : ℤ} (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (f : ℕ) {z : ℂ} :
    z ∈ complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0)
        (sq_mul_emod_four_eq_zero_or_one hD f) ↔
      ∃ m k : ℤ, z = m + k * ((f : ℂ) * complexGenerator D) := by
  rw [mem_complexOrder_iff, complexGenerator_sq_mul D f]
  set q : ℤ := (((f : ℤ) ^ 2 - f) * D) / 2
  constructor
  · rintro ⟨m, k, rfl⟩
    exact ⟨m + k * q, k, by push_cast; ring⟩
  · rintro ⟨m, k, rfl⟩
    exact ⟨m - k * q, k, by push_cast; ring⟩

/-- For `D ≤ 0` with `D ≡ 0, 1 mod 4` and any `f : ℕ`, `complexOrder (f² D)` is generated as a
`ℤ`-algebra by `f · complexGenerator D`. -/
theorem complexOrder_sq_mul_eq_adjoin {D : ℤ} (hD0 : D ≤ 0) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (f : ℕ) :
    complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0)
        (sq_mul_emod_four_eq_zero_or_one hD f) =
      Algebra.adjoin ℤ {(f : ℂ) * complexGenerator D} := by
  apply le_antisymm
  · rw [complexOrder_eq_adjoin, Algebra.adjoin_le_iff, Set.singleton_subset_iff,
      complexGenerator_sq_mul D f]
    exact add_mem (Subalgebra.intCast_mem _ _) (Algebra.subset_adjoin rfl)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_complexOrder_sq_mul_iff hD0 hD f]
    exact ⟨0, 1, by simp⟩

/-- **The order `ℤ + f 𝓞 K` embeds onto `complexOrder (f² D)`**: for a negative fundamental
discriminant `D` and a positive conductor `f`, the image of `intAddMulOrder K f` under the
distinguished complex embedding of `K = ℚ(√D)` is `complexOrder (f² D) = ℤ + ℤ · f ω_D`. -/
theorem map_toSubalgebra_intAddMulOrder_eq_complexOrder_of_isFundamentalDiscr
    {D : ℤ} (hD0 : D ≤ 0) [Fact (¬ IsSquare D)]
    (hfund : Int.IsFundamentalDiscr D) (f : ℕ) [NeZero f] :
    ((GlobalNumberFields.intAddMulOrder (QuadraticAlgebra ℚ (D : ℚ) 0) f).toSubalgebra).map
        ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ) =
      complexOrder ((f : ℤ) ^ 2 * D)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD0)
        (sq_mul_emod_four_eq_zero_or_one hfund.1 f) := by
  have hmax : toSubalgebra D hfund.1 =
      integralClosure ℤ (QuadraticAlgebra ℚ (D : ℚ) 0) :=
    (toSubalgebra_eq_integralClosure_iff D hfund.1).mpr hfund
  ext z
  rw [Subalgebra.mem_map, mem_complexOrder_sq_mul_iff hD0 hfund.1 f]
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
