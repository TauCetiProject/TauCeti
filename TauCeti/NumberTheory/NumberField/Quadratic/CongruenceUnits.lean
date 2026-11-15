/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
public import TauCeti.NumberTheory.NumberField.Quadratic.ResidueUnits
public import TauCeti.NumberTheory.NumberField.Quadratic.Units
public import TauCeti.NumberTheory.QuadraticOrder.MatrixQuotient

/-!
# Canonical period presentations, unit congruences, and residue-unit counts in quadratic fields

Let `K` be a quadratic number field (`finrank ℚ K = 2`) of discriminant `D = NumberField.discr K`.
This file supplies three ingredients connecting the intrinsic arithmetic of `𝓞 K` to the
multiplication-matrix quotients of `TauCeti.NumberTheory.QuadraticOrder.MatrixQuotient`:

1. **The canonical `(1, τ_D)` maximal-order presentation.** Setting
   `periodCoeffB D = 0` and `periodCoeffC D = -D / 4` when `D ≡ 0 (mod 4)`, and
   `periodCoeffB D = -3` and `periodCoeffC D = (9 - D) / 4` when `D ≡ 1 (mod 4)` (corresponding to
   the monic quadratic `X² + B X + C` of `τ_D = √D / 2` or `(3 + √D) / 2`), the quadratic algebra
   `QuadraticAlgebra ℤ (-periodCoeffC D) (-periodCoeffB D)` has discriminant `D` and is isomorphic
   as a `ℤ`-algebra to `𝓞 K` (`exists_ringOfIntegers_periodAlgEquiv`). When `2` is inert and `3`
   ramifies in `K`, `D ≡ 21 (mod 24)` (`emod_twenty_four_eq_twenty_one_iff`) and both reduced
   parameters `-periodCoeffC D` and `-periodCoeffB D` vanish in `ZMod 3`.
2. **Global units congruent to one modulo `(N)` in imaginary quadratic fields.** When `K` is
   totally complex, `D ≤ -3`; in any integral quadratic algebra of negative discriminant, a unit
   congruent to `1` modulo `(N)` is arbitrary for `N = 1`, lies in `{±1}` for `N = 2`, and is `1`
   for `3 ≤ N` (`ker_unitsMap_quotient_span_natCast`). Consequently the kernel of
   `(𝓞 K)ˣ →* (𝓞 K ⧸ (N))ˣ` is `⊤` at `N = 1`, `Subgroup.zpowers (-1)` at `N = 2`, and `⊥` for
   `3 ≤ N` (`ker_unitsMap_ringOfIntegers_quotient_span_natCast`), with explicit index formulas
   covering `D = -4` and `D = -3` alongside `D < -4`.
3. **Explicit residue-unit counts at levels `2`, `3`, `6`, and `8`.** Specializing
   `card_units_quotient_span_natCast_of_prime` and `card_units_quotient_span_natCast_mul_prod`
   evaluates `#(𝓞 K ⧸ (N))ˣ` in closed form in terms of `χ_D(2)` and `χ_D(3)`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open Ideal Module Polynomial NumberField QuadraticAlgebra
open scoped NumberField QuadraticAlgebra
open TauCeti.Multiquadratic (fundamentalDiscriminantChar isFundamentalDiscr_discr
  fundamentalDiscriminantChar_isQuadratic fundamentalDiscriminantChar_two
  fundamentalDiscriminantChar_natCast_eq_legendreSym)

namespace QuadraticAlgebra

/-- In an integral quadratic algebra of negative discriminant, every unit is either `±1` or has
imaginary coordinate `±1` (the latter occurring only at discriminants `-3` and `-4`). -/
private theorem units_re_or_im_of_discr_lt_zero {a b : ℤ} (hd : discr a b < 0)
    (u : (QuadraticAlgebra ℤ a b)ˣ) :
    (u = 1 ∨ u = -1) ∨ ((u : QuadraticAlgebra ℤ a b).im = 1 ∨
      (u : QuadraticAlgebra ℤ a b).im = -1) := by
  have hd3 : discr a b ≤ -3 := by
    have := discr_emod_four_eq_zero_or_one a b
    omega
  have hnorm_unit : IsUnit (norm (u : QuadraticAlgebra ℤ a b)) :=
    isUnit_iff_norm_isUnit.mp u.isUnit
  have hnorm_nonneg : 0 ≤ norm (u : QuadraticAlgebra ℤ a b) :=
    norm_nonneg_of_discr_nonpos hd.le _
  have hnorm : norm (u : QuadraticAlgebra ℤ a b) = 1 := by
    rcases Int.isUnit_iff.mp hnorm_unit with h1 | h1 <;> omega
  have h4 := four_mul_norm_eq (u : QuadraticAlgebra ℤ a b)
  rw [hnorm, mul_one] at h4
  by_cases him : (u : QuadraticAlgebra ℤ a b).im = 0
  · left
    rw [him, trace_def, him] at h4
    have hre : (u : QuadraticAlgebra ℤ a b).re = 1 ∨ (u : QuadraticAlgebra ℤ a b).re = -1 :=
      sq_eq_one_iff.mp (by nlinarith)
    rcases hre with h1 | h1
    · left; apply Units.ext; ext <;> simp [h1, him]
    · right; apply Units.ext; ext <;> simp [h1, him]
  · right
    have him_pos : 0 < (u : QuadraticAlgebra ℤ a b).im ^ 2 := sq_pos_iff.mpr him
    have hbd : 3 * (u : QuadraticAlgebra ℤ a b).im ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (trace (u : QuadraticAlgebra ℤ a b)),
        sq_nonneg (u : QuadraticAlgebra ℤ a b).im]
    have him_sq : (u : QuadraticAlgebra ℤ a b).im ^ 2 = 1 := by omega
    exact sq_eq_one_iff.mp him_sq

/-- **Kernel of unit reduction modulo `(N)` for `discr a b < 0`**: for `N ≠ 0`, the units of
`QuadraticAlgebra ℤ a b` congruent to `1` modulo `(N)` are all units for `N = 1`, `{±1}` for
`N = 2`, and `{1}` for `3 ≤ N` — including at discriminants `-3` and `-4`. -/
theorem ker_unitsMap_quotient_span_natCast {a b : ℤ} (hd : discr a b < 0) {N : ℕ} (hN : N ≠ 0) :
    (Units.map (Ideal.Quotient.mk (Ideal.span {(N : QuadraticAlgebra ℤ a b)}) :
        QuadraticAlgebra ℤ a b →*
          QuadraticAlgebra ℤ a b ⧸ Ideal.span {(N : QuadraticAlgebra ℤ a b)})).ker =
      if N = 1 then ⊤ else if N = 2 then Subgroup.zpowers (-1) else ⊥ := by
  have hmem (u : (QuadraticAlgebra ℤ a b)ˣ) :
      u ∈ (Units.map (Ideal.Quotient.mk (Ideal.span {(N : QuadraticAlgebra ℤ a b)}) :
          QuadraticAlgebra ℤ a b →*
            QuadraticAlgebra ℤ a b ⧸ Ideal.span {(N : QuadraticAlgebra ℤ a b)})).ker ↔
        (N : ℤ) ∣ ((u : QuadraticAlgebra ℤ a b).re - 1) ∧
          (N : ℤ) ∣ (u : QuadraticAlgebra ℤ a b).im := by
    rw [MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, MonoidHom.coe_ofClass, Units.val_one,
      ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, mem_span_natCast_iff]
    simp
  split_ifs with h1 h2
  · subst h1
    rw [Subgroup.eq_top_iff']
    intro u
    rw [hmem]
    simp
  · subst h2
    refine le_antisymm (fun u hu ↦ ?_) ?_
    · obtain ⟨_, him⟩ := (hmem u).mp hu
      rcases units_re_or_im_of_discr_lt_zero hd u with (rfl | rfl) | (him1 | him1)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · rw [him1] at him; omega
      · rw [him1] at him; omega
    · rw [Subgroup.zpowers_le, hmem]
      simp
  · have hN3 : 3 ≤ N := by omega
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    obtain ⟨hre, him⟩ := (hmem u).mp hu
    rcases units_re_or_im_of_discr_lt_zero hd u with (rfl | rfl) | (him1 | him1)
    · rfl
    · simp only [Units.val_neg, Units.val_one, re_neg, re_one] at hre
      have h2 : (N : ℤ) ∣ 2 := by
        convert dvd_neg.mpr hre using 1
        norm_num
      have hle := Int.le_of_dvd (by omega) h2
      omega
    · rw [him1] at him
      have hle := Int.le_of_dvd (by omega) him
      omega
    · rw [him1] at him
      have hle := Int.le_of_dvd (by omega) (dvd_neg.mpr him)
      omega

end QuadraticAlgebra

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Canonical `(1, τ_D)` polynomial coefficients and maximal-order isomorphism -/

/-- Linear coefficient `B` of the canonical monic quadratic `X² + B X + C` satisfied by the
period generator `τ_D = √D / 2` (`D ≡ 0 (mod 4)`) or `τ_D = (3 + √D) / 2` (`D ≡ 1 (mod 4)`). -/
def periodCoeffB (D : ℤ) : ℤ :=
  if D % 4 = 0 then 0 else -3

/-- Constant coefficient `C` of the canonical monic quadratic `X² + B X + C` satisfied by `τ_D`. -/
def periodCoeffC (D : ℤ) : ℤ :=
  if D % 4 = 0 then -D / 4 else (9 - D) / 4

/-- Unfolding lemma for `periodCoeffB`. -/
theorem periodCoeffB_def (D : ℤ) :
    periodCoeffB D = if D % 4 = 0 then 0 else -3 :=
  (rfl)

/-- Unfolding lemma for `periodCoeffC`. -/
theorem periodCoeffC_def (D : ℤ) :
    periodCoeffC D = if D % 4 = 0 then -D / 4 else (9 - D) / 4 :=
  (rfl)

/-- For `D ≡ 0, 1 (mod 4)`, the quadratic algebra `QuadraticAlgebra ℤ (-periodCoeffC D)
(-periodCoeffB D)` has discriminant `D`. -/
theorem discr_neg_periodCoeff (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    QuadraticAlgebra.discr (-periodCoeffC D) (-periodCoeffB D) = D := by
  rw [QuadraticAlgebra.discr_def, periodCoeffB_def, periodCoeffC_def]
  rcases hD with h0 | h1 <;> split_ifs <;> norm_num <;> omega

/-- Value of `-periodCoeffC (-4)` (the Gaussian discriminant). -/
@[simp]
theorem neg_periodCoeffC_neg_four : -periodCoeffC (-4) = -1 := by decide

/-- Value of `-periodCoeffB (-4)` (the Gaussian discriminant). -/
@[simp]
theorem neg_periodCoeffB_neg_four : -periodCoeffB (-4) = 0 := by decide

/-- Value of `-periodCoeffC (-3)` (the Eisenstein discriminant). -/
@[simp]
theorem neg_periodCoeffC_neg_three : -periodCoeffC (-3) = -3 := by decide

/-- Value of `-periodCoeffB (-3)` (the Eisenstein discriminant). -/
@[simp]
theorem neg_periodCoeffB_neg_three : -periodCoeffB (-3) = 3 := by decide

/-- When `D ≡ 21 (mod 24)`, both `-periodCoeffC D` and `-periodCoeffB D` vanish in `ZMod 3`. -/
theorem neg_periodCoeff_zmod_three_of_emod_twenty_four {D : ℤ} (hD : D % 24 = 21) :
    ((-periodCoeffC D : ℤ) : ZMod 3) = 0 ∧ ((-periodCoeffB D : ℤ) : ZMod 3) = 0 := by
  have h4 : D % 4 ≠ 0 := by omega
  have hC : (3 : ℤ) ∣ -periodCoeffC D := by
    simp only [periodCoeffC_def, h4, ↓reduceIte]
    omega
  have hB : (3 : ℤ) ∣ -periodCoeffB D := by
    simp only [periodCoeffB_def, h4, ↓reduceIte]
    omega
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hC,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hB⟩

/-- For a fundamental discriminant `D`, `2` is inert (`χ_D(2) = -1`) and `3` ramifies
(`χ_D(3) = 0`) if and only if `D ≡ 21 (mod 24)`. -/
theorem emod_twenty_four_eq_twenty_one_iff {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantChar D hD 2 = -1 ∧
        fundamentalDiscriminantChar D hD 3 = 0 ↔
      D % 24 = 21 := by
  have h4 := hD.emod_four_eq_zero_or_one
  have h2 : fundamentalDiscriminantChar D hD 2 = -1 ↔ D % 8 = 5 := by
    rw [fundamentalDiscriminantChar_two, ZMod.χ₈_int_eq_if_mod_eight]
    split_ifs <;> simp <;> omega
  have h3 : fundamentalDiscriminantChar D hD 3 = 0 ↔ D % 3 = 0 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [show (3 : ZMod D.natAbs) = ((3 : ℕ) : ℤ) by norm_num,
      fundamentalDiscriminantChar_natCast_eq_legendreSym hD (by decide),
      legendreSym.eq_zero_iff 3 D, ZMod.intCast_zmod_eq_zero_iff_dvd]
    omega
  rw [h2, h3]
  omega

/-- An algebraic integer generating `𝓞 K` over `ℤ` and not lying in `ℤ` presents `𝓞 K` as an
integral quadratic algebra. -/
private noncomputable def ringOfIntegersAlgEquivOfAdjoin {g : 𝓞 K} {a b : ℤ}
    (hg_sq : g * g = a • 1 + b • g) (hg_top : Algebra.adjoin ℤ {g} = ⊤)
    (hg_notMem : (g : K) ∉ (algebraMap ℚ K).range) :
    𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b := by
  let f : QuadraticAlgebra ℤ a b →ₐ[ℤ] 𝓞 K := QuadraticAlgebra.lift ⟨g, hg_sq⟩
  have hsurj : Function.Surjective f := (QuadraticAlgebra.lift_surjective_iff _).mpr hg_top
  have hinj : Function.Injective f := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro z hz
    have hzK : (z.re : K) + (z.im : K) * (g : K) = 0 := by
      have := congrArg (algebraMap (𝓞 K) K) hz
      simpa [f, zsmul_eq_mul] using this
    have him : z.im = 0 := by
      by_contra hne
      apply hg_notMem
      refine ⟨-(z.re : ℚ) / (z.im : ℚ), ?_⟩
      have hrat : algebraMap ℚ K (-(z.re : ℚ) / (z.im : ℚ)) = -(z.re : K) / (z.im : K) := by
        simp
      rw [hrat, div_eq_iff (by exact_mod_cast hne)]
      linear_combination -hzK
    have hre : z.re = 0 := by
      simpa [him] using hzK
    exact QuadraticAlgebra.ext hre him
  exact (AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm

/-- **Canonical period-algebra presentation of `𝓞 K`**: for any quadratic number field `K` of
discriminant `D = discr K`, `𝓞 K` is isomorphic as a `ℤ`-algebra to
`QuadraticAlgebra ℤ (-periodCoeffC D) (-periodCoeffB D)`. -/
theorem exists_ringOfIntegers_periodAlgEquiv (hK : finrank ℚ K = 2) :
    Nonempty (𝓞 K ≃ₐ[ℤ]
      QuadraticAlgebra ℤ (-periodCoeffC (discr K)) (-periodCoeffB (discr K))) := by
  obtain ⟨θ, d, hmin, hgen, hsf⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  have hD4 := (isFundamentalDiscr_discr hK).emod_four_eq_zero_or_one
  by_cases hd4 : d % 4 = 1
  · set ω₀ := halfGen hmin hd4
    have hdisc : discr K = d := discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4
    have hω_sq : ω₀ * ω₀ = ((d - 1) / 4) • (1 : 𝓞 K) + (1 : ℤ) • ω₀ := by
      have haeval := minpoly.aeval ℤ ω₀
      have hc : (1 - d) / 4 = -((d - 1) / 4) := by omega
      rw [minpoly_halfGen hmin hd4, hc] at haeval
      simp only [map_add, map_sub, map_pow, map_neg, map_intCast, aeval_X, zsmul_eq_mul,
        eq_intCast, Int.cast_one, one_mul] at haeval ⊢
      linear_combination haeval
    have hω_notMem : (ω₀ : K) ∉ (algebraMap ℚ K).range := by
      rintro ⟨q, hq⟩
      exact gen_notMem_range hmin ⟨2 * q - 1, by
        rw [coe_halfGen] at hq
        rw [map_sub, map_mul, map_one, map_ofNat, hq]
        ring⟩
    let e₁ := ringOfIntegersAlgEquivOfAdjoin hω_sq
      (adjoin_halfGen_eq_top_of_mod_four_eq_one hmin hgen hsf hd4) hω_notMem
    obtain ⟨e₂⟩ := (QuadraticAlgebra.nonempty_algEquiv_int_iff (a := (d - 1) / 4) (b := 1)
      (a' := -periodCoeffC (discr K)) (b' := -periodCoeffB (discr K))).mpr <| by
        rw [discr_neg_periodCoeff (discr K) hD4, hdisc, QuadraticAlgebra.discr_def]
        omega
    exact ⟨e₁.trans e₂⟩
  · have hdisc : discr K = 4 * d := discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf hd4
    have hθ_sq : θ * θ = d • (1 : 𝓞 K) + (0 : ℤ) • θ := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      simpa [sq, zsmul_eq_mul, RingOfIntegers.coe_eq_algebraMap] using coe_gen_sq hmin
    let e₁ := ringOfIntegersAlgEquivOfAdjoin hθ_sq
      (adjoin_gen_eq_top_of_mod_four_ne_one hmin hgen hsf hd4) (gen_notMem_range hmin)
    obtain ⟨e₂⟩ := (QuadraticAlgebra.nonempty_algEquiv_int_iff (a := d) (b := 0)
      (a' := -periodCoeffC (discr K)) (b' := -periodCoeffB (discr K))).mpr <| by
        rw [discr_neg_periodCoeff (discr K) hD4, hdisc, QuadraticAlgebra.discr_def]
        ring
    exact ⟨e₁.trans e₂⟩

/-! ### Imaginary quadratic discriminants and unit congruences -/

/-- Every imaginary quadratic field has negative discriminant (`discr K ≤ -3`). -/
theorem discr_lt_zero_of_isTotallyComplex [IsTotallyComplex K] (hK : finrank ℚ K = 2) :
    discr K < 0 := by
  obtain ⟨θ, d, hmin, hgen, hsf, hd⟩ :=
    exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top_of_isTotallyComplex hK
  by_cases hd4 : d % 4 = 1
  · rw [discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4]
    exact hd
  · rw [discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf hd4]
    omega

/-- For an imaginary quadratic field, `discr K < -4` holds precisely away from `-4` and `-3`. -/
theorem discr_lt_neg_four_iff [IsTotallyComplex K] (hK : finrank ℚ K = 2) :
    discr K < -4 ↔ discr K ≠ -4 ∧ discr K ≠ -3 := by
  have hlt := discr_lt_zero_of_isTotallyComplex hK
  have h4 := (isFundamentalDiscr_discr hK).emod_four_eq_zero_or_one
  omega

/-- **Kernel of `(𝓞 K)ˣ →* (𝓞 K ⧸ (N))ˣ` in an imaginary quadratic field**: for `N ≠ 0`, the
units of `𝓞 K` congruent to `1` modulo `(N)` form `⊤` at `N = 1`, `Subgroup.zpowers (-1)` at
`N = 2`, and `⊥` for `3 ≤ N`. -/
theorem ker_unitsMap_ringOfIntegers_quotient_span_natCast [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {N : ℕ} (hN : N ≠ 0) :
    (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) :
        𝓞 K →* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})).ker =
      if N = 1 then ⊤ else if N = 2 then Subgroup.zpowers (-1) else ⊥ := by
  obtain ⟨e⟩ := exists_ringOfIntegers_periodAlgEquiv hK
  have hd : QuadraticAlgebra.discr (-periodCoeffC (discr K)) (-periodCoeffB (discr K)) < 0 := by
    rw [discr_neg_periodCoeff (discr K) (isFundamentalDiscr_discr hK).emod_four_eq_zero_or_one]
    exact discr_lt_zero_of_isTotallyComplex hK
  have hker := QuadraticAlgebra.ker_unitsMap_quotient_span_natCast hd hN
  let A := QuadraticAlgebra ℤ (-periodCoeffC (discr K)) (-periodCoeffB (discr K))
  let eu : (𝓞 K)ˣ ≃* Aˣ := Units.mapEquiv e.toRingEquiv.toMulEquiv
  have hcomap :
      (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) :
          𝓞 K →* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})).ker =
        (Units.map (Ideal.Quotient.mk (Ideal.span {(N : A)}) :
          A →* A ⧸ Ideal.span {(N : A)})).ker.comap eu.toMonoidHom := by
    ext u
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, Units.ext_iff, Units.coe_map,
      MonoidHom.coe_ofClass, Units.val_one,
      ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun ⟨w, hw⟩ ↦ ?_⟩
    · refine ⟨e w, ?_⟩
      simpa [eu] using congrArg e hw
    · refine ⟨e.symm w, ?_⟩
      have := congrArg e.symm hw
      simpa [eu] using this
  rw [hcomap, hker]
  split_ifs with h1 h2
  · exact Subgroup.comap_top _
  · have heu : eu (-1) = -1 := Units.ext (by simp [eu])
    ext u
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨k, hk⟩ ↦ ⟨k, eu.injective (by simpa [heu] using hk)⟩,
      fun ⟨k, hk⟩ ↦ ⟨k, by simpa [heu] using congrArg eu hk⟩⟩
  · exact MonoidHom.ker_eq_bot_iff _ |>.mpr eu.injective

/-- The subgroup `Subgroup.zpowers (-1)` of `(𝓞 K)ˣ` has order `2`. -/
theorem card_zpowers_neg_one_units_ringOfIntegers :
    Nat.card (Subgroup.zpowers (-1 : (𝓞 K)ˣ)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  refine orderOf_eq_prime (Units.ext (by simp)) fun h ↦ ?_
  have h0 : (-1 : 𝓞 K) = 1 := Units.ext_iff.mp h
  have h2 : (2 : 𝓞 K) = 0 := by linear_combination -h0
  exact two_ne_zero h2

/-- Explicit residue-unit count `#(𝓞 K ⧸ (2))ˣ = 2 - χ_D(2)` in a quadratic field. -/
theorem card_units_quotient_span_two (hK : finrank ℚ K = 2) :
    (Nat.card (𝓞 K ⧸ span {(2 : 𝓞 K)})ˣ : ℤ) =
      2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2 := by
  simpa using card_units_quotient_span_natCast_of_prime hK 2

/-- Explicit residue-unit count `#(𝓞 K ⧸ (3))ˣ = 2 * (3 - χ_D(3))` in a quadratic field. -/
theorem card_units_quotient_span_three (hK : finrank ℚ K = 2) :
    (Nat.card (𝓞 K ⧸ span {(3 : 𝓞 K)})ˣ : ℤ) =
      2 * (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3) := by
  simpa using card_units_quotient_span_natCast_of_prime hK 3

/-- Explicit residue-unit count `#(𝓞 K ⧸ (6))ˣ = 2 * (2 - χ_D(2)) * (3 - χ_D(3))` in a quadratic
field. -/
theorem card_units_quotient_span_six (hK : finrank ℚ K = 2) :
    (Nat.card (𝓞 K ⧸ span {(6 : 𝓞 K)})ˣ : ℤ) =
      2 * (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2) *
        (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3) := by
  have h := card_units_quotient_span_natCast_mul_prod hK (f := 6) (by decide)
  have hpf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by decide) (by decide),
      Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    rfl
  rw [hpf, Finset.prod_pair (by decide), Finset.prod_pair (by decide)] at h
  push_cast at h
  linarith

/-- Explicit residue-unit count `#(𝓞 K ⧸ (8))ˣ = 16 * (2 - χ_D(2))` in a quadratic field. -/
theorem card_units_quotient_span_eight (hK : finrank ℚ K = 2) :
    (Nat.card (𝓞 K ⧸ span {(8 : 𝓞 K)})ˣ : ℤ) =
      16 * (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2) := by
  have h := card_units_quotient_span_natCast_mul_prod hK (f := 8) (by decide)
  have hpf : (8 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 3) (by decide) Nat.prime_two
  rw [hpf, Finset.prod_singleton, Finset.prod_singleton] at h
  push_cast at h
  linarith

end TauCeti.NumberField
