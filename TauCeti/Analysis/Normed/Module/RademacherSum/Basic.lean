/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.RademacherSum.Moment
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Second moments of finite Rademacher sums

The Rademacher second moment `R₂(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖²)^(1/2)` of a finite family `y` in a
seminormed group is the quadratic mean of the norms of its signed sums, the signs `ε : ι → ℤˣ`
being averaged uniformly over the finite sign cube. It agrees with `TauCeti.rademacherMoment 2 y`
and is the quantity in which Rademacher type and cotype are defined. Being a finite average, it
needs neither completeness, nor scalars, nor a measure space.

We record the specialization of the general moment API to `R₂` — absolute homogeneity, invariance
under reindexing and zero-padding, comparison along bounded additive maps, and the summand bounds
`‖yᵢ‖ ≤ R₂(y) ≤ ∑ i, ‖yᵢ‖` — and evaluate `R₂` in inner product spaces. Because distinct signs are
orthogonal on average, in an inner product space `R₂(y)` is the `ℓ²` norm `(∑ i, ‖yᵢ‖²)^(1/2)` of
the family; in particular `n` copies of a vector `y` of a real normed space have `R₂ = √n ‖y‖`.

## Main declarations

* `TauCeti.rademacherCoeff`: the first Rademacher Fourier coefficient linear map.
* `TauCeti.rademacherSecondMoment`: the Rademacher second moment `R₂(y)`.
* `TauCeti.rademacherMoment_two`: `rademacherMoment 2 y = rademacherSecondMoment y`.
* `TauCeti.rademacherSecondMoment_comp_equiv`: invariance under reindexing.
* `TauCeti.rademacherSecondMoment_sumElim_zero`: invariance under padding with zeros.
* `TauCeti.rademacherSecondMoment_smul_const`: `R₂(aᵢ • y) = R₂(a) ‖y‖`.
* `TauCeti.norm_le_rademacherSecondMoment` and `TauCeti.rademacherSecondMoment_le_sum_norm`:
  `‖yᵢ‖ ≤ R₂(y) ≤ ∑ i, ‖yᵢ‖`, the lower bound in real normed spaces.
* `TauCeti.rademacherSecondMoment_eq_norm_toLp_two`: in an inner product space `R₂(y)` is the
  `ℓ²` norm of `y`.
* `TauCeti.rademacherSecondMoment_const`: `card ι` copies of `y` have `R₂ = √(card ι) ‖y‖`.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012), §9.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §6.2.
-/

public section

noncomputable section

open Finset
open scoped BigOperators

namespace TauCeti

section Signs

variable {ι : Type*} [Fintype ι]

/-- Over the sign cube, summing a function that negates when flipping the `i`-th sign gives
`0`. -/
theorem sum_eq_zero_of_mulSingle_neg {M : Type*} [DecidableEq ι] [AddCommGroup M] (i : ι)
    (f : (ι → ℤˣ) → M) (hf : ∀ ε, f (Pi.mulSingle i (-1) * ε) = -f ε) :
    ∑ ε : ι → ℤˣ, f ε = 0 :=
  Finset.sum_involution (fun ε _ ↦ Pi.mulSingle i (-1) * ε)
    (fun ε _ ↦ by simp [hf ε])
    (fun ε _ _ h ↦ absurd (congrFun h i) (by simp))
    (fun _ _ ↦ Finset.mem_univ _)
    fun ε _ ↦ funext fun k ↦ by by_cases hk : k = i <;> simp [hk]

/-- Over the sign cube, summing `ε i • (ε j • m)` gives `card (ι → ℤˣ) • m` on the diagonal and
`0` off it. -/
theorem sum_units_smul_units_smul {M : Type*} [DecidableEq ι] [AddCommGroup M] (i j : ι) (m : M) :
    ∑ ε : ι → ℤˣ, ε i • (ε j • m) = if i = j then Fintype.card (ι → ℤˣ) • m else 0 := by
  split_ifs with hij
  · subst hij; simp [← mul_smul]
  · exact sum_eq_zero_of_mulSingle_neg i (fun ε ↦ ε i • (ε j • m)) fun ε ↦ by
      simp [Ne.symm hij, ← mul_smul]

/-- Averaged over the sign cube, the product of two signs is `1` on the diagonal and `0` off it:
distinct Rademacher signs are orthogonal. -/
theorem expect_units_apply_mul_apply [DecidableEq ι] (i j : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) = if i = j then 1 else 0 := by
  have h := sum_units_smul_units_smul (M := ℝ) i j 1
  simp only [Units.smul_def, zsmul_eq_mul, mul_one, nsmul_eq_mul] at h
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, h]
  split_ifs <;> simp

/-- Summing `ε i • ∑ j, ε j • x j` over the sign cube recovers `card (ι → ℤˣ) • x i`. -/
theorem sum_units_smul_sum_units_smul {M : Type*} [DecidableEq ι] [AddCommGroup M] (x : ι → M)
    (i : ι) : ∑ ε : ι → ℤˣ, ε i • ∑ j, ε j • x j = Fintype.card (ι → ℤˣ) • x i := by
  simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]; simp [sum_units_smul_units_smul]

/-- The first Rademacher Fourier coefficient linear map sending `Φ : (ι → ℤˣ) → M` to the
family `k ↦ |ι → ℤˣ|⁻¹ • ∑ ε, ε k • Φ ε`. -/
def rademacherCoeff (𝕜 : Type*) {M : Type*} [DecidableEq ι] [DivisionSemiring 𝕜]
    [AddCommGroup M] [Module 𝕜 M] : ((ι → ℤˣ) → M) →ₗ[𝕜] (ι → M) where
  toFun Φ k := (Fintype.card (ι → ℤˣ) : 𝕜)⁻¹ • ∑ ε : ι → ℤˣ, ε k • Φ ε
  map_add' Φ Ψ := by ext k; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c Φ := by
    ext k
    simp only [Pi.smul_apply, RingHom.id_apply]
    have hcomm (ε : ι → ℤˣ) : ε k • (c • Φ ε) = c • (ε k • Φ ε) := by
      rw [Units.smul_def, Units.smul_def, smul_comm]
    rw [Finset.smul_sum]
    simp_rw [hcomm, ← Finset.smul_sum]
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul,
      (Nat.cast_commute (Fintype.card (ι → ℤˣ)) c).inv_left₀.eq]

/-- Evaluating the `k`-th Rademacher Fourier coefficient of `Φ`. -/
theorem rademacherCoeff_apply (𝕜 : Type*) {M : Type*} [DecidableEq ι] [DivisionSemiring 𝕜]
    [AddCommGroup M] [Module 𝕜 M] (Φ : (ι → ℤˣ) → M) (k : ι) :
    rademacherCoeff 𝕜 Φ k = (Fintype.card (ι → ℤˣ) : 𝕜)⁻¹ • ∑ ε : ι → ℤˣ, ε k • Φ ε :=
  (rfl)

/-- Extracting the Rademacher coefficients of a Rademacher sum `ε ↦ ∑ j, ε j • x j` recovers
`x` in any module over a characteristic-zero division semiring. -/
@[simp]
theorem rademacherCoeff_sum_units_smul {𝕜 M : Type*} [DecidableEq ι] [DivisionSemiring 𝕜]
    [CharZero 𝕜] [AddCommGroup M] [Module 𝕜 M] (x : ι → M) :
    rademacherCoeff 𝕜 (fun ε : ι → ℤˣ ↦ ∑ j, ε j • x j) = x := by
  ext i
  rw [rademacherCoeff_apply, sum_units_smul_sum_units_smul, ← Nat.cast_smul_eq_nsmul 𝕜,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- A `𝕜`-linear map commutes with taking Rademacher Fourier coefficients. -/
theorem map_rademacherCoeff {𝕜 M N F : Type*} [DecidableEq ι] [DivisionSemiring 𝕜]
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N] [FunLike F M N]
    [LinearMapClass F 𝕜 M N] (f : F) (Φ : (ι → ℤˣ) → M) (k : ι) :
    f (rademacherCoeff 𝕜 Φ k) = rademacherCoeff 𝕜 (fun ε ↦ f (Φ ε)) k := by
  simp [rademacherCoeff_apply, map_smul, map_sum, Units.smul_def]

/-- Taking `star` commutes with taking Rademacher Fourier coefficients over a trivially starred
division semiring. -/
@[simp]
theorem star_rademacherCoeff {𝕜 M : Type*} [DecidableEq ι] [DivisionSemiring 𝕜] [Star 𝕜]
    [TrivialStar 𝕜] [AddCommGroup M] [Module 𝕜 M] [StarAddMonoid M] [StarModule 𝕜 M]
    (Φ : (ι → ℤˣ) → M) (k : ι) :
    star (rademacherCoeff 𝕜 Φ k) = rademacherCoeff 𝕜 (fun ε ↦ star (Φ ε)) k := by
  simp [rademacherCoeff_apply, Units.smul_def]

/-- Rademacher Fourier coefficients of a family of self-adjoint elements are self-adjoint. -/
theorem isSelfAdjoint_rademacherCoeff {𝕜 M : Type*} [DecidableEq ι] [DivisionSemiring 𝕜] [Star 𝕜]
    [TrivialStar 𝕜] [AddCommGroup M] [Module 𝕜 M] [StarAddMonoid M] [StarModule 𝕜 M]
    {Φ : (ι → ℤˣ) → M} (hΦ : ∀ ε, IsSelfAdjoint (Φ ε)) (k : ι) :
    IsSelfAdjoint (rademacherCoeff 𝕜 Φ k) := by
  rw [IsSelfAdjoint, star_rademacherCoeff]
  exact congrArg (rademacherCoeff 𝕜 · k) (funext fun ε ↦ (hΦ ε).star_eq)

/-- Sign-cube coefficient transfer for a bilinear pairing: pairing the Rademacher Fourier
coefficients `rademacherCoeff 𝕜 Φ k` with `b k` and summing over `k` equals averaging
`B (Φ ε) (∑ k, ε k • b k)` over the sign cube. -/
theorem sum_bilinear_rademacherCoeff {𝕜 M N P : Type*} [DecidableEq ι] [Semifield 𝕜]
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N] [AddCommGroup P] [Module 𝕜 P]
    (B : M →ₗ[𝕜] N →ₗ[𝕜] P) (Φ : (ι → ℤˣ) → M) (b : ι → N) :
    ∑ k, B (rademacherCoeff 𝕜 Φ k) (b k) =
      (Fintype.card (ι → ℤˣ) : 𝕜)⁻¹ • ∑ ε : ι → ℤˣ, B (Φ ε) (∑ k, ε k • b k) := by
  simp_rw [rademacherCoeff_apply, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    Units.smul_def, map_zsmul, LinearMap.smul_apply, ← Finset.smul_sum]
  rw [Finset.sum_comm]

/-- Sign-cube coefficient transfer for an `ℝ`-bilinear pairing into an `RCLike` scalar field,
expressed as an expectation `𝔼` over the sign cube. -/
theorem sum_bilinear_rademacherCoeff_eq_expect {𝕜 M N : Type*} [DecidableEq ι] [RCLike 𝕜]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N] (B : M →ₗ[ℝ] N →ₗ[ℝ] 𝕜)
    (Φ : (ι → ℤˣ) → M) (b : ι → N) :
    ∑ k, B (rademacherCoeff ℝ Φ k) (b k) = 𝔼 ε : ι → ℤˣ, B (Φ ε) (∑ k, ε k • b k) := by
  rw [sum_bilinear_rademacherCoeff, Finset.expect_eq_sum_div_card, Finset.card_univ,
    RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, RCLike.ofReal_natCast, div_eq_inv_mul]

/-- A Rademacher sum of self-adjoint elements is self-adjoint. -/
theorem isSelfAdjoint_sum_units_smul {M : Type*} [AddCommGroup M] [StarAddMonoid M]
    {x : ι → M} (hx : ∀ i, IsSelfAdjoint (x i)) (ε : ι → ℤˣ) :
    IsSelfAdjoint (∑ i, ε i • x i) := by
  rw [IsSelfAdjoint, star_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Units.smul_def, star_zsmul, (hx i).star_eq]

/-- Expanding the fourth power of a Rademacher sum into a four-fold sum of sign products. -/
theorem sum_units_smul_mul₄ {A : Type*} [NonUnitalNonAssocRing A]
    (x : ι → A) (ε : ι → ℤˣ) :
    (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        ((ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ)) • (x i * x j * x k * x l) := by
  have h3 : (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) =
      ∑ i, ∑ j, ∑ k, (ε i • x i) * (ε j • x j) * (ε k • x k) := by
    rw [Fintype.sum_mul_sum]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [h3]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Units.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

/-- Summed over the sign cube, the product of four Rademacher signs splits into `card (ι → ℤˣ)`
times the three pair matchings minus twice the quadruple diagonal. -/
theorem sum_units_apply_mul₄ [DecidableEq ι] (i j k l : ι) :
    ∑ ε : ι → ℤˣ, (ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
      (Fintype.card (ι → ℤˣ) : ℤ) *
        ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) - 2 * (if i = j ∧ j = k ∧ k = l then 1 else 0)) := by
  have h2 (a b : ι) : ∑ ε : ι → ℤˣ, (ε a : ℤ) * (ε b : ℤ) =
      if a = b then (Fintype.card (ι → ℤˣ) : ℤ) else 0 := by
    simpa [Units.smul_def, mul_assoc] using sum_units_smul_units_smul (M := ℤ) a b 1
  have hsq (u : ℤˣ) : (u : ℤ) * (u : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  by_cases hij : i = j
  · subst hij; simp_rw [hsq, one_mul, h2]
    by_cases hkl : k = l <;> by_cases hik : i = k <;> subst_vars <;> simp_all
  · by_cases hik : i = k
    · subst hik
      have h (ε : ι → ℤˣ) : (ε i : ℤ) * (ε j : ℤ) * (ε i : ℤ) * (ε l : ℤ) =
          (ε j : ℤ) * (ε l : ℤ) := by linear_combination (ε j : ℤ) * (ε l : ℤ) * hsq (ε i)
      simp_rw [h, h2]; by_cases hjl : j = l <;> subst_vars <;> simp_all
    · by_cases hil : i = l
      · subst hil
        have h (ε : ι → ℤˣ) : (ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε i : ℤ) =
            (ε j : ℤ) * (ε k : ℤ) := by linear_combination (ε j : ℤ) * (ε k : ℤ) * hsq (ε i)
        simp_rw [h, h2]; by_cases hjk : j = k <;> subst_vars <;> simp_all
      · simp only [hij, hik, hil, false_and, ite_false, mul_zero, add_zero, sub_zero]
        exact sum_eq_zero_of_mulSingle_neg i
          (fun ε : ι → ℤˣ ↦ (ε i : ℤ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ)) fun ε ↦ by
            simp [Ne.symm hij, Ne.symm hik, Ne.symm hil]

/-- Averaged over the sign cube, the product of four Rademacher signs splits into the three pair
matchings minus twice the quadruple diagonal. -/
theorem expect_units_apply_mul₄ [DecidableEq ι] (i j k l : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
      (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) - 2 * (if i = j ∧ j = k ∧ k = l then 1 else 0) := by
  have hcast := congrArg (Int.cast (R := ℝ)) (sum_units_apply_mul₄ i j k l)
  push_cast at hcast
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, hcast,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- Exact algebraic expansion of the fourth Rademacher moment into the three pair matchings minus
twice the diagonal fourth product. -/
theorem inv_card_smul_sum_units_smul_mul₄ {𝕜 A : Type*} [DecidableEq ι]
    [DivisionSemiring 𝕜] [CharZero 𝕜] [NonUnitalRing A] [Module 𝕜 A] (x : ι → A) :
    (Fintype.card (ι → ℤˣ) : 𝕜)⁻¹ • ∑ ε : ι → ℤˣ,
        (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) =
      (∑ i, x i * x i) * (∑ i, x i * x i) + (∑ i, ∑ j, x i * x j * x i * x j) +
      (∑ i, x i * (∑ j, x j * x j) * x i) - 2 • ∑ i, x i * x i * x i * x i := by
  have hsum : ∑ ε : ι → ℤˣ,
        (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) =
      Fintype.card (ι → ℤˣ) • ((∑ i, x i * x i) * (∑ i, x i * x i) +
        (∑ i, ∑ j, x i * x j * x i * x j) + (∑ i, x i * (∑ j, x j * x j) * x i) -
        2 • ∑ i, x i * x i * x i * x i) := by
    simp_rw [sum_units_smul_mul₄]
    have hswap (f : (ι → ℤˣ) → ι → ι → ι → ι → A) :
        ∑ ε, ∑ i, ∑ j, ∑ k, ∑ l, f ε i j k l = ∑ i, ∑ j, ∑ k, ∑ l, ∑ ε, f ε i j k l := by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hswap]
    simp_rw [← Finset.sum_smul, sum_units_apply_mul₄, mul_zsmul, natCast_zsmul, ← Finset.smul_sum]
    congr 1
    simp_rw [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    refine congrArg₂ Sub.sub (congrArg₂ HAdd.hAdd (congrArg₂ HAdd.hAdd ?_ ?_) ?_) ?_
    · rw [Finset.sum_mul]; simp [ite_smul, ite_and, Finset.mul_sum, mul_assoc]
    · simp [ite_smul, ite_and]
    · simp [ite_smul, ite_and, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    · simp [mul_ite, ite_smul, ite_and, Finset.smul_sum, two_smul]
  rw [hsum, ← Nat.cast_smul_eq_nsmul 𝕜,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

end Signs

variable {ι κ 𝕜 E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [SeminormedAddCommGroup E]

/-- The Rademacher second moment `R₂(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖²)^(1/2)` of a finite family, the
signs `ε : ι → ℤˣ` being averaged uniformly over the sign cube. -/
def rademacherSecondMoment (y : ι → E) : ℝ :=
  √(𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2)

/-- The defining average of the Rademacher second moment. -/
theorem rademacherSecondMoment_def (y : ι → E) :
    rademacherSecondMoment y = √(𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2) :=
  (rfl)

/-- At exponent `2`, `rademacherMoment` agrees with `rademacherSecondMoment`. -/
theorem rademacherMoment_two (y : ι → E) :
    rademacherMoment 2 y = rademacherSecondMoment y := by
  rw [rademacherMoment_def, rademacherSecondMoment_def, Real.sqrt_eq_rpow]
  simp

/-- Rademacher second moments are nonnegative. -/
theorem rademacherSecondMoment_nonneg (y : ι → E) : 0 ≤ rademacherSecondMoment y :=
  Real.sqrt_nonneg _

/-- Squaring the Rademacher second moment recovers the average squared norm of the signed
sums. -/
theorem rademacherSecondMoment_sq (y : ι → E) :
    rademacherSecondMoment y ^ 2 = 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg fun _ _ ↦ sq_nonneg _)

/-- A bound on the average squared norm of the signed sums bounds the Rademacher second
moment. -/
theorem rademacherSecondMoment_le_of_sq_le {y : ι → E} {c : ℝ} (hc : 0 ≤ c)
    (h : 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2 ≤ c ^ 2) : rademacherSecondMoment y ≤ c :=
  Real.sqrt_le_iff.2 ⟨hc, h⟩

/-- If every signed sum of `y` is at most `K` times the corresponding signed sum of `z`, then
`R₂(y) ≤ K R₂(z)`. -/
theorem rademacherSecondMoment_le_mul {F : Type*} [SeminormedAddCommGroup F] {y : ι → E}
    {z : ι → F} {K : ℝ} (h : ∀ ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ≤ K * ‖∑ i, ε i • z i‖) :
    rademacherSecondMoment y ≤ K * rademacherSecondMoment z := by
  simpa only [rademacherMoment_two] using rademacherMoment_le_mul two_pos h

/-- An additive map with `‖f x‖ ≤ M ‖x‖` multiplies Rademacher second moments by at most
`M`. -/
theorem rademacherSecondMoment_map_le {F 𝓕 : Type*} [SeminormedAddCommGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) (y : ι → E) :
    rademacherSecondMoment (fun i ↦ f (y i)) ≤ M * rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using rademacherMoment_map_le two_pos f hM y

/-- An additive map with `‖x‖ ≤ K ‖f x‖` divides Rademacher second moments by at most `K`. -/
theorem rademacherSecondMoment_le_mul_map {F 𝓕 : Type*} [SeminormedAddCommGroup F]
    [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ} (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖)
    (y : ι → E) :
    rademacherSecondMoment y ≤ K * rademacherSecondMoment (fun i ↦ f (y i)) := by
  simpa only [rademacherMoment_two] using rademacherMoment_le_mul_map two_pos f hK y

/-- The zero family has Rademacher second moment zero. -/
@[simp]
theorem rademacherSecondMoment_zero : rademacherSecondMoment (0 : ι → E) = 0 := by
  simpa only [rademacherMoment_two] using rademacherMoment_zero (ι := ι) (E := E) two_ne_zero

/-- An empty Rademacher sum has second moment zero. -/
@[simp]
theorem rademacherSecondMoment_of_isEmpty [IsEmpty ι] (y : ι → E) :
    rademacherSecondMoment y = 0 := by
  simpa only [rademacherMoment_two] using rademacherMoment_of_isEmpty two_ne_zero y

/-- Reindexing a family along an equivalence does not change its Rademacher second moment. -/
theorem rademacherSecondMoment_comp_equiv (e : κ ≃ ι) (y : ι → E) :
    rademacherSecondMoment (y ∘ e) = rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using rademacherMoment_comp_equiv e 2 y

/-- Padding a family with zeros does not change its Rademacher second moment. -/
theorem rademacherSecondMoment_sumElim_zero (y : ι → E) :
    rademacherSecondMoment (Sum.elim y (0 : κ → E)) = rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using rademacherMoment_sumElim_zero (κ := κ) 2 y

/-- Multiplying a family by a scalar multiplies its Rademacher second moment by the norm of
that scalar. -/
theorem rademacherSecondMoment_smul [NormedField 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (y : ι → E) :
    rademacherSecondMoment (fun i ↦ c • y i) = ‖c‖ * rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using rademacherMoment_smul two_ne_zero c y

/-- The Rademacher second moment of a family of multiples of one vector is that of the family of
coefficients times the norm of the vector. -/
theorem rademacherSecondMoment_smul_const [NormedField 𝕜] [NormedSpace 𝕜 E] (a : ι → 𝕜)
    (y : E) : rademacherSecondMoment (fun i ↦ a i • y) = rademacherSecondMoment a * ‖y‖ := by
  simpa only [rademacherMoment_two] using rademacherMoment_smul_const two_ne_zero a y

/-- The Rademacher second moment is at most the sum of the norms, the norm of every signed
sum being at most that sum. -/
theorem rademacherSecondMoment_le_sum_norm (y : ι → E) :
    rademacherSecondMoment y ≤ ∑ i, ‖y i‖ := by
  simpa only [rademacherMoment_two] using rademacherMoment_le_sum_norm two_pos y

/-- Every member of a family has norm at most the Rademacher second moment of the family: the
signed sums for `ε` and for the sign pattern agreeing with `-ε` off `i` add up to `2 εᵢ yᵢ`. -/
theorem norm_le_rademacherSecondMoment [NormedSpace ℝ E] (y : ι → E) (i : ι) :
    ‖y i‖ ≤ rademacherSecondMoment y := by
  simpa only [rademacherMoment_two] using norm_le_rademacherMoment one_le_two y i

section InnerProductSpace

variable [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

variable (𝕜) in
include 𝕜 in
/-- In an inner product space the average squared norm of the signed sums of a family is the sum
of the squared norms of its members. -/
theorem expect_norm_sum_units_smul_sq (y : ι → H) :
    𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  have h (ε : ι → ℤˣ) : ‖∑ i, ε i • y i‖ ^ 2 =
      ∑ i, ∑ j, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * RCLike.re (inner 𝕜 (y i) (y j)) := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), sum_inner, map_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum, map_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    simp [Units.smul_def, ← Int.cast_smul_eq_zsmul 𝕜, inner_smul_left, inner_smul_right]
    ring
  simp_rw [h, expect_sum_comm, ← expect_mul, expect_units_apply_mul_apply, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, ite_true, norm_sq_eq_re_inner (𝕜 := 𝕜)]

variable (𝕜) in
include 𝕜 in
/-- In an inner product space the Rademacher second moment of a family is its `ℓ²` norm. -/
theorem rademacherSecondMoment_eq_norm_toLp_two (y : ι → H) :
    rademacherSecondMoment y = ‖WithLp.toLp 2 y‖ := by
  rw [rademacherSecondMoment, expect_norm_sum_units_smul_sq 𝕜, PiLp.norm_eq_of_L2]

end InnerProductSpace

/-- In a real normed space the Rademacher second moment of `card ι` copies of a vector `y` is
`√(card ι) ‖y‖`. -/
theorem rademacherSecondMoment_const [NormedSpace ℝ E] (y : E) :
    rademacherSecondMoment (fun _ : ι ↦ y) = √(Fintype.card ι) * ‖y‖ := by
  have h := rademacherSecondMoment_smul_const (fun _ : ι ↦ (1 : ℝ)) y
  simp only [one_smul] at h
  rw [h, rademacherSecondMoment_eq_norm_toLp_two ℝ, PiLp.norm_eq_of_L2]
  simp

end TauCeti
