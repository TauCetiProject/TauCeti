/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.MeanInequalities

/-!
# Rademacher type and cotype

For a finite family `y : ι → E` in a normed group, the *Rademacher second moment*
`R₂(y) = (𝔼_ε ‖∑ i, ε i • y i‖²)^(1/2)` averages over the uniform finite cube of signs
`ε : ι → ℤˣ`. A space has *Rademacher type `p`* with constant `C` if
`R₂(y) ≤ C (∑ i, ‖y i‖ ^ p)^(1/p)` for every finite family, and *Rademacher cotype `q`* with
constant `C` if `(∑ i, ‖y i‖ ^ q)^(1/q) ≤ C R₂(y)`. These are the isomorphic invariants measuring
how far random signed sums in `E` are from the orthogonal sums of a Hilbert space; they enter the
Gaussian comparison and the cotype-2 summing bound of the Grothendieck–Pisier factorization
theory. Complex spaces are covered through their underlying real spaces.

## Main definitions

* `TauCeti.rademacherSecondMoment y`: the Rademacher second moment `R₂(y)`.
* `TauCeti.HasType p C E`: `E` has Rademacher type `p` with constant `C`.
* `TauCeti.HasCotype q C E`: `E` has Rademacher cotype `q` with constant `C`.

## Main statements

* `TauCeti.expect_sign_mul_sign`: distinct coordinates of the sign cube are orthogonal.
* `TauCeti.rademacherSecondMoment_comp_equiv`, `TauCeti.rademacherSecondMoment_sumElim_zero`,
  `TauCeti.rademacherSecondMoment_smul`, `TauCeti.rademacherSecondMoment_add_le`: invariance under
  reindexing and zero-padding, homogeneity and the triangle inequality.
* `TauCeti.sq_rademacherSecondMoment_eq_sum`: in an inner product space,
  `R₂(y)² = ∑ i, ‖y i‖²`.
* `TauCeti.HasType.linearIsometry`, `TauCeti.HasType.continuousLinearEquiv`,
  `TauCeti.HasType.prod` and their cotype counterparts: transport along isometric embeddings
  (so to subspaces) with the same constant, along isomorphisms `U` with the constant multiplied
  by `‖U‖ ‖U⁻¹‖`, and to binary products.
* `TauCeti.HasType.of_exponent_le`, `TauCeti.HasCotype.of_exponent_ge`: type `p` implies type
  `p' ≤ p`, and cotype `q` implies cotype `q' ≥ q`.
* `TauCeti.hasType_one_one`: every space has type `1` with constant `1`.
* `TauCeti.hasType_two_one`, `TauCeti.hasCotype_two_one`: inner product spaces have type `2` and
  cotype `2` with constant `1`.
* `TauCeti.not_hasType_of_two_lt`, `TauCeti.not_hasCotype_of_lt_two`: no nonzero space has type
  `p > 2` or cotype `q < 2`, with any constant.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 6.
* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*, CBMS Regional
  Conference Series in Mathematics 60, §3.
-/

public section

noncomputable section

open Filter Finset
open scoped BigOperators

namespace TauCeti

variable {ι κ : Type*}

/-! ### Orthogonality on the sign cube -/

/-- Distinct coordinates of the uniform sign cube are orthogonal:
`𝔼_ε ε i ε j` is `1` if `i = j` and `0` otherwise. -/
theorem expect_sign_mul_sign [Fintype ι] [DecidableEq ι] (i j : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    simp [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  · -- Flipping the sign of the `i`-th coordinate negates the integrand.
    set f : (ι → ℤˣ) → ℝ := fun ε ↦ ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ)
    have hflip (ε : ι → ℤˣ) : f (Pi.mulSingle i (-1) * ε) = -f ε := by
      simp [f, Ne.symm hij]
    have h := Fintype.expect_equiv (Equiv.mulLeft (Pi.mulSingle i (-1 : ℤˣ)))
      (fun ε ↦ f (Pi.mulSingle i (-1) * ε)) f fun _ ↦ rfl
    simp only [hflip, expect_neg_distrib] at h
    change 𝔼 ε, f ε = 0
    linarith

/-! ### The Rademacher second moment -/

section SecondMoment

variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- The **Rademacher second moment** `R₂(y) = (𝔼_ε ‖∑ i, ε i • y i‖²)^(1/2)` of a finite family
`y`, where the average runs over the uniform cube of signs `ε : ι → ℤˣ`. -/
def rademacherSecondMoment [Fintype ι] [DecidableEq ι] (y : ι → E) : ℝ :=
  √(𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2)

variable [Fintype ι] [DecidableEq ι]

theorem rademacherSecondMoment_def (y : ι → E) :
    rademacherSecondMoment y = √(𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2) := (rfl)

theorem rademacherSecondMoment_nonneg (y : ι → E) : 0 ≤ rademacherSecondMoment y :=
  Real.sqrt_nonneg _

theorem sq_rademacherSecondMoment (y : ι → E) :
    rademacherSecondMoment y ^ 2 = 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg fun _ _ ↦ sq_nonneg _)

@[simp]
theorem rademacherSecondMoment_zero : rademacherSecondMoment (0 : ι → E) = 0 := by
  simp [rademacherSecondMoment_def]

/-- Comparison principle: if every signed sum of `x` is bounded by `c` times the corresponding
signed sum of `y`, then `R₂(x) ≤ c R₂(y)`. The two families may live in different spaces. -/
theorem rademacherSecondMoment_le_mul_of_forall_norm_le {x : ι → E} {y : ι → F} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ε : ι → ℤˣ, ‖∑ i, ε i • x i‖ ≤ c * ‖∑ i, ε i • y i‖) :
    rademacherSecondMoment x ≤ c * rademacherSecondMoment y := by
  rw [rademacherSecondMoment_def, rademacherSecondMoment_def, ← Real.sqrt_sq hc,
    ← Real.sqrt_mul (sq_nonneg c), mul_expect]
  gcongr with ε
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2

/-- Minkowski's inequality for the Rademacher second moment, in comparison form: if every signed
sum of `z` is bounded by the sum of the corresponding signed sums of `x` and `y`, then
`R₂(z) ≤ R₂(x) + R₂(y)`. -/
theorem rademacherSecondMoment_le_add_of_forall_norm_le {G : Type*} [SeminormedAddCommGroup G]
    {z : ι → G} {x : ι → E} {y : ι → F}
    (h : ∀ ε : ι → ℤˣ, ‖∑ i, ε i • z i‖ ≤ ‖∑ i, ε i • x i‖ + ‖∑ i, ε i • y i‖) :
    rademacherSecondMoment z ≤ rademacherSecondMoment x + rademacherSecondMoment y := by
  set a : (ι → ℤˣ) → ℝ := fun ε ↦ ‖∑ i, ε i • x i‖
  set b : (ι → ℤˣ) → ℝ := fun ε ↦ ‖∑ i, ε i • y i‖
  have hA := sq_rademacherSecondMoment x
  have hB := sq_rademacherSecondMoment y
  have hA0 := rademacherSecondMoment_nonneg x
  have hB0 := rademacherSecondMoment_nonneg y
  -- Cauchy–Schwarz for the average bounds the cross term.
  have hab : 𝔼 ε, a ε * b ε ≤ rademacherSecondMoment x * rademacherSecondMoment y := by
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (mul_nonneg hA0 hB0))
    rw [mul_pow, hA, hB]
    exact expect_mul_sq_le_sq_mul_sq univ a b
  rw [rademacherSecondMoment_def, Real.sqrt_le_left (add_nonneg hA0 hB0)]
  calc 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • z i‖ ^ 2
      ≤ 𝔼 ε, (a ε ^ 2 + 2 * (a ε * b ε) + b ε ^ 2) := by
        gcongr with ε
        calc ‖∑ i, ε i • z i‖ ^ 2 ≤ (a ε + b ε) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (h ε) 2
          _ = _ := by ring
    _ = 𝔼 ε, a ε ^ 2 + 2 * 𝔼 ε, a ε * b ε + 𝔼 ε, b ε ^ 2 := by
        rw [expect_add_distrib, expect_add_distrib, mul_expect]
    _ ≤ _ := by rw [← hA, ← hB]; nlinarith

/-- The triangle inequality for the Rademacher second moment. -/
theorem rademacherSecondMoment_add_le (x y : ι → E) :
    rademacherSecondMoment (x + y) ≤ rademacherSecondMoment x + rademacherSecondMoment y :=
  rademacherSecondMoment_le_add_of_forall_norm_le fun ε ↦ by
    simpa [smul_add, sum_add_distrib] using norm_add_le _ _

/-- The Rademacher second moment is absolutely homogeneous. -/
theorem rademacherSecondMoment_smul [NormedSpace ℝ E] (c : ℝ) (y : ι → E) :
    rademacherSecondMoment (c • y) = |c| * rademacherSecondMoment y := by
  have hsum (ε : ι → ℤˣ) : ∑ i, ε i • (c • y) i = c • ∑ i, ε i • y i := by
    simp [smul_sum, smul_comm (ε _) c]
  simp_rw [rademacherSecondMoment_def, hsum, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ← mul_expect, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- A bounded operator multiplies the Rademacher second moment by at most its norm. -/
theorem rademacherSecondMoment_continuousLinearMap_comp_le [NormedSpace ℝ E] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (y : ι → E) :
    rademacherSecondMoment (T ∘ y) ≤ ‖T‖ * rademacherSecondMoment y :=
  rademacherSecondMoment_le_mul_of_forall_norm_le (norm_nonneg T) fun ε ↦ by
    simpa [Units.smul_def, map_sum, map_zsmul] using T.le_opNorm (∑ i, ε i • y i)

/-- A linear isometry preserves the Rademacher second moment. -/
@[simp]
theorem rademacherSecondMoment_linearIsometry_comp [NormedSpace ℝ E] [NormedSpace ℝ F]
    (f : E →ₗᵢ[ℝ] F) (y : ι → E) :
    rademacherSecondMoment (f ∘ y) = rademacherSecondMoment y := by
  have hsum (ε : ι → ℤˣ) : ∑ i, ε i • (f ∘ y) i = f (∑ i, ε i • y i) := by
    simp [Units.smul_def, map_sum, map_zsmul]
  simp_rw [rademacherSecondMoment_def, hsum, LinearIsometry.norm_map]

/-- The Rademacher second moment is invariant under reindexing. -/
theorem rademacherSecondMoment_comp_equiv [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (y : ι → E) :
    rademacherSecondMoment (y ∘ e) = rademacherSecondMoment y := by
  rw [rademacherSecondMoment_def, rademacherSecondMoment_def]
  congr 1
  refine Fintype.expect_equiv (e.arrowCongr (Equiv.refl ℤˣ)) _ _ fun ε ↦ ?_
  rw [← e.sum_comp]
  simp

/-- Padding a family with zero vectors does not change its Rademacher second moment. -/
@[simp]
theorem rademacherSecondMoment_sumElim_zero [Fintype κ] [DecidableEq κ] (y : ι → E) :
    rademacherSecondMoment (Sum.elim y (0 : κ → E)) = rademacherSecondMoment y := by
  rw [rademacherSecondMoment_def, rademacherSecondMoment_def]
  congr 1
  rw [Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ ℤˣ) _
      (fun δ ↦ ‖∑ i, δ.1 i • y i‖ ^ 2) fun ε ↦ by simp [Fintype.sum_sum_type],
    ← univ_product_univ, expect_product]
  simp

/-- The Rademacher second moment of scalar multiples of one vector factors through the scalar
family. -/
theorem rademacherSecondMoment_smul_const [NormedSpace ℝ E] (c : ι → ℝ) (v : E) :
    rademacherSecondMoment (fun i ↦ c i • v) = rademacherSecondMoment c * ‖v‖ := by
  have hsum (ε : ι → ℤˣ) : ∑ i, ε i • c i • v = (∑ i, ε i • c i) • v := by
    simp [sum_smul, Units.smul_def, mul_smul, Int.cast_smul_eq_zsmul]
  simp_rw [rademacherSecondMoment_def, hsum, norm_smul, mul_pow, ← expect_mul,
    Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)]

/-- A family with a single member has Rademacher second moment equal to its norm. -/
theorem rademacherSecondMoment_of_unique [Unique ι] (y : ι → E) :
    rademacherSecondMoment y = ‖y default‖ := by
  have hsum (ε : ι → ℤˣ) : ‖∑ i, ε i • y i‖ = ‖y default‖ := by
    rw [Fintype.sum_unique]
    rcases Int.units_eq_one_or (ε default) with h | h <;> simp [h]
  simp_rw [rademacherSecondMoment_def, hsum, Fintype.expect_const, Real.sqrt_sq (norm_nonneg _)]

/-- The Rademacher second moment is bounded by the sum of the norms. -/
theorem rademacherSecondMoment_le_sum_norm (y : ι → E) :
    rademacherSecondMoment y ≤ ∑ i, ‖y i‖ := by
  rw [rademacherSecondMoment_def, Real.sqrt_le_left (sum_nonneg fun i _ ↦ norm_nonneg _)]
  refine expect_le univ_nonempty fun ε _ ↦ pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ ?_)
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

/-- In a real inner product space the signed sums are orthogonal on average:
`R₂(y)² = ∑ i, ‖y i‖²`. -/
theorem sq_rademacherSecondMoment_eq_sum {H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : ι → H) :
    rademacherSecondMoment y ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  have hexpand (ε : ι → ℤˣ) : ‖∑ i, ε i • y i‖ ^ 2 =
      ∑ i, ∑ j, ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ) * inner ℝ (y i) (y j) := by
    simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum, Units.smul_def,
      ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, real_inner_smul_right, mul_assoc]
  simp_rw [sq_rademacherSecondMoment, hexpand]
  rw [expect_sum_comm]
  simp_rw [expect_sum_comm, ← expect_mul, expect_sign_mul_sign, ite_mul, one_mul, zero_mul,
    sum_ite_eq, mem_univ, ite_true, real_inner_self_eq_norm_sq]

theorem rademacherSecondMoment_eq_sqrt_sum {H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : ι → H) :
    rademacherSecondMoment y = √(∑ i, ‖y i‖ ^ 2) := by
  rw [← sq_rademacherSecondMoment_eq_sum, Real.sqrt_sq (rademacherSecondMoment_nonneg y)]

/-- The constant family with value `v` has Rademacher second moment `√(card ι) ‖v‖`. -/
@[simp]
theorem rademacherSecondMoment_const [NormedSpace ℝ E] (v : E) :
    rademacherSecondMoment (fun _ : ι ↦ v) = √(Fintype.card ι) * ‖v‖ := by
  simpa [rademacherSecondMoment_eq_sqrt_sum] using rademacherSecondMoment_smul_const (ι := ι) 1 v

end SecondMoment

/-! ### Rademacher type and cotype -/

/-- A normed group `E`, typically a real Banach space, has **Rademacher type `p`** with
constant `C` if `R₂(y) ≤ C (∑ i, ‖y i‖ ^ p)^(1/p)` for every finite family `y`. The meaningful
range is `1 ≤ p ≤ 2`. -/
def HasType (p C : ℝ) (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ ⦃n : ℕ⦄ (y : Fin n → E), rademacherSecondMoment y ≤ C * (∑ i, ‖y i‖ ^ p) ^ (1 / p)

/-- A normed group `E`, typically a real Banach space, has **Rademacher cotype `q`** with
constant `C` if `(∑ i, ‖y i‖ ^ q)^(1/q) ≤ C R₂(y)` for every finite family `y`. The meaningful
range is `2 ≤ q < ∞`. -/
def HasCotype (q C : ℝ) (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ ⦃n : ℕ⦄ (y : Fin n → E), (∑ i, ‖y i‖ ^ q) ^ (1 / q) ≤ C * rademacherSecondMoment y

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {p q C D : ℝ}

theorem hasType_iff : HasType p C E ↔
    ∀ ⦃n : ℕ⦄ (y : Fin n → E), rademacherSecondMoment y ≤ C * (∑ i, ‖y i‖ ^ p) ^ (1 / p) :=
  Iff.rfl

theorem hasCotype_iff : HasCotype q C E ↔
    ∀ ⦃n : ℕ⦄ (y : Fin n → E), (∑ i, ‖y i‖ ^ q) ^ (1 / q) ≤ C * rademacherSecondMoment y :=
  Iff.rfl

/-- The `ℓᵖ` expression of a family dominated termwise by `c` times another is at most `c`
times the other's. -/
private theorem rpow_sum_rpow_le_mul {a b : ι → ℝ} (s : Finset ι) {c : ℝ} (hp : 0 < p)
    (hc : 0 ≤ c) (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ c * b i) :
    (∑ i ∈ s, a i ^ p) ^ (1 / p) ≤ c * (∑ i ∈ s, b i ^ p) ^ (1 / p) := by
  have hb (i : ι) (hi : i ∈ s) : 0 ≤ c * b i := (ha i hi).trans (hab i hi)
  calc (∑ i ∈ s, a i ^ p) ^ (1 / p) ≤ (∑ i ∈ s, (c * b i) ^ p) ^ (1 / p) := by
        gcongr with i hi
        · exact sum_nonneg fun i hi ↦ Real.rpow_nonneg (ha i hi) p
        · exact ha i hi
        · exact hab i hi
    _ ≤ c * (∑ i ∈ s, b i ^ p) ^ (1 / p) := by
        rcases hc.eq_or_lt with rfl | hc
        · simp [Real.zero_rpow hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')]
        have hb' (i : ι) (hi : i ∈ s) : 0 ≤ b i := nonneg_of_mul_nonneg_right
          (by simpa [mul_comm] using hb i hi) hc
        rw [sum_congr rfl fun i hi ↦ Real.mul_rpow hc.le (hb' i hi), ← mul_sum,
          Real.mul_rpow (Real.rpow_nonneg hc.le p) (sum_nonneg fun i hi ↦
            Real.rpow_nonneg (hb' i hi) p), ← Real.rpow_mul hc.le, mul_one_div_cancel hp.ne',
          Real.rpow_one]

/-- The `ℓᵖ` expression of `n` copies of `t ≥ 0` is `n ^ (1 / p) * t`. -/
private theorem rpow_sum_const_rpow (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (hp : p ≠ 0) :
    (∑ _ : Fin n, t ^ p) ^ (1 / p) = (n : ℝ) ^ (1 / p) * t := by
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    Real.mul_rpow n.cast_nonneg (Real.rpow_nonneg ht p), one_div, Real.rpow_rpow_inv ht hp]

/-- A zero vector space has every type, with every constant. -/
theorem hasType_of_subsingleton [Subsingleton E] (hp : p ≠ 0) : HasType p C E := fun n y ↦ by
  rw [Subsingleton.elim y 0]
  simp [Real.zero_rpow hp, Real.zero_rpow (inv_ne_zero hp)]

/-- A zero vector space has every cotype, with every constant. -/
theorem hasCotype_of_subsingleton [Subsingleton E] (hq : q ≠ 0) : HasCotype q C E := fun n y ↦ by
  rw [Subsingleton.elim y 0]
  simp [Real.zero_rpow hq, Real.zero_rpow (inv_ne_zero hq)]

namespace HasType

/-- Type inequality for families indexed by an arbitrary finite type. -/
theorem rademacherSecondMoment_le [Fintype ι] [DecidableEq ι] (h : HasType p C E)
    (y : ι → E) : rademacherSecondMoment y ≤ C * (∑ i, ‖y i‖ ^ p) ^ (1 / p) := by
  let e := Fintype.equivFin ι
  have := h (y ∘ e.symm)
  simp only [Function.comp_apply] at this
  rwa [rademacherSecondMoment_comp_equiv,
    e.symm.sum_comp (fun i ↦ ‖y i‖ ^ p)] at this

theorem mono (h : HasType p C E) (hCD : C ≤ D) : HasType p D E := fun _ y ↦
  (h y).trans (mul_le_mul_of_nonneg_right hCD
    (Real.rpow_nonneg (sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _))

/-- On a nonzero space, a type constant is at least `1`. -/
theorem one_le [Nontrivial E] (h : HasType p C E) (hp : p ≠ 0) : 1 ≤ C := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have := h (fun _ : Fin 1 ↦ v)
  rw [rademacherSecondMoment_of_unique, rpow_sum_const_rpow 1 (norm_nonneg v) hp] at this
  simp only [Nat.cast_one, Real.one_rpow, one_mul] at this
  exact (le_mul_iff_one_le_left (norm_pos_iff.2 hv)).1 this

/-- A type constant is nonnegative, unless the space is zero. -/
private theorem nonneg_or_subsingleton (h : HasType p C E) (hp : p ≠ 0) :
    0 ≤ C ∨ Subsingleton E := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Or.inr hE
  · exact Or.inl (zero_le_one.trans (h.one_le hp))

/-- Type passes to any space isometrically embedded in `E`, with the same constant. -/
theorem linearIsometry [NormedSpace ℝ E] [NormedSpace ℝ F] (h : HasType p C E)
    (f : F →ₗᵢ[ℝ] E) : HasType p C F := fun _ y ↦ by
  simpa using h (f ∘ y)

/-- Type passes to subspaces, with the same constant. -/
theorem submodule [NormedSpace ℝ E] (h : HasType p C E) (K : Submodule ℝ E) : HasType p C K :=
  h.linearIsometry K.subtypeₗᵢ

/-- Type passes along an isomorphism `U`, with the constant multiplied by `‖U‖ ‖U⁻¹‖`. -/
theorem continuousLinearEquiv [NormedSpace ℝ E] [NormedSpace ℝ F] (h : HasType p C E)
    (hp : 0 < p) (U : E ≃L[ℝ] F) :
    HasType p (‖(U : E →L[ℝ] F)‖ * ‖(U.symm : F →L[ℝ] E)‖ * C) F := by
  rcases h.nonneg_or_subsingleton hp.ne' with hC | hE
  · intro n y
    have hy : y = U ∘ (U.symm ∘ y) := by ext; simp
    have hx := rpow_sum_rpow_le_mul univ hp (norm_nonneg (U.symm : F →L[ℝ] E))
      (fun i _ ↦ norm_nonneg ((U.symm ∘ y) i))
      (fun i _ ↦ (U.symm : F →L[ℝ] E).le_opNorm (y i))
    calc rademacherSecondMoment y
        ≤ ‖(U : E →L[ℝ] F)‖ * rademacherSecondMoment (U.symm ∘ y) := by
          conv_lhs => rw [hy]
          exact rademacherSecondMoment_continuousLinearMap_comp_le (U : E →L[ℝ] F) _
      _ ≤ ‖(U : E →L[ℝ] F)‖ * (C * (∑ i, ‖(U.symm ∘ y) i‖ ^ p) ^ (1 / p)) := by
          gcongr
          exact h _
      _ ≤ ‖(U : E →L[ℝ] F)‖ * (C * (‖(U.symm : F →L[ℝ] E)‖ * (∑ i, ‖y i‖ ^ p) ^ (1 / p))) := by
          gcongr
      _ = _ := by ring
  · have : Subsingleton F := U.symm.toEquiv.subsingleton
    exact hasType_of_subsingleton hp.ne'

/-- Type `p` implies type `p'` for `0 < p' ≤ p`, with the same constant. -/
theorem of_exponent_le {p' : ℝ} (h : HasType p C E) (hp' : 0 < p') (hp'p : p' ≤ p) :
    HasType p' C E := by
  rcases h.nonneg_or_subsingleton (hp'.trans_le hp'p).ne' with hC | hE
  · exact fun n y ↦ (h y).trans (mul_le_mul_of_nonneg_left
      (Real.Lq_le_Lp_of_nonneg univ (fun i _ ↦ norm_nonneg (y i)) hp' hp'p) hC)
  · exact hasType_of_subsingleton hp'.ne'

/-- A product of spaces of type `p` has type `p`, with the sum of the constants. -/
theorem prod (hE : HasType p C E) (hF : HasType p D F) (hp : 0 < p) (hC : 0 ≤ C)
    (hD : 0 ≤ D) : HasType p (C + D) (E × F) := fun n y ↦ by
  have hsplit : rademacherSecondMoment y ≤
      rademacherSecondMoment (Prod.fst ∘ y) + rademacherSecondMoment (Prod.snd ∘ y) :=
    rademacherSecondMoment_le_add_of_forall_norm_le fun ε ↦ by
      have hz : ∑ i, ε i • y i = (∑ i, ε i • (y i).1, ∑ i, ε i • (y i).2) := by
        ext <;> simp [Prod.fst_sum, Prod.snd_sum]
      rw [hz, Prod.norm_def]
      exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  have h₁ := rpow_sum_rpow_le_mul univ hp zero_le_one (fun i _ ↦ norm_nonneg (y i).1)
    fun i _ ↦ by simpa using norm_fst_le (y i)
  have h₂ := rpow_sum_rpow_le_mul univ hp zero_le_one (fun i _ ↦ norm_nonneg (y i).2)
    fun i _ ↦ by simpa using norm_snd_le (y i)
  rw [one_mul] at h₁ h₂
  calc rademacherSecondMoment y
      ≤ C * (∑ i, ‖(y i).1‖ ^ p) ^ (1 / p) + D * (∑ i, ‖(y i).2‖ ^ p) ^ (1 / p) :=
        hsplit.trans (add_le_add (hE _) (hF _))
    _ ≤ C * (∑ i, ‖y i‖ ^ p) ^ (1 / p) + D * (∑ i, ‖y i‖ ^ p) ^ (1 / p) := by gcongr
    _ = _ := by ring

end HasType

namespace HasCotype

/-- Cotype inequality for families indexed by an arbitrary finite type. -/
theorem le_rademacherSecondMoment [Fintype ι] [DecidableEq ι] (h : HasCotype q C E)
    (y : ι → E) : (∑ i, ‖y i‖ ^ q) ^ (1 / q) ≤ C * rademacherSecondMoment y := by
  let e := Fintype.equivFin ι
  have := h (y ∘ e.symm)
  simp only [Function.comp_apply] at this
  rwa [rademacherSecondMoment_comp_equiv,
    e.symm.sum_comp (fun i ↦ ‖y i‖ ^ q)] at this

theorem mono (h : HasCotype q C E) (hCD : C ≤ D) : HasCotype q D E := fun _ y ↦
  (h y).trans (mul_le_mul_of_nonneg_right hCD (rademacherSecondMoment_nonneg y))

/-- On a nonzero space, a cotype constant is at least `1`. -/
theorem one_le [Nontrivial E] (h : HasCotype q C E) (hq : q ≠ 0) : 1 ≤ C := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have := h (fun _ : Fin 1 ↦ v)
  rw [rademacherSecondMoment_of_unique, rpow_sum_const_rpow 1 (norm_nonneg v) hq] at this
  simp only [Nat.cast_one, Real.one_rpow, one_mul] at this
  exact (le_mul_iff_one_le_left (norm_pos_iff.2 hv)).1 this

/-- A cotype constant is nonnegative, unless the space is zero. -/
private theorem nonneg_or_subsingleton (h : HasCotype q C E) (hq : q ≠ 0) :
    0 ≤ C ∨ Subsingleton E := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Or.inr hE
  · exact Or.inl (zero_le_one.trans (h.one_le hq))

/-- Cotype passes to any space isometrically embedded in `E`, with the same constant. -/
theorem linearIsometry [NormedSpace ℝ E] [NormedSpace ℝ F] (h : HasCotype q C E)
    (f : F →ₗᵢ[ℝ] E) : HasCotype q C F := fun _ y ↦ by
  simpa using h (f ∘ y)

/-- Cotype passes to subspaces, with the same constant. -/
theorem submodule [NormedSpace ℝ E] (h : HasCotype q C E) (K : Submodule ℝ E) : HasCotype q C K :=
  h.linearIsometry K.subtypeₗᵢ

/-- Cotype passes along an isomorphism `U`, with the constant multiplied by `‖U‖ ‖U⁻¹‖`. -/
theorem continuousLinearEquiv [NormedSpace ℝ E] [NormedSpace ℝ F] (h : HasCotype q C E)
    (hq : 0 < q) (U : E ≃L[ℝ] F) :
    HasCotype q (‖(U : E →L[ℝ] F)‖ * ‖(U.symm : F →L[ℝ] E)‖ * C) F := by
  rcases h.nonneg_or_subsingleton hq.ne' with hC | hE
  · intro n y
    have hy : y = U ∘ (U.symm ∘ y) := by ext; simp
    have hyx := rpow_sum_rpow_le_mul univ hq (norm_nonneg (U : E →L[ℝ] F))
      (fun i _ ↦ norm_nonneg (y i)) fun i _ ↦ by
        conv_lhs => rw [hy]
        exact (U : E →L[ℝ] F).le_opNorm _
    have hR := rademacherSecondMoment_continuousLinearMap_comp_le (U.symm : F →L[ℝ] E) y
    calc (∑ i, ‖y i‖ ^ q) ^ (1 / q)
        ≤ ‖(U : E →L[ℝ] F)‖ * (∑ i, ‖(U.symm ∘ y) i‖ ^ q) ^ (1 / q) := hyx
      _ ≤ ‖(U : E →L[ℝ] F)‖ * (C * rademacherSecondMoment (U.symm ∘ y)) := by
          gcongr
          exact h _
      _ ≤ ‖(U : E →L[ℝ] F)‖ * (C * (‖(U.symm : F →L[ℝ] E)‖ * rademacherSecondMoment y)) := by
          gcongr
          exact hR
      _ = _ := by ring
  · have : Subsingleton F := U.symm.toEquiv.subsingleton
    exact hasCotype_of_subsingleton hq.ne'

/-- Cotype `q` implies cotype `q'` for `0 < q ≤ q'`, with the same constant. -/
theorem of_exponent_ge {q' : ℝ} (h : HasCotype q C E) (hq : 0 < q) (hqq' : q ≤ q') :
    HasCotype q' C E := fun _ y ↦
  (Real.Lq_le_Lp_of_nonneg univ (fun i _ ↦ norm_nonneg (y i)) hq hqq').trans (h y)

/-- A product of spaces of cotype `q ≥ 1` has cotype `q`, with the sum of the constants. -/
theorem prod (hE : HasCotype q C E) (hF : HasCotype q D F) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hD : 0 ≤ D) : HasCotype q (C + D) (E × F) := fun n y ↦ by
  have hR₁ : rademacherSecondMoment (Prod.fst ∘ y) ≤ 1 * rademacherSecondMoment y :=
    rademacherSecondMoment_le_mul_of_forall_norm_le zero_le_one fun ε ↦ by
      simpa [Prod.fst_sum] using norm_fst_le (∑ i, ε i • y i)
  have hR₂ : rademacherSecondMoment (Prod.snd ∘ y) ≤ 1 * rademacherSecondMoment y :=
    rademacherSecondMoment_le_mul_of_forall_norm_le zero_le_one fun ε ↦ by
      simpa [Prod.snd_sum] using norm_snd_le (∑ i, ε i • y i)
  rw [one_mul] at hR₁ hR₂
  calc (∑ i, ‖y i‖ ^ q) ^ (1 / q)
      ≤ (∑ i, (‖(y i).1‖ + ‖(y i).2‖) ^ q) ^ (1 / q) := by
        gcongr with i
        · exact sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _
        · exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
    _ ≤ (∑ i, ‖(y i).1‖ ^ q) ^ (1 / q) + (∑ i, ‖(y i).2‖ ^ q) ^ (1 / q) :=
        Real.Lp_add_le_of_nonneg univ hq (fun i _ ↦ norm_nonneg _) fun i _ ↦ norm_nonneg _
    _ ≤ C * rademacherSecondMoment y + D * rademacherSecondMoment y := by
        gcongr
        · exact (hE _).trans (mul_le_mul_of_nonneg_left hR₁ hC)
        · exact (hF _).trans (mul_le_mul_of_nonneg_left hR₂ hD)
    _ = _ := by ring

end HasCotype

variable (E)

/-- Every normed group has type `1` with constant `1`. -/
theorem hasType_one_one : HasType 1 1 E := fun n y ↦ by
  simpa using rademacherSecondMoment_le_sum_norm y

/-- A real inner product space has type `2` with constant `1`. -/
theorem hasType_two_one (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    HasType 2 1 H := fun n y ↦ by
  rw [rademacherSecondMoment_eq_sqrt_sum, Real.sqrt_eq_rpow, one_mul]
  simp_rw [Real.rpow_two]
  exact le_rfl

/-- A real inner product space has cotype `2` with constant `1`. -/
theorem hasCotype_two_one (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    HasCotype 2 1 H := fun n y ↦ by
  rw [rademacherSecondMoment_eq_sqrt_sum, Real.sqrt_eq_rpow, one_mul]
  simp_rw [Real.rpow_two]
  exact le_rfl

variable {E}

/-- If `n ^ b ≤ C n ^ a` for every natural number `n`, then `b ≤ a`. -/
private theorem le_of_forall_natCast_rpow_le {a b : ℝ}
    (h : ∀ n : ℕ, (n : ℝ) ^ b ≤ C * (n : ℝ) ^ a) : b ≤ a := by
  by_contra! hab
  have hev := ((tendsto_rpow_atTop (sub_pos.2 hab)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop C)
  obtain ⟨n, hCn, hn⟩ := (hev.and (eventually_gt_atTop 0)).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := h n
  rw [← sub_add_cancel b a, Real.rpow_add hn'] at hb
  have hpos := Real.rpow_pos_of_pos hn' a
  simp only [Function.comp_apply] at hCn
  nlinarith

/-- No nonzero space has Rademacher type `p > 2`, with any constant. -/
theorem not_hasType_of_two_lt [NormedSpace ℝ E] [Nontrivial E] (hp : 2 < p) :
    ¬ HasType p C E := fun h ↦ by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have key (n : ℕ) : (n : ℝ) ^ (1 / 2 : ℝ) ≤ C * (n : ℝ) ^ (1 / p) := by
    have := h (fun _ : Fin n ↦ v)
    rw [rademacherSecondMoment_const, rpow_sum_const_rpow n (norm_nonneg v) (by positivity),
      Fintype.card_fin, Real.sqrt_eq_rpow, ← mul_assoc] at this
    exact le_of_mul_le_mul_right this (norm_pos_iff.2 hv)
  have := le_of_forall_natCast_rpow_le key
  have : (1 / p : ℝ) < 1 / 2 := one_div_lt_one_div_of_lt two_pos hp
  linarith

/-- No nonzero space has Rademacher cotype `q` with `0 < q < 2`, with any constant. -/
theorem not_hasCotype_of_lt_two [NormedSpace ℝ E] [Nontrivial E] (hq0 : 0 < q) (hq : q < 2) :
    ¬ HasCotype q C E := fun h ↦ by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have key (n : ℕ) : (n : ℝ) ^ (1 / q) ≤ C * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have := h (fun _ : Fin n ↦ v)
    rw [rademacherSecondMoment_const, rpow_sum_const_rpow n (norm_nonneg v) hq0.ne',
      Fintype.card_fin, Real.sqrt_eq_rpow, ← mul_assoc] at this
    exact le_of_mul_le_mul_right this (norm_pos_iff.2 hv)
  have := le_of_forall_natCast_rpow_le key
  have : (1 / 2 : ℝ) < 1 / q := one_div_lt_one_div_of_lt hq0 hq
  linarith

end TauCeti
