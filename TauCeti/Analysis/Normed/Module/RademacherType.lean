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
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Rademacher type and cotype

For a finite family `y : ι → E` in a normed group, the *Rademacher second moment*
`𝔼_ε ‖∑ i, ε i • y i‖²` averages over the uniform finite cube of signs `ε : ι → ℤˣ`, and its
square root is the *Rademacher norm* `R₂(y)`. A space has *Rademacher type `p`* with constant `C`
if `R₂(y) ≤ C (∑ i, ‖y i‖ ^ p)^(1/p)` for every finite family, and *Rademacher cotype `q`* with
constant `C` if `(∑ i, ‖y i‖ ^ q)^(1/q) ≤ C R₂(y)`. These are the isomorphic invariants measuring
how far random signed sums in `E` are from the orthogonal sums of a Hilbert space; they enter the
Gaussian comparison and the cotype-2 summing bound of the Grothendieck–Pisier factorization
theory. Complex spaces are covered through their underlying real spaces.

## Main definitions

* `TauCeti.rademacherSecondMoment y`: the Rademacher second moment `𝔼_ε ‖∑ i, ε i • y i‖²`.
* `TauCeti.rademacherNorm y`: its square root `R₂(y)`.
* `TauCeti.HasType p C E`: `E` has Rademacher type `p` with constant `C`.
* `TauCeti.HasCotype q C E`: `E` has Rademacher cotype `q` with constant `C`.

## Main statements

* `TauCeti.expect_sign_mul_sign`: distinct coordinates of the sign cube are orthogonal.
* `TauCeti.rademacherNorm_eq_zero_iff`: in a normed group without `2`-torsion, `R₂(y) = 0` only
  for `y = 0`.
* `TauCeti.rademacherNorm_comp_equiv`, `TauCeti.rademacherNorm_sumElim_zero`,
  `TauCeti.rademacherNorm_smul`, `TauCeti.rademacherNorm_add_le`: invariance under reindexing and
  zero-padding, homogeneity and the triangle inequality.
* `TauCeti.rademacherSecondMoment_eq_sum`: in an inner product space,
  `𝔼_ε ‖∑ i, ε i • y i‖² = ∑ i, ‖y i‖²`.
* `TauCeti.HasType.linearIsometry`, `TauCeti.HasType.continuousLinearEquiv`,
  `TauCeti.HasType.pi` and their cotype counterparts: transport along isometric embeddings
  (so to subspaces) with the same constant, along isomorphisms `U` with the constant multiplied
  by `‖U‖ ‖U⁻¹‖`, and to finite direct sums with the sum of the constants.
* `TauCeti.HasType.of_exponent_le`, `TauCeti.HasCotype.of_exponent_ge`: type `p` implies type
  `p'` for `0 < p' ≤ p`, and cotype `q > 0` implies cotype `q' ≥ q`.
* `TauCeti.hasType_one_one`: every space has type `1` with constant `1`.
* `TauCeti.hasType_two_one`, `TauCeti.hasCotype_two_one`: inner product spaces have type `2` and
  cotype `2` with constant `1`.
* `TauCeti.not_hasType_of_two_lt`, `TauCeti.not_hasCotype_of_lt_two`: no nonzero space has type
  `p > 2` or cotype `0 < q < 2`, with any constant.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 6.
* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*, CBMS Regional
  Conference Series in Mathematics 60, §3.
-/

public section

noncomputable section

open Finset
open scoped BigOperators

namespace TauCeti

variable {ι κ 𝕜 : Type*}

/-! ### Orthogonality on the sign cube -/

/-- Distinct coordinates of the uniform sign cube are orthogonal:
`𝔼_ε ε i ε j` is `1` if `i = j` and `0` otherwise. -/
theorem expect_sign_mul_sign [Fintype ι] [DecidableEq ι] (i j : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    simp [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  · -- Flipping the sign of the `i`-th coordinate negates the integrand.
    have h := Fintype.expect_equiv (Equiv.mulLeft (Pi.mulSingle i (-1 : ℤˣ)))
      (fun ε : ι → ℤˣ ↦ ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ))
      (fun ε ↦ -(((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ))) fun ε ↦ by simp [Ne.symm hij]
    rw [expect_neg_distrib] at h
    linarith

/-! ### The Rademacher second moment and the Rademacher norm -/

section SecondMoment

variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- The **Rademacher second moment** `𝔼_ε ‖∑ i, ε i • y i‖²` of a finite family `y`, where the
average runs over the uniform cube of signs `ε : ι → ℤˣ`. -/
def rademacherSecondMoment [Fintype ι] [DecidableEq ι] (y : ι → E) : ℝ :=
  𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2

/-- The **Rademacher norm** `R₂(y) = (𝔼_ε ‖∑ i, ε i • y i‖²)^(1/2)` of a finite family `y`: the
square root of its Rademacher second moment. -/
def rademacherNorm [Fintype ι] [DecidableEq ι] (y : ι → E) : ℝ :=
  √(rademacherSecondMoment y)

variable [Fintype ι] [DecidableEq ι]

theorem rademacherSecondMoment_def (y : ι → E) :
    rademacherSecondMoment y = 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • y i‖ ^ 2 := (rfl)

theorem rademacherNorm_def (y : ι → E) : rademacherNorm y = √(rademacherSecondMoment y) := (rfl)

theorem rademacherSecondMoment_nonneg (y : ι → E) : 0 ≤ rademacherSecondMoment y :=
  expect_nonneg fun _ _ ↦ sq_nonneg _

theorem rademacherNorm_nonneg (y : ι → E) : 0 ≤ rademacherNorm y :=
  Real.sqrt_nonneg _

theorem sq_rademacherNorm (y : ι → E) : rademacherNorm y ^ 2 = rademacherSecondMoment y :=
  Real.sq_sqrt (rademacherSecondMoment_nonneg y)

@[simp]
theorem rademacherSecondMoment_zero : rademacherSecondMoment (0 : ι → E) = 0 := by
  simp [rademacherSecondMoment_def]

@[simp]
theorem rademacherNorm_zero : rademacherNorm (0 : ι → E) = 0 := by
  simp [rademacherNorm_def]

/-- In a normed group without `2`-torsion, the Rademacher second moment vanishes only on the zero
family. Some torsion hypothesis is needed: if `2 • a = 0`, every signed sum of `![a, a]` vanishes.
A real normed space provides it through `HasUniqueDiv.of_isTorsionFree ℝ`. -/
@[simp]
theorem rademacherSecondMoment_eq_zero_iff {G : Type*} [NormedAddCommGroup G] [HasUniqueDiv G]
    {y : ι → G} : rademacherSecondMoment y = 0 ↔ y = 0 := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ h ▸ rademacherSecondMoment_zero⟩
  rw [rademacherSecondMoment_def, Fintype.expect_eq_zero_iff_of_nonneg fun _ ↦ sq_nonneg _] at h
  have hs (ε : ι → ℤˣ) : ∑ j, ε j • y j = 0 := by simpa using congrFun h ε
  -- Flipping the sign of the `i`-th coordinate changes the signed sum by `2 • y i`.
  have h1 := hs 1
  have h2 := hs (Pi.mulSingle i (-1))
  rw [Fintype.sum_eq_add_sum_compl i] at h1 h2
  have hc : ∑ j ∈ {i}ᶜ, (Pi.mulSingle i (-1) : ι → ℤˣ) j • y j = ∑ j ∈ {i}ᶜ, y j :=
    sum_congr rfl fun j hj ↦ by
      rw [Pi.mulSingle_eq_of_ne (by simpa using hj : j ≠ i), one_smul]
  rw [hc] at h2
  simp only [Pi.one_apply, one_smul, Pi.mulSingle_eq_same, Units.neg_smul] at h1 h2
  rw [Pi.zero_apply, ← two_nsmul_eq_zero, two_nsmul, ← sub_eq_zero.mpr (h1.trans h2.symm)]
  abel

/-- In a normed group without `2`-torsion, the Rademacher norm vanishes only on the zero family;
see `rademacherSecondMoment_eq_zero_iff`. -/
@[simp]
theorem rademacherNorm_eq_zero_iff {G : Type*} [NormedAddCommGroup G] [HasUniqueDiv G]
    {y : ι → G} : rademacherNorm y = 0 ↔ y = 0 := by
  rw [rademacherNorm_def, Real.sqrt_eq_zero (rademacherSecondMoment_nonneg y),
    rademacherSecondMoment_eq_zero_iff]

/-- Comparison principle: if every signed sum of `x` is bounded by `c` times the corresponding
signed sum of `y`, then `R₂(x) ≤ c R₂(y)`. The two families may live in different spaces. -/
theorem rademacherNorm_le_mul_of_forall_norm_le {x : ι → E} {y : ι → F} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ε : ι → ℤˣ, ‖∑ i, ε i • x i‖ ≤ c * ‖∑ i, ε i • y i‖) :
    rademacherNorm x ≤ c * rademacherNorm y := by
  rw [rademacherNorm_def, rademacherNorm_def, rademacherSecondMoment_def,
    rademacherSecondMoment_def, ← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c), mul_expect]
  gcongr with ε
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2

/-- Minkowski's inequality for the Rademacher norm, in comparison form: if every signed sum of
`z` is bounded by the sum over `k ∈ s` of the corresponding signed sums of `x k`, then
`R₂(z) ≤ ∑ k ∈ s, R₂(x k)`. The families may live in different spaces. -/
theorem rademacherNorm_le_sum_of_forall_norm_le {G : κ → Type*}
    [∀ k, SeminormedAddCommGroup (G k)] {z : ι → E} {x : ∀ k, ι → G k} (s : Finset κ)
    (h : ∀ ε : ι → ℤˣ, ‖∑ i, ε i • z i‖ ≤ ∑ k ∈ s, ‖∑ i, ε i • x k i‖) :
    rademacherNorm z ≤ ∑ k ∈ s, rademacherNorm (x k) := by
  -- The quadratic mean `M a = (𝔼_ε (a ε)²)^(1/2)` of a real function on the sign cube.
  let M : ((ι → ℤˣ) → ℝ) → ℝ := fun a ↦ √(𝔼 ε, a ε ^ 2)
  have hM (a b : (ι → ℤˣ) → ℝ) : M (a + b) ≤ M a + M b := by
    have hA : M a ^ 2 = 𝔼 ε, a ε ^ 2 := Real.sq_sqrt (expect_nonneg fun _ _ ↦ sq_nonneg _)
    have hB : M b ^ 2 = 𝔼 ε, b ε ^ 2 := Real.sq_sqrt (expect_nonneg fun _ _ ↦ sq_nonneg _)
    have hA0 : 0 ≤ M a := Real.sqrt_nonneg _
    have hB0 : 0 ≤ M b := Real.sqrt_nonneg _
    -- Cauchy–Schwarz for the average bounds the cross term.
    have hab : 𝔼 ε, a ε * b ε ≤ M a * M b := by
      refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (mul_nonneg hA0 hB0))
      rw [mul_pow, hA, hB]
      exact expect_mul_sq_le_sq_mul_sq univ a b
    rw [Real.sqrt_le_left (add_nonneg hA0 hB0)]
    calc 𝔼 ε, (a + b) ε ^ 2 = 𝔼 ε, a ε ^ 2 + 2 * 𝔼 ε, a ε * b ε + 𝔼 ε, b ε ^ 2 := by
          simp_rw [Pi.add_apply, add_sq, expect_add_distrib, mul_expect, mul_assoc]
      _ ≤ _ := by rw [← hA, ← hB]; nlinarith
  calc rademacherNorm z ≤ M (∑ k ∈ s, fun ε ↦ ‖∑ i, ε i • x k i‖) := by
        refine Real.sqrt_le_sqrt (expect_le_expect fun ε _ ↦ ?_)
        rw [Finset.sum_apply]
        exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2
    _ ≤ ∑ k ∈ s, M fun ε ↦ ‖∑ i, ε i • x k i‖ :=
        le_sum_of_subadditive M (by simp [M]) hM s _

/-- The triangle inequality for the Rademacher norm. -/
theorem rademacherNorm_add_le (x y : ι → E) :
    rademacherNorm (x + y) ≤ rademacherNorm x + rademacherNorm y := by
  simpa using rademacherNorm_le_sum_of_forall_norm_le (G := fun _ : Fin 2 ↦ E) (x := ![x, y])
    univ fun ε ↦ by simpa [smul_add, sum_add_distrib] using norm_add_le _ _

/-- The Rademacher norm is absolutely homogeneous. -/
@[simp]
theorem rademacherNorm_smul [NormedField 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (y : ι → E) :
    rademacherNorm (c • y) = ‖c‖ * rademacherNorm y := by
  have hsum (ε : ι → ℤˣ) : ∑ i, ε i • (c • y) i = c • ∑ i, ε i • y i := by
    simp [smul_sum, smul_comm (ε _) c]
  simp_rw [rademacherNorm_def, rademacherSecondMoment_def, hsum, norm_smul, mul_pow,
    ← mul_expect, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

/-- A bounded operator multiplies the Rademacher norm by at most its norm. -/
theorem rademacherNorm_continuousLinearMap_comp_le [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (y : ι → E) :
    rademacherNorm (T ∘ y) ≤ ‖T‖ * rademacherNorm y :=
  rademacherNorm_le_mul_of_forall_norm_le (norm_nonneg T) fun ε ↦ by
    simpa [Units.smul_def, map_sum, map_zsmul] using T.le_opNorm (∑ i, ε i • y i)

/-- A linear isometry preserves the Rademacher norm. -/
@[simp]
theorem rademacherNorm_linearIsometry_comp [Semiring 𝕜] [Module 𝕜 E] [Module 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) (y : ι → E) :
    rademacherNorm (f ∘ y) = rademacherNorm y := by
  have hsum (ε : ι → ℤˣ) : ∑ i, ε i • (f ∘ y) i = f (∑ i, ε i • y i) := by
    simp [Units.smul_def, map_sum, map_zsmul]
  simp_rw [rademacherNorm_def, rademacherSecondMoment_def, hsum, LinearIsometry.norm_map]

/-- The Rademacher norm is invariant under reindexing. -/
@[simp]
theorem rademacherNorm_comp_equiv [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (y : ι → E) :
    rademacherNorm (y ∘ e) = rademacherNorm y := by
  rw [rademacherNorm_def, rademacherNorm_def, rademacherSecondMoment_def,
    rademacherSecondMoment_def]
  congr 1
  refine Fintype.expect_equiv (e.arrowCongr (Equiv.refl ℤˣ)) _ _ fun ε ↦ ?_
  rw [← e.sum_comp]
  simp

/-- Padding a family with zero vectors does not change its Rademacher norm. -/
@[simp]
theorem rademacherNorm_sumElim_zero [Fintype κ] [DecidableEq κ] (y : ι → E) :
    rademacherNorm (Sum.elim y (0 : κ → E)) = rademacherNorm y := by
  rw [rademacherNorm_def, rademacherNorm_def, rademacherSecondMoment_def,
    rademacherSecondMoment_def]
  congr 1
  rw [Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ ℤˣ) _
      (fun δ ↦ ‖∑ i, δ.1 i • y i‖ ^ 2) fun ε ↦ by simp [Fintype.sum_sum_type],
    ← univ_product_univ, expect_product]
  simp

/-- The Rademacher norm of scalar multiples of one vector factors through the scalar family. -/
theorem rademacherNorm_smul_const [NormedSpace ℝ E] (c : ι → ℝ) (v : E) :
    rademacherNorm (fun i ↦ c i • v) = rademacherNorm c * ‖v‖ := by
  have hsum (ε : ι → ℤˣ) : ∑ i, ε i • c i • v = (∑ i, ε i • c i) • v := by
    simp [sum_smul, Units.smul_def, mul_smul, Int.cast_smul_eq_zsmul]
  simp_rw [rademacherNorm_def, rademacherSecondMoment_def, hsum, norm_smul, mul_pow,
    ← expect_mul, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)]

/-- A family with a single member has Rademacher norm equal to its norm. -/
@[simp]
theorem rademacherNorm_of_unique [Unique ι] (y : ι → E) :
    rademacherNorm y = ‖y default‖ := by
  have hsum (ε : ι → ℤˣ) : ‖∑ i, ε i • y i‖ = ‖y default‖ := by
    rw [Fintype.sum_unique]
    rcases Int.units_eq_one_or (ε default) with h | h <;> simp [h]
  simp_rw [rademacherNorm_def, rademacherSecondMoment_def, hsum, Fintype.expect_const,
    Real.sqrt_sq (norm_nonneg _)]

/-- The Rademacher norm is bounded by the sum of the norms. -/
theorem rademacherNorm_le_sum_norm (y : ι → E) :
    rademacherNorm y ≤ ∑ i, ‖y i‖ := by
  rw [rademacherNorm_def, rademacherSecondMoment_def,
    Real.sqrt_le_left (sum_nonneg fun i _ ↦ norm_nonneg _)]
  refine expect_le univ_nonempty fun ε _ ↦ pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ ?_)
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

/-- In a real inner product space the signed sums are orthogonal on average:
`𝔼_ε ‖∑ i, ε i • y i‖² = ∑ i, ‖y i‖²`. -/
theorem rademacherSecondMoment_eq_sum {H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : ι → H) :
    rademacherSecondMoment y = ∑ i, ‖y i‖ ^ 2 := by
  have hexpand (ε : ι → ℤˣ) : ‖∑ i, ε i • y i‖ ^ 2 =
      ∑ i, ∑ j, ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ) * inner ℝ (y i) (y j) := by
    simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum, Units.smul_def,
      ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, real_inner_smul_right, mul_assoc]
  simp_rw [rademacherSecondMoment_def, hexpand]
  rw [expect_sum_comm]
  simp_rw [expect_sum_comm, ← expect_mul, expect_sign_mul_sign, ite_mul, one_mul, zero_mul,
    sum_ite_eq, mem_univ, ite_true, real_inner_self_eq_norm_sq]

theorem rademacherNorm_eq_sqrt_sum {H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℝ H] (y : ι → H) :
    rademacherNorm y = √(∑ i, ‖y i‖ ^ 2) := by
  rw [rademacherNorm_def, rademacherSecondMoment_eq_sum]

/-- The constant family with value `v` has Rademacher norm `√(card ι) ‖v‖`. -/
@[simp]
theorem rademacherNorm_const [NormedSpace ℝ E] (v : E) :
    rademacherNorm (fun _ : ι ↦ v) = √(Fintype.card ι) * ‖v‖ := by
  simpa [rademacherNorm_eq_sqrt_sum] using rademacherNorm_smul_const (ι := ι) 1 v

end SecondMoment

/-! ### Rademacher type and cotype -/

/-- A normed group `E`, typically a real Banach space, has **Rademacher type `p`** with
constant `C` if `R₂(y) ≤ C (∑ i, ‖y i‖ ^ p)^(1/p)` for every finite family `y`. The meaningful
range is `1 ≤ p ≤ 2`. -/
def HasType (p C : ℝ) (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ ⦃n : ℕ⦄ (y : Fin n → E), rademacherNorm y ≤ C * (∑ i, ‖y i‖ ^ p) ^ (1 / p)

/-- A normed group `E`, typically a real Banach space, has **Rademacher cotype `q`** with
constant `C` if `(∑ i, ‖y i‖ ^ q)^(1/q) ≤ C R₂(y)` for every finite family `y`. The meaningful
range is `2 ≤ q < ∞`. -/
def HasCotype (q C : ℝ) (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ ⦃n : ℕ⦄ (y : Fin n → E), (∑ i, ‖y i‖ ^ q) ^ (1 / q) ≤ C * rademacherNorm y

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {p q C D : ℝ}

theorem hasType_iff : HasType p C E ↔
    ∀ ⦃n : ℕ⦄ (y : Fin n → E), rademacherNorm y ≤ C * (∑ i, ‖y i‖ ^ p) ^ (1 / p) :=
  Iff.rfl

theorem hasCotype_iff : HasCotype q C E ↔
    ∀ ⦃n : ℕ⦄ (y : Fin n → E), (∑ i, ‖y i‖ ^ q) ^ (1 / q) ≤ C * rademacherNorm y :=
  Iff.rfl

/-- A zero vector space has every nonzero exponent as a type, with every constant. -/
theorem hasType_of_subsingleton [Subsingleton E] (hp : p ≠ 0) : HasType p C E := fun n y ↦ by
  rw [Subsingleton.elim y 0]
  simp [Real.zero_rpow hp, Real.zero_rpow (inv_ne_zero hp)]

/-- A zero vector space has every nonzero exponent as a cotype, with every constant. -/
theorem hasCotype_of_subsingleton [Subsingleton E] (hq : q ≠ 0) : HasCotype q C E := fun n y ↦ by
  rw [Subsingleton.elim y 0]
  simp [Real.zero_rpow hq, Real.zero_rpow (inv_ne_zero hq)]

namespace HasType

/-- Type inequality for families indexed by an arbitrary finite type. -/
theorem rademacherNorm_le [Fintype ι] [DecidableEq ι] (h : HasType p C E) (y : ι → E) :
    rademacherNorm y ≤ C * (∑ i, ‖y i‖ ^ p) ^ (1 / p) := by
  simpa [(Fintype.equivFin ι).symm.sum_comp (fun i ↦ ‖y i‖ ^ p)] using
    h (y ∘ (Fintype.equivFin ι).symm)

theorem mono (h : HasType p C E) (hCD : C ≤ D) : HasType p D E := fun _ y ↦
  (h y).trans (mul_le_mul_of_nonneg_right hCD
    (Real.rpow_nonneg (sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _))

/-- On a nonzero space, a type constant is at least `1`. -/
theorem one_le [Nontrivial E] (h : HasType p C E) (hp : p ≠ 0) : 1 ≤ C := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have := h (fun _ : Fin 1 ↦ v)
  rw [rademacherNorm_of_unique, Real.Lp_const_of_nonneg univ (norm_nonneg v) hp,
    card_univ, Fintype.card_fin] at this
  simp only [Nat.cast_one, Real.one_rpow, one_mul] at this
  exact (le_mul_iff_one_le_left (norm_pos_iff.2 hv)).1 this

/-- A type constant is nonnegative, unless the space is zero. -/
private theorem nonneg_or_subsingleton (h : HasType p C E) (hp : p ≠ 0) :
    0 ≤ C ∨ Subsingleton E :=
  (subsingleton_or_nontrivial E).symm.imp
    (fun (_ : Nontrivial E) ↦ zero_le_one.trans (h.one_le hp)) id

/-- Type passes to any space isometrically embedded in `E`, with the same constant. -/
theorem linearIsometry [Semiring 𝕜] [Module 𝕜 E] [Module 𝕜 F]
    (h : HasType p C E) (f : F →ₗᵢ[𝕜] E) : HasType p C F := fun _ y ↦ by
  simpa using h (f ∘ y)

/-- Type passes to subspaces, with the same constant. -/
theorem submodule [Ring 𝕜] [Module 𝕜 E] (h : HasType p C E) (K : Submodule 𝕜 E) :
    HasType p C K :=
  h.linearIsometry K.subtypeₗᵢ

/-- Type passes along an isomorphism `U`, with the constant multiplied by `‖U‖ ‖U⁻¹‖`. -/
theorem continuousLinearEquiv [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (h : HasType p C E) (hp : 0 < p) (U : E ≃L[𝕜] F) :
    HasType p (‖(U : E →L[𝕜] F)‖ * ‖(U.symm : F →L[𝕜] E)‖ * C) F := by
  rcases h.nonneg_or_subsingleton hp.ne' with hC | hE
  · intro n y
    have hx := Real.Lp_le_mul_Lp_of_nonneg univ hp (norm_nonneg (U.symm : F →L[𝕜] E))
      (fun i _ ↦ norm_nonneg ((U.symm ∘ y) i))
      (fun i _ ↦ by simpa using (U.symm : F →L[𝕜] E).le_opNorm (y i))
    calc rademacherNorm y
        ≤ ‖(U : E →L[𝕜] F)‖ * rademacherNorm (U.symm ∘ y) := by
          -- `U ∘ U.symm ∘ y = y`, once the coercion of `U` to `E →L[𝕜] F` is unfolded
          simpa [Function.comp_def] using
            rademacherNorm_continuousLinearMap_comp_le (U : E →L[𝕜] F) (U.symm ∘ y)
      _ ≤ ‖(U : E →L[𝕜] F)‖ * (C * (∑ i, ‖(U.symm ∘ y) i‖ ^ p) ^ (1 / p)) := by
          gcongr
          exact h _
      _ ≤ ‖(U : E →L[𝕜] F)‖ * (C * (‖(U.symm : F →L[𝕜] E)‖ * (∑ i, ‖y i‖ ^ p) ^ (1 / p))) := by
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

/-- A finite direct sum of spaces of type `p` has type `p`, with the sum of the constants. -/
theorem pi [Fintype κ] {E : κ → Type*} [∀ k, NormedAddCommGroup (E k)] {C : κ → ℝ}
    (h : ∀ k, HasType p (C k) (E k)) (hp : 0 ≤ p) (hC : ∀ k, 0 ≤ C k) :
    HasType p (∑ k, C k) (∀ k, E k) := fun n y ↦ by
  calc rademacherNorm y ≤ ∑ k, rademacherNorm fun i ↦ y i k :=
        rademacherNorm_le_sum_of_forall_norm_le univ fun ε ↦
          (pi_norm_le_iff_of_nonneg (sum_nonneg fun _ _ ↦ norm_nonneg _)).2 fun k ↦ by
            simpa [Finset.sum_apply] using single_le_sum (f := fun k ↦ ‖∑ i, ε i • y i k‖)
              (fun _ _ ↦ norm_nonneg _) (mem_univ k)
    _ ≤ ∑ k, C k * (∑ i, ‖y i k‖ ^ p) ^ (1 / p) := sum_le_sum fun k _ ↦ h k _
    _ ≤ ∑ k, C k * (∑ i, ‖y i‖ ^ p) ^ (1 / p) :=
        sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
          (sum_nonneg fun _ _ ↦ by positivity) (sum_le_sum fun i _ ↦
            Real.rpow_le_rpow (norm_nonneg _) (norm_le_pi_norm (y i) k) hp)
          (one_div_nonneg.2 hp)) (hC k)
    _ = _ := (sum_mul ..).symm

end HasType

namespace HasCotype

/-- Cotype inequality for families indexed by an arbitrary finite type. -/
theorem le_rademacherNorm [Fintype ι] [DecidableEq ι] (h : HasCotype q C E) (y : ι → E) :
    (∑ i, ‖y i‖ ^ q) ^ (1 / q) ≤ C * rademacherNorm y := by
  simpa [(Fintype.equivFin ι).symm.sum_comp (fun i ↦ ‖y i‖ ^ q)] using
    h (y ∘ (Fintype.equivFin ι).symm)

theorem mono (h : HasCotype q C E) (hCD : C ≤ D) : HasCotype q D E := fun _ y ↦
  (h y).trans (mul_le_mul_of_nonneg_right hCD (rademacherNorm_nonneg y))

/-- On a nonzero space, a cotype constant is at least `1`. -/
theorem one_le [Nontrivial E] (h : HasCotype q C E) (hq : q ≠ 0) : 1 ≤ C := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have := h (fun _ : Fin 1 ↦ v)
  rw [rademacherNorm_of_unique, Real.Lp_const_of_nonneg univ (norm_nonneg v) hq,
    card_univ, Fintype.card_fin] at this
  simp only [Nat.cast_one, Real.one_rpow, one_mul] at this
  exact (le_mul_iff_one_le_left (norm_pos_iff.2 hv)).1 this

/-- A cotype constant is nonnegative, unless the space is zero. -/
private theorem nonneg_or_subsingleton (h : HasCotype q C E) (hq : q ≠ 0) :
    0 ≤ C ∨ Subsingleton E :=
  (subsingleton_or_nontrivial E).symm.imp
    (fun (_ : Nontrivial E) ↦ zero_le_one.trans (h.one_le hq)) id

/-- Cotype passes to any space isometrically embedded in `E`, with the same constant. -/
theorem linearIsometry [Semiring 𝕜] [Module 𝕜 E] [Module 𝕜 F]
    (h : HasCotype q C E) (f : F →ₗᵢ[𝕜] E) : HasCotype q C F := fun _ y ↦ by
  simpa using h (f ∘ y)

/-- Cotype passes to subspaces, with the same constant. -/
theorem submodule [Ring 𝕜] [Module 𝕜 E] (h : HasCotype q C E) (K : Submodule 𝕜 E) :
    HasCotype q C K :=
  h.linearIsometry K.subtypeₗᵢ

/-- Cotype passes along an isomorphism `U`, with the constant multiplied by `‖U‖ ‖U⁻¹‖`. -/
theorem continuousLinearEquiv [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (h : HasCotype q C E) (hq : 0 < q) (U : E ≃L[𝕜] F) :
    HasCotype q (‖(U : E →L[𝕜] F)‖ * ‖(U.symm : F →L[𝕜] E)‖ * C) F := by
  rcases h.nonneg_or_subsingleton hq.ne' with hC | hE
  · intro n y
    have hyx := Real.Lp_le_mul_Lp_of_nonneg univ hq (norm_nonneg (U : E →L[𝕜] F))
      (fun i _ ↦ norm_nonneg (y i)) fun i _ ↦ by
        -- `y i = U (U.symm (y i))`, once the coercion of `U` to `E →L[𝕜] F` is unfolded
        simpa using (U : E →L[𝕜] F).le_opNorm (U.symm (y i))
    have hR := rademacherNorm_continuousLinearMap_comp_le (U.symm : F →L[𝕜] E) y
    calc (∑ i, ‖y i‖ ^ q) ^ (1 / q)
        ≤ ‖(U : E →L[𝕜] F)‖ * (∑ i, ‖(U.symm ∘ y) i‖ ^ q) ^ (1 / q) := hyx
      _ ≤ ‖(U : E →L[𝕜] F)‖ * (C * rademacherNorm (U.symm ∘ y)) := by
          gcongr
          exact h _
      _ ≤ ‖(U : E →L[𝕜] F)‖ * (C * (‖(U.symm : F →L[𝕜] E)‖ * rademacherNorm y)) := by
          gcongr
          exact hR
      _ = _ := by ring
  · have : Subsingleton F := U.symm.toEquiv.subsingleton
    exact hasCotype_of_subsingleton hq.ne'

/-- Cotype `q` implies cotype `q'` for `0 < q ≤ q'`, with the same constant. -/
theorem of_exponent_ge {q' : ℝ} (h : HasCotype q C E) (hq : 0 < q) (hqq' : q ≤ q') :
    HasCotype q' C E := fun _ y ↦
  (Real.Lq_le_Lp_of_nonneg univ (fun i _ ↦ norm_nonneg (y i)) hq hqq').trans (h y)

/-- A finite direct sum of spaces of cotype `q ≥ 1` has cotype `q`, with the sum of the
constants. -/
theorem pi [Fintype κ] {E : κ → Type*} [∀ k, NormedAddCommGroup (E k)] {C : κ → ℝ}
    (h : ∀ k, HasCotype q (C k) (E k)) (hq : 1 ≤ q) (hC : ∀ k, 0 ≤ C k) :
    HasCotype q (∑ k, C k) (∀ k, E k) := fun n y ↦ by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  -- Minkowski's inequality in `ℓ^q`, iterated over the finitely many coordinates.
  have hL := le_sum_of_subadditive (fun a : Fin n → ℝ ↦ (∑ i, |a i| ^ q) ^ (1 / q))
    (by simp [Real.zero_rpow hq0, Real.zero_rpow (inv_ne_zero hq0)])
    (fun a b ↦ Real.Lp_add_le univ a b hq) univ fun k i ↦ ‖y i k‖
  simp only [Finset.sum_apply, abs_norm] at hL
  calc (∑ i, ‖y i‖ ^ q) ^ (1 / q) ≤ (∑ i, |∑ k, ‖y i k‖| ^ q) ^ (1 / q) := by
        refine Real.rpow_le_rpow (sum_nonneg fun _ _ ↦ by positivity) (sum_le_sum fun i _ ↦
          Real.rpow_le_rpow (norm_nonneg _) ?_ (zero_le_one.trans hq))
          (one_div_nonneg.2 (zero_le_one.trans hq))
        rw [abs_of_nonneg (sum_nonneg fun _ _ ↦ norm_nonneg _)]
        exact (pi_norm_le_iff_of_nonneg (sum_nonneg fun _ _ ↦ norm_nonneg _)).2 fun k ↦
          single_le_sum (f := fun k ↦ ‖y i k‖) (fun _ _ ↦ norm_nonneg _) (mem_univ k)
    _ ≤ ∑ k, (∑ i, ‖y i k‖ ^ q) ^ (1 / q) := hL
    _ ≤ ∑ k, C k * rademacherNorm fun i ↦ y i k := sum_le_sum fun k _ ↦ h k _
    _ ≤ ∑ k, C k * rademacherNorm y := by
        gcongr with k
        · exact hC k
        · refine (rademacherNorm_le_mul_of_forall_norm_le zero_le_one fun ε ↦ ?_).trans_eq
            (one_mul _)
          simpa [Finset.sum_apply] using norm_le_pi_norm (∑ i, ε i • y i) k
    _ = _ := (sum_mul ..).symm

end HasCotype

variable (E)

/-- Every normed group has type `1` with constant `1`. -/
theorem hasType_one_one : HasType 1 1 E := fun n y ↦ by
  simpa using rademacherNorm_le_sum_norm y

/-- A real inner product space has type `2` with constant `1`. -/
theorem hasType_two_one (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    HasType 2 1 H := fun n y ↦ by
  simp [rademacherNorm_eq_sqrt_sum, Real.sqrt_eq_rpow]

/-- A real inner product space has cotype `2` with constant `1`. -/
theorem hasCotype_two_one (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    HasCotype 2 1 H := fun n y ↦ by
  simp [rademacherNorm_eq_sqrt_sum, Real.sqrt_eq_rpow]

variable {E}

/-- No nonzero space has Rademacher type `p > 2`, with any constant. -/
theorem not_hasType_of_two_lt [NormedSpace ℝ E] [Nontrivial E] (hp : 2 < p) :
    ¬ HasType p C E := fun h ↦ by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have key (n : ℕ) : (n : ℝ) ^ (1 / 2 : ℝ) ≤ C * (n : ℝ) ^ (1 / p) := by
    have := h (fun _ : Fin n ↦ v)
    rw [rademacherNorm_const, Real.Lp_const_of_nonneg univ (norm_nonneg v) (by positivity),
      card_univ, Fintype.card_fin, Real.sqrt_eq_rpow, ← mul_assoc] at this
    exact le_of_mul_le_mul_right this (norm_pos_iff.2 hv)
  have := Real.le_of_forall_natCast_rpow_le_mul_rpow key
  have : (1 / p : ℝ) < 1 / 2 := one_div_lt_one_div_of_lt two_pos hp
  linarith

/-- No nonzero space has Rademacher cotype `q` with `0 < q < 2`, with any constant. -/
theorem not_hasCotype_of_lt_two [NormedSpace ℝ E] [Nontrivial E] (hq0 : 0 < q) (hq : q < 2) :
    ¬ HasCotype q C E := fun h ↦ by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have key (n : ℕ) : (n : ℝ) ^ (1 / q) ≤ C * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have := h (fun _ : Fin n ↦ v)
    rw [rademacherNorm_const, Real.Lp_const_of_nonneg univ (norm_nonneg v) hq0.ne',
      card_univ, Fintype.card_fin, Real.sqrt_eq_rpow, ← mul_assoc] at this
    exact le_of_mul_le_mul_right this (norm_pos_iff.2 hv)
  have := Real.le_of_forall_natCast_rpow_le_mul_rpow key
  have : (1 / 2 : ℝ) < 1 / q := one_div_lt_one_div_of_lt hq0 hq
  linarith

end TauCeti
