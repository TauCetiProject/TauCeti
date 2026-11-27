/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonMaclaurin

/-!
# Mean inequalities

This file collects classical inequalities complementing `Mathlib.Analysis.MeanInequalities`.

For nonnegative weights `w i` summing to `1`, the weighted geometric mean
`G(a) = ∏ i, a i ^ w i` of a nonnegative family is superadditive:

`G(a) + G(b) ≤ G(a + b)`.

Since `G` is also positively homogeneous, this says that the weighted geometric mean is concave on
the nonnegative orthant. Applied to the eigenvalues of a positive semidefinite matrix `M` with
equal weights, it gives `1 + det M ^ (1 / n) ≤ det (1 + M) ^ (1 / n)`, the core of Minkowski's
determinant inequality (`Matrix.PosSemidef.det_rpow_add_det_rpow_le`).

The proof divides by `a i + b i` and applies the inequality of arithmetic and geometric means
`Real.geom_mean_le_arith_mean_weighted` to the two normalized families, whose weighted means add
up to at most `1`.

Minkowski's inequality also holds for unconditional sums of `ℝ≥0∞`-valued families over an
arbitrary index type, with no summability hypotheses: infinite sums and infinite terms are allowed.
Mathlib states it for finite sums (`ENNReal.Lp_add_le`) and for summable `ℝ≥0`-valued families
(`NNReal.Lp_add_le_tsum`); the `ℝ≥0∞` form follows from the finite one by taking the supremum over
finite partial sums. It is the counting-measure case of `ENNReal.lintegral_Lp_add_le`, stated
without measure theory. It gives the triangle inequality for gauges defined as `ℓᵖ` sums in `ℝ≥0∞`,
such as the Hilbert–Schmidt energy of an operator. Hölder's inequality holds for such sums in the
same way, extending `ENNReal.inner_le_Lp_mul_Lq` and `NNReal.inner_le_Lp_mul_Lq_tsum`. The `ℓᵖ`
norm of such a family is antitone in the exponent, which gives the inclusions between Schatten
classes of operators. A double sum of `a j * b k` over the band `|j - k| < L` is bounded by
`2 L` times the `ℓ²` norms of `a` and `b`, the form of Cauchy–Schwarz used to pair almost
orthogonal Littlewood–Paley blocks.

Mathlib states the two-point weighted AM-GM inequality in `ℝ≥0∞` with `ℝ≥0` weights
(`ENNReal.geom_mean_le_arith_mean2_weighted`); it is restated here for the real weights `1 - θ`
and `θ`, as they appear in interpolation inequalities such as Prékopa–Leindler.

The two-point weighted AM-GM inequality is also restated after normalizing by positive scalars
`a` and `b`: `A ^ (1 - θ) * B ^ θ ≤ ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ)`,
strictly when `0 < θ < 1` and `A / a ≠ B / b`. This is the form used to compare volumes of
hyperplane sections in the Kneser–Süss equality argument for Brunn–Minkowski.

The triangle inequality for the Euclidean norm on `ℝ²`, applied to finitely many coordinate pairs
`(a i, b i)`, reads `√((∑ a i) ^ 2 + (∑ b i) ^ 2) ≤ ∑ √(a i ^ 2 + b i ^ 2)`. It bounds a norm
defined as the Euclidean combination of two component norms, each subadditive, such as the norm
of a higher-order Sobolev space.

Maclaurin's inequalities `S_l^k ≤ S_k^l` between the elementary symmetric means
`S_j = σ_j(s) / binom(card s, j)` of a multiset `s` (`Multiset.esymm_div_choose_pow_le_pow`) take
over `ℝ` the equivalent root form `S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l`, on the cone
`σ_1, …, σ_l > 0` and for nonnegative reals. The closed nonnegative orthant lies in the closure of
the cone, and on its boundary part `σ_l` vanishes. At `k = 1` and `l = card s` this is the
inequality of arithmetic and geometric means.

## Main statements

* `Real.prod_rpow_add_prod_rpow_le_prod_add_rpow`: the weighted geometric mean is superadditive.
* `Real.prod_rpow_inv_card_add_le`: the same at equal weights `1 / n`.
* `Real.concaveOn_prod_rpow`: the geometric mean is concave on the nonnegative orthant.
* `Real.sq_add_sq_le_rpow_mul_rpow`: two interpolation bounds combine into one for the Euclidean
  norms of the pairs.
* `Real.geom_mean_le_arith_mean2_weighted_div_mul`,
  `Real.geom_mean_lt_arith_mean2_weighted_div_mul`: two-point weighted AM-GM after normalizing
  by positive scalars, with the strict form.
* `Real.sqrt_sum_sq_add_sum_sq_le_sum_sqrt`: the triangle inequality in the plane for finite
  sums of coordinate pairs.
* `Real.le_div_add_rpow_mul_of_le_add_mul_rpow_mul_rpow`: absorption of a power `M^θ`, `θ < 1`,
  in a bound `M ≤ A + B M^θ N^(1 - θ)`.
* `Real.mul_rpow_mul_rpow_le_half_add`: Young's inequality
  `K X^θ F^(1 - θ) ≤ F / 2 + (2 K)^(1/θ) X`, which absorbs half of `F`.
* `ENNReal.geom_mean_le_arith_mean2_weighted_ofReal`: two-point weighted AM-GM in `ℝ≥0∞` with
  the real weights `1 - θ` and `θ`.
* `ENNReal.Lp_add_le_tsum`: Minkowski's inequality for unconditional sums in `ℝ≥0∞`.
* `ENNReal.inner_le_Lp_mul_Lq_tsum`: Hölder's inequality for unconditional sums in `ℝ≥0∞`.
* `ENNReal.Lq_le_Lp_tsum`: the `ℓᵖ` norm of an `ℝ≥0∞`-valued family is antitone in `p`.
* `ENNReal.tsum_sum_mul_le_of_card_le`: Cauchy–Schwarz for a banded double sum in `ℝ≥0∞`.
* `Real.Lq_le_Lp_of_nonneg`: the same for finite sums of nonnegative reals.
* `Real.Lp_le_mul_Lp_of_nonneg`: termwise domination `0 ≤ f i ≤ c * g i` bounds the finite
  `ℓᵖ` expression of `f` by `c` times that of `g`.
* `Real.Lp_const_of_nonneg`: the finite `ℓᵖ` expression of a constant `t ≥ 0` over `s` is
  `#s ^ (1 / p) * t`.
* `Real.prod_le_sqrt_sum_sq_div_sqrt_card_pow`: AM-GM comparing a product of nonnegative
  numbers with their root mean square, `∏ i ∈ s, σ i ≤ (√(∑ i ∈ s, σ i ^ 2) / √#s) ^ #s`, and
  its equality case `Real.prod_eq_sqrt_sum_sq_div_sqrt_card_pow_iff` (all `σ i` agree).
* `Multiset.esymm_div_choose_rpow_le_rpow`,
  `Multiset.esymm_div_choose_rpow_le_rpow_of_nonneg`: Maclaurin's inequalities in root form, on
  the cone `σ_1, …, σ_l > 0` and for nonnegative reals.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge University Press
  1952, Chapter II (§2.22 for Maclaurin's inequalities).
-/

public section

namespace Real

/-- **Superadditivity of the weighted geometric mean.** For nonnegative weights `w i` summing to
`1` and nonnegative families `a` and `b`,
`∏ i ∈ s, a i ^ w i + ∏ i ∈ s, b i ^ w i ≤ ∏ i ∈ s, (a i + b i) ^ w i`. -/
theorem prod_rpow_add_prod_rpow_le_prod_add_rpow {ι : Type*} (s : Finset ι) {w a b : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∏ i ∈ s, a i ^ w i + ∏ i ∈ s, b i ^ w i ≤ ∏ i ∈ s, (a i + b i) ^ w i := by
  have hc (i) (hi : i ∈ s) : 0 ≤ a i + b i := add_nonneg (ha i hi) (hb i hi)
  -- Factor `a i = (a i / (a i + b i)) * (a i + b i)`, and likewise for `b`; this holds even when
  -- `a i + b i = 0`, since then `a i = b i = 0`.
  have hfactor {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hfc : ∀ i ∈ s, f i ≤ a i + b i) :
      ∏ i ∈ s, f i ^ w i =
        (∏ i ∈ s, (f i / (a i + b i)) ^ w i) * ∏ i ∈ s, (a i + b i) ^ w i := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [← mul_rpow (div_nonneg (hf i hi) (hc i hi)) (hc i hi),
      div_mul_cancel_of_imp fun h => le_antisymm (h ▸ hfc i hi) (hf i hi)]
  rw [hfactor ha fun i hi => le_add_of_nonneg_right (hb i hi),
    hfactor hb fun i hi => le_add_of_nonneg_left (ha i hi), ← add_mul]
  refine mul_le_of_le_one_left (Finset.prod_nonneg fun i hi => rpow_nonneg (hc i hi) _) ?_
  -- The two normalized families have weighted arithmetic means adding up to at most `1`.
  calc ∏ i ∈ s, (a i / (a i + b i)) ^ w i + ∏ i ∈ s, (b i / (a i + b i)) ^ w i
      ≤ ∑ i ∈ s, w i * (a i / (a i + b i)) + ∑ i ∈ s, w i * (b i / (a i + b i)) :=
        add_le_add
          (geom_mean_le_arith_mean_weighted s w _ hw hw' fun i hi => div_nonneg (ha i hi) (hc i hi))
          (geom_mean_le_arith_mean_weighted s w _ hw hw' fun i hi => div_nonneg (hb i hi) (hc i hi))
    _ = ∑ i ∈ s, w i * ((a i + b i) / (a i + b i)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [add_div, mul_add]
    _ ≤ ∑ i ∈ s, w i := Finset.sum_le_sum fun i hi =>
        mul_le_of_le_one_right (hw i hi) (div_self_le_one _)
    _ = 1 := hw'

/-- The geometric mean `(∏ i, μ i) ^ (1 / n)`, `n = card ι ≥ 1`, is positively homogeneous:
`(∏ i, t * μ i) ^ (1 / n) = t * (∏ i, μ i) ^ (1 / n)` for `t ≥ 0` and `μ ≥ 0`. -/
theorem prod_mul_rpow_inv_card {ι : Type*} [Fintype ι] [Nonempty ι] {t : ℝ} (ht : 0 ≤ t)
    {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) :
    (∏ i, t * μ i) ^ (Fintype.card ι : ℝ)⁻¹ = t * (∏ i, μ i) ^ (Fintype.card ι : ℝ)⁻¹ := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    mul_rpow (pow_nonneg ht _) (Finset.prod_nonneg fun i _ ↦ hμ i),
    pow_rpow_inv_natCast ht Fintype.card_ne_zero]

/-- **Superadditivity of the geometric mean.** For nonnegative families `a` and `b` indexed by a
nonempty finite type, `(∏ i, a i) ^ (1 / n) + (∏ i, b i) ^ (1 / n) ≤ (∏ i, (a i + b i)) ^ (1 / n)`,
where `n = card ι`. This is `Real.prod_rpow_add_prod_rpow_le_prod_add_rpow` at equal weights. -/
theorem prod_rpow_inv_card_add_le {ι : Type*} [Fintype ι] [Nonempty ι] {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∏ i, a i) ^ (Fintype.card ι : ℝ)⁻¹ + (∏ i, b i) ^ (Fintype.card ι : ℝ)⁻¹ ≤
      (∏ i, (a i + b i)) ^ (Fintype.card ι : ℝ)⁻¹ := by
  rw [← finsetProd_rpow _ _ fun i _ ↦ ha i, ← finsetProd_rpow _ _ fun i _ ↦ hb i,
    ← finsetProd_rpow _ _ fun i _ ↦ add_nonneg (ha i) (hb i)]
  exact prod_rpow_add_prod_rpow_le_prod_add_rpow Finset.univ
    (fun _ _ ↦ inv_nonneg.2 (Nat.cast_nonneg _))
    (by simp [Finset.card_univ, Fintype.card_ne_zero]) (fun i _ ↦ ha i) fun i _ ↦ hb i

/-- **Concavity of the geometric mean.** The geometric mean `μ ↦ (∏ i, μ i) ^ (1 / n)`,
`n = card ι`, is concave on the nonnegative orthant. -/
theorem concaveOn_prod_rpow {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ {μ : ι → ℝ | ∀ i, 0 ≤ μ i}
      fun μ ↦ (∏ i, μ i) ^ (Fintype.card ι : ℝ)⁻¹ := by
  -- The nonnegative orthant is the product `Set.univ.pi fun _ ↦ Set.Ici 0` of half-lines.
  have hconv : Convex ℝ {μ : ι → ℝ | ∀ i, 0 ≤ μ i} := by
    simpa [Set.pi] using convex_pi (s := Set.univ) fun i _ ↦ convex_Ici (0 : ℝ)
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact (concaveOn_const 1 hconv).congr fun μ _ ↦ by simp
  refine ⟨hconv, fun μ hμ ν hν a b ha hb _ ↦ ?_⟩
  -- Superadditivity applied to `a • μ` and `b • ν`.
  have hsuper := prod_rpow_inv_card_add_le (fun i ↦ mul_nonneg ha (hμ i))
    (fun i ↦ mul_nonneg hb (hν i))
  rw [prod_mul_rpow_inv_card ha hμ, prod_mul_rpow_inv_card hb hν] at hsuper
  simpa using hsuper

/-- Two interpolation bounds `a ≤ a₀ ^ (1 - θ) a₁ ^ θ` and `b ≤ b₀ ^ (1 - θ) b₁ ^ θ` combine into
the interpolation bound for the squared Euclidean norms of the pairs `(a, b)`, `(a₀, b₀)` and
`(a₁, b₁)`, by Hölder's inequality for two terms. -/
theorem sq_add_sq_le_rpow_mul_rpow {a b a₀ a₁ b₀ b₁ θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hal : a ≤ a₀ ^ (1 - θ) * a₁ ^ θ) (hbl : b ≤ b₀ ^ (1 - θ) * b₁ ^ θ) :
    a ^ 2 + b ^ 2 ≤ (a₀ ^ 2 + b₀ ^ 2) ^ (1 - θ) * (a₁ ^ 2 + b₁ ^ 2) ^ θ := by
  have key := prod_rpow_add_prod_rpow_le_prod_add_rpow Finset.univ (w := ![1 - θ, θ])
    (a := ![a₀ ^ 2, a₁ ^ 2]) (b := ![b₀ ^ 2, b₁ ^ 2])
    (by simp [Fin.forall_fin_two, hθ.1, hθ.2]) (by simp [Fin.sum_univ_two])
    (by simp [Fin.forall_fin_two, sq_nonneg]) (by simp [Fin.forall_fin_two, sq_nonneg])
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at key
  calc a ^ 2 + b ^ 2 ≤ (a₀ ^ (1 - θ) * a₁ ^ θ) ^ 2 + (b₀ ^ (1 - θ) * b₁ ^ θ) ^ 2 :=
        add_le_add (pow_le_pow_left₀ ha hal 2) (pow_le_pow_left₀ hb hbl 2)
    _ = (a₀ ^ 2) ^ (1 - θ) * (a₁ ^ 2) ^ θ + (b₀ ^ 2) ^ (1 - θ) * (b₁ ^ 2) ^ θ := by
        rw [mul_pow, mul_pow, rpow_pow_comm ha₀, rpow_pow_comm ha₁,
          rpow_pow_comm hb₀, rpow_pow_comm hb₁]
    _ ≤ _ := key

/-- Splitting a weighted geometric mean through positive normalizers `a` and `b`:
`A ^ (1 - θ) * B ^ θ = (A / a) ^ (1 - θ) * (B / b) ^ θ * (a ^ (1 - θ) * b ^ θ)`. -/
theorem rpow_one_sub_mul_rpow_eq_div_mul {A B a b θ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    A ^ (1 - θ) * B ^ θ = (A / a) ^ (1 - θ) * (B / b) ^ θ * (a ^ (1 - θ) * b ^ θ) := by
  rw [div_rpow_of_pos_right ha, div_rpow_of_pos_right hb]
  have := (rpow_pos_of_pos ha (1 - θ)).ne'
  have := (rpow_pos_of_pos hb θ).ne'
  field_simp

/-- **Normalized weighted AM-GM.** For positive normalizers `a` and `b`, the weighted geometric
mean of `A` and `B` is at most the weighted arithmetic mean of `A / a` and `B / b` times the
weighted geometric mean of `a` and `b`. -/
theorem geom_mean_le_arith_mean2_weighted_div_mul {A B a b θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hb : 0 < b) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    A ^ (1 - θ) * B ^ θ ≤ ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ) := by
  rw [rpow_one_sub_mul_rpow_eq_div_mul ha hb]
  exact mul_le_mul_of_nonneg_right (geom_mean_le_arith_mean2_weighted (by linarith) hθ₀
    (div_nonneg hA ha.le) (div_nonneg hB hb.le) (by ring))
    (mul_nonneg (rpow_nonneg ha.le _) (rpow_nonneg hb.le _))

/-- The strict form of `Real.geom_mean_le_arith_mean2_weighted_div_mul` for `0 < θ < 1` and
`A / a ≠ B / b`. -/
theorem geom_mean_lt_arith_mean2_weighted_div_mul {A B a b θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hb : 0 < b) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hne : A / a ≠ B / b) :
    A ^ (1 - θ) * B ^ θ < ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ) := by
  rw [rpow_one_sub_mul_rpow_eq_div_mul ha hb]
  exact mul_lt_mul_of_pos_right ((geom_mean_lt_arith_mean2_weighted_iff_of_pos
    (by linarith) hθ₀ (div_nonneg hA ha.le) (div_nonneg hB hb.le) (by ring)).2 hne)
    (mul_pos (rpow_pos_of_pos ha _) (rpow_pos_of_pos hb _))

/-- **Triangle inequality in the plane.** For finite families `a` and `b`,
`√((∑ i ∈ s, a i) ^ 2 + (∑ i ∈ s, b i) ^ 2) ≤ ∑ i ∈ s, √(a i ^ 2 + b i ^ 2)`. -/
theorem sqrt_sum_sq_add_sum_sq_le_sum_sqrt {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    √((∑ i ∈ s, a i) ^ 2 + (∑ i ∈ s, b i) ^ 2) ≤ ∑ i ∈ s, √(a i ^ 2 + b i ^ 2) := by
  have h (x y : ℝ) : √(x ^ 2 + y ^ 2) = ‖(⟨x, y⟩ : ℂ)‖ := by
    rw [Complex.norm_def, Complex.normSq_mk, sq, sq]
  have hsum : (⟨∑ i ∈ s, a i, ∑ i ∈ s, b i⟩ : ℂ) = ∑ i ∈ s, ⟨a i, b i⟩ :=
    Complex.ext (by rw [Complex.re_sum]) (by rw [Complex.im_sum])
  simpa only [h, hsum] using norm_sum_le s fun i => (⟨a i, b i⟩ : ℂ)

/-- **Absorption.** If `M ≤ A + B M^θ N^(1 - θ)` with `0 ≤ θ < 1` and `M, B, N ≥ 0`, then
`M ≤ A / (1 - θ) + B^(1 / (1 - θ)) N`, by Young's inequality
`M^θ D^(1 - θ) ≤ θ M + (1 - θ) D` for `D = B^(1 / (1 - θ)) N`. -/
theorem le_div_add_rpow_mul_of_le_add_mul_rpow_mul_rpow {M A B N θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hM : 0 ≤ M) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (h : M ≤ A + B * M ^ θ * N ^ (1 - θ)) : M ≤ A / (1 - θ) + B ^ (1 / (1 - θ)) * N := by
  set D := B ^ (1 / (1 - θ)) * N
  have hD : 0 ≤ D := by positivity
  have hBN : B * N ^ (1 - θ) = D ^ (1 - θ) := by
    rw [mul_rpow (by positivity) hN, ← rpow_mul hB, one_div_mul_cancel (by linarith),
      rpow_one]
  have hY := geom_mean_le_arith_mean2_weighted hθ0 (by linarith : 0 ≤ 1 - θ) hM hD
    (by ring)
  have h' : M ≤ A + (θ * M + (1 - θ) * D) :=
    calc M ≤ A + B * M ^ θ * N ^ (1 - θ) := h
      _ = A + M ^ θ * D ^ (1 - θ) := by rw [← hBN]; ring
      _ ≤ _ := by gcongr
  rw [div_add' _ _ _ (by linarith), le_div_iff₀ (by linarith)]
  nlinarith

/-- **Young's inequality for absorption.**
`K X^θ F^(1-θ) ≤ F / 2 + (2 K)^(1/θ) X` for `K, X, F ≥ 0` and `0 < θ ≤ 1`. -/
theorem mul_rpow_mul_rpow_le_half_add {K X F θ : ℝ} (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hF : 0 ≤ F) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    K * (X ^ θ * F ^ (1 - θ)) ≤ F / 2 + (2 * K) ^ θ⁻¹ * X := by
  have hp₁ : 0 ≤ (2 * K) ^ θ⁻¹ * X := by positivity
  have hp₂ : 0 ≤ F / 2 := by positivity
  have hAM := Real.geom_mean_le_arith_mean2_weighted hθ0.le (sub_nonneg.2 hθ1) hp₁ hp₂
    (by ring)
  have h1 : ((2 * K) ^ θ⁻¹ * X) ^ θ = 2 * K * X ^ θ := by
    rw [Real.mul_rpow (by positivity) hX, Real.rpow_inv_rpow (by positivity) hθ0.ne']
  have h2 : (F / 2) ^ (1 - θ) = F ^ (1 - θ) / 2 ^ (1 - θ) := Real.div_rpow hF (by norm_num) _
  have h3 : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : 1 - θ ≤ 1)
  have h4 : (0 : ℝ) < 2 ^ (1 - θ) := by positivity
  calc K * (X ^ θ * F ^ (1 - θ)) ≤ 2 * K * X ^ θ * F ^ (1 - θ) / 2 ^ (1 - θ) := by
        rw [le_div_iff₀ h4]
        have : 0 ≤ K * X ^ θ * F ^ (1 - θ) := by positivity
        nlinarith
    _ = ((2 * K) ^ θ⁻¹ * X) ^ θ * (F / 2) ^ (1 - θ) := by rw [h1, h2]; ring
    _ ≤ θ * ((2 * K) ^ θ⁻¹ * X) + (1 - θ) * (F / 2) := hAM
    _ ≤ (2 * K) ^ θ⁻¹ * X + F / 2 := by
        gcongr ?_ + ?_
        · exact mul_le_of_le_one_left hp₁ hθ1
        · exact mul_le_of_le_one_left hp₂ (by linarith)
    _ = _ := by ring

end Real

namespace ENNReal

open scoped ENNReal

/-- The weighted AM-GM inequality in `ℝ≥0∞` for the real weights `1 - θ` and `θ`:
`a ^ (1 - θ) * b ^ θ ≤ ofReal (1 - θ) * a + ofReal θ * b` for `0 ≤ θ ≤ 1`. -/
theorem geom_mean_le_arith_mean2_weighted_ofReal {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (a b : ℝ≥0∞) : a ^ (1 - θ) * b ^ θ ≤ ENNReal.ofReal (1 - θ) * a + ENNReal.ofReal θ * b := by
  have h := geom_mean_le_arith_mean2_weighted (1 - θ).toNNReal θ.toNNReal a b <| by
    rw [← Real.toNNReal_add (sub_nonneg.2 hθ₁) hθ₀, sub_add_cancel, Real.toNNReal_one]
  rwa [Real.coe_toNNReal _ (sub_nonneg.2 hθ₁), Real.coe_toNNReal _ hθ₀] at h

/-- **Minkowski's inequality** for unconditional sums in `ℝ≥0∞`: for `1 ≤ p`,
`(∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)`.
No summability hypotheses are needed; both sides may be infinite. -/
theorem Lp_add_le_tsum {ι : Type*} (f g : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  -- Bound each finite partial sum by the finite Minkowski inequality.
  rw [one_div, rpow_inv_le_iff hp0, _root_.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  rw [← rpow_inv_le_iff hp0, ← one_div]
  grw [Lp_add_le s f g hp, _root_.sum_le_tsum s, _root_.sum_le_tsum (f := fun i ↦ g i ^ p) s]

/-- **Hölder's inequality** for unconditional sums in `ℝ≥0∞`: for conjugate exponents `p` and `q`,
`∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q)`.
No summability hypotheses are needed; both sides may be infinite. -/
theorem inner_le_Lp_mul_Lq_tsum {ι : Type*} (f g : ι → ℝ≥0∞) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  -- Bound each finite partial sum by the finite Hölder inequality.
  rw [_root_.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ (inner_le_Lp_mul_Lq s f g hpq).trans ?_
  gcongr
  · exact one_div_nonneg.2 hpq.nonneg
  · exact _root_.sum_le_tsum s
  · exact one_div_nonneg.2 hpq.symm.nonneg
  · exact _root_.sum_le_tsum s

/-- The `ℓᵖ` norms of an `ℝ≥0∞`-valued family decrease as the exponent grows: for `0 < p ≤ q`,
`(∑' i, f i ^ q) ^ (1 / q) ≤ (∑' i, f i ^ p) ^ (1 / p)`. No summability hypotheses are needed;
both sides may be infinite. This is the unconditional-sum form of `ENNReal.rpow_add_rpow_le`. -/
theorem Lq_le_Lp_tsum {ι : Type*} (f : ι → ℝ≥0∞) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑' i, f i ^ q) ^ (1 / q) ≤ (∑' i, f i ^ p) ^ (1 / p) := by
  set S := (∑' i, f i ^ p) ^ (1 / p) with hS
  have hpq' : 0 ≤ q - p := sub_nonneg.2 hpq
  -- Each term is at most the `ℓᵖ` norm `S`, so `f i ^ q ≤ f i ^ p * S ^ (q - p)`.
  have hfS (i : ι) : f i ≤ S := by
    rw [hS, one_div, le_rpow_inv_iff hp]
    exact _root_.le_tsum (f := fun i ↦ f i ^ p) i
  have hSp : S ^ p = ∑' i, f i ^ p := by rw [hS, one_div, rpow_inv_rpow hp.ne']
  rw [one_div, rpow_inv_le_iff (hp.trans_le hpq)]
  calc ∑' i, f i ^ q = ∑' i, f i ^ p * f i ^ (q - p) := by
        simp_rw [← rpow_add_of_nonneg _ _ hp.le hpq', add_sub_cancel]
    _ ≤ ∑' i, f i ^ p * S ^ (q - p) := by gcongr with i; exact hfS i
    _ = S ^ q := by
        rw [ENNReal.tsum_mul_right, ← hSp, ← rpow_add_of_nonneg _ _ hp.le hpq', add_sub_cancel]


/-- **Cauchy–Schwarz for a banded double sum.** Let `W i` be finite sets of indices, each with at
most `L` elements, such that every index `k` lies in at most `L` of them. Summing `a i * b k` over
the pairs with `k ∈ W i` gives at most `L (∑ a²)^{1/2} (∑ b²)^{1/2}`. No summability hypotheses
are needed; both sides may be infinite. -/
theorem tsum_sum_mul_le_of_card_le {ι : Type*} [DecidableEq ι] (W : ι → Finset ι) {L : ℕ}
    (hW : ∀ i, (W i).card ≤ L) (hW' : ∀ (s : Finset ι) (k : ι), (s.filter (k ∈ W ·)).card ≤ L)
    (a b : ι → ℝ≥0∞) :
    ∑' i, ∑ k ∈ W i, a i * b k ≤
      L * ((∑' i, a i ^ 2) ^ (2⁻¹ : ℝ) * (∑' k, b k ^ 2) ^ (2⁻¹ : ℝ)) := by
  rw [_root_.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  -- Cauchy–Schwarz over the finite set `T` of pairs `(i, k)` with `i ∈ s` and `k ∈ W i`, in which
  -- each first index `i` and each second index `k` occurs at most `L` times.
  set T := s.sigma W
  have ha : ∑ x ∈ T, a x.1 ^ (2 : ℝ) ≤ L * ∑' i, a i ^ 2 := by
    rw [Finset.sum_sigma]
    simp only [rpow_two, Finset.sum_const, nsmul_eq_mul]
    calc ∑ i ∈ s, ((W i).card : ℝ≥0∞) * a i ^ 2 ≤ ∑ i ∈ s, (L : ℝ≥0∞) * a i ^ 2 := by
          gcongr with i
          exact_mod_cast hW i
      _ ≤ L * ∑' i, a i ^ 2 := by
          rw [← Finset.mul_sum]
          gcongr
          exact _root_.sum_le_tsum _
  have hb : ∑ x ∈ T, b x.2 ^ (2 : ℝ) ≤ L * ∑' k, b k ^ 2 := by
    rw [Finset.sum_sigma, Finset.sum_comm' (t' := s.biUnion W)
      (s' := fun k ↦ s.filter (k ∈ W ·))]
    · simp only [rpow_two, Finset.sum_const, nsmul_eq_mul]
      calc ∑ k ∈ s.biUnion W, ((s.filter (k ∈ W ·)).card : ℝ≥0∞) * b k ^ 2
          ≤ ∑ k ∈ s.biUnion W, (L : ℝ≥0∞) * b k ^ 2 := by
            gcongr with k
            exact_mod_cast hW' s k
        _ ≤ L * ∑' k, b k ^ 2 := by
            rw [← Finset.mul_sum]
            gcongr
            exact _root_.sum_le_tsum _
    · intro i k
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2⟩, i, h.1, h.2⟩, fun h ↦ h.1⟩
  have hL : ((L : ℝ≥0∞) ^ (2⁻¹ : ℝ)) * (L : ℝ≥0∞) ^ (2⁻¹ : ℝ) = L := by
    rw [← rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc ∑ i ∈ s, ∑ k ∈ W i, a i * b k = ∑ x ∈ T, a x.1 * b x.2 := by
        rw [Finset.sum_sigma]
    _ ≤ (∑ x ∈ T, a x.1 ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑ x ∈ T, b x.2 ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        inner_le_Lp_mul_Lq T (fun x ↦ a x.1) (fun x ↦ b x.2) Real.HolderConjugate.two_two
    _ ≤ (L * ∑' i, a i ^ 2) ^ (2⁻¹ : ℝ) * (L * ∑' k, b k ^ 2) ^ (2⁻¹ : ℝ) := by
        rw [one_div]
        gcongr
    _ = (L : ℝ≥0∞) ^ (2⁻¹ : ℝ) * (L : ℝ≥0∞) ^ (2⁻¹ : ℝ) *
          ((∑' i, a i ^ 2) ^ (2⁻¹ : ℝ) * (∑' k, b k ^ 2) ^ (2⁻¹ : ℝ)) := by
        rw [mul_rpow_of_nonneg _ _ (by norm_num), mul_rpow_of_nonneg (L : ℝ≥0∞) _ (by norm_num)]
        ring
    _ = L * ((∑' i, a i ^ 2) ^ (2⁻¹ : ℝ) * (∑' k, b k ^ 2) ^ (2⁻¹ : ℝ)) := by rw [hL]

end ENNReal

namespace Real

/-- The `ℓᵖ` norms of a finite nonnegative real family decrease as the exponent grows: for
`0 < p ≤ q`, `(∑ i ∈ s, f i ^ q) ^ (1 / q) ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p)`. -/
theorem Lq_le_Lp_of_nonneg {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, f i ^ q) ^ (1 / q) ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) := by
  have hq : 0 < q := hp.trans_le hpq
  -- Transport the unconditional `ℝ≥0∞` inequality along `ENNReal.ofReal`.
  have hofReal {r : ℝ} (hr : 0 < r) :
      ENNReal.ofReal ((∑ i ∈ s, f i ^ r) ^ (1 / r)) =
        (∑' i : s, ENNReal.ofReal (f i) ^ r) ^ (1 / r) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun i hi ↦
        rpow_nonneg (hf i hi) r) (one_div_nonneg.2 hr.le), tsum_fintype,
      ENNReal.ofReal_sum_of_nonneg fun i hi ↦ rpow_nonneg (hf i hi) r]
    congr 1
    rw [← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun i _ ↦ (ENNReal.ofReal_rpow_of_nonneg
        (hf i i.property) hr.le).symm
  have h := ENNReal.Lq_le_Lp_tsum (fun i : s ↦ ENNReal.ofReal (f i)) hp hpq
  rw [← hofReal hq, ← hofReal hp] at h
  exact (ENNReal.ofReal_le_ofReal_iff (rpow_nonneg (Finset.sum_nonneg fun i hi ↦
    rpow_nonneg (hf i hi) p) _)).1 h

/-- The `ℓᵖ` expression of a finite nonnegative family dominated termwise by `c` times another is
at most `c` times the other's: if `0 ≤ f i ≤ c * g i`, then
`(∑ i ∈ s, f i ^ p) ^ (1 / p) ≤ c * (∑ i ∈ s, g i ^ p) ^ (1 / p)`. -/
theorem Lp_le_mul_Lp_of_nonneg {ι : Type*} (s : Finset ι) {f g : ι → ℝ} {p c : ℝ} (hp : 0 < p)
    (hc : 0 ≤ c) (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ c * g i) :
    (∑ i ∈ s, f i ^ p) ^ (1 / p) ≤ c * (∑ i ∈ s, g i ^ p) ^ (1 / p) := by
  calc (∑ i ∈ s, f i ^ p) ^ (1 / p) ≤ (∑ i ∈ s, (c * g i) ^ p) ^ (1 / p) := by
        gcongr with i hi
        · exact Finset.sum_nonneg fun i hi ↦ rpow_nonneg (hf i hi) p
        · exact hf i hi
        · exact hfg i hi
    _ = c * (∑ i ∈ s, g i ^ p) ^ (1 / p) := by
        simp only [mul_rpow_of_nonneg_left hc]
        rw [← Finset.mul_sum, mul_rpow_of_nonneg_left (rpow_nonneg hc p), one_div,
          rpow_rpow_inv hc hp.ne']

/-- The finite `ℓᵖ` expression of a constant `t ≥ 0` over `s` is `#s ^ (1 / p) * t`. -/
theorem Lp_const_of_nonneg {ι : Type*} (s : Finset ι) {t p : ℝ} (ht : 0 ≤ t) (hp : p ≠ 0) :
    (∑ _i ∈ s, t ^ p) ^ (1 / p) = (s.card : ℝ) ^ (1 / p) * t := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_rpow s.card.cast_nonneg (rpow_nonneg ht p), one_div,
    rpow_rpow_inv ht hp]

/-- **Arithmetic and geometric means** for nonnegative numbers, comparing the product with the
root mean square: `∏ i ∈ s, σ i ≤ (√(∑ i ∈ s, σ i ^ 2) / √#s) ^ #s`. -/
theorem prod_le_sqrt_sum_sq_div_sqrt_card_pow {ι : Type*} (s : Finset ι) (σ : ι → ℝ)
    (hσ : ∀ i ∈ s, 0 ≤ σ i) :
    ∏ i ∈ s, σ i ≤ (√(∑ i ∈ s, σ i ^ 2) / √(s.card : ℝ)) ^ s.card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hS : 0 ≤ ∑ i ∈ s, σ i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hnR : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  -- AM-GM for the squares `σᵢ²`, with unit weights.
  have hamgm := geom_mean_le_arith_mean s (fun _ ↦ (1 : ℝ)) (fun i ↦ σ i ^ 2)
    (fun _ _ ↦ zero_le_one) (by simpa using hnR) (fun i _ ↦ sq_nonneg _)
  simp only [rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hamgm
  rw [rpow_inv_le_iff_of_pos (Finset.prod_nonneg fun i _ ↦ sq_nonneg _)
    (div_nonneg hS hnR.le) hnR, rpow_natCast, Finset.prod_pow] at hamgm
  have hrhs : (∑ i ∈ s, σ i ^ 2) / s.card = (√(∑ i ∈ s, σ i ^ 2) / √(s.card : ℝ)) ^ 2 := by
    rw [div_pow, sq_sqrt hS, sq_sqrt hnR.le]
  rw [hrhs, ← pow_mul, pow_mul'] at hamgm
  exact (pow_le_pow_iff_left₀ (Finset.prod_nonneg hσ)
    (pow_nonneg (div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) _) two_ne_zero).mp hamgm

/-- **Equality case of the arithmetic and geometric means** for nonnegative numbers, compared with
the root mean square: `∏ i ∈ s, σ i = (√(∑ i ∈ s, σ i ^ 2) / √#s) ^ #s` exactly when all the
`σ i` agree. -/
theorem prod_eq_sqrt_sum_sq_div_sqrt_card_pow_iff {ι : Type*} (s : Finset ι) (σ : ι → ℝ)
    (hσ : ∀ i ∈ s, 0 ≤ σ i) :
    ∏ i ∈ s, σ i = (√(∑ i ∈ s, σ i ^ 2) / √(s.card : ℝ)) ^ s.card ↔
      ∀ j ∈ s, ∀ k ∈ s, σ j = σ k := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hN : s.card ≠ 0 := hs.card_pos.ne'
  have hNR : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hS : 0 ≤ ∑ i ∈ s, σ i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hP : 0 ≤ ∏ i ∈ s, σ i := Finset.prod_nonneg hσ
  have hr : 0 ≤ √(∑ i ∈ s, σ i ^ 2) / √(s.card : ℝ) := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  -- AM-GM with equal weights `1 / #s` for the squares `σᵢ²`.
  have hamgm := geom_mean_eq_arith_mean_weighted_iff_of_pos s (fun _ ↦ ((s.card : ℝ))⁻¹)
    (fun i ↦ σ i ^ 2) (fun _ _ ↦ inv_pos.mpr hNR)
    (by rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hNR.ne']) (fun i _ ↦ sq_nonneg _)
  have hl : ∏ i ∈ s, (σ i ^ 2) ^ ((s.card : ℝ))⁻¹ = ((∏ i ∈ s, σ i) ^ ((s.card : ℝ))⁻¹) ^ 2 := by
    rw [← Real.finsetProd_rpow s σ hσ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul (hσ i hi), ← rpow_mul (hσ i hi), mul_comm]
  have hrr : ∑ i ∈ s, ((s.card : ℝ))⁻¹ * σ i ^ 2 =
      (√(∑ i ∈ s, σ i ^ 2) / √(s.card : ℝ)) ^ 2 := by
    rw [← Finset.mul_sum, div_pow, sq_sqrt hS, sq_sqrt hNR.le, inv_mul_eq_div]
  rw [hl, hrr, pow_left_inj₀ (rpow_nonneg hP _) hr two_ne_zero] at hamgm
  have hroot : ∏ i ∈ s, σ i = (√(∑ i ∈ s, σ i ^ 2) / √(s.card : ℝ)) ^ s.card ↔
      (∏ i ∈ s, σ i) ^ ((s.card : ℝ))⁻¹ = √(∑ i ∈ s, σ i ^ 2) / √(s.card : ℝ) := by
    constructor <;> intro h
    · rw [h, pow_rpow_inv_natCast hr hN]
    · rw [← h, rpow_inv_natCast_pow hP hN]
  rw [hroot, hamgm]
  exact forall₂_congr fun j hj ↦ forall₂_congr fun k hk ↦
    pow_left_inj₀ (hσ j hj) (hσ k hk) two_ne_zero

end Real

namespace Multiset

variable (s : Multiset ℝ)

/-- **Maclaurin's inequalities**: if `σ_1(s), …, σ_l(s) > 0`, then the elementary symmetric means
`S_j = σ_j(s) / binom(card s, j)` satisfy `S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l`. -/
theorem esymm_div_choose_rpow_le_rpow {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l)
    (hpos : ∀ j ∈ Finset.Icc 1 l, 0 < s.esymm j) :
    (s.esymm l / (card s).choose l) ^ (1 / (l : ℝ)) ≤
      (s.esymm k / (card s).choose k) ^ (1 / (k : ℝ)) := by
  have hk₀ := s.esymm_div_choose_pos (hpos k (Finset.mem_Icc.mpr ⟨hk, hkl⟩))
  have hl₀ := s.esymm_div_choose_pos (hpos l (Finset.mem_Icc.mpr ⟨hk.trans hkl, le_rfl⟩))
  have hpow := s.esymm_div_choose_pow_le_pow hkl hpos
  have hlR : (0 : ℝ) < l := by exact_mod_cast hk.trans hkl
  -- Take the `(k l)`-th root of `S_l^k ≤ S_k^l`.
  have hroot := Real.rpow_le_rpow (by positivity) hpow (by positivity : 0 ≤ 1 / ((k : ℝ) * l))
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hl₀.le,
    ← Real.rpow_mul hk₀.le] at hroot
  convert hroot using 2 <;> field_simp

/-- **Maclaurin's inequalities** for nonnegative reals: if every element of `s` is nonnegative,
then the elementary symmetric means `S_j = σ_j(s) / binom(card s, j)` satisfy
`S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l`. At `k = 1` and `l = card s` this is the inequality of
arithmetic and geometric means. -/
theorem esymm_div_choose_rpow_le_rpow_of_nonneg {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l)
    (hs : ∀ a ∈ s, 0 ≤ a) :
    (s.esymm l / (card s).choose l) ^ (1 / (l : ℝ)) ≤
      (s.esymm k / (card s).choose k) ^ (1 / (k : ℝ)) := by
  by_cases hpos : ∀ j ∈ Finset.Icc 1 l, 0 < s.esymm j
  · exact s.esymm_div_choose_rpow_le_rpow hk hkl hpos
  push Not at hpos
  obtain ⟨j, hj, hj₀⟩ := hpos
  have hl : s.esymm l = 0 :=
    esymm_eq_zero_of_le hs (hj₀.antisymm (esymm_nonneg hs j)) (Finset.mem_Icc.mp hj).2
  have hlR : (1 / (l : ℝ)) ≠ 0 := one_div_ne_zero (by have := hk.trans hkl; positivity)
  rw [hl, zero_div, Real.zero_rpow hlR]
  exact Real.rpow_nonneg (div_nonneg (esymm_nonneg hs k) (Nat.cast_nonneg _)) _

end Multiset
