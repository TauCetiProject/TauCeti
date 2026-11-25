/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.LeastCommonDenominator
public import TauCeti.Probability.RandomMatrix.Compressible
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Probability.Moments.SubGaussian.AntiConcentration
import TauCeti.Probability.RandomMatrix.SmallBall

/-!
# Random subspaces are incompressible and have no arithmetic structure

Let a real random matrix have independent, uniformly sub-Gaussian entries with second moments
bounded below by one, and at least half as many columns as rows. Outside an event whose outer
probability is exponentially small in the number of columns, every unit vector orthogonal to all
columns is incompressible. The same holds for the unit normals to the span of the columns other
than a fixed one, as long as those columns still number at least half the rows. All bounds are
stated for outer probabilities, so the exceptional events need not be measurable.

Small-ball estimates for the inner product of a column with such a normal need its mass spread
over many coordinates, so this is the first step in bounding the distance of a column from the
span of the other columns. The proof applies invertibility on compressible vectors to the
transposed matrix, whose kernel is the orthogonal complement of the column span.

If in addition the entries of each column are identically distributed, these unit normals have an
exponentially large least common denominator `TauCeti.leastCommonDenominator`: for constants
`c, C > 0` depending only on the variance proxy, outside an event of outer probability at most
`C exp (-c N)`, every unit normal `x` in the `N`-dimensional column space has
`LCD_{c √N, c}(x) ≥ c √N exp (c N / d)`, where `d = N - (n - 1)` bounds the codimension of the
span of the other `n - 1` columns from below
(`exists_measureReal_exists_mem_orthogonal_span_ne_leastCommonDenominator_lt_le`). Through the
small-ball inequality for the least common denominator, this controls the distance from a
column to the span of the others, the key step of the lower bound for the least singular value of
a square random matrix.

The proof splits the unit vectors of small LCD into compressible vectors and the dyadic level
sets `D ≤ LCD < 2 D` of incompressible ones. A matrix with independent rows maps a fixed vector of
a level set close to `0` only with probability exponentially small in the number of rows; a net of
the level set with about `(C D / √N)^N` points, an operator-norm bound and a union bound over the
net and the levels conclude.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 3.6 and §5 (Theorem 5.3).
* M. Rudelson and R. Vershynin, *The smallest singular value of a random rectangular matrix*,
  Communications on Pure and Applied Mathematics 62 (2009); Lemma 4.4, Theorem 4.3 and
  Lemmas 4.6–4.8 of the preprint arXiv:0802.3956v4. Theorem 4.3 is stated there for
  identically distributed entries of unit variance and a codimension below a small multiple of
  `N`; here the entries of each column share a law, the variance is at least `1`, and the
  codimension bound only needs `N ≤ 2 (n - 1)`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Set
open scoped NNReal

namespace TauCeti.Probability

/-- For a real random matrix with independent, uniformly sub-Gaussian entries of second moments
at least one and at least half as many columns as rows, the outer probability that some
compressible unit vector is orthogonal to every column is exponentially small in the number of
columns. The constants depend only on the common variance proxy `K`. -/
theorem exists_measureReal_exists_mem_orthogonal_span_isCompressibleVector_le (K : ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ ∃ a : ℝ, 0 < a ∧
      ∀ {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        {P : Measure Ω} {A : Ω → Matrix m n ℝ},
        iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        Fintype.card m ≤ 2 * Fintype.card n →
        P.real {ω | ∃ x ∈ (Submodule.span ℝ (range fun j : n ↦
            (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ m)))ᗮ,
          TauCeti.IsCompressibleVector ⌊δ * Fintype.card m⌋₊ ρ x} ≤
          4 * Real.exp (-a * Fintype.card n) := by
  obtain ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, a, ha, hcomp⟩ :=
    exists_measureReal_exists_isCompressibleVector_norm_toEuclideanLin_lt_le K
  refine ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, a, ha, ?_⟩
  intro Ω m n _ _ _ P A hind hA hmom hdim
  classical
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  -- With no columns the bound is at least one.
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · rw [hn, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans (by norm_num)
  -- The kernel of the transposed matrix is the orthogonal complement of the column span.
  have hindT : iIndepFun (fun ij : n × m ↦ fun ω ↦ (A ω)ᵀ ij.1 ij.2) P := by
    simpa only [transpose_apply, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using
      hind.precomp Prod.swap_injective
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (hcomp hindT (fun i j ↦ hA j i) (fun i j ↦ hmom j i) hdim)
  rintro ω ⟨x, hx, hcx⟩
  refine ⟨x, hcx, ?_⟩
  rw [← ker_toEuclideanLin_conjTranspose, LinearMap.mem_ker,
    conjTranspose_eq_transpose_of_trivial] at hx
  rw [hx, norm_zero]
  positivity

/-- For a real random matrix with independent, uniformly sub-Gaussian entries of second moments
at least one, whose columns other than a fixed one number at least half its rows, the outer
probability that some compressible unit vector is orthogonal to every column other than the
fixed one is exponentially small in the number of columns. A matrix with a single column needs
no bound on its rows. The constants depend only on the common variance proxy `K`. -/
theorem exists_measureReal_exists_mem_orthogonal_span_ne_isCompressibleVector_le (K : ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ ∃ a : ℝ, 0 < a ∧
      ∀ {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        {P : Measure Ω} {A : Ω → Matrix m n ℝ},
        iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        (Fintype.card n = 1 ∨ Fintype.card m ≤ 2 * (Fintype.card n - 1)) → ∀ i : n,
        P.real {ω | ∃ x ∈ (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
            (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ m)))ᗮ,
          TauCeti.IsCompressibleVector ⌊δ * Fintype.card m⌋₊ ρ x} ≤
          4 * Real.exp (-a * Fintype.card n) := by
  obtain ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, a, ha, hspan⟩ :=
    exists_measureReal_exists_mem_orthogonal_span_isCompressibleVector_le K
  refine ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, min (a / 2) (1 / 2), lt_min (half_pos ha) one_half_pos, ?_⟩
  intro Ω m n _ _ _ P A hind hA hmom hdim i
  classical
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card n - 1 := by simp
  have hn : 1 ≤ Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  rcases hn.eq_or_lt with hn₁ | hn₂
  · -- With one column the rate is at most `1 / 2`, so the bound is at least one.
    rw [← hn₁, Nat.cast_one, mul_one]
    have hexp : 1 - 1 / 2 ≤ Real.exp (-min (a / 2) (1 / 2)) := by
      have := Real.add_one_le_exp (-min (a / 2) (1 / 2))
      linarith [min_le_right (a / 2) (1 / 2)]
    exact measureReal_le_one.trans (by linarith)
  -- Remove the fixed column; the remaining columns number at least half the rows.
  let B : Ω → Matrix m {j // j ≠ i} ℝ := fun ω ↦ (A ω).submatrix id Subtype.val
  have hindB : iIndepFun (fun ij : m × {j // j ≠ i} ↦ fun ω ↦ B ω ij.1 ij.2) P := by
    simpa only [B, submatrix_apply, id_eq, Function.comp_def, Prod.map_fst, Prod.map_snd] using
      hind.precomp (g := Prod.map id Subtype.val)
        (Function.injective_id.prodMap Subtype.val_injective)
  have hdimB : Fintype.card m ≤ 2 * Fintype.card {j // j ≠ i} := by omega
  have hrate : -a * (Fintype.card {j // j ≠ i} : ℝ) ≤
      -min (a / 2) (1 / 2) * Fintype.card n := by
    have hn' : (2 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn₂
    rw [hcard, Nat.cast_sub hn, Nat.cast_one]
    nlinarith [min_le_left (a / 2) (1 / 2)]
  simpa only [B, submatrix_apply, id_eq] using
    (hspan hindB (fun r j ↦ by simpa only [B, submatrix_apply, id_eq] using hA r j)
      (fun r j ↦ by simpa only [B, submatrix_apply, id_eq] using hmom r j) hdimB).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (by norm_num))

/-! ### The arithmetic structure of random subspaces -/

section LeastCommonDenominator

open Metric Real
open scoped ENNReal Matrix.Norms.L2Operator

/-- The union bound over a net of one level set of the LCD: the probability that a matrix of
operator norm at most `M` annihilates a unit vector whose LCD lies in `[D, 2 D)` is at most the
cardinality bound of a `4α/D`-net of the level set times the single-vector small-ball bound at
radius `t`, provided `M (4α/D) < t √(card ι)`. -/
private theorem measureReal_exists_leastCommonDenominator_mem_Ico_toEuclideanLin_eq_zero_le
    {Ω ι m : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype m] [DecidableEq m]
    {P : Measure Ω} {B : Ω → Matrix ι m ℝ}
    (hind : iIndepFun (fun jr : ι × m ↦ fun ω ↦ B ω jr.1 jr.2) P)
    {ν : ι → Measure ℝ} (hν : ∀ j r, HasLaw (fun ω ↦ B ω j r) (ν j) P) {b : ℝ}
    (hb : ∀ j v, (ν j).real (ball v 1) ≤ 1 - b) {α D : ℝ≥0} {γ M t : ℝ} (hγ : 0 < γ)
    (hD : 0 < D) (ht : 0 ≤ t) (happrox : M * (4 * α / D) < t * √(Fintype.card ι)) :
    P.real {ω | ‖B ω‖ ≤ M ∧ ∃ x : EuclideanSpace ℝ m, ‖x‖ = 1 ∧
        leastCommonDenominator α γ x ∈ Ico (D : ℝ≥0∞) (2 * D) ∧ toEuclideanLin (B ω) x = 0} ≤
      (exp 1 * (1 + √π * (2 * D + α) / √(Fintype.card m))) ^ Fintype.card m *
        (2 * exp 1 * (16 * π * (2 * t + (D : ℝ)⁻¹) / (γ * √b) +
          4 * exp (1 - α ^ 2 * b / 2))) ^ Fintype.card ι := by
  set S := {x : EuclideanSpace ℝ m |
    ‖x‖ = 1 ∧ leastCommonDenominator α γ x ∈ Ico (D : ℝ≥0∞) (2 * D)}
  obtain ⟨N, hNS, hcover, hcard⟩ :=
    exists_finset_isCover_of_forall_leastCommonDenominator_mem_Ico (S := S) fun x hx ↦ hx
  set q := 2 * exp 1 * (16 * π * (2 * t + (D : ℝ)⁻¹) / (γ * √b) + 4 * exp (1 - α ^ 2 * b / 2))
  -- Each point of the net has the single-vector small-ball bound.
  have hpt (y) (hy : y ∈ N) :
      P.real {ω | ‖toEuclideanLin (B ω) y‖ < t * √(Fintype.card ι)} ≤ q ^ Fintype.card ι := by
    obtain ⟨hy1, hyD, -⟩ := hNS hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
    have h :=
      hind.measureReal_norm_toEuclideanLin_lt_mul_sqrt_le_of_ofReal_le_leastCommonDenominator
        hν hb hy0 hγ (L := D) hD (by rwa [ENNReal.ofReal_coe_nnreal]) ht
    simpa [q, hy1] using h
  -- A vector of the level set in the kernel is `4α/D`-close to a net point, which `B ω` maps
  -- into the ball of radius `M (4α/D)`.
  have hsub : {ω | ‖B ω‖ ≤ M ∧ ∃ x : EuclideanSpace ℝ m, ‖x‖ = 1 ∧
        leastCommonDenominator α γ x ∈ Ico (D : ℝ≥0∞) (2 * D) ∧ toEuclideanLin (B ω) x = 0} ⊆
      ⋃ y ∈ N, {ω | ‖toEuclideanLin (B ω) y‖ < t * √(Fintype.card ι)} := by
    rintro ω ⟨hB, x, hx1, hxD, hx0⟩
    obtain ⟨y, hy, hxy⟩ := hcover ⟨hx1, hxD⟩
    have hd : dist x y ≤ 4 * α / D := by exact_mod_cast edist_le_coe.mp hxy
    have hop : ‖(toEuclideanLin (B ω)).toContinuousLinearMap‖ = ‖B ω‖ := by
      rw [Matrix.l2_opNorm_def, LinearEquiv.trans_apply]
    refine mem_iUnion₂.2 ⟨y, hy, ?_⟩
    calc ‖toEuclideanLin (B ω) y‖ = ‖toEuclideanLin (B ω) (y - x)‖ := by rw [map_sub, hx0, sub_zero]
      _ ≤ ‖B ω‖ * ‖y - x‖ := hop ▸ (toEuclideanLin (B ω)).toContinuousLinearMap.le_opNorm _
      _ ≤ M * (4 * α / D) := by
          rw [← dist_eq_norm, dist_comm]
          exact mul_le_mul hB hd dist_nonneg ((norm_nonneg _).trans hB)
      _ < t * √(Fintype.card ι) := happrox
  have := hind.isProbabilityMeasure
  calc _ ≤ P.real (⋃ y ∈ N, {ω | ‖toEuclideanLin (B ω) y‖ < t * √(Fintype.card ι)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ y ∈ N, P.real {ω | ‖toEuclideanLin (B ω) y‖ < t * √(Fintype.card ι)} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ N, q ^ Fintype.card ι := Finset.sum_le_sum hpt
    _ = N.card * q ^ Fintype.card ι := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)


/-- The net factor of a level set: for `D ≥ √(δ N) / 2` and `μ ≤ √δ / 2`, the base
`e (1 + √π (2 D + μ √N) / √N)` of the net cardinality is at most `e C₀ D / √N`, where
`C₀ = 2 / √δ + 3 √π`. -/
private theorem exp_one_mul_one_add_div_le {N : ℕ} {δ μ D : ℝ} (hN : 0 < (N : ℝ)) (hδ : 0 < δ)
    (hμδ : μ ≤ √δ / 2) (hD₀ : √(δ * N) / 2 ≤ D) :
    exp 1 * (1 + √π * (2 * D + μ * √N) / √N) ≤ exp 1 * (2 / √δ + 3 * √π) * (D / √N) := by
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN
  have hsδ : √(δ * N) / 2 = √δ / 2 * √N := by rw [Real.sqrt_mul hδ.le]; ring
  have h1 : 1 ≤ 2 / √δ * (D / √N) := by
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    nlinarith [hsδ, Real.sqrt_pos.2 hδ]
  have h2 : μ * √N ≤ D := by nlinarith [mul_le_mul_of_nonneg_right hμδ hs.le]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos 1).le
  have : √π * (2 * D + μ * √N) / √N ≤ 3 * √π * (D / √N) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hs]; nlinarith [Real.sqrt_nonneg π]
  nlinarith

/-- The single-vector factor of a level set: at the radius `t = η √N / D`, with `η √N ≥ 1`,
both error terms of the single-vector small-ball bound are dominated by `K₁ t`, where
`K₁ = 16 π / (ρ √b)`, as long as `D` is below the exponential threshold. -/
private theorem two_mul_exp_one_mul_add_le {N R : ℕ} {ρ b μ η c₁ D : ℝ} (hRN : R < N)
    (hηN : 1 ≤ η * √N) (hc₁ : 0 < c₁) (hc₁b : c₁ ≤ μ ^ 2 * b / 2)
    (hc₁K : 4 * exp 1 * c₁ ≤ 16 * π / (ρ * √b) * η) (hD : 0 < D)
    (hDL : D < c₁ * √N * exp (c₁ * N / (N - R : ℕ))) :
    2 * exp 1 * (16 * π * (2 * (η * √N / D) + D⁻¹) / (ρ * √b) +
      4 * exp (1 - (μ * √N) ^ 2 * b / 2)) ≤ 8 * exp 1 * (16 * π / (ρ * √b)) * η * (√N / D) := by
  set K₁ := 16 * π / (ρ * √b)
  have hN : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_le R).trans_lt hRN
  have hηpos : 0 < η := by
    by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h (Real.sqrt_nonneg (N : ℝ))]
  have hK₁ : 0 < K₁ := by
    by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hηpos.le, exp_pos 1]
  have ht : D⁻¹ ≤ η * √N / D := by rw [inv_eq_one_div]; gcongr
  have hd : (1 : ℝ) ≤ (N - R : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hRN
  -- `4 exp (1 - μ² N b / 2) ≤ 4 e exp (-c₁ N / d)`, and `D exp (-c₁ N / d) < c₁ √N`.
  have hexp : 4 * exp (1 - (μ * √N) ^ 2 * b / 2) ≤ K₁ * (η * √N / D) := by
    have he1 : exp (1 - (μ * √N) ^ 2 * b / 2) ≤ exp 1 * exp (-(c₁ * N / (N - R : ℕ))) := by
      rw [← exp_add, exp_le_exp, mul_pow, Real.sq_sqrt hN.le]
      have : c₁ * N / (N - R : ℕ) ≤ c₁ * N := div_le_self (by positivity) hd
      nlinarith
    rw [mul_div_assoc', le_div_iff₀ hD]
    calc 4 * exp (1 - (μ * √N) ^ 2 * b / 2) * D
        ≤ 4 * (exp 1 * exp (-(c₁ * N / (N - R : ℕ)))) *
            (c₁ * √N * exp (c₁ * N / (N - R : ℕ))) :=
          mul_le_mul (by gcongr) hDL.le hD.le (by positivity)
      _ = 4 * exp 1 * c₁ * √N *
          (exp (c₁ * N / (N - R : ℕ)) * exp (-(c₁ * N / (N - R : ℕ)))) := by ring
      _ = 4 * exp 1 * c₁ * √N := by rw [← exp_add, add_neg_cancel, exp_zero, mul_one]
      _ ≤ K₁ * (η * √N) := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hK : 16 * π * (2 * (η * √N / D) + D⁻¹) / (ρ * √b) = K₁ * (2 * (η * √N / D) + D⁻¹) := by
    simp only [K₁]; ring
  rw [hK]
  calc 2 * exp 1 * (K₁ * (2 * (η * √N / D) + D⁻¹) + 4 * exp (1 - (μ * √N) ^ 2 * b / 2))
      ≤ 2 * exp 1 * (K₁ * (2 * (η * √N / D) + η * √N / D) + K₁ * (η * √N / D)) := by
        gcongr
    _ = 8 * exp 1 * K₁ * η * (√N / D) := by ring

/-- The power bookkeeping of a level set: with `w = (e⁴ C₀)⁻²`, `N ≤ 2 R`, `R ≤ N` and
`u^(N - R) ≤ exp (c₁ N)` for some `c₁ ≤ 1`, the product `(e C₀ u)^N (w / u)^R` is at most
`exp (-2 N)`. -/
private theorem mul_pow_mul_pow_le_exp {N R : ℕ} {C₀ u c₁ : ℝ} (hNR : N ≤ 2 * R) (hRN : R ≤ N)
    (hC₀ : 1 ≤ C₀) (hu : 0 < u) (hud : u ^ (N - R) ≤ exp (c₁ * N)) (hc₁1 : c₁ ≤ 1) :
    (exp 1 * C₀ * u) ^ N * ((exp 4 * C₀)⁻¹ ^ 2 * u⁻¹) ^ R ≤ exp (-(2 * N)) := by
  have hC₀pos : 0 < C₀ := zero_lt_one.trans_le hC₀
  have hw1 : (exp 4 * C₀)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le (one_le_exp (by norm_num)) hC₀)
  -- `(e⁴ C₀)^(-2 R) ≤ (e⁴ C₀)^(-N)` since `N ≤ 2 R`.
  have hwR : ((exp 4 * C₀)⁻¹ ^ 2) ^ R ≤ (exp 4 * C₀)⁻¹ ^ N := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one (inv_nonneg.2 (mul_pos (exp_pos 4) hC₀pos).le) hw1 hNR
  calc _ = (exp 1 * C₀) ^ N * ((exp 4 * C₀)⁻¹ ^ 2) ^ R * u ^ (N - R) := by
        have h : u ^ N = u ^ (N - R) * u ^ R := by rw [← pow_add, Nat.sub_add_cancel hRN]
        rw [mul_pow, mul_pow, mul_pow, h, inv_pow u]
        field_simp
    _ ≤ (exp 1 * C₀) ^ N * (exp 4 * C₀)⁻¹ ^ N * exp (c₁ * N) := by gcongr
    _ = (exp 1 * C₀ * (exp 4 * C₀)⁻¹) ^ N * exp (c₁ * N) := by rw [← mul_pow]
    _ = exp (-(3 * N) + c₁ * N) := by
        have h3 : exp 1 * C₀ * (exp 4 * C₀)⁻¹ = exp (-3) := by
          rw [(by field_simp : exp 1 * C₀ * (exp 4 * C₀)⁻¹ = exp 1 / exp 4), ← exp_sub]
          norm_num
        rw [h3, ← exp_natCast_mul, ← exp_add]
        ring_nf
    _ ≤ exp (-(2 * N)) := exp_le_exp.2 (by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])

/-- The union bound over one level set is exponentially small: with the constants of the
structure theorem, the product of the net cardinality and the single-vector bound is at most
`exp (-2 N)` for every level `D` between `√(δ N) / 2` and the exponential threshold. -/
private theorem pow_mul_pow_le_exp_neg_two_mul {N R : ℕ} {δ ρ b μ η c₁ D : ℝ}
    (hNR : N ≤ 2 * R) (hδ : 0 < δ)
    (hη : 8 * exp 1 * (16 * π / (ρ * √b)) * η = (exp 4 * (2 / √δ + 3 * √π))⁻¹ ^ 2)
    (hηN : 1 ≤ η * √N) (hμ : 0 ≤ μ) (hμδ : μ ≤ √δ / 2) (hc₁ : 0 < c₁)
    (hc₁b : c₁ ≤ μ ^ 2 * b / 2) (hc₁K : 4 * exp 1 * c₁ ≤ 16 * π / (ρ * √b) * η)
    (hc₁δ : c₁ ≤ √δ / 2) (hc₁1 : c₁ ≤ 1)
    (hD₀ : √(δ * N) / 2 ≤ D) (hDL : D < c₁ * √N * exp (c₁ * N / (N - R : ℕ))) :
    (exp 1 * (1 + √π * (2 * D + μ * √N) / √N)) ^ N *
      (2 * exp 1 * (16 * π * (2 * (η * √N / D) + D⁻¹) / (ρ * √b) +
        4 * exp (1 - (μ * √N) ^ 2 * b / 2))) ^ R ≤ exp (-(2 * N)) := by
  have hN : 0 < (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h] at hηN; linarith
    · exact_mod_cast h
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN
  have hD : 0 < D := lt_of_lt_of_le (by positivity) hD₀
  have hηpos : 0 < η := by
    by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hs.le]
  have hK₁ : 0 < 16 * π / (ρ * √b) := by
    by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hηpos.le, exp_pos 1]
  -- The codimension `N - R` is positive, since otherwise the threshold is below `√(δ N) / 2`.
  have hRN : R < N := by
    by_contra! h
    rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, div_zero, exp_zero, mul_one] at hDL
    have hsδ : √(δ * N) / 2 = √δ / 2 * √N := by rw [Real.sqrt_mul hδ.le]; ring
    nlinarith [mul_le_mul_of_nonneg_right hc₁δ hs.le]
  have hS2 := two_mul_exp_one_mul_add_le hRN hηN hc₁ hc₁b hc₁K hD hDL
  set C₀ := 2 / √δ + 3 * √π
  set K₁ := 16 * π / (ρ * √b)
  set w := 8 * exp 1 * K₁ * η
  have hbase : 0 ≤ 2 * exp 1 * (16 * π * (2 * (η * √N / D) + D⁻¹) / (ρ * √b) +
      4 * exp (1 - (μ * √N) ^ 2 * b / 2)) := by
    have hK : 16 * π * (2 * (η * √N / D) + D⁻¹) / (ρ * √b) = K₁ * (2 * (η * √N / D) + D⁻¹) := by
      simp only [K₁]; ring
    rw [hK]
    positivity
  have hC₀ : 1 ≤ C₀ := by
    nlinarith [Real.sqrt_le_sqrt (by linarith [two_le_pi] : (1 : ℝ) ≤ π), Real.sqrt_one,
      (by positivity : (0 : ℝ) ≤ 2 / √δ)]
  -- With `u = D / √N`, the exponential threshold gives `u^(N - R) ≤ exp (c₁ N)`.
  have hud : (D / √N) ^ (N - R) ≤ exp (c₁ * N) := by
    have hd : (0 : ℝ) < (N - R : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hRN
    have h1 : D / √N ≤ exp (c₁ * N / (N - R : ℕ)) := by
      rw [div_le_iff₀ hs]
      nlinarith [exp_pos (c₁ * N / (N - R : ℕ))]
    calc (D / √N) ^ (N - R) ≤ exp (c₁ * N / (N - R : ℕ)) ^ (N - R) :=
          pow_le_pow_left₀ (div_pos hD hs).le h1 _
      _ = exp (c₁ * N) := by rw [← exp_natCast_mul, mul_div_cancel₀ _ hd.ne']
  calc _ ≤ (exp 1 * C₀ * (D / √N)) ^ N * (w * (D / √N)⁻¹) ^ R := by
        rw [inv_div]
        exact mul_le_mul
          (pow_le_pow_left₀ (by positivity) (exp_one_mul_one_add_div_le hN hδ hμδ hD₀) N)
          (pow_le_pow_left₀ hbase hS2 R) (by positivity) (by positivity)
    _ ≤ exp (-(2 * N)) := by
        rw [(hη : w = (exp 4 * C₀)⁻¹ ^ 2)]
        exact mul_pow_mul_pow_le_exp hNR hRN.le hC₀ (div_pos hD hs) hud hc₁1

/-- The exceptional event of the structure theorem, for the kernel of a matrix, is covered by
the compressible event, the event of a large operator norm, and the dyadic level sets of the LCD
between `√(k + 1) / 2` and the threshold `L`. Incompressible unit vectors have LCD at least
`√(k + 1) / 2`, so these level sets account for every other vector of LCD below `L`. -/
private theorem setOf_exists_leastCommonDenominator_lt_subset {Ω ι m : Type*} [Fintype ι]
    [Fintype m] [DecidableEq m] (B : Ω → Matrix ι m ℝ) (k : ℕ) (α ρ M L : ℝ) :
    {ω | ∃ x, toEuclideanLin (B ω) x = 0 ∧ ‖x‖ = 1 ∧
        leastCommonDenominator α ρ x < ENNReal.ofReal L} ⊆
      {ω | ∃ x, toEuclideanLin (B ω) x = 0 ∧ IsCompressibleVector k ρ x} ∪
        {ω | M < ‖B ω‖} ∪ ⋃ j ∈ Finset.range ⌈L / (√(k + 1) / 2)⌉₊,
          {ω | 2 ^ j * (√(k + 1) / 2) < L ∧ ‖B ω‖ ≤ M ∧ ∃ x : EuclideanSpace ℝ m, ‖x‖ = 1 ∧
            leastCommonDenominator α ρ x ∈ Ico (ENNReal.ofReal (2 ^ j * (√(k + 1) / 2)))
              (2 * ENNReal.ofReal (2 ^ j * (√(k + 1) / 2))) ∧ toEuclideanLin (B ω) x = 0} := by
  set D₀ := √(k + 1) / 2
  have hD₀ : 0 < D₀ := by positivity
  rintro ω ⟨x, hx0, hx1, hxL⟩
  rcases isCompressibleVector_or_isIncompressibleVector_iff.2 hx1 with hc | hi
  · exact Or.inl (Or.inl ⟨x, hx0, hc⟩)
  by_cases hM : M < ‖B ω‖
  · exact Or.inl (Or.inr hM)
  -- The LCD `y` lies in `[D₀, L)`, so in the dyadic level `[2^j D₀, 2^(j + 1) D₀)` for some
  -- `j < ⌈L / D₀⌉₊`.
  have h₀ := hi.ofReal_sqrt_div_two_le_leastCommonDenominator (α := α) le_rfl
  have hℓ := (ENNReal.ofReal_toReal hxL.ne_top).symm
  set y := (leastCommonDenominator α ρ x).toReal
  rw [hℓ] at h₀ hxL
  have hyL : y < L := (ENNReal.ofReal_lt_ofReal_iff'.1 hxL).1
  have hDy : D₀ ≤ y := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h₀
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near ((one_le_div hD₀).2 hDy) one_lt_two
  rw [le_div_iff₀ hD₀] at hj1
  rw [div_lt_iff₀ hD₀, pow_succ] at hj2
  have hjL : (j : ℝ) < ⌈L / D₀⌉₊ := calc
    (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
    _ ≤ L / D₀ := by rw [le_div_iff₀ hD₀]; linarith
    _ ≤ ⌈L / D₀⌉₊ := Nat.le_ceil _
  refine Or.inr (mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (by exact_mod_cast hjL),
    hj1.trans_lt hyL, not_lt.1 hM, x, hx1, ?_, hx0⟩)
  rw [hℓ, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  exact ⟨ENNReal.ofReal_le_ofReal hj1, ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by positivity⟩⟩

/-- One dyadic level set of the LCD: outside an event of probability `exp (-2 N)`, a matrix of
operator norm at most `M √R` annihilates no unit vector whose LCD lies in `[D, 2 D)`, for every
level `D` between `√(δ N) / 2` and the exponential threshold. -/
private theorem measureReal_exists_leastCommonDenominator_mem_Ico_le_exp {Ω ι m : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype m] [DecidableEq m] {P : Measure Ω}
    {B : Ω → Matrix ι m ℝ}
    (hind : iIndepFun (fun jr : ι × m ↦ fun ω ↦ B ω jr.1 jr.2) P)
    {ν : ι → Measure ℝ} (hν : ∀ j r, HasLaw (fun ω ↦ B ω j r) (ν j) P) {b : ℝ}
    (hb : ∀ j v, (ν j).real (ball v 1) ≤ 1 - b) (hNR : Fintype.card m ≤ 2 * Fintype.card ι)
    {δ ρ μ η c₁ M D : ℝ} (hδ : 0 < δ)
    (hη : 8 * exp 1 * (16 * π / (ρ * √b)) * η = (exp 4 * (2 / √δ + 3 * √π))⁻¹ ^ 2)
    (hηN : 1 ≤ η * √(Fintype.card m)) (hμ : 0 ≤ μ) (hμδ : μ ≤ √δ / 2) (hc₁ : 0 < c₁)
    (hc₁b : c₁ ≤ μ ^ 2 * b / 2) (hc₁K : 4 * exp 1 * c₁ ≤ 16 * π / (ρ * √b) * η)
    (hc₁δ : c₁ ≤ √δ / 2) (hc₁1 : c₁ ≤ 1) (hμM : 9 * M * μ ≤ η)
    (hD₀ : √(δ * Fintype.card m) / 2 ≤ D)
    (hDL : D < c₁ * √(Fintype.card m) *
      exp (c₁ * Fintype.card m / (Fintype.card m - Fintype.card ι : ℕ))) :
    P.real {ω | ‖B ω‖ ≤ M * √(Fintype.card ι) ∧ ∃ x : EuclideanSpace ℝ m, ‖x‖ = 1 ∧
        leastCommonDenominator (μ * √(Fintype.card m)) ρ x ∈
          Ico (ENNReal.ofReal D) (2 * ENNReal.ofReal D) ∧ toEuclideanLin (B ω) x = 0} ≤
      exp (-(2 * Fintype.card m)) := by
  have := hind.isProbabilityMeasure
  set N := Fintype.card m
  set R := Fintype.card ι
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h ↦ by
    rw [h, Nat.cast_zero, Real.sqrt_zero, mul_zero] at hηN; linarith
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hN0)
  have hD : 0 < D :=
    lt_of_lt_of_le (div_pos (Real.sqrt_pos.2 (mul_pos hδ (Nat.cast_pos.2 hN0))) two_pos) hD₀
  have hηpos : 0 < η := by
    by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hs.le]
  have hρb : 0 < ρ * √b := by
    by_contra! h
    have : 16 * π / (ρ * √b) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg this hηpos.le, exp_pos 1]
  have hρ : 0 < ρ := pos_of_mul_pos_left hρb (Real.sqrt_nonneg b)
  have hR : 0 < √(R : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 (by omega))
  -- The approximation radius `M √R (4 μ √N / D)` is below `t √R` for `t = η √N / D`.
  have happrox : M * √(R : ℝ) * (4 * (⟨μ * √N, by positivity⟩ : ℝ≥0) / (⟨D, hD.le⟩ : ℝ≥0)) <
      η * √N / D * √R := by
    rw [(by ring : M * √(R : ℝ) * (4 * (μ * √N) / D) = 4 * (M * μ) * (√N * √R) / D),
      (by ring : η * √N / D * √R = η * (√N * √R) / D)]
    gcongr
    have : 9 * (M * μ) ≤ η := by rw [← mul_assoc]; exact hμM
    linarith
  have hunion := measureReal_exists_leastCommonDenominator_mem_Ico_toEuclideanLin_eq_zero_le
    hind hν hb hρ (D := ⟨D, hD.le⟩) (NNReal.coe_pos.1 hD) (by positivity) happrox
  refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans (hunion.trans
    (pow_mul_pow_le_exp_neg_two_mul hNR hδ hη hηN hμ hμδ hc₁ hc₁b hc₁K hc₁δ hc₁1 hD₀ hDL))
  obtain ⟨hB, x, hx1, hxD, hx0⟩ := hω
  refine ⟨hB, x, hx1, ?_, hx0⟩
  rwa [← ENNReal.ofReal_coe_nnreal (p := ⟨D, hD.le⟩)]

/-- The number of dyadic levels: with `D₀ ≥ √(δ N) / 2` and `c₁ ≤ min (√δ / 2) 1`, the
`⌈L / D₀⌉₊` levels below the threshold `L = c₁ √N exp (c₁ N / (N - R))` contribute at most
`2 exp (-N)` when each has probability at most `exp (-2 N)`. -/
private theorem natCeil_mul_exp_le {N R : ℕ} {δ c₁ D₀ : ℝ} (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (hc₁δ : c₁ ≤ √δ / 2) (hc₁1 : c₁ ≤ 1) (hD₀ : √(δ * N) / 2 ≤ D₀) :
    (⌈c₁ * √N * exp (c₁ * N / (N - R : ℕ)) / D₀⌉₊ : ℝ) * exp (-(2 * N)) ≤
      2 * exp (-(N : ℝ)) := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  rcases ((by positivity : (0 : ℝ) ≤ √(δ * N) / 2).trans hD₀).eq_or_lt with h | hD₀pos
  · rw [← h, div_zero, Nat.ceil_zero, Nat.cast_zero, zero_mul]; positivity
  have hdiv : c₁ * N / (N - R : ℕ) ≤ c₁ * N := by
    rcases Nat.eq_zero_or_pos (N - R) with h | h
    · rw [h, Nat.cast_zero, div_zero]; positivity
    · exact div_le_self (by positivity) (by exact_mod_cast h)
  have hLt : c₁ * √N * exp (c₁ * N / (N - R : ℕ)) / D₀ ≤ exp (c₁ * N) := by
    rw [div_le_iff₀ hD₀pos]
    have hsδ : √(δ * N) / 2 = √δ / 2 * √N := by rw [Real.sqrt_mul hδ.le]; ring
    calc c₁ * √N * exp (c₁ * N / (N - R : ℕ)) ≤ √δ / 2 * √N * exp (c₁ * N) := by gcongr
      _ ≤ exp (c₁ * N) * D₀ := by nlinarith [exp_pos (c₁ * N)]
  calc (⌈c₁ * √N * exp (c₁ * N / (N - R : ℕ)) / D₀⌉₊ : ℝ) * exp (-(2 * N))
      ≤ (exp (c₁ * N) + exp (c₁ * N)) * exp (-(2 * N)) := by
        gcongr
        exact (Nat.ceil_lt_add_one (by positivity)).le.trans
          (add_le_add hLt (one_le_exp (by positivity)))
    _ = 2 * exp (c₁ * N - 2 * N) := by rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ 2 * exp (-(N : ℝ)) := by gcongr; nlinarith [hN]

/-- The structure theorem for the kernel of one random matrix `B`, with explicit constants: the
probability that `B` annihilates a unit vector whose LCD is below the exponential threshold is
at most the probability of a compressible vector in the kernel, plus the operator-norm tail
`2 exp (-R)` and the sum `2 exp (-N)` of the dyadic level sets. -/
private theorem measureReal_exists_toEuclideanLin_eq_zero_leastCommonDenominator_lt_le
    {Ω ι m : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype m] [DecidableEq m]
    {P : Measure Ω} {B : Ω → Matrix ι m ℝ}
    (hind : iIndepFun (fun jr : ι × m ↦ fun ω ↦ B ω jr.1 jr.2) P)
    {ν : ι → Measure ℝ} (hν : ∀ j r, HasLaw (fun ω ↦ B ω j r) (ν j) P) {b : ℝ}
    (hb : ∀ j v, (ν j).real (ball v 1) ≤ 1 - b) {c₀ : ℝ≥0}
    (hB : ∀ j r, HasSubgaussianMGF (fun ω ↦ B ω j r) c₀ P)
    (hNR : Fintype.card m ≤ 2 * Fintype.card ι) {δ ρ μ η c₁ M : ℝ} (hδ : 0 < δ)
    (hη : 8 * exp 1 * (16 * π / (ρ * √b)) * η = (exp 4 * (2 / √δ + 3 * √π))⁻¹ ^ 2)
    (hηN : 1 ≤ η * √(Fintype.card m)) (hμ : 0 ≤ μ) (hμδ : μ ≤ √δ / 2) (hc₁ : 0 < c₁)
    (hc₁b : c₁ ≤ μ ^ 2 * b / 2) (hc₁K : 4 * exp 1 * c₁ ≤ 16 * π / (ρ * √b) * η)
    (hc₁δ : c₁ ≤ √δ / 2) (hc₁1 : c₁ ≤ 1) (hM : 28 * √(c₀ : ℝ) ≤ M) (hμM : 9 * M * μ ≤ η) :
    P.real {ω | ∃ x, toEuclideanLin (B ω) x = 0 ∧ ‖x‖ = 1 ∧
        leastCommonDenominator (μ * √(Fintype.card m)) ρ x <
          ENNReal.ofReal (c₁ * √(Fintype.card m) *
            exp (c₁ * Fintype.card m / (Fintype.card m - Fintype.card ι : ℕ)))} ≤
      P.real {ω | ∃ x, toEuclideanLin (B ω) x = 0 ∧
          IsCompressibleVector ⌊δ * Fintype.card m⌋₊ ρ x} +
        2 * exp (-(Fintype.card ι : ℝ)) + 2 * exp (-(Fintype.card m : ℝ)) := by
  have := hind.isProbabilityMeasure
  set N := Fintype.card m
  set R := Fintype.card ι
  set Lt := c₁ * √N * exp (c₁ * N / (N - R : ℕ))
  have hD₀ : √(δ * N) / 2 ≤ √((⌊δ * N⌋₊ : ℝ) + 1) / 2 := by
    gcongr
    exact (Nat.lt_floor_add_one _).le
  set D₀ := √((⌊δ * N⌋₊ : ℝ) + 1) / 2
  have hD₀pos : 0 < D₀ := by positivity
  -- Each dyadic level below the threshold has probability at most `exp (-2 N)`.
  have hlevel (j : ℕ) : P.real {ω | 2 ^ j * D₀ < Lt ∧ ‖B ω‖ ≤ M * √R ∧
      ∃ x : EuclideanSpace ℝ m, ‖x‖ = 1 ∧ leastCommonDenominator (μ * √N) ρ x ∈
        Ico (ENNReal.ofReal (2 ^ j * D₀)) (2 * ENNReal.ofReal (2 ^ j * D₀)) ∧
          toEuclideanLin (B ω) x = 0} ≤ exp (-(2 * N)) := by
    by_cases hj : 2 ^ j * D₀ < Lt
    · refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
        (measureReal_exists_leastCommonDenominator_mem_Ico_le_exp hind hν hb hNR hδ hη hηN hμ hμδ
          hc₁ hc₁b hc₁K hc₁δ hc₁1 hμM
          (hD₀.trans (le_mul_of_one_le_left hD₀pos.le (one_le_pow₀ one_le_two))) hj)
      exact hω.2
    · simp only [hj, false_and, Set.ofPred_false, measureReal_empty]
      positivity
  have hcount := natCeil_mul_exp_le hδ hc₁ hc₁δ hc₁1 (R := R) hD₀
  have h28 : 28 * (NNReal.sqrt c₀ : ℝ) * √R ≤ M * √R := by rw [Real.coe_sqrt]; gcongr
  have hnorm : P.real {ω | M * √R < ‖B ω‖} ≤ 2 * exp (-(R : ℝ)) :=
    (measureReal_mono (fun ω hω ↦ lt_of_le_of_lt h28 hω) (measure_ne_top _ _)).trans
      (hind.measureReal_l2_opNorm_gt_le_of_card_le_two_mul (L := NNReal.sqrt c₀)
        (fun j r ↦ by rw [NNReal.sq_sqrt]; exact hB j r) hNR)
  calc _ ≤ _ := measureReal_mono (setOf_exists_leastCommonDenominator_lt_subset B ⌊δ * N⌋₊
        (μ * √N) ρ (M * √R) Lt) (measure_ne_top _ _)
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _)
        (measureReal_biUnion_finset_le _ _))
    _ ≤ _ := add_le_add (add_le_add le_rfl hnorm)
        ((Finset.sum_le_sum fun j _ ↦ hlevel j).trans (by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; exact hcount))

/-- The structure theorem for the unit normals to the span of the columns other than `i`, with
explicit constants. It applies the kernel version to `B = 2 Aᵀ` restricted to the other columns:
`B` has the same kernel as the transpose, and the entries `2 A r j` give mass at most `1 - b` to
every open interval of length `2`, by the anti-concentration of sub-Gaussian variables. -/
private theorem measureReal_exists_mem_orthogonal_span_ne_leastCommonDenominator_lt_le_add
    {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] {P : Measure Ω}
    {A : Ω → Matrix m n ℝ} {ν : n → Measure ℝ} {K : ℝ≥0}
    (hind : iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    (hA : ∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P)
    (hmom : ∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) (hν : ∀ i j, HasLaw (fun ω ↦ A ω i j) (ν j) P)
    (hdim : Fintype.card m ≤ 2 * (Fintype.card n - 1)) (i : n) {b δ ρ μ η c₁ M : ℝ}
    (hbK : b ≤ 9 / (4096 * √2 * ((K : ℝ) + 1) ^ 2)) (hδ : 0 < δ)
    (hη : 8 * exp 1 * (16 * π / (ρ * √b)) * η = (exp 4 * (2 / √δ + 3 * √π))⁻¹ ^ 2)
    (hηN : 1 ≤ η * √(Fintype.card m)) (hμ : 0 ≤ μ) (hμδ : μ ≤ √δ / 2) (hc₁ : 0 < c₁)
    (hc₁b : c₁ ≤ μ ^ 2 * b / 2) (hc₁K : 4 * exp 1 * c₁ ≤ 16 * π / (ρ * √b) * η)
    (hc₁δ : c₁ ≤ √δ / 2) (hc₁1 : c₁ ≤ 1) (hM : 56 * √(K : ℝ) ≤ M) (hμM : 9 * M * μ ≤ η) :
    P.real {ω | ∃ x ∈ (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
        (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ m)))ᗮ, ‖x‖ = 1 ∧
      leastCommonDenominator (μ * √(Fintype.card m)) ρ x <
        ENNReal.ofReal (c₁ * √(Fintype.card m) *
          exp (c₁ * Fintype.card m / (Fintype.card m - (Fintype.card n - 1) : ℕ)))} ≤
      P.real {ω | ∃ x ∈ (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
          (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ m)))ᗮ,
        IsCompressibleVector ⌊δ * Fintype.card m⌋₊ ρ x} +
        2 * exp (-((Fintype.card n - 1 : ℕ) : ℝ)) + 2 * exp (-(Fintype.card m : ℝ)) := by
  classical
  have := hind.isProbabilityMeasure
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card n - 1 := by simp
  obtain ⟨r₀⟩ : Nonempty m := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero fun h ↦ by
    rw [h, Nat.cast_zero, Real.sqrt_zero, mul_zero] at hηN; linarith)
  set B : Ω → Matrix {j // j ≠ i} m ℝ := fun ω ↦ (2 : ℝ) • ((A ω).submatrix id Subtype.val)ᴴ
  have hBe (ω : Ω) (j : {j // j ≠ i}) (r : m) : B ω j r = 2 * A ω r j := by simp [B]
  have hker (ω : Ω) (x : EuclideanSpace ℝ m) :
      x ∈ (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
        (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ m)))ᗮ ↔
        toEuclideanLin (B ω) x = 0 := by
    have h := ker_toEuclideanLin_conjTranspose
      ((A ω).submatrix id (Subtype.val : {j // j ≠ i} → n))
    simp only [submatrix_apply, id_eq] at h
    rw [← h, LinearMap.mem_ker]
    simp [B, smul_eq_zero]
  have hBind : iIndepFun (fun jr : {j // j ≠ i} × m ↦ fun ω ↦ B ω jr.1 jr.2) P := by
    simp only [hBe]
    exact (hind.precomp (g := fun jr : {j // j ≠ i} × m ↦ (jr.2, jr.1.val))
      fun _ _ h ↦ Prod.ext (Subtype.ext (Prod.mk.inj h).2) (Prod.mk.inj h).1).comp
      (fun _ x ↦ 2 * x) fun _ ↦ measurable_id.const_mul 2
  have hBν (j : {j // j ≠ i}) (r : m) :
      HasLaw (fun ω ↦ B ω j r) ((ν j).map (2 * ·)) P := by
    simp only [hBe]
    exact (hasLaw_map (measurable_id.const_mul 2).aemeasurable).fun_comp (hν r j)
  -- The law of `2 A r j` gives mass at most `1 - b` to open intervals of length `2`.
  have hBb (j : {j // j ≠ i}) (v : ℝ) : ((ν j).map (2 * ·)).real (ball v 1) ≤ 1 - b := by
    rw [← (hBν j r₀).map_eq]
    simp only [hBe]
    refine (((hA r₀ j).mono (le_add_of_nonneg_right zero_le_one)).measureReal_map_two_mul_ball_le
      (hmom r₀ j) v).trans ?_
    push_cast
    linarith
  -- The entries of `B` are sub-Gaussian with variance proxy `4 K`.
  obtain ⟨c₀, hBsub, hc₀⟩ : ∃ c₀ : ℝ≥0, (∀ j r, HasSubgaussianMGF (fun ω ↦ B ω j r) c₀ P) ∧
      (c₀ : ℝ) = 2 ^ 2 * K := ⟨_, fun j r ↦ ((hA r j).const_mul 2).congr
        (ae_of_all _ fun ω ↦ (hBe ω j r).symm), NNReal.coe_mul _ _⟩
  have hcore := measureReal_exists_toEuclideanLin_eq_zero_leastCommonDenominator_lt_le hBind hBν
    hBb hBsub (by rw [hcard]; exact hdim) hδ hη hηN hμ hμδ hc₁ hc₁b hc₁K hc₁δ hc₁1
    (by rw [hc₀, Real.sqrt_mul (by positivity), Real.sqrt_sq two_pos.le]; linarith) hμM
  rw [hcard] at hcore
  refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans (hcore.trans_eq ?_)
  · obtain ⟨x, hx, hx1, hxL⟩ := hω
    exact ⟨x, (hker ω x).1 hx, hx1, hxL⟩
  · congr 3
    ext ω
    simp only [Set.mem_ofPred_eq, hker]

/-- The final exponential bookkeeping: for `0 ≤ c ≤ min (a / 2) (1 / 2)` and `N ≤ 2 (n - 1)`, the
three error terms of the structure theorem sum to at most `8 exp (-c N)`. -/
private theorem four_mul_exp_add_two_mul_exp_add_two_mul_exp_le {N n : ℕ} {a c : ℝ}
    (hc : 0 ≤ c) (hca : c ≤ a / 2) (hc1 : c ≤ 1 / 2) (hdim : N ≤ 2 * (n - 1)) :
    4 * exp (-a * n) + 2 * exp (-((n - 1 : ℕ) : ℝ)) + 2 * exp (-(N : ℝ)) ≤
      8 * exp (-c * N) := by
  have hdim' : (N : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hdim
  have hn : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : exp (-a * n) ≤ exp (-c * N) := exp_le_exp.2 (by nlinarith [hN])
  have h2 : exp (-((n - 1 : ℕ) : ℝ)) ≤ exp (-c * N) := exp_le_exp.2 (by nlinarith [hN])
  have h3 : exp (-(N : ℝ)) ≤ exp (-c * N) := exp_le_exp.2 (by nlinarith [hN])
  linarith

/-- The constants of the structure theorem, chosen from the variance proxy `K` and the
compressibility constants `δ` and `ρ`: `b` from anti-concentration, `η` from the union bound over
the level sets, `μ` from the approximation by nets, and `c₁` from the exponential threshold. -/
private theorem exists_structure_constants (K : ℝ≥0) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ b η μ c₁ M : ℝ, b ≤ 9 / (4096 * √2 * ((K : ℝ) + 1) ^ 2) ∧ 0 < η ∧
      8 * exp 1 * (16 * π / (ρ * √b)) * η = (exp 4 * (2 / √δ + 3 * √π))⁻¹ ^ 2 ∧ 0 < μ ∧
      μ ≤ √δ / 2 ∧ 0 < c₁ ∧ c₁ ≤ μ ^ 2 * b / 2 ∧ 4 * exp 1 * c₁ ≤ 16 * π / (ρ * √b) * η ∧
      c₁ ≤ √δ / 2 ∧ c₁ ≤ 1 ∧ 56 * √(K : ℝ) ≤ M ∧ 9 * M * μ ≤ η := by
  set b : ℝ := 9 / (4096 * √2 * ((K : ℝ) + 1) ^ 2)
  set K₁ : ℝ := 16 * π / (ρ * √b)
  set η : ℝ := (exp 4 * (2 / √δ + 3 * √π))⁻¹ ^ 2 / (8 * exp 1 * K₁)
  set M : ℝ := 56 * √(K : ℝ) + 1
  set μ : ℝ := min (η / (9 * M)) (√δ / 2)
  have hsb : 0 < √b := Real.sqrt_pos.2 (by positivity)
  have hK₁ : 0 < K₁ := div_pos (by positivity) (mul_pos hρ hsb)
  have hη : 0 < η := div_pos (by positivity) (mul_pos (by positivity) hK₁)
  have hμ : 0 < μ := lt_min (by positivity) (by positivity)
  refine ⟨b, η, μ, min (min (μ ^ 2 * b / 2) (K₁ * η / (4 * exp 1))) (min (√δ / 2) 1), M, le_rfl,
    hη, by simp only [η, K₁]; field_simp, hμ, min_le_right _ _,
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) one_pos),
    (min_le_left _ _).trans (min_le_left _ _), ?_, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), le_add_of_nonneg_right zero_le_one, ?_⟩
  · have h : min (min (μ ^ 2 * b / 2) (K₁ * η / (4 * exp 1))) (min (√δ / 2) 1) ≤
        K₁ * η / (4 * exp 1) := (min_le_left _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h; linarith
  · have h : μ ≤ η / (9 * M) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h; linarith

/-- In small dimensions the structure theorem is trivial: if `η √N < 1`, then `N < η⁻²`, so
`8 exp (η⁻²) exp (-c N) ≥ 1` for `c ≤ 1`. -/
private theorem one_le_mul_exp_inv_sq_mul_exp {N : ℕ} {η c : ℝ} (hη : 0 < η) (hc1 : c ≤ 1)
    (hηN : ¬1 ≤ η * √N) : 1 ≤ 8 * exp (η⁻¹ ^ 2) * exp (-c * N) := by
  have hs : √(N : ℝ) < η⁻¹ := by
    have h := mul_lt_mul_of_pos_left (not_le.1 hηN) (inv_pos.2 hη)
    rwa [← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul, mul_one] at h
  have hN : (N : ℝ) < η⁻¹ ^ 2 := calc
    (N : ℝ) = √(N : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
    _ < η⁻¹ ^ 2 := pow_lt_pow_left₀ hs (Real.sqrt_nonneg _) two_ne_zero
  have h1 : 1 ≤ exp (η⁻¹ ^ 2) * exp (-c * N) := by
    rw [← exp_add, one_le_exp_iff]
    nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ N)]
  nlinarith

/-- **Random subspaces have no arithmetic structure** (Rudelson–Vershynin). For every variance
proxy `K` there are constants `c, C > 0` with the following property. Let `A` be a real random
`N × n` matrix with independent entries, each sub-Gaussian with variance proxy `K` and of second
moment at least `1`, whose column `j` has identically distributed entries of law `ν j`, and with
`N ≤ 2 (n - 1)`. Then for every column `i`, outside an event of outer probability at most
`C exp (-c N)`, every unit vector orthogonal to the columns other than `i` has least common
denominator `LCD_{c √N, c}` at least `c √N exp (c N / d)`, where `d = N - (n - 1)` bounds the
codimension of their span from below. For square matrices `d = 1`, so the LCD of the unit normals
is exponentially large in `N`. -/
theorem exists_measureReal_exists_mem_orthogonal_span_ne_leastCommonDenominator_lt_le
    (K : ℝ≥0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        {P : Measure Ω} {A : Ω → Matrix m n ℝ} {ν : n → Measure ℝ},
        iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        (∀ i j, HasLaw (fun ω ↦ A ω i j) (ν j) P) →
        Fintype.card m ≤ 2 * (Fintype.card n - 1) → ∀ i : n,
        P.real {ω | ∃ x ∈ (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
            (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ m)))ᗮ, ‖x‖ = 1 ∧
          leastCommonDenominator (c * √(Fintype.card m)) c x <
            ENNReal.ofReal (c * √(Fintype.card m) *
              exp (c * Fintype.card m / (Fintype.card m - (Fintype.card n - 1) : ℕ)))} ≤
          C * exp (-c * Fintype.card m) := by
  obtain ⟨δ, hδ, -, ρ, hρ, -, a, ha, hcomp⟩ :=
    exists_measureReal_exists_mem_orthogonal_span_ne_isCompressibleVector_le K
  obtain ⟨b, η, μ, c₁, M, hbK, hη, hηK, hμ, hμδ, hc₁, hc₁b, hc₁K, hc₁δ, hc₁1, hM, hμM⟩ :=
    exists_structure_constants K hδ (NNReal.coe_pos.2 hρ)
  set c : ℝ := min (min c₁ μ) (min (ρ : ℝ) (min a 1 / 2))
  have hc : 0 < c := lt_min (lt_min hc₁ hμ) (lt_min hρ (by positivity))
  refine ⟨c, 8 * exp (η⁻¹ ^ 2), hc, by positivity, ?_⟩
  intro Ω m n _ _ _ P A ν hind hA hmom hν hdim i
  have := hind.isProbabilityMeasure
  by_cases hηN : 1 ≤ η * √(Fintype.card m)
  swap
  · -- In small dimensions, `N < η⁻²`, the bound is at least one.
    have hc1 : c ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two).trans (by norm_num)))
    exact measureReal_le_one.trans (one_le_mul_exp_inv_sq_mul_exp hη hc1 hηN)
  -- Smaller tolerances and a larger threshold reduce to the version with explicit constants.
  refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
    ((measureReal_exists_mem_orthogonal_span_ne_leastCommonDenominator_lt_le_add hind hA hmom hν
      hdim i (ρ := ρ) hbK hδ hηK hηN hμ.le hμδ hc₁ hc₁b hc₁K hc₁δ hc₁1 hM hμM).trans ?_)
  · obtain ⟨x, hx, hx1, hxL⟩ := hω
    have hcc₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hcμ : c ≤ μ := (min_le_left _ _).trans (min_le_right _ _)
    refine ⟨x, hx, hx1, lt_of_le_of_lt (leastCommonDenominator_anti (by gcongr)
      ((min_le_right _ _).trans (min_le_left _ _))) (hxL.trans_le (ENNReal.ofReal_le_ofReal ?_))⟩
    gcongr
  · have hca : c ≤ a / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
      (div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two))
    have hc12 : c ≤ 1 / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
      (div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two))
    refine (add_le_add (add_le_add (hcomp hind hA hmom (Or.inr hdim) i) le_rfl) le_rfl).trans
      ((four_mul_exp_add_two_mul_exp_add_two_mul_exp_le hc.le hca hc12 hdim).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by norm_num)
      (one_le_exp (by positivity))) (exp_pos _).le

end LeastCommonDenominator

end TauCeti.Probability
