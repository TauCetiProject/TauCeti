/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import TauCeti.Analysis.Calculus.FormalMultilinearSeries

/-!
# Scalar formal multilinear series

This file computes the formal composition of two scalar series in an arbitrary algebra. The
algebra need not be commutative: variables retain their original order inside every composition
block. It also evaluates the change-of-origin series of a scalar series on constant vectors, and
uses this to express the iterated derivatives of a scalar power series over a complete nontrivially
normed field, at any point of its ball of convergence, as the termwise differentiated series; at
zero they recover the coefficients. Termwise differentiation of a scalar series represents the
derivative on the same ball, and gives the Euler operator `y * f' y` as `∑ n * c n * y ^ n`. It
also computes the scalar series of `z ↦ f (z ^ m)` on a ball of radius at most `1` from that of
`f`, in any normed algebra with `‖1‖ = 1`. Over a densely normed field, a scalar series whose sum
has no zero in a disk about the origin converges on that disk, because the sum is `0` wherever the
series diverges.

In any normed `𝕜`-algebra `A` with summable geometric series (not necessarily commutative), the
higher geometric series `∑ₙ C(n + k, k) xⁿ` has convergence radius at least `1`
(`TauCeti.one_le_ofScalars_choose_radius`) and represents `(1 - x)⁻¹ʳ ^ (k + 1)` on the open unit
ball (`TauCeti.hasFPowerSeriesOnBall_inverse_one_sub_pow`), extending Mathlib's
`hasFPowerSeriesOnBall_inverse_one_sub` (`k = 0`). Eventual summable majorants on smaller radii
give convergence radius lower bounds
(`FormalMultilinearSeries.le_radius_ofScalars_of_eventually_le`) and analyticity of the sum on
the corresponding open ball
(`FormalMultilinearSeries.analyticOnNhd_ofScalarsSum_of_eventually_le`,
`FormalMultilinearSeries.analyticOnNhd_tsum_mul_pow_of_eventually_le`). Every one-variable
scalar-valued formal multilinear series is `ofScalars` of its `coeff` sequence
(`FormalMultilinearSeries.ofScalars_coeff`). Over a topological field `𝕜`, the scalar series
`FormalMultilinearSeries.ofScalars 𝕜 c` agrees with `TauCeti.mkPiRingSeries 𝕜 c`
(`TauCeti.mkPiRingSeries_eq_ofScalars`).
-/

public section

open scoped BigOperators ENNReal

namespace FormalMultilinearSeries

/-- Every one-variable scalar-valued formal multilinear series equals `ofScalars` applied to its
scalar coefficient sequence. -/
@[simp]
theorem ofScalars_coeff {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (p : FormalMultilinearSeries 𝕜 𝕜 𝕜) : ofScalars 𝕜 p.coeff = p := by
  ext n
  simp [ofScalars, mul_comm]

variable {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E] [IsTopologicalRing E]

/-- Composing two scalar formal multilinear series gives the scalar series whose coefficients are
obtained by summing over compositions. This remains valid for noncommutative target algebras. -/
theorem ofScalars_comp_ofScalars (c d : ℕ → 𝕜) :
    (ofScalars E c).comp (ofScalars E d) =
      ofScalars E fun n ↦ ∑ p : Composition n, c p.length * ∏ i, d (p.blocksFun i) := by
  have prod_ofFn_smul {m : ℕ} (a : Fin m → 𝕜) (b : Fin m → E) :
      (List.ofFn fun i ↦ a i • b i).prod = (∏ i, a i) • (List.ofFn b).prod := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, Fin.prod_univ_succ]
      simp only [List.prod_cons, ih]
      exact smul_mul_smul_comm _ _ _ _
  ext n v
  simp only [FormalMultilinearSeries.comp, ofScalars]
  rw [sum_apply, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hprod :
      (List.ofFn fun i : Fin p.length ↦ (ofScalars E d).applyComposition p v i).prod =
        (∏ i, d (p.blocksFun i)) • (List.ofFn v).prod := by
    simp only [applyComposition, ofScalars, _root_.smul_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply]
    rw [prod_ofFn_smul]
    congr 1
    have hblocks :
        List.ofFn (fun i : Fin p.length ↦ (List.ofFn (v ∘ p.embedding i)).prod) =
          ((List.ofFn v).splitWrtComposition p).map List.prod := by
      refine List.ext_getElem (by simp) fun i hi₁ hi₂ ↦ ?_
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_splitWrtComposition]
      refine congrArg List.prod (List.ext_getElem ?_ fun j hj₁ hj₂ ↦ by
        simpa using congrArg v (Fin.ext (p.coe_embedding _ _)))
      simpa [p.sizeUpTo_le] using
        (Nat.sub_eq_of_eq_add' (p.sizeUpTo_succ' ⟨i, by simpa using hi₁⟩)).symm
    rw [hblocks, ← List.prod_flatten, List.splitWrtComposition,
      List.flatten_splitWrtCompositionAux (by simp)]
  simp only [compAlongComposition_apply, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [hprod, smul_smul]

/-- Evaluating a term of the change-of-origin series of a scalar series at two constant vectors
produces the corresponding binomial coefficient. -/
theorem changeOriginSeries_ofScalars_apply {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedCommRing R] [NormedAlgebra 𝕂 R] (c : ℕ → 𝕂) (x y : R) (n l : ℕ) :
    (((ofScalars R c).changeOriginSeries n l) (fun _ ↦ x)) (fun _ ↦ y) =
      Nat.choose (n + l) l • (c (n + l) • (x ^ l * y ^ n)) := by
  -- The change-of-origin API exposes this coefficient through its defining finite sum. After
  -- unfolding it, each summand places `x` at the `l` indices of its finset and `y` elsewhere.
  rw [changeOriginSeries]
  simp only [_root_.sum_apply]
  simp_rw [changeOriginSeriesTerm_apply]
  have hx (s : {s : Finset (Fin (n + l)) // s.card = l}) :
      ofScalars R c (n + l) (s.val.piecewise (fun _ ↦ x) (fun _ ↦ y)) =
        c (n + l) • (x ^ l * y ^ n) := by
    simp only [ofScalars, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      List.prod_ofFn, Finset.prod_piecewise, Finset.univ_inter, Finset.prod_const,
      Finset.card_univ_sdiff, Fintype.card_fin, s.property, Nat.add_sub_cancel]
  simp_rw [hx]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin]

/-- Inside its ball of convergence, the iterated derivatives of a scalar power series are
given by the termwise differentiated series. -/
theorem _root_.HasFPowerSeriesOnBall.iteratedDeriv_eq_tsum_descFactorial_mul_pow
    {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂]
    {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) 0 r) {y : 𝕂} (hy : ‖y‖ₑ < r) (n : ℕ) :
    iteratedDeriv n f y = ∑' k : ℕ, (k.descFactorial n : 𝕂) * c k * y ^ (k - n) := by
  set p := ofScalars 𝕂 c
  -- the `n`-th derivative at `y` is `n!` times the `n`-th coefficient of the series recentred
  -- at `y`, and that coefficient is the sum of the change-of-origin series
  have hderiv : iteratedDeriv n f y = (n.factorial : 𝕂) * p.changeOrigin y n fun _ ↦ 1 := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    simpa only [zero_add, nsmul_eq_mul] using ((hf.changeOrigin hy).factorial_smul 1 n).symm
  have hsum := ContinuousMultilinearMap.hasSum_eval
    ((p.hasFPowerSeriesOnBall_changeOrigin n (hf.r_pos.trans_le hf.r_le)).hasSum
      (mem_eball_zero_iff.mpr (hy.trans_le hf.r_le))) fun _ ↦ (1 : 𝕂)
  rw [zero_add] at hsum
  -- reindex along `l ↦ l + n`: the terms with `k < n` vanish since `k.descFactorial n = 0`
  rw [hderiv]
  refine (((add_left_injective n).hasSum_iff fun k hk ↦ ?_).mp
    ((hsum.mul_left _).congr_fun fun l ↦ ?_)).tsum_eq.symm
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp fun h ↦ hk ⟨k - n, Nat.sub_add_cancel h⟩)]
  · simp only [Function.comp_apply, p, changeOriginSeries_ofScalars_apply, add_comm l n,
      Nat.add_sub_cancel_left, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
      nsmul_eq_mul, smul_eq_mul, one_pow, mul_one]
    rw [Nat.choose_symm_add]
    ring

/-- The iterated derivatives at zero of the sum of a scalar formal multilinear series over a
complete nontrivially normed field recover its coefficients, up to the factorial normalization. -/
theorem iteratedDeriv_ofScalarsSum_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (c : ℕ → 𝕜) (hc : 0 < (ofScalars 𝕜 c).radius) (n : ℕ) :
    iteratedDeriv n (ofScalarsSum (E := 𝕜) c) 0 = n.factorial * c n := by
  have h := ((ofScalars 𝕜 c).hasFPowerSeriesOnBall hc).iteratedDeriv_eq_tsum_descFactorial_mul_pow
    (y := 0) (by simpa using hc) n
  rw [ofScalarsSum, h, tsum_eq_single n fun k hk ↦ ?_]
  · simp [Nat.descFactorial_self]
  · rcases hk.lt_or_gt with hk | hk
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hk]
    · simp [zero_pow (Nat.sub_ne_zero_of_lt hk)]

/-- **Termwise differentiation of a scalar power series.** If `f` is the sum of the scalar power
series `∑ c n * (z - x) ^ n` on the ball of radius `r` about `x`, then `deriv f` is the sum on
the same ball of the termwise differentiated series `∑ (n + 1) * c (n + 1) * (z - x) ^ n`. -/
theorem _root_.HasFPowerSeriesOnBall.deriv_ofScalars {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    [CompleteSpace 𝕂] {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {x : 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) x r) :
    HasFPowerSeriesOnBall (deriv f) (ofScalars 𝕂 fun n ↦ (n + 1) * c (n + 1)) x r := by
  have h := (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).comp_hasFPowerSeriesOnBall hf.fderiv
  convert h using 1
  · ext y
    exact fderiv_apply_one_eq_deriv.symm
  · -- both series are scalar, so it suffices to compare their coefficients
    ext n : 1
    ext
    rw [apply_eq_prod_smul_coeff, coeff_ofScalars, apply_eq_prod_smul_coeff]
    congr 1
    have h1 := derivSeries_coeff_one (ofScalars 𝕂 c) n
    rw [coeff_ofScalars, nsmul_eq_mul, Nat.cast_succ] at h1
    rw [← h1, coeff, coeff, ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.apply_apply]

/-- **The Euler operator on a scalar power series.** If `f` is the sum of the scalar power series
`∑ c n * z ^ n` on the ball of radius `r` about `0`, then for `y` in that ball,
`y * f' y = ∑ n * c n * y ^ n`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_mul_deriv_ofScalars {𝕂 : Type*}
    [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) 0 r) {y : 𝕂} (hy : ‖y‖ₑ < r) :
    HasSum (fun n : ℕ ↦ n * c n * y ^ n) (y * deriv f y) := by
  have h := (hf.deriv_ofScalars.hasSum (mem_eball_zero_iff.mpr hy)).mul_left y
  rw [zero_add] at h
  -- the term of index `0` vanishes, and the remaining terms are those of `h` shifted by one
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa [ofScalars_apply_eq, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h

/-- **Second-order Euler operator on a scalar power series.** If `f` is the sum of the scalar
power series `∑ c n * z ^ n` on the ball of radius `r` about `0`, then for `y` in that ball,
`y ^ 2 * f'' y = ∑ n * (n - 1) * c n * y ^ n`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_mul_sq_deriv_deriv_ofScalars {𝕂 : Type*}
    [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) 0 r) {y : 𝕂} (hy : ‖y‖ₑ < r) :
    HasSum (fun n : ℕ ↦ (n : 𝕂) * ((n : 𝕂) - 1) * c n * y ^ n)
      (y ^ 2 * deriv (deriv f) y) := by
  have h := (hf.deriv_ofScalars.hasSum_mul_deriv_ofScalars hy).mul_left y
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa [sq, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h

/-- **Substituting `z ^ m` into a scalar power series.** Let `A` be a normed algebra over `𝕂`
with `‖1‖ = 1`, for instance `𝕂` itself. If `f` is the sum of the scalar power series
`∑ c k • z ^ k` on the ball of radius `r ≤ 1` about `0` in `A`, then for `0 < m` the function
`z ↦ f (z ^ m)` is the sum on the same ball of the scalar power series with coefficient `c k` at
the exponent `m * k`, and coefficient `0` at the exponents not divisible by `m`. -/
theorem _root_.HasFPowerSeriesOnBall.comp_pow_ofScalars {𝕂 A : Type*} [NontriviallyNormedField 𝕂]
    [NormedRing A] [NormOneClass A] [NormedAlgebra 𝕂 A] {f : A → A} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars A c) 0 r) (hr : r ≤ 1) {m : ℕ} (hm : 0 < m) :
    HasFPowerSeriesOnBall (fun z ↦ f (z ^ m))
      (ofScalars A fun n ↦ if m ∣ n then c (n / m) else 0) 0 r := by
  have hinj : Function.Injective fun k : ℕ ↦ m * k := fun _ _ e ↦ Nat.eq_of_mul_eq_mul_left hm e
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun ρ hρ ↦ ?_, hf.r_pos, fun {y} hy ↦ ?_⟩
  · -- the expanded series is dominated termwise by the original one, as `ρ < r ≤ 1`
    obtain ⟨C, -, hC⟩ := (ofScalars A c).norm_mul_pow_le_of_lt_radius (hρ.trans_le hf.r_le)
    have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast (hρ.trans_le hr).le
    refine le_radius_of_bound _ C fun n ↦ ?_
    rw [ofScalars_norm]
    split_ifs with hn
    · obtain ⟨k, rfl⟩ := hn
      have hk := hC k
      rw [ofScalars_norm] at hk
      rw [Nat.mul_div_cancel_left _ hm]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ρ.property hρ1
          (Nat.le_mul_of_pos_left k hm))
        (norm_nonneg _)).trans hk
    · simpa using (mul_nonneg (norm_nonneg _) (pow_nonneg ρ.property 0)).trans (hC 0)
  · -- the series of `f` at `y ^ m`, reindexed along the multiples of `m`
    have hy1 : ‖y‖ₑ ≤ 1 := (mem_eball_zero_iff.mp hy).le.trans hr
    have hym : y ^ m ∈ Metric.eball (0 : A) r := by
      rw [mem_eball_zero_iff]
      calc ‖y ^ m‖ₑ ≤ ‖y‖ₑ ^ m := by simpa [eNorm_eq_nnNorm] using mod_cast nnNorm_pow_le y m
        _ ≤ ‖y‖ₑ := pow_le_of_le_one zero_le hy1 hm.ne'
        _ < r := mem_eball_zero_iff.mp hy
    have hs := hf.hasSum hym
    simp only [ofScalars_apply_eq, zero_add] at hs ⊢
    refine (hinj.hasSum_iff fun n hn ↦ ?_).mp (hs.congr_fun fun k ↦ ?_)
    · split_ifs with h
      · exact absurd ⟨n / m, Nat.mul_div_cancel' h⟩ hn
      · exact zero_smul _ _
    · simp [Nat.mul_div_cancel_left _ hm, ← pow_mul]

/-- **Zero-freeness of the analytic sum forces the disk into the disk of convergence.** Over a
densely normed field, if the sum of a scalar series, which is `0` where the series does not
converge, has no zero in a disk about the origin, then that disk lies in the disk of convergence. -/
theorem le_radius_ofScalars_of_ofScalarsSum_ne_zero {𝕜 : Type*} [DenselyNormedField 𝕜]
    (a : ℕ → 𝕜) {r : ℝ≥0∞} (hne : ∀ z : 𝕜, ‖z‖ₑ < r → ofScalarsSum (E := 𝕜) a z ≠ 0) :
    r ≤ (ofScalars 𝕜 a).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun t ht ↦ ?_
  obtain ⟨u, htu, hur⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ht
  obtain ⟨z, htz, hzu⟩ := NormedField.exists_lt_nnNorm_lt 𝕜 (ENNReal.coe_lt_coe.mp htu)
  have hz : ‖z‖ₑ < r := (eNorm_lt_coe.mpr hzu).trans hur
  have hsum : Summable fun n : ℕ ↦ a n * z ^ n := by
    by_contra h
    refine hne z hz ?_
    simpa only [ofScalarsSum_eq_tsum, smul_eq_mul] using tsum_eq_zero_of_not_summable h
  refine (ENNReal.coe_le_coe.mpr htz.le).trans (le_radius_of_tendsto _ (l := 0) ?_)
  simpa [ofScalars_norm] using hsum.tendsto_atTop_zero.norm

/-- **Eventual summable majorant radius criterion.** If `‖c k‖ * r ^ k` is eventually bounded by
a summable sequence, then `r` is at most the radius of convergence of `ofScalars E c`. -/
theorem le_radius_ofScalars_of_eventually_le {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing E] [NormedAlgebra 𝕜 E] {c : ℕ → 𝕜} {u : ℕ → ℝ} {r : NNReal}
    (hu : Summable u) (hc : ∀ᶠ k in Filter.atTop, ‖c k‖ * (r : ℝ) ^ k ≤ u k) :
    (r : ℝ≥0∞) ≤ (ofScalars E c).radius := by
  refine le_radius_of_summable_norm _ (hu.of_norm_bounded_eventually_nat ?_)
  filter_upwards [hc, Filter.eventually_ge_atTop 1] with k hck hk
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg k))]
  exact (mul_le_mul_of_nonneg_right (ofScalars_norm_le E c k hk) (pow_nonneg r.coe_nonneg k)).trans
    hck

/-- Analyticity of the sum of a scalar power series on any open ball within its radius of
convergence. -/
theorem analyticOnNhd_ofScalarsSum_of_le_radius {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing E] [NormedAlgebra 𝕜 E] [CompleteSpace E] {c : ℕ → 𝕜} {R : ℝ≥0∞}
    (hR : 0 < R) (h : R ≤ (ofScalars E c).radius) :
    AnalyticOnNhd 𝕜 (ofScalarsSum (E := E) c) (Metric.eball 0 R) := fun _ hz ↦
  ((ofScalars E c).hasFPowerSeriesOnBall (hR.trans_le h)).analyticAt_of_mem
    (Metric.eball_subset_eball h hz)

/-- **Summable-majorant analyticity criterion.** If for every `r < R` the terms `‖c k‖ * r ^ k`
are eventually bounded by a summable sequence, then `ofScalarsSum (E := E) c` is analytic on
`Metric.eball 0 R`. -/
theorem analyticOnNhd_ofScalarsSum_of_eventually_le {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing E] [NormedAlgebra 𝕜 E] [CompleteSpace E] {c : ℕ → 𝕜} {R : ℝ≥0∞}
    (hR : 0 < R)
    (hc : ∀ r : NNReal, (r : ℝ≥0∞) < R →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ᶠ k in Filter.atTop, ‖c k‖ * (r : ℝ) ^ k ≤ u k) :
    AnalyticOnNhd 𝕜 (ofScalarsSum (E := E) c) (Metric.eball 0 R) :=
  analyticOnNhd_ofScalarsSum_of_le_radius hR <| ENNReal.le_of_forall_nnreal_lt fun r hr ↦ by
    obtain ⟨u, hu, hcu⟩ := hc r hr
    exact le_radius_ofScalars_of_eventually_le hu hcu

/-- **Summable-majorant analyticity criterion on a metric ball.** If for every `r < R` the terms
`‖c k‖ * r ^ k` are eventually bounded by a summable sequence, then `z ↦ ∑' k, c k * z ^ k` is
analytic on `Metric.ball 0 R`. -/
theorem analyticOnNhd_tsum_mul_pow_of_eventually_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] {c : ℕ → 𝕜} {R : ℝ} (hR : 0 < R)
    (hc : ∀ r : NNReal, (r : ℝ) < R →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ᶠ k in Filter.atTop, ‖c k‖ * (r : ℝ) ^ k ≤ u k) :
    AnalyticOnNhd 𝕜 (fun z : 𝕜 ↦ ∑' k : ℕ, c k * z ^ k) (Metric.ball 0 R) := by
  have han := analyticOnNhd_ofScalarsSum_of_eventually_le (𝕜 := 𝕜) (E := 𝕜)
    (ENNReal.ofReal_pos.mpr hR) fun r hr ↦
      hc r (by simpa only [ENNReal.ofReal_eq_coe_nnreal hR.le, ENNReal.coe_lt_coe,
        ← NNReal.coe_lt_coe, NNReal.coe_mk] using hr)
  simp_rw [← smul_eq_mul, ← ofScalarsSum_eq_tsum (E := 𝕜) (c := c)]
  exact han.mono fun z hz ↦ by
    simpa only [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_ofReal_iff hR, Metric.mem_ball]
      using hz

/-- **Polynomial-growth radius criterion.** If the coefficients `c : ℕ → 𝕜` satisfy an eventual
polynomial bound `‖c k‖ ≤ C * (k + 1) ^ m`, then the scalar series `ofScalars E c` has
convergence radius at least `1`. -/
theorem one_le_radius_ofScalars_of_eventually_norm_le_mul_pow {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedRing E] [NormedAlgebra 𝕜 E]
    {c : ℕ → 𝕜} {C : ℝ} {m : ℕ}
    (hc : ∀ᶠ k in Filter.atTop, ‖c k‖ ≤ C * ((k : ℝ) + 1) ^ m) :
    1 ≤ (ofScalars E c).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  rw [ENNReal.coe_lt_one_iff] at hr
  have hC : 0 ≤ max C 0 := le_max_right C 0
  have hu : Summable fun k : ℕ ↦ (max C 0 * 2 ^ m) * ((k : ℝ) ^ m * (r : ℝ) ^ k) :=
    (summable_pow_mul_geometric_of_norm_lt_one m (r := (r : ℝ))
      (by simpa [Real.norm_of_nonneg r.coe_nonneg] using NNReal.coe_lt_one.mpr hr)).mul_left _
  refine le_radius_ofScalars_of_eventually_le (r := r) hu ?_
  filter_upwards [hc, Filter.eventually_ge_atTop 1] with k hck hk
  have hk1 : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hck' : ‖c k‖ ≤ max C 0 * 2 ^ m * (k : ℝ) ^ m := by
    refine hck.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)).trans ?_)
    calc
      max C 0 * ((k : ℝ) + 1) ^ m ≤ max C 0 * (2 * (k : ℝ)) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hk1 m) hC
      _ = max C 0 * 2 ^ m * (k : ℝ) ^ m := by rw [mul_pow, mul_assoc]
  exact (mul_le_mul_of_nonneg_right hck' (pow_nonneg r.coe_nonneg k)).trans_eq (mul_assoc _ _ _)

end FormalMultilinearSeries

namespace TauCeti

open scoped NNReal Ring

/-- The scalar multilinear series `∑ₙ C(n + k, k) xⁿ` in any normed `𝕜`-algebra `A` has radius of
convergence at least `1`. -/
theorem one_le_ofScalars_choose_radius (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] (k : ℕ) :
    1 ≤ (FormalMultilinearSeries.ofScalars A fun n : ℕ ↦ ((n + k).choose k : 𝕜)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  rw [ENNReal.coe_lt_one_iff] at hr
  apply FormalMultilinearSeries.le_radius_of_summable
  rw [← summable_nat_add_iff 1]
  have hmaj : Summable fun n : ℕ ↦ (((n + 1 + k).choose k : ℕ) : ℝ) * (r : ℝ) ^ (n + 1) :=
    (summable_nat_add_iff (f := fun m : ℕ ↦ (((m + k).choose k : ℕ) : ℝ) * (r : ℝ) ^ m) 1).2
      (summable_choose_mul_geometric_of_norm_lt_one k (by simpa using hr))
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hmaj
  gcongr
  refine (FormalMultilinearSeries.ofScalars_norm_le A _ (n + 1) (Nat.succ_pos n)).trans ?_
  simpa using Nat.norm_cast_le (α := 𝕜) ((n + 1 + k).choose k)

/-- In a normed `𝕜`-algebra `A` with summable geometric series, `(1 - x)⁻¹ʳ ^ (k + 1)` is
represented on the open unit ball by the scalar series `∑ₙ C(n + k, k) xⁿ`. -/
theorem hasFPowerSeriesOnBall_inverse_one_sub_pow (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A] (k : ℕ) :
    HasFPowerSeriesOnBall (fun x : A ↦ (1 - x)⁻¹ʳ ^ (k + 1))
      (FormalMultilinearSeries.ofScalars A fun n : ℕ ↦ ((n + k).choose k : 𝕜)) 0 1 where
  r_le := one_le_ofScalars_choose_radius 𝕜 A k
  r_pos := zero_lt_one
  hasSum {y} hy := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] at hy
    rw [zero_add]
    convert hasSum_choose_mul_geometric_of_norm_lt_one' k hy using 1
    ext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/-- Over any topological field `𝕜`, the one-variable series `TauCeti.mkPiRingSeries 𝕜 c` coincides
with `FormalMultilinearSeries.ofScalars 𝕜 c`. -/
theorem mkPiRingSeries_eq_ofScalars {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (c : ℕ → 𝕜) :
    mkPiRingSeries 𝕜 c = FormalMultilinearSeries.ofScalars 𝕜 c := by
  ext1 n
  rw [mkPiRingSeries_def, ← (FormalMultilinearSeries.ofScalars 𝕜 c n).mkPiRing_apply_one_eq_self]
  simp [FormalMultilinearSeries.ofScalars]

end TauCeti
