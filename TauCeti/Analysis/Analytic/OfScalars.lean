/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Scalar formal multilinear series

This file computes the formal composition of two scalar series in an arbitrary algebra. The
algebra need not be commutative: variables retain their original order inside every composition
block. It also evaluates the change-of-origin series of a scalar series on constant vectors, and
uses this to express the iterated derivatives of a scalar power series over a complete nontrivially
normed field, at any point of its ball of convergence, as the termwise differentiated series; at
zero they recover the coefficients. It also computes the scalar series of `z ↦ f (z ^ m)` on a
ball of radius at most `1` from that of `f`, in any normed algebra with `‖1‖ = 1`. Over a densely
normed field, a scalar series whose sum has no zero in a disk about the origin converges on that
disk, because the sum is `0` wherever the series diverges.

In any normed `𝕜`-algebra `A` with summable geometric series (not necessarily commutative), the
higher geometric series `∑ₙ C(n + k, k) xⁿ` has convergence radius at least `1`
(`TauCeti.one_le_ofScalars_choose_radius`) and represents `(1 - x)⁻¹ʳ ^ (k + 1)` on the open unit
ball (`TauCeti.hasFPowerSeriesOnBall_inverse_one_sub_pow`), extending Mathlib's
`hasFPowerSeriesOnBall_inverse_one_sub` (`k = 0`).
-/

public section

open scoped BigOperators ENNReal

namespace FormalMultilinearSeries

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
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ρ.2 hρ1 (Nat.le_mul_of_pos_left k hm))
        (norm_nonneg _)).trans hk
    · simpa using (mul_nonneg (norm_nonneg _) (pow_nonneg ρ.2 0)).trans (hC 0)
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

end TauCeti
