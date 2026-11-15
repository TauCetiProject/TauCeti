/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.NumberTheory.LSeries.Positivity
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Bounds

/-!
# Estermann's residue lower bound for a pair of quadratic characters

For nonprincipal quadratic characters `χ` and `ψ` of levels `M` and `N` whose common-level product
`χ.mul ψ` is also nonprincipal, the four-factor product
`F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` has a simple pole at `s = 1` with positive residue
`λ = L(1, χ) L(1, ψ) L(1, χ.mul ψ)` (`DirichletCharacter.residue_pair_mul_of_mul_ne_one`) and
nonnegative Dirichlet coefficients on `Re(s) > 1`.

Subtracting the principal part `λ / (s - 1)` produces an entire function `G` bounded by
`O((M N)²)` on the circle `|s - 2| = 3 / 2`. Expanding `G(β)` in its Taylor series around `s = 2`
for `β < 1` close to `1`, the first `K` derivatives of `F` at `2` contribute at least the leading
Dirichlet coefficient `1`, the pole subtraction contributes a finite geometric sum in `2 - β`
whose `1 / (1 - β)` term cancels the principal part on the left, and Cauchy's derivative bounds
control the tail above `K ≍ log(M N)`. When `Re F(β) ≤ 0`, this yields Estermann's algebraic
lower bound `λ ≫_ε (1 - β) (M N) ^ (-ε)`, and dividing out the power upper bounds for `L(1, χ)`
and `L(1, χ.mul ψ)` (`DirichletCharacter.norm_LFunction_one_le_mul_rpow`) isolates `L(1, ψ)`.

No primitivity is assumed in either theorem: the product character stays at `Nat.lcm M N`.

## Main results

* `DirichletCharacter.exists_pos_residue_pair_ge`: for every `ε > 0`, there exist
  `δ ∈ (0, 1 / 2)` and `c > 0` such that whenever `β ∈ [1 - δ, 1)` satisfies `Re F(β) ≤ 0`, the
  simple-pole residue `L(1, χ) L(1, ψ) L(1, χ.mul ψ)` is at least `c (1 - β) (M N) ^ (-ε)`.
* `DirichletCharacter.exists_pos_LFunction_one_re_ge_of_pair_re_nonpos`: under the same hypotheses,
  `Re L(1, ψ) ≥ c (1 - β) (M N) ^ (-ε)`.

## References

* T. Estermann, *On Dirichlet's L functions*, J. London Math. Soc. 23 (1948), 275–279.
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Complex Finset Filter Metric
open scoped ComplexOrder Nat Topology

namespace DirichletCharacter

private noncomputable def pairPoleProduct {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s

private noncomputable def pairRegularization {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  dslope (pairPoleProduct χ ψ) 1

private theorem pairPoleProduct_one {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) :
    pairPoleProduct χ ψ 1 = χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 := by
  simp [pairPoleProduct, LFunctionTrivChar₁]

private theorem differentiable_pairRegularization {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) :
    Differentiable ℂ (pairRegularization χ ψ) := by
  have hP : Differentiable ℂ (pairPoleProduct χ ψ) := fun s ↦
    (((differentiable_LFunctionTrivChar₁ 1 s).mul (differentiable_LFunction hχ s)).mul
      (differentiable_LFunction hψ s)).mul (differentiable_LFunction hχψ s)
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope univ_mem).mpr hP.differentiableOn)

private theorem pairRegularization_eq_sub_div {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    pairRegularization χ ψ s =
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s -
        (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1) / (s - 1) := by
  rw [pairRegularization, dslope_of_ne _ hs, slope_def_field, pairPoleProduct_one,
    pairPoleProduct, LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar,
    LFunction_modOne_eq, sub_div]
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hs0]

private theorem exists_norm_pairRegularization_le :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
      χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
      ∀ s ∈ sphere (2 : ℂ) (3 / 2),
        ‖pairRegularization χ ψ s‖ ≤ C₀ * ((M : ℝ) * N) ^ 2 := by
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (2 : ℂ) (3 / 2)).exists_bound_of_continuousOn
    (differentiable_LFunctionTrivChar₁ 1).continuous.continuousOn
  have hB₀_nonneg : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 2 (mem_closedBall_self (by norm_num)))
  refine ⟨max 1 (2 * (343 * B₀ + 1)), le_max_left _ _,
    fun {M N} _ _ χ ψ hχ hψ hχψ s hs ↦ ?_⟩
  have hs_cb : s ∈ closedBall (2 : ℂ) (3 / 2) := sphere_subset_closedBall hs
  have hs1_norm : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have htri := norm_sub_le (s - 1) (1 : ℂ)
    have hsph : ‖s - 2‖ = 3 / 2 := mem_sphere_iff_norm.mp hs
    have heq : s - 1 - 1 = s - 2 := by ring
    rw [heq, hsph, norm_one] at htri
    linarith
  have hs1 : s ≠ 1 := sub_ne_zero.mp fun h ↦ by rw [h, norm_zero] at hs1_norm; linarith
  have hlev {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) (hρ : ρ ≠ 1) :
      ‖ρ.LFunction 1‖ ≤ L :=
    (ρ.norm_LFunction_one_le_one_add_log hρ).trans <| by
      linarith [Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (NeZero.pos L) : (0 : ℝ) < L)]
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  have hP1 : ‖pairPoleProduct χ ψ 1‖ ≤ ((M : ℝ) * N) ^ 2 := by
    rw [pairPoleProduct_one, norm_mul, norm_mul]
    calc
      ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ * ‖(χ.mul ψ).LFunction 1‖
        ≤ (M : ℝ) * N * Nat.lcm M N :=
        mul_le_mul (mul_le_mul (hlev χ hχ) (hlev ψ hψ) (norm_nonneg _) (by positivity))
          (hlev (χ.mul ψ) hχψ) (norm_nonneg _) (by positivity)
      _ ≤ (M : ℝ) * N * ((M : ℝ) * N) := by gcongr
      _ = ((M : ℝ) * N) ^ 2 := by ring
  have hPs : ‖pairPoleProduct χ ψ s‖ ≤ 343 * B₀ * ((M : ℝ) * N) ^ 2 := by
    rw [pairPoleProduct, mul_assoc (LFunctionTrivChar₁ 1 s), mul_assoc (LFunctionTrivChar₁ 1 s),
      norm_mul]
    calc
      ‖LFunctionTrivChar₁ 1 s‖ * ‖χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖
        ≤ B₀ * (343 * ((M : ℝ) * N) ^ 2) :=
        mul_le_mul (hB₀ s hs_cb)
          (norm_LFunction_mul_mul_le_of_mem_closedBall χ ψ hχ hψ hχψ hs_cb)
          (norm_nonneg _) hB₀_nonneg
      _ = 343 * B₀ * ((M : ℝ) * N) ^ 2 := by ring
  rw [pairRegularization, dslope_of_ne _ hs1, slope_def_field, norm_div]
  calc
    ‖pairPoleProduct χ ψ s - pairPoleProduct χ ψ 1‖ / ‖s - 1‖
      ≤ (‖pairPoleProduct χ ψ s‖ + ‖pairPoleProduct χ ψ 1‖) / (1 / 2) :=
      div_le_div₀ (by positivity) (norm_sub_le _ _) (by norm_num) hs1_norm
    _ ≤ (343 * B₀ * ((M : ℝ) * N) ^ 2 + ((M : ℝ) * N) ^ 2) / (1 / 2) := by gcongr
    _ = 2 * (343 * B₀ + 1) * ((M : ℝ) * N) ^ 2 := by ring
    _ ≤ max 1 (2 * (343 * B₀ + 1)) * ((M : ℝ) * N) ^ 2 := by
      gcongr; exact le_max_right _ _

private theorem iteratedDeriv_pairRegularization_two {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) (n : ℕ) :
    iteratedDeriv n (pairRegularization χ ψ) 2 =
      iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2 -
        (-1) ^ n * n ! * (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1) := by
  set res := χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1
  set U : Set ℂ := {s : ℂ | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have hEq : Set.EqOn (LSeries (χ.zetaMulPairCoeffs ψ))
      (pairRegularization χ ψ + fun s ↦ res / (s - 1)) U := by
    intro s hs
    have hs1 : s ≠ 1 := fun h ↦ by simp [U, h] at hs
    rw [(LSeriesHasSum_zetaMulPairCoeffs χ ψ hs).LSeries_eq, Pi.add_apply,
      pairRegularization_eq_sub_div χ ψ hs1, sub_add_cancel]
  have hG : ContDiffAt ℂ n (pairRegularization χ ψ) 2 :=
    (differentiable_pairRegularization hχ hψ hχψ).contDiff.contDiffAt
  have hdiv : ContDiffAt ℂ n (fun s : ℂ ↦ res / (s - 1)) 2 :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (by norm_num)
  have hderiv_div : iteratedDeriv n (fun s : ℂ ↦ res / (s - 1)) 2 = (-1) ^ n * n ! * res := by
    have hcomp := congrFun (iteratedDeriv_comp_sub_const n (fun y : ℂ ↦ res / y) 1) 2
    rw [hcomp, TauCeti.iteratedDeriv_const_div]
    norm_num
  rw [hEq.iteratedDeriv_of_isOpen hU n h2, iteratedDeriv_add hG hdiv, hderiv_div,
    add_sub_cancel_right]

private theorem one_le_sum_taylor_LSeries_zetaMulPairCoeffs {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) {β : ℝ} (hβ : β < 2) {K : ℕ} (hK : 1 ≤ K) :
    1 ≤ ∑ n ∈ range K,
      ((2 - β) ^ n / n !) *
        ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2).re := by
  have habs : LSeries.abscissaOfAbsConv (χ.zetaMulPairCoeffs ψ) < (2 : ℝ) := by
    have hle := (LSeriesHasSum_zetaMulPairCoeffs χ ψ (s := (3 / 2 : ℂ))
      (by norm_num)).LSeriesSummable.abscissaOfAbsConv_le
    exact lt_of_le_of_lt hle (by norm_num)
  have hterm_nonneg (n : ℕ) : 0 ≤ ((2 - β) ^ n / n !) *
      ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2).re := by
    have halt := LSeries.iteratedDeriv_alternating (zetaMulPairCoeffs_nonneg hχ hψ) habs n
    have hre : 0 ≤ ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2).re := by
      simpa using (Complex.nonneg_iff.mp halt).1
    have : 0 < 2 - β := sub_pos.mpr hβ
    positivity
  have h0_mem : 0 ∈ range K := mem_range.mpr hK
  have hF2 : 1 ≤ (LSeries (χ.zetaMulPairCoeffs ψ) 2).re := by
    have hsum : HasSum (fun m : ℕ ↦ (LSeries.term (χ.zetaMulPairCoeffs ψ) 2 m).re)
        (LSeries (χ.zetaMulPairCoeffs ψ) 2).re := by
      have h2re : 1 < (2 : ℂ).re := by norm_num
      have hL := LSeriesHasSum_zetaMulPairCoeffs χ ψ h2re
      rw [← hL.LSeries_eq] at hL
      exact Complex.hasSum_re hL
    have h1 : (LSeries.term (χ.zetaMulPairCoeffs ψ) 2 1).re = 1 := by simp
    have hm (m : ℕ) : 0 ≤ (LSeries.term (χ.zetaMulPairCoeffs ψ) 2 m).re :=
      (Complex.nonneg_iff.mp (LSeries.term_nonneg (zetaMulPairCoeffs_nonneg hχ hψ m) 2)).1
    calc
      (1 : ℝ) = (LSeries.term (χ.zetaMulPairCoeffs ψ) 2 1).re := h1.symm
      _ ≤ ∑' m, (LSeries.term (χ.zetaMulPairCoeffs ψ) 2 m).re :=
        hsum.summable.le_tsum 1 fun m _ ↦ hm m
      _ = (LSeries (χ.zetaMulPairCoeffs ψ) 2).re := hsum.tsum_eq
  calc
    (1 : ℝ) ≤ ((2 - β) ^ 0 / 0 !) *
        ((-1) ^ 0 * iteratedDeriv 0 (LSeries (χ.zetaMulPairCoeffs ψ)) 2).re := by
      simpa [iteratedDeriv_zero] using hF2
    _ ≤ ∑ n ∈ range K, ((2 - β) ^ n / n !) *
        ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2).re :=
      single_le_sum (fun n _ ↦ hterm_nonneg n) h0_mem

private theorem norm_pairRegularization_sub_sum_taylor_le {C₀ : ℝ}
    {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1)
    (hGsph : ∀ s ∈ sphere (2 : ℂ) (3 / 2),
      ‖pairRegularization χ ψ s‖ ≤ C₀ * ((M : ℝ) * N) ^ 2)
    {β : ℝ} (hβlo : 3 / 4 ≤ β) (hβhi : β < 1) (K : ℕ) :
    ‖pairRegularization χ ψ β - ∑ n ∈ range K,
        (n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (pairRegularization χ ψ) 2‖ ≤
      6 * C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ K := by
  set G := pairRegularization χ ψ
  set t : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n G 2
  have hGdiff := differentiable_pairRegularization hχ hψ hχψ
  have hβ2_eq : (β : ℂ) - 2 = ((β - 2 : ℝ) : ℂ) := by push_cast; ring
  have hβball : (β : ℂ) ∈ ball (2 : ℂ) (3 / 2) := by
    rw [mem_ball_iff_norm, hβ2_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hTail : HasSum (fun m ↦ t (m + K)) (G β - ∑ n ∈ range K, t n) :=
    (hasSum_nat_add_iff' K).mpr
      (Complex.hasSum_taylorSeries_on_ball hGdiff.differentiableOn hβball)
  have ht_norm (n : ℕ) : ‖t n‖ ≤ C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ n := by
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
      (by norm_num : (0 : ℝ) < 3 / 2) hGdiff.diffContOnCl hGsph
    have hβ2 : ‖(β : ℂ) - 2‖ ≤ 5 / 4 := by
      rw [hβ2_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    simp only [t, smul_eq_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
    calc
      (n ! : ℝ)⁻¹ * (‖(β : ℂ) - 2‖ ^ n * ‖iteratedDeriv n G 2‖)
        ≤ (n ! : ℝ)⁻¹ * ((5 / 4) ^ n * (n ! * (C₀ * ((M : ℝ) * N) ^ 2) / (3 / 2) ^ n)) := by
        gcongr
      _ = C₀ * ((M : ℝ) * N) ^ 2 * ((5 / 4) ^ n / (3 / 2) ^ n) := by field_simp
      _ = C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ n := by rw [← div_pow]; norm_num
  have hgeom : HasSum (fun m : ℕ ↦ C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ K * (5 / 6) ^ m)
      (6 * C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ K) := by
    convert (hasSum_geometric_of_lt_one (by norm_num) (by norm_num : (5 / 6 : ℝ) < 1)).mul_left
      (C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ K) using 1
    ring
  have hbound (m : ℕ) : ‖t (m + K)‖ ≤
      C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ K * (5 / 6) ^ m := by
    refine (ht_norm (m + K)).trans_eq ?_
    rw [add_comm, pow_add]
    ring
  have hdom : Summable fun m : ℕ ↦ ‖t (m + K)‖ :=
    hgeom.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  rw [← hTail.tsum_eq]
  exact (norm_tsum_le_tsum_norm hdom).trans <|
    (Summable.tsum_le_tsum hbound hdom hgeom.summable).trans_eq hgeom.tsum_eq

private theorem re_taylor_term_pairRegularization {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) (β : ℝ) (n : ℕ) :
    ((n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (pairRegularization χ ψ) 2).re =
      ((2 - β) ^ n / n !) * ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2).re -
        (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re * (2 - β) ^ n := by
  set res := χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1
  have hsub : (β : ℂ) - 2 = (-1 : ℂ) * ((2 - β : ℝ) : ℂ) := by push_cast; ring
  have hpow : ((β : ℂ) - 2) ^ n = (((2 - β) ^ n : ℝ) : ℂ) * (-1) ^ n := by
    rw [hsub, mul_pow, ← Complex.ofReal_pow, mul_comm]
  have hfac0 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by
    rw [← pow_add, Even.neg_one_pow ⟨n, rfl⟩]
  have heq : (n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (pairRegularization χ ψ) 2 =
      (((2 - β) ^ n / n ! : ℝ) : ℂ) *
        ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2) -
        res * (((2 - β) ^ n : ℝ) : ℂ) := by
    simp only [smul_eq_mul, hpow, iteratedDeriv_pairRegularization_two hχ hψ hχψ n]
    push_cast
    calc
      (n ! : ℂ)⁻¹ * ((2 - β : ℂ) ^ n * (-1) ^ n *
          (iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2 - (-1) ^ n * n ! * res))
        = (2 - β : ℂ) ^ n / n ! *
            ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2) -
            ((n ! : ℂ)⁻¹ * n !) * ((-1 : ℂ) ^ n * (-1) ^ n) * res * (2 - β : ℂ) ^ n := by ring
      _ = (2 - β : ℂ) ^ n / n ! *
            ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2) -
            res * (2 - β : ℂ) ^ n := by rw [inv_mul_cancel₀ hfac0, hn1, one_mul, one_mul]
  rw [heq, sub_re, Complex.re_ofReal_mul, Complex.re_mul_ofReal]

private theorem pair_taylor_truncation_bound {C₀ : ℝ}
    {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1)
    (hGsph : ∀ s ∈ sphere (2 : ℂ) (3 / 2),
      ‖pairRegularization χ ψ s‖ ≤ C₀ * ((M : ℝ) * N) ^ 2)
    {β : ℝ} (hβlo : 3 / 4 ≤ β) (hβhi : β < 1) {K : ℕ} (hK : 1 ≤ K) :
    1 - (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re -
        6 * C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ K ≤
      (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re *
        ((2 - β) ^ K / (1 - β)) := by
  set res := χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1
  set t : ℕ → ℂ := fun n ↦
    (n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (pairRegularization χ ψ) 2
  have h2β1 : (2 - β : ℝ) - 1 = 1 - β := by ring
  have hsum_re : (∑ n ∈ range K, t n).re =
      (∑ n ∈ range K, ((2 - β) ^ n / n !) *
        ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2).re) -
        res.re * (((2 - β) ^ K - 1) / (1 - β)) := by
    rw [Complex.re_sum, sum_congr rfl fun n _ ↦ re_taylor_term_pairRegularization hχ hψ hχψ β n,
      sum_sub_distrib, ← mul_sum, geom_sum_eq (by linarith : (2 - β : ℝ) ≠ 1) K, h2β1]
  have hGβ_re : (pairRegularization χ ψ β).re =
      (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re +
        res.re / (1 - β) := by
    have hβ1 : (β : ℂ) - 1 = -((1 - β : ℝ) : ℂ) := by push_cast; ring
    have hdiv : res / ((β : ℂ) - 1) = -(res * (((1 - β)⁻¹ : ℝ) : ℂ)) := by
      rw [hβ1, div_neg, div_eq_mul_inv, ← Complex.ofReal_inv]
    rw [pairRegularization_eq_sub_div χ ψ (Complex.ofReal_ne_one.mpr hβhi.ne),
      hdiv, sub_neg_eq_add, add_re, Complex.re_mul_ofReal, div_eq_mul_inv]
  have h1le := one_le_sum_taylor_LSeries_zetaMulPairCoeffs (β := β) hχq hψq (by linarith) hK
  have hrem_re : -(6 * C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ K) ≤
      (pairRegularization χ ψ β - ∑ n ∈ range K, t n).re :=
    neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans
      (norm_pairRegularization_sub_sum_taylor_le hχ hψ hχψ hGsph hβlo hβhi K))
  have hident : (pairRegularization χ ψ β - ∑ n ∈ range K, t n).re =
      (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re -
        (∑ n ∈ range K, ((2 - β) ^ n / n !) *
          ((-1) ^ n * iteratedDeriv n (LSeries (χ.zetaMulPairCoeffs ψ)) 2).re) +
        res.re * ((2 - β) ^ K / (1 - β)) := by
    rw [sub_re, hGβ_re, hsum_re]
    have h1β : (1 - β : ℝ) ≠ 0 := by linarith
    field_simp [h1β]
    ring
  linarith

private theorem exists_cutoff_pair_taylor {C₀ ε δ : ℝ} (hC₀ : 1 ≤ C₀) (hδpos : 0 < δ)
    (hδeps : δ ≤ ε * Real.log (6 / 5) / 2) {M N : ℕ} [NeZero M] [NeZero N]
    {β : ℝ} (hβ1 : 1 - δ ≤ β) (hβ2 : β < 1) :
    ∃ K : ℕ, 1 ≤ K ∧ 6 * C₀ * ((M : ℝ) * N) ^ 2 * (5 / 6) ^ K ≤ 1 / 2 ∧
      (2 - β) ^ K ≤
        Real.exp ((1 + Real.log (12 * C₀) / Real.log (6 / 5)) * δ) * ((M : ℝ) * N) ^ ε := by
  have hlog65 : 0 < Real.log (6 / 5) := Real.log_pos (by norm_num)
  have hMN1 : (1 : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.mul_pos (NeZero.pos M) (NeZero.pos N)
  have hMN0 : 0 < (M : ℝ) * N := zero_lt_one.trans_le hMN1
  let X : ℝ := 12 * C₀ * ((M : ℝ) * N) ^ 2
  have hX1 : 1 < X := by
    have : 1 ≤ C₀ * ((M : ℝ) * N) ^ 2 := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hMN1)
    have : X = 12 * (C₀ * ((M : ℝ) * N) ^ 2) := by ring
    linarith
  let K : ℕ := ⌊Real.log X / Real.log (6 / 5)⌋₊ + 1
  refine ⟨K, Nat.succ_le_succ (Nat.zero_le _), ?_, ?_⟩
  · have hKlt : Real.log X / Real.log (6 / 5) < K :=
      (Nat.lt_floor_add_one (Real.log X / Real.log (6 / 5))).trans_eq (by push_cast [K]; rfl)
    have hexp : X < (6 / 5 : ℝ) ^ K := by
      rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow]
      exact (div_lt_iff₀ hlog65).mp hKlt
    have hinv : (5 / 6 : ℝ) ^ K = ((6 / 5 : ℝ) ^ K)⁻¹ := by rw [← inv_pow]; norm_num
    have hX2 : 6 * C₀ * ((M : ℝ) * N) ^ 2 = X / 2 := by ring
    rw [hinv, ← div_eq_mul_inv, div_le_iff₀ (by positivity), hX2]
    linarith
  · have hKle : (K : ℝ) ≤ 1 + Real.log X / Real.log (6 / 5) := by
      have hfl := Nat.floor_le (div_nonneg (Real.log_nonneg hX1.le) hlog65.le)
      push_cast [K]; linarith
    have h2βpos : 0 < 2 - β := by linarith
    have hlog2β : Real.log (2 - β) ≤ δ := (Real.log_le_sub_one_of_pos h2βpos).trans (by linarith)
    have hlogX : Real.log X = Real.log (12 * C₀) + 2 * Real.log ((M : ℝ) * N) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; rfl
    have hKlog : (K : ℝ) * Real.log (2 - β) ≤
        (1 + Real.log (12 * C₀) / Real.log (6 / 5)) * δ + Real.log ((M : ℝ) * N) * ε := by
      calc
        (K : ℝ) * Real.log (2 - β) ≤ (K : ℝ) * δ :=
          mul_le_mul_of_nonneg_left hlog2β (Nat.cast_nonneg K)
        _ ≤ (1 + Real.log X / Real.log (6 / 5)) * δ := mul_le_mul_of_nonneg_right hKle hδpos.le
        _ = (1 + Real.log (12 * C₀) / Real.log (6 / 5)) * δ +
              Real.log ((M : ℝ) * N) * (2 * δ / Real.log (6 / 5)) := by rw [hlogX]; ring
        _ ≤ (1 + Real.log (12 * C₀) / Real.log (6 / 5)) * δ + Real.log ((M : ℝ) * N) * ε := by
          have hcoeff : 2 * δ / Real.log (6 / 5) ≤ ε := (div_le_iff₀ hlog65).mpr (by linarith)
          gcongr; exact Real.log_nonneg hMN1
    rw [← Real.exp_log (pow_pos h2βpos K), Real.log_pow, Real.rpow_def_of_pos hMN0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hKlog

/-- **Estermann's residue lower bound.** For every `ε > 0`, there exist `δ ∈ (0, 1 / 2)` and
`c > 0` such that for any nonprincipal quadratic characters `χ` (level `M`) and `ψ` (level `N`)
with `χ.mul ψ ≠ 1`, and any real `β ∈ [1 - δ, 1)` at which the four-factor product has
nonpositive real part, the simple-pole residue `L(1, χ) L(1, ψ) L(1, χ.mul ψ)` has real part at
least `c (1 - β) (M N) ^ (-ε)`. -/
theorem exists_pos_residue_pair_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 2), ∃ c > 0,
      ∀ {M N : ℕ} [NeZero M] [NeZero N]
        (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
        χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
        ∀ {β : ℝ}, β ∈ Set.Ico (1 - δ) 1 →
          (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0 →
          c * (1 - β) * ((M : ℝ) * N) ^ (-ε) ≤
            (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re := by
  obtain ⟨C₀, hC₀, hGsph⟩ := exists_norm_pairRegularization_le
  have : 0 < Real.log (6 / 5) := Real.log_pos (by norm_num)
  let δ : ℝ := min (1 / 4) (ε * Real.log (6 / 5) / 2)
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ14 : δ ≤ 1 / 4 := min_le_left _ _
  let C₂ : ℝ := (1 + Real.log (12 * C₀) / Real.log (6 / 5)) * δ
  refine ⟨δ, ⟨hδpos, hδ14.trans_lt (by norm_num)⟩, (2 * Real.exp C₂)⁻¹, by positivity,
    fun {M N} _ _ χ ψ hχq hψq hχ hψ hχψ {β} hβ hFβ ↦ ?_⟩
  obtain ⟨K, hK1, htail, hpowK⟩ :=
    exists_cutoff_pair_taylor hC₀ hδpos (min_le_right _ _) (M := M) (N := N) hβ.1 hβ.2
  have htrunc := pair_taylor_truncation_bound (K := K) hχq hψq hχ hψ hχψ (hGsph χ ψ hχ hψ hχψ)
    (by linarith [hβ.1]) hβ.2 hK1
  have hhalf : (1 / 2 : ℝ) ≤
      (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re * ((2 - β) ^ K / (1 - β)) := by
    linarith
  have hMN0 : 0 < (M : ℝ) * N :=
    mul_pos (Nat.cast_pos.mpr (NeZero.pos M)) (Nat.cast_pos.mpr (NeZero.pos N))
  have h1βpos : 0 < 1 - β := sub_pos.mpr hβ.2
  have h2βpos : 0 < 2 - β := by linarith [hβ.2]
  calc
    (2 * Real.exp C₂)⁻¹ * (1 - β) * ((M : ℝ) * N) ^ (-ε)
      = (1 - β) / (2 * (Real.exp C₂ * ((M : ℝ) * N) ^ ε)) := by
      rw [Real.rpow_neg hMN0.le]; field_simp
    _ ≤ (1 - β) / (2 * (2 - β) ^ K) :=
      div_le_div_of_nonneg_left h1βpos.le (by positivity) (by linarith)
    _ ≤ (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re := by
      rw [div_le_iff₀ (by positivity)]
      have hh : 1 / 2 * (1 - β) ≤
          (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re * (2 - β) ^ K :=
        (le_div_iff₀ h1βpos).mp (by rw [mul_div_assoc]; exact hhalf)
      linarith

/-- **Estermann's two-character comparison for `L(1, ψ)`.** Under the hypotheses of
`exists_pos_residue_pair_ge`, dividing out the power upper bounds for `L(1, χ)` and
`L(1, χ.mul ψ)` gives `Re L(1, ψ) ≥ c (1 - β) (M N) ^ (-ε)`. -/
theorem exists_pos_LFunction_one_re_ge_of_pair_re_nonpos {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 2), ∃ c > 0,
      ∀ {M N : ℕ} [NeZero M] [NeZero N]
        (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
        χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
        ∀ {β : ℝ}, β ∈ Set.Ico (1 - δ) 1 →
          (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0 →
          c * (1 - β) * ((M : ℝ) * N) ^ (-ε) ≤ (ψ.LFunction 1).re := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, c₀, hc₀, hres⟩ := exists_pos_residue_pair_ge hε3
  let K : ℝ := 1 + 1 / (ε / 3)
  refine ⟨δ, hδ, c₀ / K ^ 2, by positivity,
    fun {M N} _ _ χ ψ hχq hψq hχ hψ hχψ {β} hβ hFβ ↦ ?_⟩
  have hlo := hres χ ψ hχq hψq hχ hψ hχψ hβ hFβ
  have ha := Complex.pos_iff.mp (LFunction_apply_one_pos hχq hχ)
  have hb := Complex.pos_iff.mp (LFunction_apply_one_pos hψq hψ)
  have hd := Complex.pos_iff.mp (LFunction_apply_one_pos (isQuadratic_mul hχq hψq) hχψ)
  have hre_prod : (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re =
      (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re := by
    simp [mul_re, ha.2.symm, hb.2.symm, hd.2.symm]
  have hMN_pos : 0 < (M : ℝ) * N :=
    mul_pos (Nat.cast_pos.mpr (NeZero.pos M)) (Nat.cast_pos.mpr (NeZero.pos N))
  have hM_le : (M : ℝ) ≤ (M : ℝ) * N :=
    le_mul_of_one_le_right (Nat.cast_nonneg M) (Nat.one_le_cast.mpr NeZero.one_le)
  have hlcm_le : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  have ha_ub : (χ.LFunction 1).re ≤ K * ((M : ℝ) * N) ^ (ε / 3) :=
    (Complex.re_le_norm _).trans <| (χ.norm_LFunction_one_le_mul_rpow hχ hε3).trans (by gcongr)
  have hd_ub : ((χ.mul ψ).LFunction 1).re ≤ K * ((M : ℝ) * N) ^ (ε / 3) :=
    (Complex.re_le_norm _).trans <|
      ((χ.mul ψ).norm_LFunction_one_le_mul_rpow hχψ hε3).trans (by gcongr)
  have hcomb : c₀ * (1 - β) * ((M : ℝ) * N) ^ (-(ε / 3)) ≤
      (ψ.LFunction 1).re * (K ^ 2 * ((M : ℝ) * N) ^ (2 * (ε / 3))) := by
    refine hlo.trans ?_
    rw [hre_prod]
    calc
      (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re
        = (ψ.LFunction 1).re * ((χ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re) := by ring
      _ ≤ (ψ.LFunction 1).re *
          ((K * ((M : ℝ) * N) ^ (ε / 3)) * (K * ((M : ℝ) * N) ^ (ε / 3))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul ha_ub hd_ub hd.1.le (by positivity)) hb.1.le
      _ = (ψ.LFunction 1).re * (K ^ 2 * ((M : ℝ) * N) ^ (2 * (ε / 3))) := by
        rw [mul_mul_mul_comm, ← sq, ← Real.rpow_add hMN_pos]; ring_nf
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hexp : -ε = -(ε / 3) + -(2 * (ε / 3)) := by ring
  calc
    c₀ * (1 - β) * ((M : ℝ) * N) ^ (-ε)
      = c₀ * (1 - β) * ((M : ℝ) * N) ^ (-(ε / 3)) * ((M : ℝ) * N) ^ (-(2 * (ε / 3))) := by
      rw [hexp, Real.rpow_add hMN_pos]; ring
    _ ≤ (ψ.LFunction 1).re * (K ^ 2 * ((M : ℝ) * N) ^ (2 * (ε / 3))) *
          ((M : ℝ) * N) ^ (-(2 * (ε / 3))) :=
      mul_le_mul_of_nonneg_right hcomb (by positivity)
    _ = (ψ.LFunction 1).re * K ^ 2 *
          (((M : ℝ) * N) ^ (2 * (ε / 3)) * ((M : ℝ) * N) ^ (-(2 * (ε / 3)))) := by ring
    _ = (ψ.LFunction 1).re * K ^ 2 := by
      rw [← Real.rpow_add hMN_pos, add_neg_cancel, Real.rpow_zero, mul_one]

end DirichletCharacter
