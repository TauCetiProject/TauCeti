/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Normed.Module.Bases.Unconditional
public import TauCeti.MeasureTheory.Function.Lp.HaarBasis.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Burkholder
import TauCeti.Basic.Real.ConjExponents
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.RCLike

/-!
# Unconditionality of the Haar basis of `Lᵖ([0, 1])`

For `1 < p < ∞` and `𝕜` equal to `ℝ` or `ℂ` (`[RCLike 𝕜]`), the Haar basis of `Lᵖ([0, 1]; 𝕜)` is
unconditional. Each term `(haarBasis 𝕜 p hp).coord n f • haarBasis 𝕜 p hp n` of the Haar expansion
is the dyadic martingale difference `dyadicProj 𝕜 p (n + 1) f - dyadicProj 𝕜 p n f`, so bounding
signed partial sums of the Haar expansion amounts to bounding Haar martingale transforms
`∑ n < N, ε n • (dyadicProj 𝕜 p (n + 1) f - dyadicProj 𝕜 p n f)` for signs `ε n = ±1`:

* **Case `2 ≤ p < ∞` over `ℝ` (Burkholder's Bellman induction).** Both `dyadicProj ℝ p N f` and the
  signed transform `g_N` are step functions constant on the `N` dyadic atoms numbered
  `N, …, 2 * N - 1`. Splitting the atom `N` into its two halves `2 * N` and `2 * N + 1` adds
  opposite increments `±a` to the averages of `f` and `±ε N * a` to `g_N`, so Burkholder's
  midpoint inequality (`TauCeti.two_mul_burkholderPhi_abs_le`) makes
  `∫ x, Φ_p(|dyadicProj ℝ p N f x|, |g_N x|)` nondecreasing in `N`, and nonnegative at `N = 1`
  where `|g_1| = |dyadicProj ℝ p 1 f|`. Burkholder's majorization (`TauCeti.mul_burkholderPhi_le`)
  then yields the bound `‖g_N‖_p ≤ (p - 1) ‖f‖_p`.
* **Orthogonality at `p = 2` and Hölder duality for `1 < p < 2`.** Each `dyadicProj 𝕜 p N` is
  symmetric with respect to the `(Lᵖ, L^q)` integral pairing (`integral_dyadicProj_mul`). On `L²`
  the projections are self-adjoint and consecutive differences are pairwise orthogonal, giving
  projection constant at most `1` over both `ℝ` and `ℂ`. On `Lᵖ(I; ℝ)` for `1 < p < 2`, pairing
  against `L^q` via the isometric embedding `MeasureTheory.Lp.toDual` transfers the `(q - 1)` bound
  from `q = p / (p - 1) > 2`, yielding the unified bound
  `p* - 1 = max p (p / (p - 1)) - 1` for real `±1`-multipliers and finite coordinate projections
  (Burkholder showed `p* - 1` is optimal for real `±1`-transforms; that lower bound is not proved
  here).
* **Complex scalars.** Decomposing `f ∈ Lᵖ(I; 𝕜)` into real and imaginary parts via
  `RCLike.reCLM` and `RCLike.imCLM` gives the bound `2 (p* - 1)` for finite coordinate projections
  over `𝕜`, from which unconditional convergence of the Haar expansion and the unconditional basis
  `TauCeti.unitInterval.unconditionalHaarBasis` follow.

## Main definitions

* `TauCeti.unitInterval.unconditionalHaarBasis 𝕜 p hp1 hp`: the Haar system as an
  `UnconditionalSchauderBasis ℕ 𝕜 (Lp 𝕜 p (volume : Measure I))` for `1 < p < ∞`.

## Main results

* `TauCeti.unitInterval.integral_dyadicProj_mul`: `dyadicProj` is symmetric for the `(Lᵖ, L^q)`
  integral pairing.
* `TauCeti.unitInterval.inner_haarBasis_eq_zero`: the Haar functions are pairwise orthogonal in
  `L²([0, 1]; 𝕜)`.
* `TauCeti.unitInterval.norm_sum_smul_dyadicProj_sub_real_le`: Burkholder's `p* - 1` bound
  for real Haar sign transforms on `Lᵖ([0, 1]; ℝ)`, `1 < p < ∞`.
* `TauCeti.unitInterval.norm_proj_haarBasis_real_le` and
  `TauCeti.unitInterval.norm_proj_haarBasis_le`: uniform bounds `p* - 1` (over `ℝ`) and
  `2 (p* - 1)` (over `𝕜`) on all finite coordinate projections of the Haar basis.
* `TauCeti.unitInterval.hasSum_haarBasis`: the Haar expansion of every `f ∈ Lᵖ([0, 1]; 𝕜)`
  converges unconditionally for `1 < p < ∞`.
* `TauCeti.unitInterval.unconditionalHaarBasis_real_nnNormProjBound_le`,
  `TauCeti.unitInterval.unconditionalHaarBasis_nnNormProjBound_le`, and
  `TauCeti.unitInterval.unconditionalHaarBasis_two_nnNormProjBound_le_one`: bounds on the
  unconditional basis constant.
* `TauCeti.unitInterval.norm_multiplier_unconditionalHaarBasis_real_le` and
  `TauCeti.unitInterval.norm_multiplier_unconditionalHaarBasis_le`: `(p* - 1) ‖a‖` and
  `4 (p* - 1) ‖a‖` operator-norm bounds for bounded Haar multipliers.

## References

* D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*,
  Ann. Probab. **12** (1984), 647–702.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Graduate Texts in
  Mathematics 233, Springer (2016), §6.1 (Theorems 6.1.3 and 6.1.8).
-/

public section

noncomputable section

open MeasureTheory Filter TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology unitInterval ComplexConjugate InnerProductSpace lp

namespace TauCeti.unitInterval

/-! ### Symmetry of dyadic projections and `L²` orthogonality -/

/-- **Symmetry of dyadic averaging projections.** For Hölder conjugate exponents `p` and `q`,
`dyadicProj` is symmetric with respect to the integral pairing between `Lᵖ(I; 𝕜)` and
`L^q(I; 𝕜)`. -/
theorem integral_dyadicProj_mul {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (N : ℕ) (f : Lp 𝕜 p (volume : Measure I))
    (g : Lp 𝕜 q (volume : Measure I)) :
    ∫ x, dyadicProj 𝕜 p N f x * g x = ∫ x, f x * dyadicProj 𝕜 q N g x := by
  have : q.HolderConjugate p := ENNReal.HolderConjugate.symm
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [← Lp.toDual_apply (q := p) (q' := q) (dyadicProj 𝕜 p 0 f) g,
      ← Lp.toDual_apply (q := p) (q' := q) f (dyadicProj 𝕜 q 0 g)]
    simp
  have hL : ∫ x, dyadicProj 𝕜 p N f x * g x =
      ∑ m ∈ Finset.Ico N (2 * N),
        ((volume.real (dyadicCell m))⁻¹ : 𝕜) * (∫ y in dyadicCell m, f y) *
          ∫ x in dyadicCell m, g x := by
    have hpair :
        ∫ x, dyadicProj 𝕜 p N f x * g x = Lp.toDual 𝕜 volume q p g (dyadicProj 𝕜 p N f) := by
      rw [Lp.toDual_apply]
      exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    rw [hpair, dyadicProj_eq_sum hN f, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, Lp.toDual_indicatorConstLp, mul_one, smul_eq_mul, setAverage_eq,
      RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv]
  have hR : ∫ x, f x * dyadicProj 𝕜 q N g x =
      ∑ m ∈ Finset.Ico N (2 * N),
        ((volume.real (dyadicCell m))⁻¹ : 𝕜) * (∫ y in dyadicCell m, f y) *
          ∫ x in dyadicCell m, g x := by
    rw [← Lp.toDual_apply (q := p) (q' := q) f (dyadicProj 𝕜 q N g),
      dyadicProj_eq_sum hN g, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, Lp.toDual_indicatorConstLp, mul_one, smul_eq_mul, setAverage_eq,
      RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv]
    ring
  exact hL.trans hR.symm

/-- On `L²(I; 𝕜)`, the dyadic averaging projections are self-adjoint. -/
theorem inner_dyadicProj_eq {𝕜 : Type*} [RCLike 𝕜] (N : ℕ)
    (f g : Lp 𝕜 2 (volume : Measure I)) :
    ⟪dyadicProj 𝕜 2 N f, g⟫_𝕜 = ⟪f, dyadicProj 𝕜 2 N g⟫_𝕜 := by
  have : ENNReal.HolderConjugate 2 2 := by simpa using Real.HolderConjugate.two_two.ennrealOfReal
  let conjL : 𝕜 →L[ℝ] 𝕜 := RCLike.conjCLE.toContinuousLinearMap
  have h1 : ⟪dyadicProj 𝕜 2 N f, g⟫_𝕜 =
      ∫ x, (conjL.compLpL 2 volume (dyadicProj 𝕜 2 N f)) x * g x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [conjL.coeFn_compLpL (dyadicProj 𝕜 2 N f)] with x hx
    simp [conjL, hx, RCLike.inner_apply, mul_comm]
  have h2 : ⟪f, dyadicProj 𝕜 2 N g⟫_𝕜 =
      ∫ x, (conjL.compLpL 2 volume f) x * dyadicProj 𝕜 2 N g x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [conjL.coeFn_compLpL f] with x hx
    simp [conjL, hx, RCLike.inner_apply, mul_comm]
  rw [h1, h2, compLpL_dyadicProj]
  exact integral_dyadicProj_mul N (conjL.compLpL 2 volume f) g

/-- **Orthogonality of dyadic martingale differences in `L²`.** -/
theorem inner_dyadicProj_sub_eq_zero {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} (hnm : n ≠ m)
    (f g : Lp 𝕜 2 (volume : Measure I)) :
    ⟪dyadicProj 𝕜 2 (n + 1) f - dyadicProj 𝕜 2 n f,
      dyadicProj 𝕜 2 (m + 1) g - dyadicProj 𝕜 2 m g⟫_𝕜 = 0 := by
  let u := dyadicProj 𝕜 2 (m + 1) g - dyadicProj 𝕜 2 m g
  calc ⟪dyadicProj 𝕜 2 (n + 1) f - dyadicProj 𝕜 2 n f, u⟫_𝕜
      = ⟪f, (dyadicProj 𝕜 2 (n + 1) - dyadicProj 𝕜 2 n) u⟫_𝕜 := by
        rw [sub_apply, inner_sub_left, inner_dyadicProj_eq, inner_dyadicProj_eq, ← inner_sub_right]
    _ = 0 := by
        dsimp only [u]
        rw [← sub_apply (dyadicProj 𝕜 2 (m + 1)) (dyadicProj 𝕜 2 m) g,
          ← SchauderBasis.succSub, ← SchauderBasis.succSub,
          (SchauderBasis.succSub_ortho (dyadicProj_dyadicProj 𝕜 2) n m g).trans (ite_eq_right hnm),
          inner_zero_right]

/-- **The Haar functions are pairwise orthogonal in `L²([0, 1]; 𝕜)`.** -/
theorem inner_haarBasis_eq_zero {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} (hnm : n ≠ m) :
    ⟪haarBasis 𝕜 2 ENNReal.ofNat_ne_top n, haarBasis 𝕜 2 ENNReal.ofNat_ne_top m⟫_𝕜 = 0 := by
  set b := haarBasis 𝕜 2 ENNReal.ofNat_ne_top
  have hvec (k : ℕ) : b k = dyadicProj 𝕜 2 (k + 1) (b k) - dyadicProj 𝕜 2 k (b k) := by
    have hc : b.coord k (b k) = 1 := by simp [b.ortho]
    calc b k = (1 : 𝕜) • b k := (one_smul 𝕜 (b k)).symm
      _ = b.coord k (b k) • b k := by rw [hc]
      _ = dyadicProj 𝕜 2 (k + 1) (b k) - dyadicProj 𝕜 2 k (b k) :=
          coord_smul_haarBasis ENNReal.ofNat_ne_top k (b k)
  rw [hvec n, hvec m]
  exact inner_dyadicProj_sub_eq_zero hnm (b n) (b m)

/-- On `L²([0, 1]; 𝕜)`, every finite coordinate projection of the Haar basis is a contraction. -/
theorem norm_proj_haarBasis_two_le_one {𝕜 : Type*} [RCLike 𝕜] (A : Finset ℕ) :
    ‖GeneralSchauderBasis.proj (haarBasis 𝕜 2 ENNReal.ofNat_ne_top) A‖ ≤ 1 := by
  classical
  let b := haarBasis 𝕜 2 ENNReal.ofNat_ne_top
  refine (GeneralSchauderBasis.proj b A).opNorm_le_bound zero_le_one fun f => ?_
  rw [one_mul]
  let N := (A.sup id).succ
  let d : ℕ → Lp 𝕜 2 (volume : Measure I) := fun n => b.coord n f • b n
  have horth : ⟪∑ n ∈ A, d n, ∑ m ∈ Finset.range N \ A, d m⟫_𝕜 = 0 := by
    rw [sum_inner]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [inner_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hnm : n ≠ m := fun h => (Finset.mem_sdiff.1 hm).2 (h ▸ hn)
    dsimp only [d, b]
    rw [coord_smul_haarBasis, coord_smul_haarBasis]
    exact inner_dyadicProj_sub_eq_zero hnm f f
  have hsum : (∑ n ∈ A, d n) + ∑ m ∈ Finset.range N \ A, d m = dyadicProj 𝕜 2 N f := by
    rw [add_comm, Finset.sum_sdiff (Finset.subset_range_sup_succ A),
      ← SchauderBasis.proj_apply b N f, haarBasis_proj]
  have hle_proj : ‖dyadicProj 𝕜 2 N f‖ ≤ ‖f‖ := by
    simpa using (dyadicProj 𝕜 2 N).le_of_opNorm_le (norm_dyadicProj_le 𝕜 2 N) f
  have hsq : ‖∑ n ∈ A, d n‖ * ‖∑ n ∈ A, d n‖ ≤ ‖f‖ * ‖f‖ :=
    calc ‖∑ n ∈ A, d n‖ * ‖∑ n ∈ A, d n‖
        ≤ ‖∑ n ∈ A, d n‖ * ‖∑ n ∈ A, d n‖ +
            ‖∑ m ∈ Finset.range N \ A, d m‖ * ‖∑ m ∈ Finset.range N \ A, d m‖ :=
          le_add_of_nonneg_right (mul_self_nonneg _)
      _ = ‖(∑ n ∈ A, d n) + ∑ m ∈ Finset.range N \ A, d m‖ *
            ‖(∑ n ∈ A, d n) + ∑ m ∈ Finset.range N \ A, d m‖ :=
          (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth).symm
      _ = ‖dyadicProj 𝕜 2 N f‖ * ‖dyadicProj 𝕜 2 N f‖ := by rw [hsum]
      _ ≤ ‖f‖ * ‖f‖ := mul_self_le_mul_self (norm_nonneg _) hle_proj
  rw [GeneralSchauderBasis.proj_apply]
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 hsq

/-! ### Haar martingale transforms and Burkholder's Bellman estimate for `2 ≤ p < ∞` -/

/-- Value of the Haar martingale transform `∑ n < N, ε n • (dyadicProj (n + 1) f - dyadicProj n f)`
on the dyadic cell numbered `m`. -/
private def transformCell (f : I → ℝ) (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => ε 0 * ⨍ y in dyadicCell 1, f y
  | m + 2 =>
      transformCell f ε ((m + 2) / 2) +
        ε ((m + 2) / 2) *
          ((⨍ y in dyadicCell (m + 2), f y) - ⨍ y in dyadicCell ((m + 2) / 2), f y)
decreasing_by omega

private theorem transformCell_one (f : I → ℝ) (ε : ℕ → ℝ) :
    transformCell f ε 1 = ε 0 * ⨍ y in dyadicCell 1, f y := by
  rw [transformCell]

private theorem transformCell_of_two_le (f : I → ℝ) (ε : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) :
    transformCell f ε m =
      transformCell f ε (m / 2) +
        ε (m / 2) * ((⨍ y in dyadicCell m, f y) - ⨍ y in dyadicCell (m / 2), f y) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [transformCell]

/-- For `0 < N`, the partial sum `∑ n < N, ε n • (dyadicProj ℝ p (n + 1) f - dyadicProj ℝ p n f)`
is almost everywhere the step function `x ↦ transformCell f ε (dyadicAtom N x)`. -/
private theorem sum_smul_dyadicProj_sub_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] {N : ℕ} (hN : 0 < N)
    (ε : ℕ → ℝ) (f : Lp ℝ p (volume : Measure I)) :
    (∑ n ∈ Finset.range N, ε n • (dyadicProj ℝ p (n + 1) f - dyadicProj ℝ p n f)) =ᵐ[volume]
      fun x => transformCell f ε (dyadicAtom N x) := by
  have hfint : Integrable f := (Lp.memLp f).integrable Fact.out
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, dyadicProj_zero, zero_apply,
      sub_zero]
    filter_upwards [Lp.coeFn_smul (ε 0) (dyadicProj ℝ p 1 f), dyadicProj_ae_eq one_ne_zero f,
      condExp_dyadicFiltration_ae_eq 1 hfint] with x hsmul hproj hcond
    obtain ⟨h1, h2⟩ := dyadicAtom_mem_Ico one_pos x
    have hatom : dyadicAtom 1 x = 1 := by omega
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hproj, hcond, hatom, transformCell_one]
  | succ k ih =>
    set M := k + 1
    have hM : 0 < M := Nat.succ_pos k
    rw [Finset.sum_range_succ]
    let S := ∑ n ∈ Finset.range M, ε n • (dyadicProj ℝ p (n + 1) f - dyadicProj ℝ p n f)
    let Δ := dyadicProj ℝ p (M + 1) f - dyadicProj ℝ p M f
    filter_upwards [Lp.coeFn_add S (ε M • Δ), ih hM, Lp.coeFn_smul (ε M) Δ,
      Lp.coeFn_sub (dyadicProj ℝ p (M + 1) f) (dyadicProj ℝ p M f),
      dyadicProj_ae_eq (Nat.succ_ne_zero M) f,
      condExp_dyadicFiltration_ae_eq (M + 1) hfint,
      dyadicProj_ae_eq hM.ne' f,
      condExp_dyadicFiltration_ae_eq M hfint]
      with x hadd hS hsmul hsub hp1 hc1 hp0 hc0
    have hS' : S x = transformCell f ε (dyadicAtom M x) := hS
    rw [hadd, Pi.add_apply, hS', hsmul, Pi.smul_apply, smul_eq_mul, hsub, Pi.sub_apply,
      hp1, hc1, hp0, hc0]
    rcases lt_or_ge (dyadicAtom (M + 1) x) (2 * M) with hlt | hge
    · rw [dyadicAtom_eq_of_lt_two_mul hlt, sub_self, mul_zero, add_zero]
    · rw [transformCell_of_two_le f ε (m := dyadicAtom (M + 1) x) (by omega),
        dyadicAtom_succ_div_two hge, dyadicAtom_eq_of_two_mul_le hM hge]

/-- Splitting `dyadicCell M` into its halves `2 * M` and `2 * M + 1` increases the measure-weighted
Burkholder Bellman integrand. -/
private theorem burkholderPhi_dyadicCell_le {f : I → ℝ} (hf : Integrable f) {r : ℝ} (hr : 2 ≤ r)
    {ε : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hεM : |ε M| = 1) :
    volume.real (dyadicCell M) *
        burkholderPhi r |⨍ y in dyadicCell M, f y| |transformCell f ε M| ≤
      volume.real (dyadicCell (2 * M)) *
          burkholderPhi r |⨍ y in dyadicCell (2 * M), f y| |transformCell f ε (2 * M)| +
        volume.real (dyadicCell (2 * M + 1)) *
          burkholderPhi r |⨍ y in dyadicCell (2 * M + 1), f y|
            |transformCell f ε (2 * M + 1)| := by
  set uM := ⨍ y in dyadicCell M, f y with huM_def
  set u0 := ⨍ y in dyadicCell (2 * M), f y with hu0_def
  set u1 := ⨍ y in dyadicCell (2 * M + 1), f y with hu1_def
  set vM := transformCell f ε M with hvM_def
  let a := (u0 - u1) / 2
  have hmid : uM = 2⁻¹ * (u0 + u1) := by
    simpa only [← huM_def, ← hu0_def, ← hu1_def, smul_eq_mul] using
      setAverage_dyadicCell_eq_half_smul_add hf.integrableOn hM
  have hu0 : u0 = uM + a := by dsimp only [a]; linarith
  have hu1 : u1 = uM - a := by dsimp only [a]; linarith
  have hdiv0 : 2 * M / 2 = M := by omega
  have hdiv1 : (2 * M + 1) / 2 = M := by omega
  have hv0 : transformCell f ε (2 * M) = vM + ε M * a := by
    rw [transformCell_of_two_le f ε (by omega), hdiv0, ← hvM_def, ← hu0_def, ← huM_def, hu0]
    ring
  have hv1 : transformCell f ε (2 * M + 1) = vM - ε M * a := by
    rw [transformCell_of_two_le f ε (by omega), hdiv1, ← hvM_def, ← hu1_def, ← huM_def, hu1]
    ring
  have hvol0 : volume.real (dyadicCell (2 * M)) = volume.real (dyadicCell M) / 2 := by
    simpa using volume_real_dyadicCell_two_mul_add (e := 0) hM two_pos
  have hvol1 : volume.real (dyadicCell (2 * M + 1)) = volume.real (dyadicCell M) / 2 :=
    volume_real_dyadicCell_two_mul_add (e := 1) hM one_lt_two
  have hbell := two_mul_burkholderPhi_abs_le hr uM vM a hεM
  have hvol_nonneg : 0 ≤ volume.real (dyadicCell M) / 2 :=
    div_nonneg measureReal_nonneg zero_le_two
  have hmul := mul_le_mul_of_nonneg_left hbell hvol_nonneg
  rw [hvol0, hvol1, hv0, hv1, hu0, hu1]
  linarith

/-- Burkholder's inductive Bellman inequality over the dyadic atoms at step `N ≥ 1`. -/
private theorem sum_burkholderPhi_nonneg {f : I → ℝ} (hf : Integrable f) {r : ℝ} (hr : 2 ≤ r)
    {ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) :
    ∀ k : ℕ, 0 ≤ ∑ m ∈ Finset.Ico (k + 1) (2 * (k + 1)),
      volume.real (dyadicCell m) *
        burkholderPhi r |⨍ y in dyadicCell m, f y| |transformCell f ε m|
  | 0 => by
    have hIco : Finset.Ico 1 (2 * (0 + 1)) = {1} := rfl
    rw [hIco, Finset.sum_singleton, transformCell_one, abs_mul, hε 0, one_mul, burkholderPhi_def]
    set u := |⨍ y in dyadicCell 1, f y|
    have hu : 0 ≤ u := abs_nonneg _
    have hphi : 0 ≤ (u + u) ^ (r - 1) * ((r - 1) * u - u) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (by nlinarith)
    exact mul_nonneg measureReal_nonneg hphi
  | k + 1 => by
    let M := k + 1
    let Φ : ℕ → ℝ := fun m =>
      volume.real (dyadicCell m) *
        burkholderPhi r |⨍ y in dyadicCell m, f y| |transformCell f ε m|
    have ih : 0 ≤ ∑ m ∈ Finset.Ico M (2 * M), Φ m := sum_burkholderPhi_nonneg hf hr hε k
    have hbot : ∑ m ∈ Finset.Ico M (2 * M), Φ m = Φ M + ∑ m ∈ Finset.Ico (M + 1) (2 * M), Φ m :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) Φ
    have htop : ∑ m ∈ Finset.Ico (M + 1) (2 * (M + 1)), Φ m =
        (∑ m ∈ Finset.Ico (M + 1) (2 * M), Φ m) + Φ (2 * M) + Φ (2 * M + 1) := by
      have h2M : 2 * (M + 1) = 2 * M + 1 + 1 := by omega
      rw [h2M, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
    have hstep : Φ M ≤ Φ (2 * M) + Φ (2 * M + 1) :=
      burkholderPhi_dyadicCell_le hf hr (Nat.succ_pos k) (hε M)
    linarith

/-- For `0 < N` and `1 ≤ p < ∞`, the `p.toReal`-th power of the `Lᵖ` norm of a function almost
everywhere equal to `G ∘ dyadicAtom N` is the atom sum of `|G m| ^ p.toReal`. -/
private theorem norm_rpow_eq_sum_dyadicAtom {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {N : ℕ}
    (hN : 0 < N) {g : Lp ℝ p (volume : Measure I)} {G : ℕ → ℝ}
    (hg : g =ᵐ[volume] fun x => G (dyadicAtom N x)) :
    ‖g‖ ^ p.toReal =
      ∑ m ∈ Finset.Ico N (2 * N), volume.real (dyadicCell m) * |G m| ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hint : ∫ x, ‖g x‖ ^ p.toReal = ∫ x, |G (dyadicAtom N x)| ^ p.toReal := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx, Real.norm_eq_abs]
  rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp g, hint,
    integral_comp_dyadicAtom hN (fun m => |G m| ^ p.toReal)]
  simp only [smul_eq_mul]

/-- **Burkholder's Haar martingale transform inequality for `2 ≤ p < ∞`.** For real `f ∈ Lᵖ(I)` and
signs `|ε n| = 1`, the signed partial sum has `Lᵖ` norm at most `(p - 1) ‖f‖`. -/
theorem norm_sum_smul_dyadicProj_sub_le_of_two_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : 2 ≤ p)
    (hp : p ≠ ∞) (N : ℕ) {ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1)
    (f : Lp ℝ p (volume : Measure I)) :
    ‖∑ n ∈ Finset.range N, ε n • (dyadicProj ℝ p (n + 1) f - dyadicProj ℝ p n f)‖ ≤
      (p.toReal - 1) * ‖f‖ := by
  set r := p.toReal
  have hr2 : 2 ≤ r := by simpa [r] using ENNReal.toReal_mono hp hp2
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg (by linarith) (norm_nonneg f)
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hfint : Integrable f := (Lp.memLp f).integrable Fact.out
  set S := ∑ n ∈ Finset.range N, ε n • (dyadicProj ℝ p (n + 1) f - dyadicProj ℝ p n f)
  set P := dyadicProj ℝ p N f
  -- Express `‖S‖ ^ r` and `‖P‖ ^ r` as atom sums and apply Burkholder's majorization.
  have hSr : ‖S‖ ^ r =
      ∑ m ∈ Finset.Ico N (2 * N), volume.real (dyadicCell m) * |transformCell f ε m| ^ r :=
    norm_rpow_eq_sum_dyadicAtom hp hN (sum_smul_dyadicProj_sub_ae_eq hN ε f)
  have hPr : ‖P‖ ^ r =
      ∑ m ∈ Finset.Ico N (2 * N), volume.real (dyadicCell m) * |⨍ y in dyadicCell m, f y| ^ r :=
    norm_rpow_eq_sum_dyadicAtom hp hN
      ((dyadicProj_ae_eq hN.ne' f).trans (condExp_dyadicFiltration_ae_eq N hfint))
  set c := (r - 1) ^ (r - 1) / r ^ (r - 2)
  have hc_pos : 0 ≤ c :=
    div_nonneg (Real.rpow_nonneg hr1.le _) (Real.rpow_nonneg hr0.le _)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hbell_nonneg : 0 ≤ c * ∑ m ∈ Finset.Ico (k + 1) (2 * (k + 1)),
      volume.real (dyadicCell m) *
        burkholderPhi r |⨍ y in dyadicCell m, f y| |transformCell f ε m| :=
    mul_nonneg hc_pos (sum_burkholderPhi_nonneg hfint hr2 hε k)
  have hmaj : c * (∑ m ∈ Finset.Ico (k + 1) (2 * (k + 1)),
      volume.real (dyadicCell m) *
        burkholderPhi r |⨍ y in dyadicCell m, f y| |transformCell f ε m|) ≤
      (r - 1) ^ r * ‖P‖ ^ r - ‖S‖ ^ r := by
    rw [Finset.mul_sum, hPr, hSr, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun m _ => ?_
    have hm := mul_burkholderPhi_le hr2 (abs_nonneg (⨍ y in dyadicCell m, f y))
      (abs_nonneg (transformCell f ε m))
    have hvm := mul_le_mul_of_nonneg_left hm (measureReal_nonneg (μ := volume) (s := dyadicCell m))
    linarith
  have hpow_le : ‖S‖ ^ r ≤ ((r - 1) * ‖P‖) ^ r := by
    rw [Real.mul_rpow hr1.le (norm_nonneg P)]
    linarith
  have hSP : ‖S‖ ≤ (r - 1) * ‖P‖ :=
    (Real.rpow_le_rpow_iff (norm_nonneg S) (mul_nonneg hr1.le (norm_nonneg P)) hr0).1 hpow_le
  have hPf : ‖P‖ ≤ ‖f‖ := by
    simpa [P] using (dyadicProj ℝ p (k + 1)).le_of_opNorm_le (norm_dyadicProj_le ℝ p (k + 1)) f
  exact hSP.trans (mul_le_mul_of_nonneg_left hPf hr1.le)

/-! ### Hölder duality for `1 < p < 2` and unified bounds -/

/-- **Hölder duality for Haar martingale transforms.** If `p` and `q` are Hölder conjugate with
`2 ≤ q < ∞`, then real Haar sign transforms on `Lᵖ(I; ℝ)` have norm at most `(q - 1) ‖f‖`. -/
theorem norm_sum_smul_dyadicProj_sub_le_of_holderConjugate {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [p.HolderConjugate q] (hq2 : 2 ≤ q) (hq : q ≠ ∞) (N : ℕ)
    {ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) (f : Lp ℝ p (volume : Measure I)) :
    ‖∑ n ∈ Finset.range N, ε n • (dyadicProj ℝ p (n + 1) f - dyadicProj ℝ p n f)‖ ≤
      (q.toReal - 1) * ‖f‖ := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hr2 : 2 ≤ q.toReal := by simpa using ENNReal.toReal_mono hq hq2
  set S := ∑ n ∈ Finset.range N, ε n • (dyadicProj ℝ p (n + 1) f - dyadicProj ℝ p n f)
  have hq1 : 0 ≤ q.toReal - 1 := by linarith
  rw [← (Lp.toDual ℝ volume p q).norm_map S]
  refine (Lp.toDual ℝ volume p q S).opNorm_le_bound (mul_nonneg hq1 (norm_nonneg f)) fun g => ?_
  set Sg := ∑ n ∈ Finset.range N, ε n • (dyadicProj ℝ q (n + 1) g - dyadicProj ℝ q n g)
  have hpair : Lp.toDual ℝ volume p q S g = Lp.toDual ℝ volume p q f Sg := by
    simp only [S, Sg, map_sum, map_smul, map_sub, sum_apply, smul_apply, sub_apply,
      Lp.toDual_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_dyadicProj_mul, integral_dyadicProj_mul]
  rw [hpair]
  calc ‖Lp.toDual ℝ volume p q f Sg‖
      ≤ ‖Lp.toDual ℝ volume p q f‖ * ‖Sg‖ := (Lp.toDual ℝ volume p q f).le_opNorm Sg
    _ = ‖f‖ * ‖Sg‖ := by rw [(Lp.toDual ℝ volume p q).norm_map]
    _ ≤ ‖f‖ * ((q.toReal - 1) * ‖g‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_smul_dyadicProj_sub_le_of_two_le hq2 hq N hε g)
          (norm_nonneg f)
    _ = (q.toReal - 1) * ‖f‖ * ‖g‖ := by ring

/-- **Burkholder's bound for real Haar martingale transforms, `1 < p < ∞`.** For every
`f ∈ Lᵖ(I; ℝ)` and signs `|ε n| = 1`, the signed partial sum has norm at most `(p* - 1) ‖f‖`,
where `p* = max p (p / (p - 1))`. -/
theorem norm_sum_smul_dyadicProj_sub_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) (N : ℕ) {ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1)
    (f : Lp ℝ p (volume : Measure I)) :
    ‖∑ n ∈ Finset.range N, ε n • (dyadicProj ℝ p (n + 1) f - dyadicProj ℝ p n f)‖ ≤
      (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖f‖ := by
  set r := p.toReal
  have hr1 : 1 < r := by simpa [r] using ENNReal.toReal_strict_mono hp hp1
  rcases le_or_gt 2 p with hp2 | hp2
  · have hr2 : 2 ≤ r := by simpa [r] using ENNReal.toReal_mono hp hp2
    have hmax : max r (r / (r - 1)) = r :=
      max_eq_left (div_le_self (by linarith) (by linarith))
    rw [hmax]
    exact norm_sum_smul_dyadicProj_sub_le_of_two_le hp2 hp N hε f
  · have hr2 : r < 2 := by simpa [r] using ENNReal.toReal_strict_mono ENNReal.ofNat_ne_top hp2
    have hrq : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent hr1
    let q : ℝ≥0∞ := ENNReal.ofReal (r / (r - 1))
    have : p.HolderConjugate q := by simpa [r, q, ENNReal.ofReal_toReal hp] using hrq.ennrealOfReal
    have hq_toReal : q.toReal = r / (r - 1) :=
      ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))
    have hq2_real : 2 ≤ r / (r - 1) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hq2 : 2 ≤ q := by simpa [q] using ENNReal.ofReal_le_ofReal hq2_real
    have hmax : max r (r / (r - 1)) = r / (r - 1) := max_eq_right (by linarith)
    rw [hmax, ← hq_toReal]
    exact norm_sum_smul_dyadicProj_sub_le_of_holderConjugate hq2 ENNReal.ofReal_ne_top N hε f

/-- **Bound for `±1`-signed Haar martingale transforms on `Lᵖ(I; 𝕜)`, `1 < p < ∞`.** -/
theorem norm_sum_ofReal_smul_dyadicProj_sub_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (N : ℕ) {ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1)
    (f : Lp 𝕜 p (volume : Measure I)) :
    ‖∑ n ∈ Finset.range N, (ε n : 𝕜) • (dyadicProj 𝕜 p (n + 1) f - dyadicProj 𝕜 p n f)‖ ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖f‖ := by
  let T : Lp 𝕜 p (volume : Measure I) →L[𝕜] Lp 𝕜 p (volume : Measure I) :=
    ∑ n ∈ Finset.range N, (ε n : 𝕜) • (dyadicProj 𝕜 p (n + 1) - dyadicProj 𝕜 p n)
  let T₀ : Lp ℝ p (volume : Measure I) → Lp ℝ p (volume : Measure I) := fun g =>
    ∑ n ∈ Finset.range N, ε n • (dyadicProj ℝ p (n + 1) g - dyadicProj ℝ p n g)
  have hTf : T f =
      ∑ n ∈ Finset.range N, (ε n : 𝕜) • (dyadicProj 𝕜 p (n + 1) f - dyadicProj 𝕜 p n f) := by
    simp [T]
  rw [← hTf]
  refine TauCeti.norm_apply_le_two_mul_of_compLp_ofRealCLM T T₀ (fun g => ?_)
    (by linarith [ENNReal.two_le_max_toReal_div_toReal_sub_one hp1 hp])
    (norm_sum_smul_dyadicProj_sub_real_le hp1 hp N hε) f
  let ofRealLp := (RCLike.ofRealCLM (K := 𝕜)).compLpL p (volume : Measure I)
  have hcoe (u : Lp ℝ p (volume : Measure I)) :
      (RCLike.ofRealCLM (K := 𝕜)).compLp u = ofRealLp u := rfl
  rw [hcoe, hcoe, sum_apply]
  dsimp only [T₀]
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_apply, sub_apply, ← RCLike.real_smul_eq_coe_smul (K := 𝕜) (ε n), map_smul, map_sub,
    compLpL_dyadicProj, compLpL_dyadicProj]

/-! ### Finite coordinate projections and the unconditional Haar basis -/

/-- Every finite coordinate projection of the real Haar basis on `Lᵖ([0, 1]; ℝ)`, `1 < p < ∞`, has
operator norm at most `max p (p / (p - 1)) - 1`. -/
theorem norm_proj_haarBasis_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (A : Finset ℕ) :
    ‖GeneralSchauderBasis.proj (haarBasis ℝ p hp) A‖ ≤
      max p.toReal (p.toReal / (p.toReal - 1)) - 1 := by
  have hC0 : 0 ≤ max p.toReal (p.toReal / (p.toReal - 1)) - 1 := by
    linarith [ENNReal.two_le_max_toReal_div_toReal_sub_one hp1 hp]
  refine (haarBasis ℝ p hp).norm_proj_le_of_forall_range_abs_eq_one hC0 (fun N ε hε f => ?_) A
  simp_rw [RCLike.ofReal_real_eq_id, id_eq, coord_smul_haarBasis]
  exact norm_sum_smul_dyadicProj_sub_real_le hp1 hp N hε f

/-- Every finite coordinate projection of the Haar basis on `Lᵖ([0, 1]; 𝕜)`, `1 < p < ∞`, has
operator norm at most `2 * (max p (p / (p - 1)) - 1)`. -/
theorem norm_proj_haarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) (A : Finset ℕ) :
    ‖GeneralSchauderBasis.proj (haarBasis 𝕜 p hp) A‖ ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) := by
  have hC0 : 0 ≤ 2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) := by
    linarith [ENNReal.two_le_max_toReal_div_toReal_sub_one hp1 hp]
  refine (haarBasis 𝕜 p hp).norm_proj_le_of_forall_range_abs_eq_one hC0 (fun N ε hε f => ?_) A
  simp_rw [coord_smul_haarBasis]
  exact norm_sum_ofReal_smul_dyadicProj_sub_le hp1 hp N hε f

/-- **Unconditional convergence of the Haar expansion.** For `1 < p < ∞` and `f ∈ Lᵖ([0, 1]; 𝕜)`,
the Haar series of `f` converges unconditionally to `f`. -/
theorem hasSum_haarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) (f : Lp 𝕜 p (volume : Measure I)) :
    HasSum (fun n => (haarBasis 𝕜 p hp).coord n f • haarBasis 𝕜 p hp n) f :=
  (haarBasis 𝕜 p hp).hasSum_of_norm_proj_le (norm_proj_haarBasis_le hp1 hp) f

/-- **The unconditional Haar basis of `Lᵖ([0, 1]; 𝕜)`**, `1 < p < ∞`. -/
def unconditionalHaarBasis (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    UnconditionalSchauderBasis ℕ 𝕜 (Lp 𝕜 p (volume : Measure I)) :=
  (haarBasis 𝕜 p hp).toUnconditionalSchauderBasis (hasSum_haarBasis hp1 hp)

/-- `unconditionalHaarBasis` is built from `haarBasis` via `hasSum_haarBasis`. -/
theorem unconditionalHaarBasis_def {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    unconditionalHaarBasis 𝕜 p hp1 hp =
      (haarBasis 𝕜 p hp).toUnconditionalSchauderBasis (hasSum_haarBasis hp1 hp) :=
  (rfl)

/-- Viewing `unconditionalHaarBasis` as a classical Schauder basis recovers `haarBasis`. -/
@[simp]
theorem toSchauderBasis_unconditionalHaarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    (unconditionalHaarBasis 𝕜 p hp1 hp).toSchauderBasis = haarBasis 𝕜 p hp := by
  rw [unconditionalHaarBasis_def,
    SchauderBasis.toSchauderBasis_toUnconditionalSchauderBasis]

/-- The basis vectors of `unconditionalHaarBasis` are those of `haarBasis`. -/
@[simp]
theorem coe_unconditionalHaarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    ⇑(unconditionalHaarBasis 𝕜 p hp1 hp) = ⇑(haarBasis 𝕜 p hp) := by
  rw [unconditionalHaarBasis_def, GeneralSchauderBasis.coe_toUnconditionalSchauderBasis]

/-- The `n`-th vector of `unconditionalHaarBasis` is the `Lᵖ` class of `haarFun n`. -/
theorem unconditionalHaarBasis_apply {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (n : ℕ) :
    unconditionalHaarBasis 𝕜 p hp1 hp n =
      ((memLp_haarFun p n).ofReal (K := 𝕜)).toLp fun x => (haarFun n x : 𝕜) := by
  simp

/-- The `n`-th vector of the unconditional Haar basis is a.e. the Haar function `hₙ`. -/
theorem coeFn_unconditionalHaarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (n : ℕ) :
    unconditionalHaarBasis 𝕜 p hp1 hp n =ᵐ[volume] fun x => (haarFun n x : 𝕜) := by
  rw [coe_unconditionalHaarBasis]
  exact coeFn_haarBasis hp n

/-- The coordinate functionals of `unconditionalHaarBasis` coincide with those of `haarBasis`. -/
@[simp]
theorem unconditionalHaarBasis_coord {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    (unconditionalHaarBasis 𝕜 p hp1 hp).coord = (haarBasis 𝕜 p hp).coord := by
  rw [unconditionalHaarBasis_def, GeneralSchauderBasis.toUnconditionalSchauderBasis_coord]

/-- The finite coordinate projections of `unconditionalHaarBasis` agree with those of
`haarBasis`. -/
theorem unconditionalHaarBasis_proj {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (A : Finset ℕ) :
    (unconditionalHaarBasis 𝕜 p hp1 hp).proj A =
      GeneralSchauderBasis.proj (haarBasis 𝕜 p hp) A := by
  rw [unconditionalHaarBasis_def, GeneralSchauderBasis.toUnconditionalSchauderBasis_proj]

/-- Projecting `unconditionalHaarBasis` onto `Finset.range N` gives `dyadicProj 𝕜 p N`. -/
@[simp]
theorem unconditionalHaarBasis_proj_range {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (N : ℕ) :
    (unconditionalHaarBasis 𝕜 p hp1 hp).proj (Finset.range N) = dyadicProj 𝕜 p N := by
  rw [← (unconditionalHaarBasis 𝕜 p hp1 hp).toSchauderBasis_proj,
    toSchauderBasis_unconditionalHaarBasis, haarBasis_proj]

/-- Each term of the unconditional Haar expansion is a dyadic martingale difference. -/
theorem coord_smul_unconditionalHaarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (n : ℕ) (f : Lp 𝕜 p (volume : Measure I)) :
    (unconditionalHaarBasis 𝕜 p hp1 hp).coord n f • unconditionalHaarBasis 𝕜 p hp1 hp n =
      dyadicProj 𝕜 p (n + 1) f - dyadicProj 𝕜 p n f := by
  rw [unconditionalHaarBasis_coord, coe_unconditionalHaarBasis, coord_smul_haarBasis]

/-- **Unconditional basis constant of the real Haar basis.** For `1 < p < ∞`, the unconditional
projection constant of `unconditionalHaarBasis ℝ p hp1 hp` is at most
`max p (p / (p - 1)) - 1`. -/
theorem unconditionalHaarBasis_real_nnNormProjBound_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) :
    ((unconditionalHaarBasis ℝ p hp1 hp).nnNormProjBound : ℝ) ≤
      max p.toReal (p.toReal / (p.toReal - 1)) - 1 := by
  set C := max p.toReal (p.toReal / (p.toReal - 1)) - 1
  have hC0 : 0 ≤ C := by linarith [ENNReal.two_le_max_toReal_div_toReal_sub_one hp1 hp]
  exact (Real.le_toNNReal_iff_coe_le hC0).1
    ((unconditionalHaarBasis ℝ p hp1 hp).nnNormProjBound_le fun A => by
      rw [Real.coe_toNNReal C hC0, unconditionalHaarBasis_proj]
      exact norm_proj_haarBasis_real_le hp1 hp A)

/-- **Unconditional basis constant of the Haar basis over `𝕜`.** For `1 < p < ∞`, the unconditional
projection constant of `unconditionalHaarBasis 𝕜 p hp1 hp` is at most
`2 * (max p (p / (p - 1)) - 1)`. -/
theorem unconditionalHaarBasis_nnNormProjBound_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞) :
    ((unconditionalHaarBasis 𝕜 p hp1 hp).nnNormProjBound : ℝ) ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) := by
  set C := 2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1)
  have hC0 : 0 ≤ C := by linarith [ENNReal.two_le_max_toReal_div_toReal_sub_one hp1 hp]
  exact (Real.le_toNNReal_iff_coe_le hC0).1
    ((unconditionalHaarBasis 𝕜 p hp1 hp).nnNormProjBound_le fun A => by
      rw [Real.coe_toNNReal C hC0, unconditionalHaarBasis_proj]
      exact norm_proj_haarBasis_le hp1 hp A)

/-- On `L²([0, 1]; 𝕜)`, the unconditional basis constant of the Haar basis is at most `1`. -/
theorem unconditionalHaarBasis_two_nnNormProjBound_le_one {𝕜 : Type*} [RCLike 𝕜] :
    (unconditionalHaarBasis 𝕜 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).nnNormProjBound ≤ 1 :=
  (unconditionalHaarBasis 𝕜 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).nnNormProjBound_le
    fun A => by
      rw [unconditionalHaarBasis_proj]
      exact norm_proj_haarBasis_two_le_one A

/-- **Norm bound for real Haar multipliers.** For `1 < p < ∞` and `a ∈ ℓ^∞(ℕ, ℝ)`, the Haar
multiplier `(unconditionalHaarBasis ℝ p hp1 hp).multiplier a` on `Lᵖ([0, 1]; ℝ)` has operator norm
at most `(max p (p / (p - 1)) - 1) * ‖a‖`. -/
theorem norm_multiplier_unconditionalHaarBasis_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) (a : ℓ^∞(ℕ, ℝ)) :
    ‖(unconditionalHaarBasis ℝ p hp1 hp).multiplier a‖ ≤
      (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖a‖ :=
  (unconditionalHaarBasis ℝ p hp1 hp).norm_multiplier_le_of_forall_range_abs_eq_one
    (by linarith [ENNReal.two_le_max_toReal_div_toReal_sub_one hp1 hp])
    (fun N ε hε f => by
      simp_rw [coord_smul_unconditionalHaarBasis]
      exact norm_sum_smul_dyadicProj_sub_real_le hp1 hp N hε f) a

/-- **Norm bound for Haar multipliers over `𝕜`.** For `1 < p < ∞` and `a ∈ ℓ^∞(ℕ, 𝕜)`, the Haar
multiplier `(unconditionalHaarBasis 𝕜 p hp1 hp).multiplier a` on `Lᵖ([0, 1]; 𝕜)` has operator norm
at most `4 * (max p (p / (p - 1)) - 1) * ‖a‖`. -/
theorem norm_multiplier_unconditionalHaarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞) (a : ℓ^∞(ℕ, 𝕜)) :
    ‖(unconditionalHaarBasis 𝕜 p hp1 hp).multiplier a‖ ≤
      4 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖a‖ :=
  ((unconditionalHaarBasis 𝕜 p hp1 hp).norm_multiplier_le_two_mul_of_forall_range_abs_eq_one
    (C := 2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1))
    (by linarith [ENNReal.two_le_max_toReal_div_toReal_sub_one hp1 hp])
    (fun N ε hε f => by
      simp_rw [coord_smul_unconditionalHaarBasis]
      exact norm_sum_ofReal_smul_dyadicProj_sub_le hp1 hp N hε f) a).trans_eq (by ring)

end TauCeti.unitInterval
