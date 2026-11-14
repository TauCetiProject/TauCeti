/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Pullback of Besov spaces along diffeomorphisms with bounded derivatives

Let `E` be a finite-dimensional real inner product space, `F` a complete complex normed space,
`χ : ContDiffBump (0 : E)` a Littlewood–Paley bump function, `s ∈ ℝ`, and `1 ≤ p, q ≤ ∞`. Let
`φ : E ≃ E` be a bijection such that `φ` and `φ⁻¹` have temperate growth and uniformly bounded
iterated derivatives of positive orders (`1 ≤ n ≤ N` for `φ` and `1 ≤ n ≤ N + 1` for `φ⁻¹`, with
`N > |s|`; in particular any smooth diffeomorphism whose derivatives of every positive order, and
those of its inverse, are uniformly bounded).

Pullback `TemperedDistribution.compCLM F φ` restricts to a bounded linear map on the inhomogeneous
Besov space `B^s_{p,q}(E; F)` (`TauCeti.BesovSpace.compCLM`), and when both `φ` and `φ⁻¹` satisfy
the positive-order derivative bounds up to `⌊|s|⌋₊ + 2`, it is a bounded linear equivalence
`B^s_{p,q}(E; F) ≃L[ℂ] B^s_{p,q}(E; F)` (`TauCeti.BesovSpace.compEquiv`,
`TauCeti.BesovSpace.compEquivOfContDiff`), inverse to pullback by `φ⁻¹` and agreeing with
distributional pullback on `𝓢'(E, F)`.

Crucially:
* The operator norm bound `C` depends only on the partition bump `χ` (hence `E` and `finrank ℝ E`),
  the smoothness `s`, `N`, and the uniform bound `L` on positive-order derivatives — **not** on
  `p` or `q` (`TauCeti.BesovSpace.exists_norm_compCLM_le`,
  `TauCeti.BesovSpace.exists_norm_compEquiv_le`).
* Zero-th order bounds on `‖φ x‖` never enter: translations `x ↦ x + a` induce bounded linear
  equivalences of `B^s_{p,q}(E; F)` with operator norms bounded uniformly in `a`, `p`, and `q`
  (`TauCeti.BesovSpace.translateEquiv`, `TauCeti.BesovSpace.exists_norm_translateEquiv_le`).

## Mathematical proof

We prove the off-diagonal Littlewood–Paley block decay estimate
(`TauCeti.exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le`):

`‖Δⱼ (φ^* Δₖ u)‖_p ≤ K 2^{-M |j - k|} ‖Δₖ u‖_p`

by inductively tracking twisted pullbacks `g • φ^* f` for smooth multipliers `g` with bounded
derivatives:
* **High output frequency (`j > k`)**: `Δⱼ (g • φ^* f)` has spectrum in the `j`-th dyadic annulus,
  so the reverse Bernstein inequality bounds its `Lᵖ` norm by `2^{-jM}` times its `M`-th order
  derivatives. Iterating `∂_w (g • φ^* f) = (∂_w g) • φ^* f + ∑ᵢ (a_{w,i} g) • φ^* (∂_{bᵢ} f)`
  (`TemperedDistribution.lineDerivOp_compCLM`) and Bernstein's inequality on `f` bounds those
  derivatives by `O(2^{kM})` using derivatives `1 ≤ n ≤ M` of `φ` and `n = 1` of `φ⁻¹`.
* **Low output frequency (`j < k`)**: on the `k`-th dyadic annulus, `Δₖ u = ∑_ℓ ∂_{b_ℓ} h_ℓ` with
  `‖h_ℓ‖_p = O(2^{-k} ‖Δₖ u‖_p)`. Applying `TemperedDistribution.compCLM_lineDerivOp` writes
  `g • φ^* (∂_{b_ℓ} h_ℓ) = ∑ᵢ ∂_{bᵢ} ((g c_{ℓ,i}) • φ^* h_ℓ) - ∑ᵢ ∂_{bᵢ}(g c_{ℓ,i}) • φ^* h_ℓ`,
  where `c_{ℓ,i}(x) = ⟪bᵢ, Dφ⁻¹(φ x) b_ℓ⟫`. Faà di Bruno's bound
  (`TauCeti.norm_iteratedFDeriv_comp_le_of_contDiffAt`) controls derivatives of `c_{ℓ,i}` up to
  order `M` purely from derivatives `1 ≤ n ≤ M` of `φ` and `1 ≤ n ≤ M + 1` of `φ⁻¹`, while
  Bernstein's inequality on `Δⱼ` costs `O(2^j)` per derivative.

Summing over `d = k - j ∈ ℤ` with `M = N > |s|` via `lp.exists_hasSum_and_norm_le_of_summable`
yields boundedness on `B^s_{p,q}` uniformly in `1 ≤ p, q ≤ ∞`.

## Main declarations

* `TauCeti.exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le`: off-diagonal decay
  `‖Δⱼ (φ^* Δₖ u)‖_p ≤ K 2^{-M |j - k|} ‖Δₖ u‖_p` uniform in `p`.
* `TauCeti.BesovSpace.exists_toDistr_eq_compCLM_and_norm_le`: quantitative Besov norm bound for
  pullback along `φ`, uniform in `1 ≤ p, q ≤ ∞`.
* `TemperedDistribution.MemBesov.compCLM`, `TemperedDistribution.memBesov_compCLM_iff`: stability
  and invariance of `MemBesov` under diffeomorphism pullback.
* `TauCeti.BesovSpace.compCLM`, `TauCeti.BesovSpace.exists_norm_compCLM_le`: pullback as a
  continuous linear map on `B^s_{p,q}` with `p, q`-independent operator norm bound.
* `TauCeti.BesovSpace.compEquiv`, `TauCeti.BesovSpace.compEquivOfContDiff`,
  `TauCeti.BesovSpace.exists_norm_compEquiv_le`,
  `TauCeti.BesovSpace.exists_norm_compEquivOfContDiff_le`: diffeomorphism pullback as a bounded
  linear automorphism of `B^s_{p,q}`, inverse to pullback by `φ⁻¹`.
* `TauCeti.BesovSpace.translateEquiv`, `TauCeti.BesovSpace.compContinuousLinearEquiv`: translations
  and continuous linear automorphisms on `B^s_{p,q}`.

## References

* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, §4.3 (diffeomorphism invariance of
  `B^s_{p,q}`).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, §2.7.
-/

public section

noncomputable section

open MeasureTheory Metric Distribution FourierTransform
open scoped ContDiff ENNReal SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

open TemperedDistribution

/-! ### Derivative bounds for chain-rule coefficients -/

section ChainRuleCoeffs

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The `i`-th coordinate functional of an orthonormal basis `b`, viewed as a continuous real-linear
map into `ℂ`. -/
private def coordComplexCLM {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (i : ι) :
    E →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ (b i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem coordComplexCLM_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (i : ι) (v : E) :
    coordComplexCLM b i v = ((b.toBasis.coord i v : ℝ) : ℂ) := by
  rw [coordComplexCLM, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, innerSL_apply_apply,
    b.toBasis.coord_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_coordComplexCLM_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (i : ι) : ‖coordComplexCLM b i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    rw [coordComplexCLM, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      Complex.norm_real, Real.norm_eq_abs, innerSL_apply_apply, one_mul]
    exact (abs_real_inner_le_norm (b i) v).trans_eq (by rw [b.orthonormal.1 i, one_mul])

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Positive-order bounds up to `M` on `φ` control derivatives up to `M - 1` of the forward
chain-rule coefficient `x ↦ ((bᵢ^*(Dφ(x) w) : ℝ) : ℂ)` by `max 1 L * ‖w‖`. -/
private theorem norm_iteratedFDeriv_coord_fderiv_apply_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    {M : ℕ} {L : ℝ} (hφL : ∀ m, 1 ≤ m → m ≤ M → ∀ x, ‖iteratedFDeriv ℝ m φ x‖ ≤ L)
    (i : ι) (w : E) {n : ℕ} (hn : n + 1 ≤ M) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ ((b.toBasis.coord i (fderiv ℝ φ y w) : ℝ) : ℂ)) x‖ ≤
      max 1 L * ‖w‖ := by
  have heq : (fun y ↦ ((b.toBasis.coord i (fderiv ℝ φ y w) : ℝ) : ℂ)) =
      fun y ↦ coordComplexCLM b i (fderiv ℝ φ y w) :=
    funext fun y ↦ (coordComplexCLM_apply b i _).symm
  rw [heq]
  calc ‖iteratedFDeriv ℝ n (fun y ↦ coordComplexCLM b i (fderiv ℝ φ y w)) x‖
      ≤ ‖coordComplexCLM b i‖ * ‖iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ φ y w) x‖ :=
        (coordComplexCLM b i).norm_iteratedFDeriv_comp_left
          ((hφ.fderiv_apply w).1.contDiffAt) (by exact_mod_cast le_top)
    _ ≤ 1 * (‖iteratedFDeriv ℝ (n + 1) φ x‖ * ‖w‖) :=
        mul_le_mul (norm_coordComplexCLM_le b i)
          (hφ.1.norm_iteratedFDeriv_fderiv_apply_le (by simp) w x)
          (norm_nonneg _) zero_le_one
    _ ≤ max 1 L * ‖w‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right
          ((hφL (n + 1) (by omega) hn x).trans (le_max_right 1 L)) (norm_nonneg w)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Positive-order bounds `1 ≤ m ≤ M` on `φ` and `1 ≤ m ≤ M + 1` on `φ⁻¹` control derivatives up
to order `M` of the inverse chain-rule coefficient `x ↦ ((bᵢ^*(Dφ⁻¹(φ x) b_ℓ) : ℝ) : ℂ)` by
`M! * max 1 L ^ (M + 1)`, without any bound on `‖φ x‖`. -/
private theorem norm_iteratedFDeriv_coord_fderiv_symm_comp_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {M : ℕ} {L : ℝ}
    (hφL : ∀ m, 1 ≤ m → m ≤ M → ∀ x, ‖iteratedFDeriv ℝ m φ x‖ ≤ L)
    (hψL : ∀ m, 1 ≤ m → m ≤ M + 1 → ∀ y, ‖iteratedFDeriv ℝ m φ.symm y‖ ≤ L)
    (i ℓ : ι) {n : ℕ} (hn : n ≤ M) (x : E) :
    ‖iteratedFDeriv ℝ n (fun z ↦ ((b.toBasis.coord i (fderiv ℝ φ.symm (φ z) (b ℓ)) : ℝ) : ℂ)) x‖ ≤
      M.factorial * max 1 L ^ (M + 1) := by
  set Ψ : E → ℂ := fun y ↦ ((b.toBasis.coord i (fderiv ℝ φ.symm y (b ℓ)) : ℝ) : ℂ)
  have hΨ_tg : Ψ.HasTemperateGrowth :=
    (RCLike.hasTemperateGrowth_ofReal ℂ).comp
      ((b.toBasis.coord i).toContinuousLinearMap.hasTemperateGrowth.comp (hψ.fderiv_apply (b ℓ)))
  have hΨ_bd (r : ℕ) (hr : r ≤ n) : ‖iteratedFDeriv ℝ r Ψ (φ x)‖ ≤ max 1 L := by
    have h := norm_iteratedFDeriv_coord_fderiv_apply_le b hψ hψL i (b ℓ) (n := r) (by omega) (φ x)
    rwa [b.orthonormal.1 ℓ, mul_one] at h
  have hφ_bd (r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
      ‖iteratedFDeriv ℝ r φ x‖ ≤ max 1 L ^ r :=
    (hφL r hr1 (hrn.trans hn) x).trans
      ((le_max_right 1 L).trans (le_self_pow₀ (le_max_left 1 L) (by omega)))
  have hcomp : (fun z ↦ ((b.toBasis.coord i (fderiv ℝ φ.symm (φ z) (b ℓ)) : ℝ) : ℂ)) = Ψ ∘ φ := rfl
  rw [hcomp]
  calc ‖iteratedFDeriv ℝ n (Ψ ∘ φ) x‖
      ≤ n.factorial * max 1 L * max 1 L ^ n :=
        norm_iteratedFDeriv_comp_le_of_contDiffAt
          (hΨ_tg.1.contDiffAt.of_le (by exact_mod_cast le_top))
          (hφ.1.contDiffAt.of_le (by exact_mod_cast le_top)) hΨ_bd hφ_bd
    _ ≤ M.factorial * max 1 L * max 1 L ^ M := by
        have h1 : (n.factorial : ℝ) ≤ M.factorial := by exact_mod_cast Nat.factorial_le hn
        have h2 : max 1 L ^ n ≤ max 1 L ^ M := pow_le_pow_right₀ (le_max_left 1 L) hn
        gcongr
    _ = M.factorial * max 1 L ^ (M + 1) := by rw [pow_succ']; ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Uniform Leibniz bound for the product of two scalar functions `E → ℂ`. -/
private theorem norm_iteratedFDeriv_mul_le_two_pow_mul {M : ℕ} {g₁ g₂ : E → ℂ} {G₁ G₂ : ℝ}
    (hg₁ : ContDiff ℝ M g₁) (hg₂ : ContDiff ℝ M g₂)
    (hG₁ : ∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g₁ x‖ ≤ G₁)
    (hG₂ : ∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g₂ x‖ ≤ G₂) {n : ℕ} (hn : n ≤ M) (x : E) :
    ‖iteratedFDeriv ℝ n (g₁ * g₂) x‖ ≤ 2 ^ M * (G₁ * G₂) := by
  have hB : ‖ContinuousLinearMap.mul ℝ ℂ‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ by simp
  have hG₁0 : 0 ≤ G₁ := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hG₁).1
  have hG₂0 : 0 ≤ G₂ := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hG₂).1
  refine ((ContinuousLinearMap.mul ℝ ℂ).norm_iteratedFDeriv_le_two_pow_mul_of_bilinear hB hg₁ hg₂
    hG₁ hG₂ hn x).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hn) (mul_nonneg hG₁0 hG₂0)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Derivative bounds for `x ↦ bᵢ^*(Dφ⁻¹(φ x) b_ℓ) * g(x)` and its directional derivative along
`bᵢ`, used in the low-output-frequency induction step. -/
private theorem norm_iteratedFDeriv_coord_symm_mul_and_fderiv_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {M : ℕ} {L : ℝ}
    (hφL : ∀ m, 1 ≤ m → m ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ m φ x‖ ≤ L)
    (hψL : ∀ m, 1 ≤ m → m ≤ M + 2 → ∀ y, ‖iteratedFDeriv ℝ m φ.symm y‖ ≤ L)
    {g : E → ℂ} {G : ℝ} (hg : g.HasTemperateGrowth)
    (hgG : ∀ n ≤ M + 1, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) (i ℓ : ι) :
    let c : E → ℂ := fun x ↦ ((b.toBasis.coord i (fderiv ℝ φ.symm (φ x) (b ℓ)) : ℝ) : ℂ)
    let G' : ℝ := 2 ^ (M + 1) * ((M + 1).factorial * max 1 L ^ (M + 2) * G)
    c.HasTemperateGrowth ∧
      (∀ n ≤ M + 1, ∀ x, ‖iteratedFDeriv ℝ n (c * g) x‖ ≤ G') ∧
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ (c * g) z (b i)) x‖ ≤ G') := by
  intro c G'
  have hc : c.HasTemperateGrowth :=
    ((RCLike.hasTemperateGrowth_ofReal ℂ).comp
      ((b.toBasis.coord i).toContinuousLinearMap.hasTemperateGrowth.comp
        (hψ.fderiv_apply (b ℓ)))).comp hφ
  have hcg (n : ℕ) (hn : n ≤ M + 1) (x : E) : ‖iteratedFDeriv ℝ n (c * g) x‖ ≤ G' :=
    norm_iteratedFDeriv_mul_le_two_pow_mul (hc.1.of_le (by exact_mod_cast le_top))
      (hg.1.of_le (by exact_mod_cast le_top))
      (fun r hr y ↦ norm_iteratedFDeriv_coord_fderiv_symm_comp_le b hφ hψ hφL hψL i ℓ hr y)
      hgG hn x
  refine ⟨hc, hcg, fun n hn x ↦ ?_⟩
  simpa [b.orthonormal.1] using (hc.mul hg).1.norm_iteratedFDeriv_fderiv_apply_le_of_forall_le
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast le_top) hcg (b i) n hn x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Bounded derivatives of positive orders `1 ≤ n ≤ N` admit a single common bound. -/
private theorem exists_forall_norm_iteratedFDeriv_le_of_pos {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : E → H} {N : ℕ}
    (hbd : ∀ n, 1 ≤ n → n ≤ N → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∃ L, ∀ n, 1 ≤ n → n ≤ N → ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ L := by
  choose C hC using fun n ↦ (em (1 ≤ n ∧ n ≤ N)).elim
    (fun hn ↦ (hbd n hn.1 hn.2).imp fun _ h _ ↦ h) fun hn ↦ ⟨0, fun h ↦ absurd h hn⟩
  exact ⟨∑ n ∈ Finset.Icc 1 N, max (C n) 0, fun n hn₁ hn₂ x ↦
    (hC n ⟨hn₁, hn₂⟩ x).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (f := fun n ↦ max (C n) 0)
        (fun _ _ ↦ le_max_right _ _) (Finset.mem_Icc.2 ⟨hn₁, hn₂⟩)))⟩

end ChainRuleCoeffs

/-! ### Interaction of diffeomorphism pullback with Littlewood–Paley blocks -/

/-- Order-zero estimate: for `g` bounded by `G` and `‖Dφ⁻¹‖ ≤ L`, every block `Δⱼ (g • φ^* f)` of
`f ∈ Lᵖ` is an `Lᵖ` function of norm at most `K * max 1 L ^ finrank ℝ E * G * ‖f‖_p`, uniformly in
`1 ≤ p ≤ ∞`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_norm_le
    (χ : ContDiffBump (0 : E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth) {L : ℝ},
      (∀ y, ‖fderiv ℝ φ.symm y‖ ≤ L) → ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ x, ‖g x‖ ≤ G) → ∀ (j : ℕ) (f : Lp F p (volume : Measure E)),
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F χ j (smulLeftCLM F g (compCLM F φ hφ hψ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ K * max 1 L ^ Module.finrank ℝ E * G * ‖f‖ := by
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) χ
  refine ⟨max CΔ 0, le_max_right _ _, fun {p} _ {φ} hφ hψ {L} hL {g G} hg hG j f ↦ ?_⟩
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  obtain ⟨u₁, hu₁, hu₁n⟩ := Lp.exists_compCLM_toTemperedDistribution_eq_and_norm_le hφ hψ hL f
  obtain ⟨u₂, hu₂, hu₂n⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le hg hG u₁
  obtain ⟨v, hv, hvn⟩ := hΔ j u₂
  refine ⟨v, by rw [hu₁, hu₂, hv], ?_⟩
  calc ‖v‖ ≤ max CΔ 0 * ‖u₂‖ := hvn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (norm_nonneg _))
    _ ≤ max CΔ 0 * (G * (max 1 L ^ Module.finrank ℝ E * ‖f‖)) := by
        gcongr
        exact hu₂n.trans (mul_le_mul_of_nonneg_left hu₁n hG0)
    _ = max CΔ 0 * max 1 L ^ Module.finrank ℝ E * G * ‖f‖ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_add_sum_le_iteratedLineDerivOp_succ {H : Type*} [SeminormedAddCommGroup H]
    {d k : ℕ} {C R L G : ℝ} (hG : 0 ≤ G) (m : Fin (k + 1) → E) (f v₀ : H) (vᵢ : Fin d → H)
    (hv₀ : ‖v₀‖ ≤ 2 ^ (k * k) * ((d + 1 : ℝ) * max 1 L * max 1 (C * R)) ^ k *
      max 1 L ^ d * (∏ j, ‖Fin.init m j‖) * (G * ‖m (Fin.last k)‖) * ‖f‖)
    (hvᵢ : ∀ i, ‖vᵢ i‖ ≤ 2 ^ (k * k) * ((d + 1 : ℝ) * max 1 L * max 1 (C * R)) ^ k *
      max 1 L ^ d * (∏ j, ‖Fin.init m j‖) * (2 ^ k * (max 1 L * ‖m (Fin.last k)‖ * G)) *
      (max 1 (C * R) * ‖f‖)) :
    ‖v₀ + ∑ i, vᵢ i‖ ≤ 2 ^ ((k + 1) * (k + 1)) *
      ((d + 1 : ℝ) * max 1 L * max 1 (C * R)) ^ (k + 1) *
      max 1 L ^ d * (∏ i, ‖m i‖) * G * ‖f‖ := by
  set P := 2 ^ (k * k) * ((d + 1 : ℝ) * max 1 L * max 1 (C * R)) ^ k * max 1 L ^ d *
    (∏ i, ‖m i‖) * G * ‖f‖
  have hP : 0 ≤ P := by positivity
  have hm : (∏ j, ‖Fin.init m j‖) * ‖m (Fin.last k)‖ = ∏ i, ‖m i‖ :=
    (Fin.prod_univ_castSucc fun i ↦ ‖m i‖).symm
  set Q := (2 : ℝ) ^ (2 * k + 1) * (max 1 L * max 1 (C * R))
  have hv₀' : ‖v₀‖ ≤ P * Q := by
    have h1 : (1 : ℝ) ≤ Q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
      (by nlinarith [le_max_left 1 L, le_max_left 1 (C * R)])
    calc ‖v₀‖ ≤ P * 1 := hv₀.trans_eq (by simp only [P, ← hm]; ring)
      _ ≤ P * Q := mul_le_mul_of_nonneg_left h1 hP
  have hvᵢ' (i : Fin d) : ‖vᵢ i‖ ≤ P * Q := by
    have hpow2 : (2 : ℝ) ^ k ≤ 2 ^ (2 * k + 1) := pow_le_pow_right₀ one_le_two (by omega)
    calc ‖vᵢ i‖ ≤ P * (2 ^ k * (max 1 L * max 1 (C * R))) :=
          (hvᵢ i).trans_eq (by simp only [P, ← hm]; ring)
      _ ≤ P * Q := by dsimp only [Q]; gcongr
  calc ‖v₀ + ∑ i, vᵢ i‖ ≤ ‖v₀‖ + ∑ i, ‖vᵢ i‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ P * Q + ∑ _i : Fin d, P * Q := add_le_add hv₀' (Finset.sum_le_sum fun i _ ↦ hvᵢ' i)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hkk : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by ring
        simp only [P, Q, hkk, pow_add, pow_succ]
        ring

/-- **Combined Leibniz, chain-rule, and Bernstein bound for band-limited functions.** Let `f ∈ Lᵖ`
have Fourier transform vanishing outside `closedBall 0 R`, let `φ` have derivatives `1 ≤ n ≤ k`
bounded by `L`, let `‖Dφ⁻¹‖ ≤ L`, and let `g` have derivatives `n ≤ k` bounded by `G`. Then
`∂^{m} (g • φ^* f)` lies in `Lᵖ` with norm growing at most like `max 1 (C * R) ^ k` in `R`,
uniformly in `1 ≤ p ≤ ∞`. -/
private theorem exists_iteratedLineDerivOp_smulLeftCLM_compCLM_eq_and_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ) {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth) {L : ℝ},
      (∀ n, 1 ≤ n → n ≤ k → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ y, ‖fderiv ℝ φ.symm y‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : Fin k → E,
      ∃ v : Lp F p (volume : Measure E),
        ∂^{m} (smulLeftCLM F g (compCLM F φ hφ hψ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ 2 ^ (k * k) * ((Module.finrank ℝ E + 1 : ℝ) * max 1 L * max 1 (C * R)) ^ k *
          max 1 L ^ Module.finrank ℝ E * (∏ i, ‖m i‖) * G * ‖f‖ := by
  obtain ⟨C, hC, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
  set b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  refine ⟨C, hC, fun {p} _ k ↦ ?_⟩
  induction k with
  | zero =>
    intro φ hφ hψ L _ hψL g G hg hgG R _ f _ m
    obtain ⟨hG, hg₀⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
    obtain ⟨u₁, hu₁, hu₁n⟩ := Lp.exists_compCLM_toTemperedDistribution_eq_and_norm_le hφ hψ hψL f
    obtain ⟨v, hv, hvn⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le hg hg₀ u₁
    refine ⟨v, by simpa [hu₁] using hv, ?_⟩
    calc ‖v‖ ≤ G * (max 1 L ^ d * ‖f‖) := hvn.trans (mul_le_mul_of_nonneg_left hu₁n hG)
      _ = _ := by simp [d]; ring
  | succ k ih =>
    intro φ hφ hψ L hφL hψL g G hg hgG R hR f hf m
    set w := m (Fin.last k)
    have hG : 0 ≤ G := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).1
    have hφL' : ∀ n, 1 ≤ n → n ≤ k → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L :=
      fun n hn1 hnk ↦ hφL n hn1 (by omega)
    obtain ⟨v₀, hv₀, hv₀n⟩ := ih hφ hψ hφL' hψL (hg.fderiv_apply w)
      (hg.1.norm_iteratedFDeriv_fderiv_apply_le_of_forall_le (by
        rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast le_top) hgG w)
      hR f hf (Fin.init m)
    set a : Fin d → E → ℂ := fun i x ↦ ((b.toBasis.coord i (fderiv ℝ φ x w) : ℝ) : ℂ)
    have ha_tg (i : Fin d) : (a i).HasTemperateGrowth :=
      (RCLike.hasTemperateGrowth_ofReal ℂ).comp
        ((b.toBasis.coord i).toContinuousLinearMap.hasTemperateGrowth.comp (hφ.fderiv_apply w))
    have ha_bd (i : Fin d) : ∀ n ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ n (a i * g) x‖ ≤ 2 ^ k * (max 1 L * ‖w‖ * G) := fun n hn x ↦
      norm_iteratedFDeriv_mul_le_two_pow_mul ((ha_tg i).1.of_le (by exact_mod_cast le_top))
        (hg.1.of_le (by exact_mod_cast le_top))
        (fun r hr y ↦ norm_iteratedFDeriv_coord_fderiv_apply_le b hφ hφL i w (n := r) (by omega) y)
        (fun r hr y ↦ hgG r (by omega) y) hn x
    choose f' hf' hf'n using fun i : Fin d ↦ hB hR f hf (b i)
    have hf'v (i : Fin d) : IsVanishingOn (𝓕 (f' i : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ :=
      hf' i ▸ isVanishingOn_fourier_lineDerivOp hf (b i)
    choose vᵢ hvᵢ hvᵢn using fun i : Fin d ↦
      ih hφ hψ hφL' hψL ((ha_tg i).mul hg) (ha_bd i) hR (f' i) (hf'v i) (Fin.init m)
    refine ⟨v₀ + ∑ i, vᵢ i, ?_, norm_add_sum_le_iteratedLineDerivOp_succ hG m f v₀ vᵢ hv₀n fun i ↦
      (hvᵢn i).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
    · rw [LineDeriv.iteratedLineDerivOp_succ_right, lineDerivOp_smulLeftCLM hg,
        lineDerivOp_compCLM b.toBasis hφ hψ, b.coe_toBasis, map_sum,
        LineDeriv.iteratedLineDerivOp_add, hv₀, LineDeriv.iteratedLineDerivOp_sum,
        Lp.toTemperedDistribution_add, Lp.toTemperedDistribution_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smulLeftCLM_smulLeftCLM_apply (ha_tg i) hg, hf' i, hvᵢ i]
    · have hbi := hf'n i
      rw [b.orthonormal.1 i, mul_one] at hbi
      exact hbi.trans (mul_le_mul_of_nonneg_right (le_max_right 1 (C * R)) (norm_nonneg f))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem two_mul_rOut_div_rIn_mul (χ : ContDiffBump (0 : E)) (k : ℕ) :
    2 * χ.rOut / χ.rIn * (2 ^ k * χ.rIn) = 2 ^ (k + 1) * χ.rOut := by
  field_simp [χ.rIn_pos.ne']
  ring

/-- **High output frequency, low input frequency.** For `j > k` and `f ∈ Lᵖ` band-limited to
`closedBall 0 (2^k χ.rOut)`, the block `Δⱼ (g • φ^* f)` has `Lᵖ` norm at most
`K G (2^k / 2^j)^M ‖f‖_p`, where `K` depends only on `χ`, `M`, and the derivative bound `L`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_lt
    (χ : ContDiffBump (0 : E)) (M : ℕ) (L : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth),
      (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ y, ‖fderiv ℝ φ.symm y‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ {j k : ℕ}, k < j →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (2 ^ k * χ.rOut))ᶜ →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F χ j (smulLeftCLM F g (compCLM F φ hφ hψ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ K * G * ((2 : ℝ) ^ k / 2 ^ j) ^ M * ‖f‖ := by
  set b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  obtain ⟨Cr, hCr, hrev⟩ :=
    b.exists_norm_le_div_pow_mul_sum_norm_of_iteratedLineDerivOp_eq (F := F) (2 * χ.rOut / χ.rIn)
  obtain ⟨CB, -, hleib⟩ :=
    exists_iteratedLineDerivOp_smulLeftCLM_compCLM_eq_and_norm_le (E := E) (F := F)
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) χ
  obtain ⟨_, -, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_norm_le (F := F) χ
  set A := 2 * Cr * d * ((d + 1 : ℝ) * max 1 L * max 1 (CB * χ.rOut)) / χ.rIn
  have hA : 0 ≤ A := by have := χ.rIn_pos; positivity
  refine ⟨2 ^ (M * M) * A ^ M * max 1 L ^ d * max CΔ 0, by positivity,
    fun {p} _ {φ} hφ hψ hφL hψL {g G} hg hgG {j k} hkj f hf ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hG, hg₀⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
  obtain ⟨w, hw, -⟩ := h₀ hφ hψ hψL hg hg₀ (j + 1) f
  refine ⟨w, hw, ?_⟩
  have hR : (0 : ℝ) < 2 ^ j * χ.rIn := by have := χ.rIn_pos; positivity
  have hwv : IsVanishingOn (𝓕 (w : 𝓢'(E, F)) : 𝓢'(E, F))
      (ball 0 (2 ^ j * χ.rIn) ∪ (closedBall 0 (2 * χ.rOut / χ.rIn * (2 ^ j * χ.rIn)))ᶜ) := by
    rw [two_mul_rOut_div_rIn_mul, ← hw]
    simpa only [Set.compl_sdiff, Set.union_comm] using
      isVanishingOn_fourier_littlewoodPaleyBlock_succ χ j _
  have hR' : (0 : ℝ) < 2 ^ k * χ.rOut := by have := χ.rOut_pos; positivity
  choose y hy hyn using fun i : Fin M → Fin d ↦ hleib M hφ hψ hφL hψL hg hgG hR' f hf (b ∘ i)
  choose z hz hzn using fun i : Fin M → Fin d ↦ hΔ (j + 1) (y i)
  have hder (i : Fin M → Fin d) : ∂^{⇑b ∘ i} (w : 𝓢'(E, F)) = z i := by
    rw [← hw, ← littlewoodPaleyBlock_iteratedLineDerivOp, hy i, hz i]
  have hmax : max 1 (CB * (2 ^ k * χ.rOut)) ≤ 2 ^ k * max 1 (CB * χ.rOut) := by
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
    refine max_le (by nlinarith [le_max_left 1 (CB * χ.rOut)]) ?_
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hz' (i : Fin M → Fin d) : ‖z i‖ ≤ max CΔ 0 *
      (2 ^ (M * M) * ((d + 1 : ℝ) * max 1 L * (2 ^ k * max 1 (CB * χ.rOut))) ^ M *
        max 1 L ^ d * G * ‖f‖) := by
    have hyi := hyn i
    simp only [Function.comp_apply, b.orthonormal.1, Finset.prod_const_one, mul_one] at hyi
    exact (hzn i).trans (mul_le_mul (le_max_left _ _) (hyi.trans (by gcongr))
      (norm_nonneg _) (le_max_right _ _))
  calc ‖w‖ ≤ (Cr / (2 ^ j * χ.rIn)) ^ M * ∑ i, ‖z i‖ := hrev M hR w z hwv hder
    _ ≤ (Cr / (2 ^ j * χ.rIn)) ^ M * ∑ _i : Fin M → Fin d,
          max CΔ 0 * (2 ^ (M * M) * ((d + 1 : ℝ) * max 1 L *
            (2 ^ k * max 1 (CB * χ.rOut))) ^ M * max 1 L ^ d * G * ‖f‖) := by
        gcongr with i; exact hz' i
    _ = 2 ^ (M * M) * A ^ M * max 1 L ^ d * max CΔ 0 * G *
          ((2 : ℝ) ^ k / 2 ^ (j + 1)) ^ M * ‖f‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, A, d, div_pow, mul_pow, pow_succ]
        have := χ.rIn_pos; push_cast; field_simp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_sum_sum_sub_le_annulus_step {H : Type*} [SeminormedAddCommGroup H]
    (χ : ContDiffBump (0 : E)) {d M j : ℕ} {Crep CB Cc K G R : ℝ}
    (hCB : 0 ≤ CB) (hCc : 0 ≤ Cc) (hK : 0 ≤ K) (hG : 0 ≤ G) (hR : 0 < R)
    (f : H) (h : Fin d → H) (y' z : Fin d → Fin d → H)
    (hh : ∀ ℓ, ‖h ℓ‖ ≤ Crep / R * ‖f‖)
    (hy' : ∀ ℓ i, ‖y' ℓ i‖ ≤ CB * (2 ^ j * χ.rOut) *
      (K * (2 ^ (M + 1) * (Cc * G)) * ((2 : ℝ) ^ j / R) ^ M * ‖h ℓ‖))
    (hz : ∀ ℓ i, ‖z ℓ i‖ ≤ K * (2 ^ (M + 1) * (Cc * G)) * ((2 : ℝ) ^ j / R) ^ M * ‖h ℓ‖) :
    ‖∑ ℓ, ∑ i, (y' ℓ i - z ℓ i)‖ ≤ (d : ℝ) ^ 2 * Crep * (CB * χ.rOut + 1) * 2 ^ (M + 1) * Cc * K *
      G * ((2 : ℝ) ^ j / R) ^ (M + 1) * ‖f‖ := by
  set G' : ℝ := 2 ^ (M + 1) * (Cc * G)
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  have hterm (ℓ i : Fin d) : ‖y' ℓ i - z ℓ i‖ ≤
      Crep * (CB * χ.rOut + 1) * 2 ^ (M + 1) * Cc * K * G *
        ((2 : ℝ) ^ j / R) ^ (M + 1) * ‖f‖ := calc
    ‖y' ℓ i - z ℓ i‖ ≤ ‖y' ℓ i‖ + ‖z ℓ i‖ := norm_sub_le _ _
    _ ≤ (CB * χ.rOut * 2 ^ j + 1) * (K * G' * ((2 : ℝ) ^ j / R) ^ M) * ‖h ℓ‖ :=
        (add_le_add (hy' ℓ i) (hz ℓ i)).trans_eq (by ring)
    _ ≤ (CB * χ.rOut + 1) * 2 ^ j * (K * G' * ((2 : ℝ) ^ j / R) ^ M) * (Crep / R * ‖f‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (hh ℓ)
          (norm_nonneg _) (by have := χ.rOut_pos; positivity)
    _ = _ := by simp only [G', div_eq_mul_inv]; ring
  calc ‖∑ ℓ, ∑ i, (y' ℓ i - z ℓ i)‖
      ≤ ∑ ℓ, ∑ i, ‖y' ℓ i - z ℓ i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _ℓ : Fin d, ∑ _i : Fin d, Crep * (CB * χ.rOut + 1) * 2 ^ (M + 1) * Cc * K * G *
          ((2 : ℝ) ^ j / R) ^ (M + 1) * ‖f‖ :=
        Finset.sum_le_sum fun ℓ _ ↦ Finset.sum_le_sum fun i _ ↦ hterm ℓ i
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Low output frequency, high input frequency.** For `f ∈ Lᵖ` with annular spectrum
`R ≤ ‖ξ‖ ≤ B R`, every block `Δⱼ (g • φ^* f)` has `Lᵖ` norm at most `K G (2^j / R)^M ‖f‖_p`,
where `K` depends only on `χ`, `B`, `M`, and the bound `L` on derivatives `1 ≤ n ≤ M` of `φ` and
`1 ≤ n ≤ M + 1` of `φ⁻¹`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_annulus
    (χ : ContDiffBump (0 : E)) (B : ℝ) (M : ℕ) (L : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth),
      (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ M + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ (j : ℕ) {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F χ j (smulLeftCLM F g (compCLM F φ hφ hψ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ K * G * ((2 : ℝ) ^ j / R) ^ M * ‖f‖ := by
  set b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  obtain ⟨Crep, hCrep, hrep⟩ := b.exists_eq_sum_lineDerivOp_and_norm_le (F := F) B
  obtain ⟨CB, hCB, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
  obtain ⟨K₀, hK₀, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_norm_le (F := F) χ
  induction M with
  | zero =>
    refine ⟨K₀ * max 1 L ^ d, by positivity, fun {p} _ {φ} hφ hψ _ hψL {g G} hg hgG j R _ f _ ↦ ?_⟩
    obtain ⟨w, hw, hwn⟩ := h₀ hφ hψ
      (fun y ↦ by simpa only [norm_iteratedFDeriv_one] using hψL 1 le_rfl le_rfl y)
      hg (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).2 j f
    exact ⟨w, hw, by simpa [d] using hwn⟩
  | succ M ih =>
    obtain ⟨K, hK, hKb⟩ := ih
    set Cc : ℝ := (M + 1).factorial * max 1 L ^ (M + 2)
    have hCc : 0 ≤ Cc := by positivity
    refine ⟨(d : ℝ) ^ 2 * Crep * (CB * χ.rOut + 1) * 2 ^ (M + 1) * Cc * K,
      by have := χ.rOut_pos; positivity,
      fun {p} _ {φ} hφ hψ hφL hψL {g G} hg hgG j R hR f hf ↦ ?_⟩
    have hG : 0 ≤ G := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).1
    obtain ⟨h, hfh, hh⟩ := hrep hR f hf
    set c : Fin d → Fin d → E → ℂ := fun ℓ i x ↦
      ((b.toBasis.coord i (fderiv ℝ φ.symm (φ x) (b ℓ)) : ℝ) : ℂ)
    have hc (ℓ i : Fin d) :=
      norm_iteratedFDeriv_coord_symm_mul_and_fderiv_le b hφ hψ hφL hψL hg hgG i ℓ
    have hφL' := fun n hn1 (hnM : n ≤ M) ↦ hφL n hn1 (by omega)
    have hψL' := fun n hn1 (hnM : n ≤ M + 1) ↦ hψL n hn1 (by omega)
    choose y hy hyn using fun (ℓ i : Fin d) ↦ hKb hφ hψ hφL' hψL' ((hc ℓ i).1.mul hg)
      (fun n hn ↦ (hc ℓ i).2.1 n (by omega)) j hR (h ℓ) (hh ℓ).1
    have hR' : (0 : ℝ) < 2 ^ j * χ.rOut := by have := χ.rOut_pos; positivity
    choose y' hy' hy'n using fun (ℓ i : Fin d) ↦ hB hR' (y ℓ i) (by
      rw [← hy ℓ i]; exact isVanishingOn_fourier_littlewoodPaleyBlock χ j _) (b i)
    choose z hz hzn using fun (ℓ i : Fin d) ↦ hKb hφ hψ hφL' hψL'
      (((hc ℓ i).1.mul hg).fderiv_apply (b i)) (hc ℓ i).2.2 j hR (h ℓ) (hh ℓ).1
    refine ⟨∑ ℓ, ∑ i, (y' ℓ i - z ℓ i), ?_, norm_sum_sum_sub_le_annulus_step χ hCB hCc hK
      hG hR f h y' z (fun ℓ ↦ (hh ℓ).2) (fun ℓ i ↦ ?_) hzn⟩
    · rw [hfh, map_sum, map_sum, map_sum, Lp.toTemperedDistribution_sum]
      refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
      rw [compCLM_lineDerivOp b.toBasis hφ hψ, b.coe_toBasis, map_sum, map_sum,
        Lp.toTemperedDistribution_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hleib : smulLeftCLM F (c ℓ i * g) (∂_{b i} (compCLM F φ hφ hψ (h ℓ : 𝓢'(E, F)))) =
          ∂_{b i} (smulLeftCLM F (c ℓ i * g) (compCLM F φ hφ hψ (h ℓ : 𝓢'(E, F)))) -
            smulLeftCLM F (fun z ↦ fderiv ℝ (c ℓ i * g) z (b i))
              (compCLM F φ hφ hψ (h ℓ : 𝓢'(E, F))) := by
        rw [lineDerivOp_smulLeftCLM ((hc ℓ i).1.mul hg)]; abel
      rw [smulLeftCLM_smulLeftCLM_apply (hc ℓ i).1 hg, hleib, map_sub,
        littlewoodPaleyBlock_lineDerivOp, hy ℓ i, hy' ℓ i, hz ℓ i, Lp.toTemperedDistribution_sub]
    · have hy'i := hy'n ℓ i
      rw [b.orthonormal.1 i, mul_one] at hy'i
      exact hy'i.trans (mul_le_mul_of_nonneg_left (hyn ℓ i) (by positivity))

/-- **Off-diagonal decay of a diffeomorphism pullback between Littlewood–Paley blocks.** Let `M`
be a natural number and `L` a real number. There is `K ≥ 0`, depending only on `χ`, `M` and `L`,
with the following property. Let `φ : E ≃ E` be a bijection such that `φ` and `φ⁻¹` have temperate
growth, the derivatives of `φ` of order `1 ≤ n ≤ M` are bounded by `L`, and the derivatives of
`φ⁻¹` of order `1 ≤ n ≤ M + 1` are bounded by `L`. Then for all `1 ≤ p ≤ ∞`, if the block `Δₖ u`
of a tempered distribution is an `Lᵖ` function `f`, for every `j` the block `Δⱼ (φ^* f)` is an
`Lᵖ` function of norm at most `K 2^{-M |j - k|} ‖f‖_p`. -/
theorem exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le
    (χ : ContDiffBump (0 : E)) (M : ℕ) (L : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth),
      (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ M + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ∀ (j k : ℕ) (u : 𝓢'(E, F)) (f : Lp F p (volume : Measure E)),
      littlewoodPaleyBlock F χ k u = f →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F χ j (compCLM F φ hφ hψ (f : 𝓢'(E, F))) = v ∧
        ‖v‖ ≤ K * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
  obtain ⟨K₁, hK₁, h₁⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_lt (F := F) χ M L
  obtain ⟨K₂, hK₂, h₂⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_annulus
      (F := F) χ (2 * χ.rOut / χ.rIn) M L
  obtain ⟨K₀, hK₀, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_norm_le (F := F) χ
  have hrIn := χ.rIn_pos
  set Ktot := K₁ + K₂ * (2 / χ.rIn) ^ M + K₀ * max 1 L ^ Module.finrank ℝ E
  refine ⟨Ktot, by positivity, fun {p} _ {φ} hφ hψ hφL hψL j k u f hf ↦ ?_⟩
  have hg : (fun _ : E ↦ (1 : ℂ)).HasTemperateGrowth := .const 1
  have hg1 : ∀ n ≤ M, ∀ x : E, ‖iteratedFDeriv ℝ n (fun _ : E ↦ (1 : ℂ)) x‖ ≤ 1 := by
    rintro (_ | n) _ x <;> simp [iteratedFDeriv_succ_const]
  have hψ1 : ∀ y, ‖fderiv ℝ φ.symm y‖ ≤ L := fun y ↦ by
    simpa only [norm_iteratedFDeriv_one] using hψL 1 le_rfl (by omega) y
  have hK (K' : ℝ) (hKK : K' ≤ Ktot) :
      K' * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ ≤
        Ktot * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by gcongr
  have h2n : 0 ≤ K₂ * (2 / χ.rIn) ^ M := by positivity
  have h0n : 0 ≤ K₀ * max 1 L ^ Module.finrank ℝ E := by positivity
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · obtain ⟨v, hv, hvn⟩ := h₁ hφ hψ hφL hψ1 hg hg1 hkj f
      (hf ▸ isVanishingOn_fourier_littlewoodPaleyBlock χ k u)
    rw [smulLeftCLM_const, one_smul] at hv
    refine ⟨v, hv, (hvn.trans_eq ?_).trans (hK K₁ (by linarith))⟩
    rw [mul_one, Real.pow_div_pow_pow_eq_rpow_of_le two_pos hkj.le]
  · obtain ⟨v, hv, hvn⟩ := h₀ hφ hψ hψ1 (G := 1) hg (fun _ ↦ by simp) k f
    rw [smulLeftCLM_const, one_smul] at hv
    exact ⟨v, hv, (by simpa using hvn :
      ‖v‖ ≤ K₀ * max 1 L ^ Module.finrank ℝ E * (2 : ℝ) ^ (-(M * |(k : ℝ) - k|)) * ‖f‖).trans
      (hK _ (by linarith))⟩
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hR : (0 : ℝ) < 2 ^ k * χ.rIn := by positivity
    obtain ⟨v, hv, hvn⟩ := h₂ hφ hψ hφL hψL hg hg1 j hR f (by
      rw [two_mul_rOut_div_rIn_mul, ← hf]
      simpa only [Set.compl_sdiff, Set.union_comm] using
        isVanishingOn_fourier_littlewoodPaleyBlock_succ χ k u)
    rw [smulLeftCLM_const, one_smul] at hv
    have hdiv : (2 : ℝ) ^ j / (2 ^ k * χ.rIn) = (2 / χ.rIn) * ((2 : ℝ) ^ j / 2 ^ (k + 1)) := by
      rw [pow_succ]; field_simp
    refine ⟨v, hv, (hvn.trans_eq ?_).trans (hK (K₂ * (2 / χ.rIn) ^ M) (by linarith))⟩
    rw [mul_one, hdiv, mul_pow, abs_sub_comm,
      ← Real.pow_div_pow_pow_eq_rpow_of_le two_pos hjk.le]
    ring

/-! ### Quantitative pullback bound on Besov spaces -/

/-- **Pullback along a diffeomorphism is bounded on Besov spaces.** Let `N` be a natural number
with `|s| < N`, and let `L` be a real number. There is `C ≥ 0`, depending only on `χ`, `s`, `N`
and `L`, with the following property. Let `φ : E ≃ E` be a bijection such that `φ` and `φ⁻¹` have
temperate growth, the derivatives of `φ` of order `1 ≤ n ≤ N` are bounded by `L`, and those of
`φ⁻¹` of order `1 ≤ n ≤ N + 1` are bounded by `L`. Then for all `1 ≤ p, q ≤ ∞` and every
`u ∈ B^s_{p,q}`, the pullback `φ^* u` lies in `B^s_{p,q}` with `‖φ^* u‖ ≤ C ‖u‖`. -/
theorem BesovSpace.exists_toDistr_eq_compCLM_and_norm_le (χ : ContDiffBump (0 : E))
    {s : ℝ} {N : ℕ} (hN : |s| < N) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth),
      (∀ n, 1 ≤ n → n ≤ N → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace F χ s p q),
      ∃ v : BesovSpace F χ s p q, v.toDistr = compCLM F φ hφ hψ u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  set r : ℝ := 2 ^ (|s| - N)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  obtain ⟨K, hK, hblock⟩ := exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le (F := F) χ N L
  refine ⟨K * ∑' d : ℤ, r ^ d.natAbs, by positivity, fun {φ} hφ hψ hφL hψL {p q} _ _ u ↦ ?_⟩
  set c : ℕ → ℂ := fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)
  choose v hv hvn using fun j k ↦
    hblock hφ hψ hφL hψL j k u.toDistr (u.block k) (u.coe_block k).symm
  have hentry (j k : ℕ) :
      ‖c j • v j k‖ ≤ K * r ^ ((k : ℤ) - j).natAbs * ‖u.weightedBlocks k‖ := by
    have hexp : s * j + -(N * |(j : ℝ) - k|) ≤ (|s| - N) * |(j : ℝ) - k| + s * k := by
      have := (le_abs_self (s * (j - k))).trans_eq (abs_mul s ((j : ℝ) - k))
      nlinarith
    have hr : r ^ ((k : ℤ) - j).natAbs = (2 : ℝ) ^ ((|s| - N) * |(j : ℝ) - k|) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, Nat.cast_natAbs, Int.cast_abs,
        abs_sub_comm, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    rw [norm_smul, Complex.norm_of_nonneg (by positivity), u.norm_weightedBlocks_apply k, hr]
    calc (2 : ℝ) ^ (s * j) * ‖v j k‖
        ≤ (2 : ℝ) ^ (s * j) * (K * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖u.block k‖) := by
          gcongr; exact hvn j k
      _ = K * (2 : ℝ) ^ (s * j + -(N * |(j : ℝ) - k|)) * ‖u.block k‖ := by
          rw [Real.rpow_add two_pos]; ring
      _ ≤ K * (2 : ℝ) ^ ((|s| - N) * |(j : ℝ) - k| + s * k) * ‖u.block k‖ := by
          gcongr; exact one_le_two
      _ = _ := by rw [Real.rpow_add two_pos]; ring
  have hsum : Summable fun d : ℤ ↦ r ^ d.natAbs :=
    summable_int_iff_summable_nat_and_neg.2
      ⟨by simpa using summable_geometric_of_lt_one hr0 hr1,
        by simpa using summable_geometric_of_lt_one hr0 hr1⟩
  obtain ⟨W, hWj, hWn⟩ := lp.exists_hasSum_and_norm_le_of_summable u.weightedBlocks
    (fun _ ↦ by positivity) hsum hK (fun j k ↦ c j • v j k) hentry
  have hW (j : ℕ) : (W j : 𝓢'(E, F)) =
      c j • littlewoodPaleyBlock F χ j (compCLM F φ hφ hψ u.toDistr) := by
    have h₁ := ((Lp.toTemperedDistributionCLM F volume p).continuous.tendsto _).comp
      (hWj j).tendsto_sum_nat
    have h₂ := ((c j • (littlewoodPaleyBlock F χ j ∘L compCLM F φ hφ hψ)).continuous.tendsto _).comp
      (tendsto_sum_littlewoodPaleyBlock χ u.toDistr)
    refine tendsto_nhds_unique h₁ (h₂.congr fun n ↦ ?_)
    simp only [Function.comp_apply, map_sum, map_smul, smul_apply,
      ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply]
    simp_rw [← u.coe_block, hv]
  refine ⟨⟨compCLM F φ hφ hψ u.toDistr, W, hW⟩, rfl, ?_⟩
  rw [← BesovSpace.norm_weightedBlocks, ← u.norm_weightedBlocks]
  exact hWn.trans_eq (by ring)

end TauCeti

/-! ### Stability and invariance of `MemBesov` -/

namespace TemperedDistribution

open TauCeti

variable {χ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Diffeomorphism pullback preserves `MemBesov`.** If `u ∈ B^s_{p,q}`, `φ` and `φ⁻¹` have
temperate growth, `φ` has bounded derivatives of orders `1 ≤ n ≤ ⌊|s|⌋₊ + 1`, and `φ⁻¹` has
bounded derivatives of orders `1 ≤ n ≤ ⌊|s|⌋₊ + 2`, then `φ^* u ∈ B^s_{p,q}`. -/
theorem MemBesov.compCLM {u : 𝓢'(E, F)} (hu : u.MemBesov χ s p q) {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    (TemperedDistribution.compCLM F φ hφ hψ u).MemBesov χ s p q := by
  obtain ⟨L₁, hL₁⟩ := exists_forall_norm_iteratedFDeriv_le_of_pos hbdφ
  obtain ⟨L₂, hL₂⟩ := exists_forall_norm_iteratedFDeriv_le_of_pos hbdψ
  obtain ⟨C, -, hC⟩ := BesovSpace.exists_toDistr_eq_compCLM_and_norm_le (F := F) χ
    (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _) (max L₁ L₂)
  obtain ⟨v, hv, -⟩ := hC hφ hψ
    (fun n hn1 hn2 x ↦ (hL₁ n hn1 hn2 x).trans (le_max_left _ _))
    (fun n hn1 hn2 y ↦ (hL₂ n hn1 hn2 y).trans (le_max_right _ _)) hu.toBesovSpace
  rw [← hu.toDistr_toBesovSpace, ← hv]
  exact v.memBesov_toDistr

/-- **Diffeomorphism invariance of `MemBesov`.** When both `φ` and `φ⁻¹` have temperate growth and
bounded derivatives of positive orders `1 ≤ n ≤ ⌊|s|⌋₊ + 2`, a tempered distribution `u` lies in
`B^s_{p,q}` if and only if `φ^* u` does. -/
theorem memBesov_compCLM_iff {u : 𝓢'(E, F)} {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    (TemperedDistribution.compCLM F φ hφ hψ u).MemBesov χ s p q ↔ u.MemBesov χ s p q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compCLM hφ hψ (fun n hn1 hn2 ↦ hbdφ n hn1 (by omega)) hbdψ⟩
  simpa only [compCLM_symm_compCLM hφ hψ hφ] using
    h.compCLM hψ hφ (fun n hn1 hn2 ↦ hbdψ n hn1 (by omega)) hbdφ

end TemperedDistribution

/-! ### Continuous linear maps and equivalences on `BesovSpace` -/

namespace TauCeti.BesovSpace

open TemperedDistribution

variable {χ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (F χ s p q) in
/-- **Pullback of Besov spaces** along a bijection `φ : E ≃ E` such that `φ` and `φ⁻¹` have
temperate growth and bounded positive-order derivatives (`1 ≤ n ≤ ⌊|s|⌋₊ + 1` for `φ` and
`1 ≤ n ≤ ⌊|s|⌋₊ + 2` for `φ⁻¹`), as a bounded linear operator on `B^s_{p,q}`. Its operator norm
is bounded independently of `p` and `q` (`TauCeti.BesovSpace.exists_norm_compCLM_le`). -/
def compCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memBesov_toDistr.compCLM hφ hψ hbdφ hbdψ).toBesovSpace
      map_add' _ _ := ext (by simp)
      map_smul' _ _ := ext (by simp) } <| by
    obtain ⟨L₁, hL₁⟩ := exists_forall_norm_iteratedFDeriv_le_of_pos hbdφ
    obtain ⟨L₂, hL₂⟩ := exists_forall_norm_iteratedFDeriv_le_of_pos hbdψ
    obtain ⟨C, -, hC⟩ := exists_toDistr_eq_compCLM_and_norm_le (F := F) χ
      (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _) (max L₁ L₂)
    refine ⟨C, fun u ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := hC hφ hψ
      (fun n hn1 hn2 x ↦ (hL₁ n hn1 hn2 x).trans (le_max_left _ _))
      (fun n hn1 hn2 y ↦ (hL₂ n hn1 hn2 y).trans (le_max_right _ _)) (p := p) (q := q) u
    have : (u.memBesov_toDistr.compCLM hφ hψ hbdφ hbdψ).toBesovSpace = v := ext (by simp [hv])
    simpa [this] using hvn

@[simp]
theorem toDistr_compCLM {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    (compCLM F χ s p q φ hφ hψ hbdφ hbdψ u).toDistr =
      TemperedDistribution.compCLM F φ hφ hψ u.toDistr := by
  simp [compCLM]

/-- **Uniform operator norm bound for Besov pullback.** Let `N` be a natural number with `|s| < N`,
and let `L` be a real number. There is `C ≥ 0`, depending only on `χ`, `s`, `N` and `L`, such that
whenever `φ` has derivatives of order `1 ≤ n ≤ N` bounded by `L` and `φ⁻¹` has derivatives of
order `1 ≤ n ≤ N + 1` bounded by `L`, the operator norm of `BesovSpace.compCLM` on `B^s_{p,q}` is
at most `C` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compCLM_le (χ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
      (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
      (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ N → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ‖compCLM F χ s p q φ hφ hψ hbdφ hbdψ‖ ≤ C := by
  obtain ⟨C, hC, hcomp⟩ := exists_toDistr_eq_compCLM_and_norm_le (F := F) χ hN L
  refine ⟨C, hC, fun {p q} _ _ φ hφ hψ hbdφ hbdψ hφL hψL ↦ ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun u ↦ ?_
  obtain ⟨v, hv, hvn⟩ := hcomp hφ hψ hφL hψL (p := p) (q := q) u
  have : compCLM F χ s p q φ hφ hψ hbdφ hbdψ u = v := ext (by simp [hv])
  rwa [this]

/-- Pullback along the identity equivalence is the identity on `B^s_{p,q}`. -/
@[simp]
theorem compCLM_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth)
    (hbd₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm y‖ ≤ C) :
    compCLM F χ s p q (Equiv.refl E) h₁ h₂ hbd₁ hbd₂ = ContinuousLinearMap.id ℂ _ := by
  ext u : 2
  simp

/-- **Contravariant functoriality of Besov pullback**: `(ψ ∘ φ)^* = φ^* ∘ ψ^*`. -/
theorem compCLM_trans {φ ψ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hφs : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdφs : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hψ : (ψ : E → E).HasTemperateGrowth) (hψs : (ψ.symm : E → E).HasTemperateGrowth)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ C)
    (hbdψs : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n ψ.symm y‖ ≤ C)
    (h₁ : (φ.trans ψ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans ψ).symm : E → E).HasTemperateGrowth)
    (hbd₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (φ.trans ψ) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (φ.trans ψ).symm y‖ ≤ C) :
    compCLM F χ s p q (φ.trans ψ) h₁ h₂ hbd₁ hbd₂ =
      compCLM F χ s p q φ hφ hφs hbdφ hbdφs ∘L compCLM F χ s p q ψ hψ hψs hbdψ hbdψs := by
  ext u : 2
  simp [TemperedDistribution.compCLM_trans hφ hφs hψ hψs h₁ h₂]

/-- Pulling back along `φ` and then along `φ⁻¹` gives back the Besov element. -/
@[simp]
theorem compCLM_symm_compCLM {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hbdψ' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hbdφ' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ.symm.symm x‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    compCLM F χ s p q φ.symm hψ hφ' hbdψ' hbdφ' (compCLM F χ s p q φ hφ hψ hbdφ hbdψ u) = u := by
  ext1
  simp

/-- Pulling back along `φ⁻¹` and then along `φ` gives back the Besov element. -/
@[simp]
theorem compCLM_compCLM_symm {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hbdψ' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hbdφ' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ.symm.symm x‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    compCLM F χ s p q φ hφ hψ hbdφ hbdψ (compCLM F χ s p q φ.symm hψ hφ' hbdψ' hbdφ' u) = u := by
  ext1
  simp

/-- Pulling back `g • u` along `φ` on `B^s_{p,q}` equals `(g ∘ φ) • φ^* u`. -/
theorem compCLM_smulLeftCLM {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbdg : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    (hbdgφ : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (g ∘ φ) x‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    compCLM F χ s p q φ hφ hψ hbdφ hbdψ (smulLeftCLM F χ s p q g hg hbdg u) =
      smulLeftCLM F χ s p q (g ∘ φ) (hg.comp hφ) hbdgφ
        (compCLM F χ s p q φ hφ hψ hbdφ hbdψ u) := by
  ext1
  simp [TemperedDistribution.compCLM_smulLeftCLM hφ hψ hg]

variable (F χ s p q) in
/-- **Diffeomorphism invariance of Besov spaces.** Let `φ : E ≃ E` be a bijection such that `φ`
and `φ⁻¹` have temperate growth and bounded derivatives of positive orders `1 ≤ n ≤ ⌊|s|⌋₊ + 2`.
Then pullback along `φ` is a bounded linear equivalence `B^s_{p,q}(E; F) ≃L[ℂ] B^s_{p,q}(E; F)`,
with inverse the pullback along `φ⁻¹`. -/
def compEquiv (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    BesovSpace F χ s p q ≃L[ℂ] BesovSpace F χ s p q :=
  ContinuousLinearEquiv.equivOfInverse
    (compCLM F χ s p q φ hφ hψ (fun n hn1 hn2 ↦ hbdφ n hn1 (by omega)) hbdψ)
    (compCLM F χ s p q φ.symm hψ hφ (fun n hn1 hn2 ↦ hbdψ n hn1 (by omega)) hbdφ)
    (compCLM_symm_compCLM hφ hψ hφ _ hbdψ _ hbdφ)
    (compCLM_compCLM_symm hφ hψ hφ _ hbdψ _ hbdφ)

theorem compEquiv_apply {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    compEquiv F χ s p q φ hφ hψ hbdφ hbdψ u =
      compCLM F χ s p q φ hφ hψ (fun n hn1 hn2 ↦ hbdφ n hn1 (by omega)) hbdψ u :=
  (rfl)

@[simp]
theorem compEquiv_symm {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    (compEquiv F χ s p q φ hφ hψ hbdφ hbdψ).symm =
      compEquiv F χ s p q φ.symm hψ hφ hbdψ hbdφ := by
  ext u
  rfl

@[simp]
theorem toDistr_compEquiv {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    (compEquiv F χ s p q φ hφ hψ hbdφ hbdψ u).toDistr =
      TemperedDistribution.compCLM F φ hφ hψ u.toDistr := by
  simp [compEquiv_apply]

@[simp]
theorem compEquiv_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth)
    (hbd₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm y‖ ≤ C) :
    compEquiv F χ s p q (Equiv.refl E) h₁ h₂ hbd₁ hbd₂ = ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  simp

/-- **Contravariant functoriality of `compEquiv`**: `(ψ ∘ φ)^* = φ^* ∘ ψ^*`. -/
theorem compEquiv_trans {φ ψ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hφs : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdφs : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hψ : (ψ : E → E).HasTemperateGrowth) (hψs : (ψ.symm : E → E).HasTemperateGrowth)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ C)
    (hbdψs : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n ψ.symm y‖ ≤ C)
    (h₁ : (φ.trans ψ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans ψ).symm : E → E).HasTemperateGrowth)
    (hbd₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (φ.trans ψ) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (φ.trans ψ).symm y‖ ≤ C) :
    compEquiv F χ s p q (φ.trans ψ) h₁ h₂ hbd₁ hbd₂ =
      (compEquiv F χ s p q ψ hψ hψs hbdψ hbdψs).trans
        (compEquiv F χ s p q φ hφ hφs hbdφ hbdφs) := by
  ext u : 3
  simp [TemperedDistribution.compCLM_trans hφ hφs hψ hψs h₁ h₂]

/-- **Uniform operator norm bounds for `compEquiv` and its inverse.** Let `N` be a natural number
with `|s| < N`, and let `L` be a real number. There is `C ≥ 0`, depending only on `χ`, `s`, `N`
and `L`, such that whenever both `φ` and `φ⁻¹` have derivatives of order `1 ≤ n ≤ N + 1` bounded by
`L`, both `compEquiv` and its inverse have operator norm at most `C` on `B^s_{p,q}` for all
`1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compEquiv_le (χ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
      (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
      (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ‖(compEquiv F χ s p q φ hφ hψ hbdφ hbdψ :
        BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C ∧
      ‖((compEquiv F χ s p q φ hφ hψ hbdφ hbdψ).symm :
        BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_compCLM_le (F := F) (s := s) χ hN L
  refine ⟨C, hC, fun {p q} _ _ φ hφ hψ hbdφ hbdψ hφL hψL ↦ ⟨?_, ?_⟩⟩
  · exact hnorm hφ hψ (fun n hn1 hn2 ↦ hbdφ n hn1 (by omega)) hbdψ
      (fun n hn1 hn2 ↦ hφL n hn1 (by omega)) hψL
  · rw [compEquiv_symm]
    exact hnorm hψ hφ (fun n hn1 hn2 ↦ hbdψ n hn1 (by omega)) hbdφ
      (fun n hn1 hn2 ↦ hψL n hn1 (by omega)) hφL

variable (F χ s p q) in
/-- **Pullback isomorphism for smooth diffeomorphisms with bounded derivatives of every positive
order.** If `φ : E ≃ E` and `φ⁻¹` are smooth with uniformly bounded derivatives of every positive
order, then pullback along `φ` is a bounded linear equivalence of `B^s_{p,q}(E; F)`, inverse to
pullback along `φ⁻¹` and agreeing with distributional pullback. -/
def compEquivOfContDiff (φ : E ≃ E) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ φ.symm)
    (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    BesovSpace F χ s p q ≃L[ℂ] BesovSpace F χ s p q :=
  compEquiv F χ s p q φ
    (.of_norm_iteratedFDeriv_le_of_pos hφ hbdφ)
    (.of_norm_iteratedFDeriv_le_of_pos hψ hbdψ)
    (fun n hn _ ↦ hbdφ n hn) (fun n hn _ ↦ hbdψ n hn)

@[simp]
theorem toDistr_compEquivOfContDiff {φ : E ≃ E} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ φ.symm)
    (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    (compEquivOfContDiff F χ s p q φ hφ hψ hbdφ hbdψ u).toDistr =
      TemperedDistribution.compCLM F φ
        (.of_norm_iteratedFDeriv_le_of_pos hφ hbdφ)
        (.of_norm_iteratedFDeriv_le_of_pos hψ hbdψ) u.toDistr := by
  simp [compEquivOfContDiff]

@[simp]
theorem compEquivOfContDiff_symm {φ : E ≃ E} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ φ.symm)
    (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    (compEquivOfContDiff F χ s p q φ hφ hψ hbdφ hbdψ).symm =
      compEquivOfContDiff F χ s p q φ.symm hψ hφ hbdψ hbdφ := by
  ext u
  rfl

@[simp]
theorem compEquivOfContDiff_refl (h₁ : ContDiff ℝ ∞ (Equiv.refl E))
    (h₂ : ContDiff ℝ ∞ (Equiv.refl E).symm)
    (hbd₁ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm y‖ ≤ C) :
    compEquivOfContDiff F χ s p q (Equiv.refl E) h₁ h₂ hbd₁ hbd₂ =
      ContinuousLinearEquiv.refl ℂ _ :=
  compEquiv_refl _ _ _ _

theorem compEquivOfContDiff_trans {φ ψ : E ≃ E}
    (hφ : ContDiff ℝ ∞ φ) (hφs : ContDiff ℝ ∞ φ.symm)
    (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdφs : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hψ : ContDiff ℝ ∞ ψ) (hψs : ContDiff ℝ ∞ ψ.symm)
    (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ C)
    (hbdψs : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n ψ.symm y‖ ≤ C)
    (h₁ : ContDiff ℝ ∞ (φ.trans ψ)) (h₂ : ContDiff ℝ ∞ (φ.trans ψ).symm)
    (hbd₁ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (φ.trans ψ) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (φ.trans ψ).symm y‖ ≤ C) :
    compEquivOfContDiff F χ s p q (φ.trans ψ) h₁ h₂ hbd₁ hbd₂ =
      (compEquivOfContDiff F χ s p q ψ hψ hψs hbdψ hbdψs).trans
        (compEquivOfContDiff F χ s p q φ hφ hφs hbdφ hbdφs) :=
  compEquiv_trans _ _ _ _ _ _ _ _ _ _ _ _

/-- **Uniform operator norm bounds for `compEquivOfContDiff` and its inverse.** Let `N` be a
natural number with `|s| < N`, and let `L` be a real number. There is `C ≥ 0`, depending only on
`χ`, `s`, `N` and `L` (and **not** on `p` or `q`), such that whenever both `φ` and `φ⁻¹` have
derivatives of order `1 ≤ n ≤ N + 1` bounded by `L`, both `compEquivOfContDiff` and its inverse
have operator norm at most `C` on `B^s_{p,q}` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compEquivOfContDiff_le (χ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N)
    (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {φ : E ≃ E}
      (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ φ.symm)
      (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
      (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ‖(compEquivOfContDiff F χ s p q φ hφ hψ hbdφ hbdψ :
        BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C ∧
      ‖((compEquivOfContDiff F χ s p q φ hφ hψ hbdφ hbdψ).symm :
        BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_compEquiv_le (F := F) (s := s) χ hN L
  exact ⟨C, hC, fun hφ hψ hbdφ hbdψ hφL hψL ↦ hnorm _ _ _ _ hφL hψL⟩

/-! ### Translations and continuous linear automorphisms -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem compCLM_congr_equiv {φ₁ φ₂ : E ≃ E} (h : φ₁ = φ₂)
    (hφ₁ : (φ₁ : E → E).HasTemperateGrowth) (hψ₁ : (φ₁.symm : E → E).HasTemperateGrowth)
    (hφ₂ : (φ₂ : E → E).HasTemperateGrowth) (hψ₂ : (φ₂.symm : E → E).HasTemperateGrowth) :
    TemperedDistribution.compCLM F φ₁ hφ₁ hψ₁ = TemperedDistribution.compCLM F φ₂ hφ₂ hψ₂ := by
  subst h
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_iteratedFDeriv_addRight_le (a : E) {n : ℕ} (hn : 1 ≤ n) (x : E) :
    ‖iteratedFDeriv ℝ n (Equiv.addRight a) x‖ ≤ 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hfn : (Equiv.addRight a : E → E) = fun y ↦ ContinuousLinearMap.id ℝ E y + a := rfl
  rw [hfn, iteratedFDeriv_succ_add_const]
  exact ((ContinuousLinearMap.id ℝ E).norm_iteratedFDeriv_le_norm (by omega) x).trans
    ContinuousLinearMap.norm_id_le

variable (F χ s p q) in
/-- **Translation equivalence on Besov spaces.** Translating by `a ∈ E` (`u ↦ u(· + a)`) is a
bounded linear automorphism of `B^s_{p,q}(E; F)` whose operator norm is bounded uniformly in `a`,
`p`, and `q` (`TauCeti.BesovSpace.exists_norm_translateEquiv_le`). -/
def translateEquiv (a : E) : BesovSpace F χ s p q ≃L[ℂ] BesovSpace F χ s p q :=
  compEquiv F χ s p q (Equiv.addRight a)
    (by dsimp only [Equiv.coe_addRight]; fun_prop)
    (by dsimp only [Equiv.addRight_symm_apply]; fun_prop)
    (fun _ hn _ ↦ ⟨1, norm_iteratedFDeriv_addRight_le a hn⟩)
    (fun _ hn _ ↦ ⟨1, norm_iteratedFDeriv_addRight_le (-a) hn⟩)

@[simp]
theorem toDistr_translateEquiv (a : E) (u : BesovSpace F χ s p q) :
    (translateEquiv F χ s p q a u).toDistr =
      TemperedDistribution.compCLM F (Equiv.addRight a)
        (by dsimp only [Equiv.coe_addRight]; fun_prop)
        (by dsimp only [Equiv.addRight_symm_apply]; fun_prop) u.toDistr := by
  rw [translateEquiv, toDistr_compEquiv]

@[simp]
theorem translateEquiv_zero :
    translateEquiv F χ s p q (0 : E) = ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  have h := DFunLike.congr_fun (compCLM_congr_equiv (F := F)
    (φ₁ := Equiv.addRight (0 : E)) (φ₂ := Equiv.refl E) (by ext x; simp)
    (by dsimp only [Equiv.coe_addRight]; fun_prop)
    (by dsimp only [Equiv.addRight_symm_apply]; fun_prop) .id .id) u.toDistr
  exact (toDistr_translateEquiv 0 u).trans
    (h.trans (DFunLike.congr_fun (TemperedDistribution.compCLM_refl .id .id) u.toDistr))

@[simp]
theorem translateEquiv_symm (a : E) :
    (translateEquiv F χ s p q a).symm = translateEquiv F χ s p q (-a) := by
  ext u : 3
  rw [translateEquiv, compEquiv_symm, toDistr_compEquiv, toDistr_translateEquiv,
    compCLM_congr_equiv (Equiv.addRight_symm a)]

theorem translateEquiv_add (a b : E) :
    translateEquiv F χ s p q (a + b) =
      (translateEquiv F χ s p q b).trans (translateEquiv F χ s p q a) := by
  ext u : 3
  have hab : Equiv.addRight (a + b) = (Equiv.addRight a).trans (Equiv.addRight b) := by
    ext x; simp [add_assoc]
  have h₁ : ((Equiv.addRight a).trans (Equiv.addRight b) : E → E).HasTemperateGrowth := by
    change (fun x ↦ x + a + b).HasTemperateGrowth; fun_prop
  have h₂ : (((Equiv.addRight a).trans (Equiv.addRight b)).symm : E → E).HasTemperateGrowth := by
    change (fun x ↦ x + -b + -a).HasTemperateGrowth; fun_prop
  rw [ContinuousLinearEquiv.trans_apply, toDistr_translateEquiv, toDistr_translateEquiv,
    toDistr_translateEquiv, compCLM_congr_equiv hab _ _ h₁ h₂,
    TemperedDistribution.compCLM_trans, ContinuousLinearMap.comp_apply]

/-- **Uniform translation invariance of Besov norms.** For every `χ` and `s`, there is `C ≥ 0`
such that `‖translateEquiv F χ s p q a‖ ≤ C` for all `a ∈ E` and all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_translateEquiv_le (χ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (a : E),
      ‖(translateEquiv F χ s p q a : BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_compEquiv_le (F := F) (s := s) χ
    (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _) 1
  exact ⟨C, hC, fun {p q} _ _ a ↦ (hnorm _ _ _ _
    (fun _ hn _ x ↦ norm_iteratedFDeriv_addRight_le a hn x)
    (fun _ hn _ y ↦ norm_iteratedFDeriv_addRight_le (-a) hn y)).1⟩

variable (F χ s p q) in
/-- **Pullback along a continuous linear equivalence** `e : E ≃L[ℝ] E` on `B^s_{p,q}(E; F)`. -/
def compContinuousLinearEquiv (e : E ≃L[ℝ] E) :
    BesovSpace F χ s p q ≃L[ℂ] BesovSpace F χ s p q :=
  compEquiv F χ s p q e.toEquiv
    e.hasTemperateGrowth
    e.symm.hasTemperateGrowth
    (fun _ hn _ ↦ ⟨‖(e : E →L[ℝ] E)‖, (e : E →L[ℝ] E).norm_iteratedFDeriv_le_norm hn⟩)
    (fun _ hn _ ↦ ⟨‖(e.symm : E →L[ℝ] E)‖, (e.symm : E →L[ℝ] E).norm_iteratedFDeriv_le_norm hn⟩)

@[simp]
theorem toDistr_compContinuousLinearEquiv (e : E ≃L[ℝ] E) (u : BesovSpace F χ s p q) :
    (compContinuousLinearEquiv F χ s p q e u).toDistr =
      TemperedDistribution.compCLM F e.toEquiv
        e.hasTemperateGrowth e.symm.hasTemperateGrowth u.toDistr :=
  toDistr_compEquiv (φ := e.toEquiv) e.hasTemperateGrowth e.symm.hasTemperateGrowth _ _ u

@[simp]
theorem compContinuousLinearEquiv_symm (e : E ≃L[ℝ] E) :
    (compContinuousLinearEquiv F χ s p q e).symm =
      compContinuousLinearEquiv F χ s p q e.symm := by
  ext u
  rfl

@[simp]
theorem compContinuousLinearEquiv_refl :
    compContinuousLinearEquiv F χ s p q (ContinuousLinearEquiv.refl ℝ E) =
      ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  have h := DFunLike.congr_fun (compCLM_congr_equiv (F := F)
    (φ₁ := (ContinuousLinearEquiv.refl ℝ E).toEquiv) (φ₂ := Equiv.refl E) rfl
    (ContinuousLinearEquiv.refl ℝ E).hasTemperateGrowth
    (ContinuousLinearEquiv.refl ℝ E).symm.hasTemperateGrowth .id .id) u.toDistr
  exact (toDistr_compContinuousLinearEquiv _ u).trans
    (h.trans (DFunLike.congr_fun (TemperedDistribution.compCLM_refl .id .id) u.toDistr))

theorem compContinuousLinearEquiv_trans (e₁ e₂ : E ≃L[ℝ] E) :
    compContinuousLinearEquiv F χ s p q (e₁.trans e₂) =
      (compContinuousLinearEquiv F χ s p q e₂).trans
        (compContinuousLinearEquiv F χ s p q e₁) := by
  ext u : 3
  rw [ContinuousLinearEquiv.trans_apply, toDistr_compContinuousLinearEquiv,
    toDistr_compContinuousLinearEquiv, toDistr_compContinuousLinearEquiv]
  exact DFunLike.congr_fun (TemperedDistribution.compCLM_trans
    (φ := e₁.toEquiv) (χ := e₂.toEquiv)
    e₁.hasTemperateGrowth e₁.symm.hasTemperateGrowth
    e₂.hasTemperateGrowth e₂.symm.hasTemperateGrowth
    (e₁.trans e₂).hasTemperateGrowth (e₁.trans e₂).symm.hasTemperateGrowth) u.toDistr

end TauCeti.BesovSpace
