/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Off-diagonal decay of Littlewood–Paley blocks under diffeomorphism pullback

Let `E` be a finite-dimensional real inner product space, `F` a complete complex normed space, and
`χ : ContDiffBump (0 : E)` a Littlewood–Paley bump function. Let `φ : E ≃ E` be a bijection such
that `φ` and `φ⁻¹` have temperate growth, the iterated derivatives of `φ` of positive orders
`1 ≤ n ≤ M` are bounded by `L`, and those of `φ⁻¹` of orders `1 ≤ n ≤ M + 1` are bounded by `L`.

For every `1 ≤ p ≤ ∞`, if the `k`-th inhomogeneous Littlewood–Paley block `Δₖ u` of a tempered
distribution `u` is an `Lᵖ` function `f`, then for every `j` the `j`-th block `Δⱼ (φ^* f)` of its
pullback along `φ` (`TemperedDistribution.compCLM`) is an `Lᵖ` function satisfying the off-diagonal
decay estimate (`TauCeti.exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le`)

`‖Δⱼ (φ^* Δₖ u)‖_p ≤ K 2^{-M |j - k|} ‖Δₖ u‖_p`,

where `K ≥ 0` depends only on `χ`, `M`, and `L` — neither on `p` nor on `‖φ 0‖`.

## Mathematical proof

We inductively track twisted pullbacks `g • φ^* f` for smooth multipliers `g` with bounded
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

## Main declarations

* `TauCeti.exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le`: off-diagonal decay
  `‖Δⱼ (φ^* Δₖ u)‖_p ≤ K 2^{-M |j - k|} ‖Δₖ u‖_p` uniform in `1 ≤ p ≤ ∞`.

## References

* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, §4.3.
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

end TauCeti
