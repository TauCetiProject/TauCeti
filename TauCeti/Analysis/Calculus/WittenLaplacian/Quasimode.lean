/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.WittenLaplacian.Localization
public import TauCeti.Analysis.Calculus.WittenLaplacian.Quadratic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Quasimodes of the Witten Laplacian at the critical points

Witten's analytic proof of the Morse inequalities compares, for large `t`, the number of
low-lying eigenvalues of the Witten Laplacian `Δ_t` (`TauCeti.euclideanWittenLaplacian`) in each
degree with the number of critical points of that Morse index. One half of this comparison is the
gap in degrees that are no Morse index (`TauCeti.Analysis.Calculus.WittenLaplacian.Gap`). This
file proves the other half: in degree `m`, the quadratic form of `Δ_t` is small on a space of
test forms whose dimension is the number of critical points of index `m`.

The test forms are the ground states of the harmonic-oscillator models, cut off near their
critical points. Suppose that near `p` the function `f` is the quadratic model
`y ↦ b + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` with every `aᵢ ≠ 0`. The translated Gaussian ground state
`Ψ_t(x) = Ψ_{0,s₀}(x - p) = π^{-n/4} e^{-t ∑ᵢ |aᵢ| (xᵢ - pᵢ)² / 2} dx^{s₀}`
(`TauCeti.diagonalQuadraticWittenEigenform`, `s₀ = {i | aᵢ < 0}`) is annihilated by `Δ_t` of the
model (`TauCeti.euclideanWittenLaplacian_diagonalQuadraticWittenEigenform`). For a cutoff `θ`
equal to `1` on the ball of radius `ρ` around `p` and supported where `f` is the model, the
Leibniz rule `TauCeti.euclideanWittenLaplacian_smul_apply` gives at every point

`⟨Δ_t (θ Ψ_t), θ Ψ_t⟩ = θ (2 t ∑ᵢ |aᵢ| (xᵢ - pᵢ) ∂ᵢθ - ∑ᵢ ∂ᵢ²θ) |Ψ_t|²`

(`TauCeti.sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_mul`), which
vanishes on the ball of radius `ρ`, where `θ` is constant. Outside it the squared Gaussian is at
most `e^{-t c ρ²}` times its value at `p`, with `c = minᵢ |aᵢ|`, while on a small ball around `p`
it is at least `e^{-t c ρ² / 2}` times that value. So the ratio of the quadratic form to the
squared norm is bounded by a multiple of `(1 + t) e^{-t c ρ² / 2}`, and for every `ε > 0` it is at
most `ε` for all large `t`
(`TauCeti.exists_forall_integral_sum_euclideanWittenLaplacian_smul_mul_le`): the cut-off ground
state is a quasimode.

The quasimodes at different critical points have disjoint supports, so `Δ_t`, a local operator,
does not mix them, and they span a space on which the quadratic form is at most `ε` times the
squared norm, for any `ε > 0` and all large `t`
(`TauCeti.exists_forall_exists_finrank_eq_forall_integral_sum_euclideanWittenLaplacian_mul_le`).
Its dimension is the number of critical points of index `m`. Combined with the gap in the other
degrees and a gap above the ground state in the degree of the index, this is the min-max statement
that the low-lying spectrum of `Δ_t` in degree `m` has exactly as many eigenvalues as there are
critical points of index `m`. As in `TauCeti.Analysis.Calculus.WittenLaplacian.Gap`, these are
statements about the quadratic form on compactly supported smooth forms, not about a self-adjoint
realization of `Δ_t`.

## Main results

* `TauCeti.sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_mul`: the pointwise
  energy of a cut-off ground state.
* `TauCeti.exists_forall_integral_sum_euclideanWittenLaplacian_smul_mul_le`: a cut-off ground
  state has energy at most `ε` times its squared norm for large `t`.
* `TauCeti.exists_forall_exists_finrank_eq_forall_integral_sum_euclideanWittenLaplacian_mul_le`:
  in degree `m`, the quadratic form of `Δ_t` is at most `ε` times the squared norm on a space of
  smooth compactly supported forms whose dimension is the number of critical points of index `m`.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Texts and
  Monographs in Physics, Springer (1987), Chapter 11 (the upper bound on the low-lying
  eigenvalues by cut-off harmonic-oscillator ground states).
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-! ### The translated ground state -/

section GroundState

variable {a p : ι → ℝ} {t : ℝ}

/-- The Gaussian factor of the translated ground state, without its normalizing constant. -/
private def gauss (a p : ι → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2) / 2)

/-- The normalizing constant `π^{n/4}` of the Hermite ground state. -/
private def gaussConst (ι : Type*) [Fintype ι] : ℝ :=
  √(√Real.pi) ^ Fintype.card ι

private theorem gaussConst_pos : 0 < gaussConst ι := by
  unfold gaussConst
  positivity

private theorem gauss_pos (a p : ι → ℝ) (t : ℝ) (x : ι → ℝ) : 0 < gauss a p t x :=
  Real.exp_pos _

private theorem gauss_eq (a p : ι → ℝ) (t : ℝ) :
    gauss a p t = fun x ↦ Real.exp (-t * diagonalQuadratic (fun i ↦ |a i|) (x - p)) := by
  funext x
  simp only [gauss, diagonalQuadratic_apply, Pi.sub_apply, ← Finset.sum_div]
  ring_nf

private theorem hasFDerivAt_gauss (a p : ι → ℝ) (t : ℝ) (x : ι → ℝ) :
    HasFDerivAt (gauss a p t)
      (gauss a p t x • (-t) • ((∑ i, (|a i| * (x - p) i) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (ContinuousLinearMap.id ℝ (ι → ℝ)))) x := by
  rw [gauss_eq]
  have h := (((hasFDerivAt_diagonalQuadratic (fun i ↦ |a i|) (x - p)).comp x
    ((hasFDerivAt_id x).sub_const p)).const_mul (-t)).exp
  exact h

/-- The partial derivatives of the Gaussian: `∂ᵢ gauss = -t |aᵢ| (xᵢ - pᵢ) gauss`. -/
private theorem fderiv_gauss_apply_single [DecidableEq ι] (a p : ι → ℝ) (t : ℝ) (x : ι → ℝ)
    (i : ι) :
    fderiv ℝ (gauss a p t) x (Pi.single i 1) =
      -(t * (|a i| * (x i - p i))) * gauss a p t x := by
  rw [(hasFDerivAt_gauss a p t x).fderiv]
  simp [Pi.single_apply]
  ring

private theorem contDiff_gauss (a p : ι → ℝ) (t : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (gauss a p t) := by
  rw [gauss_eq]
  exact Real.contDiff_exp.comp
    (((contDiff_diagonalQuadratic _).comp (contDiff_id.sub contDiff_const)).const_smul (-t))

variable [LinearOrder ι]

/-- The translated ground state is the Gaussian `gauss` times `dx^{s}`, up to normalization. -/
private theorem wittenGroundState_eq (a p : ι → ℝ) (ht : 0 ≤ t) (s : Finset ι) :
    (fun x ↦ diagonalQuadraticWittenEigenform a t 0 s (x - p)) =
      fun x ↦ ((gaussConst ι)⁻¹ * gauss a p t x) • Pi.single s (1 : ℝ) := by
  funext x
  rw [diagonalQuadraticWittenEigenform_zero_apply a ht, div_eq_inv_mul]
  rfl

/-- The model `y ↦ b + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` annihilates its translated ground state. -/
private theorem euclideanWittenLaplacian_wittenGroundState (a p : ι → ℝ) (b : ℝ) (ht : 0 ≤ t) :
    euclideanWittenLaplacian (fun y ↦ b + diagonalQuadratic a (y - p)) t
      (fun x ↦ diagonalQuadraticWittenEigenform a t 0 (Finset.univ.filter fun i ↦ a i < 0)
        (x - p)) = 0 := by
  rw [euclideanWittenLaplacian_const_add]
  have h := euclideanWittenLaplacian_comp_add_right (diagonalQuadratic a) t
    (diagonalQuadraticWittenEigenform a t 0 (Finset.univ.filter fun i ↦ a i < 0)) (-p)
  simp only [← sub_eq_add_neg] at h
  rw [h, euclideanWittenLaplacian_diagonalQuadraticWittenEigenform a ht,
    diagonalQuadraticWittenEigenvalue_zero_filter_neg, zero_smul]
  rfl

end GroundState

/-! ### The energy of a cut-off ground state -/

variable [LinearOrder ι]

/-- **The pointwise energy of a cut-off ground state.** Let `Ψ_t(x) = Ψ_{0,s₀}(x - p)` be the
Gaussian ground state of the harmonic-oscillator model at `p`, with `s₀ = {i | aᵢ < 0}`, and let
`θ` be a `C²` function such that, near every point where `θ` does not vanish, `f` is the model
`y ↦ b + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2`. For `t ≥ 0`, at every point

`⟨Δ_t (θ Ψ_t), θ Ψ_t⟩ = θ (2 t ∑ᵢ |aᵢ| (xᵢ - pᵢ) ∂ᵢθ - ∑ᵢ ∂ᵢ²θ) |Ψ_t|²`.

Only the derivatives of `θ` contribute, since `Δ_t Ψ_t = 0` where `f` is the model. -/
theorem sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_mul {f θ : (ι → ℝ) → ℝ}
    {a p : ι → ℝ} {b t : ℝ} (ht : 0 ≤ t) (hθ : ContDiff ℝ 2 θ)
    (hf : ∀ x, θ x ≠ 0 → f =ᶠ[𝓝 x] fun y ↦ b + diagonalQuadratic a (y - p)) (x : ι → ℝ) :
    ∑ s, euclideanWittenLaplacian f t (θ • fun y ↦ diagonalQuadraticWittenEigenform a t 0
        (Finset.univ.filter fun i ↦ a i < 0) (y - p)) x s *
      (θ • fun y ↦ diagonalQuadraticWittenEigenform a t 0
        (Finset.univ.filter fun i ↦ a i < 0) (y - p)) x s =
      θ x * (2 * t * ∑ i, |a i| * (x i - p i) * fderiv ℝ θ x (Pi.single i 1) -
        ∑ i, fderiv ℝ (fderiv ℝ θ) x (Pi.single i 1) (Pi.single i 1)) *
        ∑ s, diagonalQuadraticWittenEigenform a t 0
          (Finset.univ.filter fun i ↦ a i < 0) (x - p) s ^ 2 := by
  set s₀ : Finset ι := Finset.univ.filter fun i ↦ a i < 0
  set Ψ : (ι → ℝ) → Finset ι → ℝ := fun y ↦ diagonalQuadraticWittenEigenform a t 0 s₀ (y - p)
    with hΨ_def
  have hΨ : ContDiff ℝ 2 Ψ :=
    (contDiff_diagonalQuadraticWittenEigenform a t 0 s₀).comp (contDiff_id.sub contDiff_const)
  by_cases hx : θ x = 0
  · simp [hx]
  have hfx := hf x hx
  have hfC : ContDiffAt ℝ 2 f x :=
    ((contDiff_const.add ((contDiff_diagonalQuadratic a).comp
      (contDiff_id.sub contDiff_const))).contDiffAt).congr_of_eventuallyEq hfx
  have hΔΨ : euclideanWittenLaplacian f t Ψ x = 0 := by
    rw [(hfx.euclideanWittenLaplacian (EventuallyEq.refl _ Ψ) t).eq_of_nhds,
      euclideanWittenLaplacian_wittenGroundState a p b ht]
    rfl
  have hG := wittenGroundState_eq a p ht s₀
  set κ := gaussConst ι
  have hdΨ : ∀ v, fderiv ℝ Ψ x v =
      (κ⁻¹ * fderiv ℝ (gauss a p t) x v) • (Pi.single s₀ 1 : Finset ι → ℝ) := by
    intro v
    have h₁ := (((contDiff_gauss a p t (n := 1)).differentiable one_ne_zero x).hasFDerivAt.const_mul
      κ⁻¹).smul_const (Pi.single s₀ 1 : Finset ι → ℝ)
    rw [hΨ_def, hG, h₁.fderiv]
    simp
  have hΨx : Ψ x = (κ⁻¹ * gauss a p t x) • (Pi.single s₀ 1 : Finset ι → ℝ) := congrFun hG x
  have hsq : ∑ s, diagonalQuadraticWittenEigenform a t 0 s₀ (x - p) s ^ 2 =
      (κ⁻¹ * gauss a p t x) ^ 2 := by
    change ∑ s, Ψ x s ^ 2 = _
    simp [hΨx, Pi.single_apply]
  have hsum : ∑ i, fderiv ℝ θ x (Pi.single i 1) * κ⁻¹ * -(t * |a i| * (x i - p i)) *
      gauss a p t x =
      -(t * κ⁻¹ * gauss a p t x) * ∑ i, |a i| * (x i - p i) * fderiv ℝ θ x (Pi.single i 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [euclideanWittenLaplacian_smul_apply hfC hθ.contDiffAt hΨ.contDiffAt, hΔΨ, hsq]
  simp only [hdΨ, fderiv_gauss_apply_single, hΨx, Pi.smul_apply', Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply, ← mul_assoc]
  rw [hsum]
  ring

/-! ### The Gaussian away from and near its centre -/

section Gauss

omit [LinearOrder ι]

/-- The squared Gaussian is `e^{-t ∑ᵢ |aᵢ| (xᵢ - pᵢ)²}`. -/
private theorem gauss_sq (a p : ι → ℝ) (t : ℝ) (x : ι → ℝ) :
    gauss a p t x ^ 2 = Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2)) := by
  rw [gauss, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Outside the ball of radius `ρ` around `p`, the quadratic form `∑ᵢ |aᵢ| (xᵢ - pᵢ)²` is at
least `c ρ²` when every `|aᵢ| ≥ c`. -/
private theorem mul_sq_le_sum_of_notMem_ball {a p x : ι → ℝ} {c ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ i, c ≤ |a i|) (hx : x ∉ ball p ρ) :
    c * ρ ^ 2 ≤ ∑ i, |a i| * (x i - p i) ^ 2 := by
  rw [mem_ball, dist_pi_lt_iff hρ] at hx
  simp only [not_forall, not_lt] at hx
  obtain ⟨i, hi⟩ := hx
  rw [Real.dist_eq] at hi
  have hρi : ρ ^ 2 ≤ (x i - p i) ^ 2 := by
    rw [← sq_abs (x i - p i)]
    exact pow_le_pow_left₀ hρ.le hi 2
  calc c * ρ ^ 2 ≤ |a i| * (x i - p i) ^ 2 :=
        mul_le_mul (hc i) hρi (sq_nonneg _) (abs_nonneg _)
    _ ≤ ∑ j, |a j| * (x j - p j) ^ 2 :=
        Finset.single_le_sum (f := fun j ↦ |a j| * (x j - p j) ^ 2)
          (fun j _ ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _))
          (Finset.mem_univ i)

/-- On the ball of radius `δ` around `p`, the quadratic form `∑ᵢ |aᵢ| (xᵢ - pᵢ)²` is at most
`(∑ᵢ |aᵢ|) δ²`. -/
private theorem sum_le_mul_sq_of_mem_ball {a p x : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hx : x ∈ ball p δ) :
    ∑ i, |a i| * (x i - p i) ^ 2 ≤ (∑ i, |a i|) * δ ^ 2 := by
  rw [mem_ball, dist_pi_lt_iff hδ] at hx
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hi := hx i
  rw [Real.dist_eq] at hi
  rw [← sq_abs (x i - p i)]
  exact pow_le_pow_left₀ (abs_nonneg _) hi.le 2

/-- `(t A + B) e^{-γ t}` tends to `0` as `t → ∞`, for `γ > 0`. -/
private theorem tendsto_mul_add_mul_exp_neg (A B : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun t ↦ (t * A + B) * Real.exp (-(γ * t))) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 γ hγ).mul_const A
  have h₀ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 γ hγ).mul_const B
  simpa [Real.rpow_one, Real.rpow_zero, add_mul, mul_right_comm _ A, mul_comm _ B] using
    h₁.add h₀

omit [Fintype ι] in
/-- The coefficients of a nondegenerate model are bounded away from zero. -/
private theorem exists_pos_le_abs [Finite ι] {a : ι → ℝ} (ha : ∀ i, a i ≠ 0) :
    ∃ c, 0 < c ∧ ∀ i, c ≤ |a i| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i ↦ isEmptyElim i⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i ↦ |a i|
  exact ⟨|a i₀|, abs_pos.2 (ha i₀), hi₀⟩

end Gauss

/-- A radius `δ ≤ ρ` small enough that `S δ² ≤ c ρ² / 2`. -/
private theorem exists_radius {c S ρ : ℝ} (hc : 0 < c) (hS : 0 ≤ S) (hρ : 0 < ρ) :
    ∃ δ, 0 < δ ∧ δ ≤ ρ ∧ S * δ ^ 2 ≤ c * ρ ^ 2 / 2 := by
  set δ := min ρ (c * ρ / (2 * (S + c)))
  have hδ : 0 < δ := lt_min hρ (by positivity)
  have hδρ : δ ≤ ρ := min_le_left _ _
  have h₂ : S * δ ≤ c * ρ / 2 := by
    calc S * δ ≤ S * (c * ρ / (2 * (S + c))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hS
      _ ≤ c * ρ / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
        nlinarith [mul_pos hc hρ, mul_nonneg hS (mul_pos hc hρ).le]
  refine ⟨δ, hδ, hδρ, ?_⟩
  calc S * δ ^ 2 = S * δ * δ := by ring
    _ ≤ c * ρ / 2 * ρ := mul_le_mul h₂ hδρ hδ.le (by positivity)
    _ = c * ρ ^ 2 / 2 := by ring

omit [LinearOrder ι] in
/-- **The energy bound away from the centre.** If the continuous compactly supported weights `w₁`
and `w₀` vanish on the ball of radius `ρ` around `p`, then integrated against the squared
Gaussian `K e^{-t ∑ᵢ |aᵢ| (xᵢ - pᵢ)²}` the weight `t w₁ - w₀` is at most
`(t ∫ |w₁| + ∫ |w₀|) K e^{-t c ρ²}`, where every `|aᵢ| ≥ c`. -/
private theorem integral_sub_mul_exp_le {a p : ι → ℝ} {c ρ t K : ℝ} (hρ : 0 < ρ)
    (hca : ∀ i, c ≤ |a i|) (ht : 0 ≤ t) (hK : 0 ≤ K) {w₁ w₀ : (ι → ℝ) → ℝ} (hw₁ : Continuous w₁)
    (hw₀ : Continuous w₀) (hw₁c : HasCompactSupport w₁) (hw₀c : HasCompactSupport w₀)
    (hw₁ρ : ∀ x ∈ ball p ρ, w₁ x = 0) (hw₀ρ : ∀ x ∈ ball p ρ, w₀ x = 0) :
    ∫ x, (t * w₁ x - w₀ x) * (K * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2))) ≤
      (t * (∫ x, |w₁ x|) + ∫ x, |w₀ x|) * (K * Real.exp (-(t * (c * ρ ^ 2)))) := by
  have hQ : Continuous fun x : ι → ℝ ↦ ∑ i, |a i| * (x i - p i) ^ 2 := continuous_finsetSum _
    fun i _ ↦ continuous_const.mul (((continuous_apply i).sub continuous_const).pow 2)
  have hA : Integrable fun x ↦ |w₁ x| := (hw₁.integrable_of_hasCompactSupport hw₁c).abs
  have hB : Integrable fun x ↦ |w₀ x| := (hw₀.integrable_of_hasCompactSupport hw₀c).abs
  have hint : Integrable fun x ↦
      (t * w₁ x - w₀ x) * (K * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2))) :=
    ((continuous_const.mul hw₁).sub hw₀).mul (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hQ).neg)) |>.integrable_of_hasCompactSupport
      (hw₁c.mul_left.sub hw₀c).mul_right
  have hR : (t * (∫ x, |w₁ x|) + ∫ x, |w₀ x|) * (K * Real.exp (-(t * (c * ρ ^ 2)))) =
      ∫ x, (t * |w₁ x| + |w₀ x|) * (K * Real.exp (-(t * (c * ρ ^ 2)))) := by
    rw [integral_mul_const, integral_add (hA.const_mul t) hB, integral_const_mul]
  rw [hR]
  refine integral_mono hint ((hA.const_mul t).add hB |>.mul_const _) fun x ↦ ?_
  by_cases hx : x ∈ ball p ρ
  · simp only [hw₁ρ x hx, hw₀ρ x hx, mul_zero, sub_zero, zero_mul, abs_zero, add_zero, le_refl]
  have hexp : Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2)) ≤
      Real.exp (-(t * (c * ρ ^ 2))) := Real.exp_le_exp.2
    (neg_le_neg (mul_le_mul_of_nonneg_left (mul_sq_le_sum_of_notMem_ball hρ hca hx) ht))
  have h₁ : t * w₁ x - w₀ x ≤ t * |w₁ x| + |w₀ x| := by
    nlinarith [le_abs_self (w₁ x), neg_abs_le (w₀ x)]
  calc (t * w₁ x - w₀ x) * (K * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2)))
      ≤ (t * |w₁ x| + |w₀ x|) * (K * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2))) :=
        mul_le_mul_of_nonneg_right h₁ (by positivity)
    _ ≤ (t * |w₁ x| + |w₀ x|) * (K * Real.exp (-(t * (c * ρ ^ 2)))) := by gcongr

omit [LinearOrder ι] in
/-- **The norm bound near the centre.** If the continuous compactly supported `θ` is `1` on the
ball of radius `ρ ≥ δ` around `p`, then `∫ θ² K e^{-t ∑ᵢ |aᵢ| (xᵢ - pᵢ)²}` is at least
`vol(B(p, δ)) K e^{-t (∑ᵢ |aᵢ|) δ²}`. -/
private theorem mul_le_integral_sq_mul_exp {a p : ι → ℝ} {δ ρ t K : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (ht : 0 ≤ t) (hK : 0 ≤ K) {θ : (ι → ℝ) → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hθ1 : ∀ x ∈ ball p ρ, θ x = 1) :
    volume.real (ball p δ) * (K * Real.exp (-(t * ((∑ i, |a i|) * δ ^ 2)))) ≤
      ∫ x, θ x ^ 2 * (K * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2))) := by
  have hQ : Continuous fun x : ι → ℝ ↦ ∑ i, |a i| * (x i - p i) ^ 2 := continuous_finsetSum _
    fun i _ ↦ continuous_const.mul (((continuous_apply i).sub continuous_const).pow 2)
  have hθ2c : HasCompactSupport fun x ↦ θ x ^ 2 := by
    refine hθc.mono fun x hx ↦ ?_
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff two_ne_zero] at hx ⊢
    exact hx
  have hint : Integrable fun x ↦ θ x ^ 2 * (K * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2))) :=
    ((hθ.pow 2).mul (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hQ).neg))).integrable_of_hasCompactSupport
      hθ2c.mul_right
  refine (setIntegral_ge_of_const_le measurableSet_ball measure_ball_lt_top.ne
    (fun x hx ↦ ?_) hint.integrableOn).trans
    (setIntegral_le_integral hint (Eventually.of_forall fun x ↦ by positivity))
  rw [hθ1 x (ball_subset_ball hδρ hx), one_pow, one_mul]
  gcongr
  exact sum_le_mul_sq_of_mem_ball hδ hx

/-- The weight of `t` in the pointwise energy of a cut-off ground state. -/
private def weight₁ (a p : ι → ℝ) (θ : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  θ x * (2 * ∑ i, |a i| * (x i - p i) * fderiv ℝ θ x (Pi.single i 1))

/-- The constant weight in the pointwise energy of a cut-off ground state. -/
private def weight₀ (θ : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  θ x * ∑ i, fderiv ℝ (fderiv ℝ θ) x (Pi.single i 1) (Pi.single i 1)

/-- The weights are continuous, and vanish where `θ` is locally constant. -/
private theorem weights_spec {a p : ι → ℝ} {ρ : ℝ} {θ : (ι → ℝ) → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hθ1 : ∀ x ∈ ball p ρ, θ x = 1) :
    Continuous (weight₁ a p θ) ∧ Continuous (weight₀ θ) ∧
      (∀ x ∈ ball p ρ, weight₁ a p θ x = 0) ∧ ∀ x ∈ ball p ρ, weight₀ θ x = 0 := by
  have hθ' : ∀ x ∈ ball p ρ, fderiv ℝ θ x = 0 := fun x hx ↦ by
    rw [(eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) hθ1).fderiv_eq]
    exact fderiv_const_apply _
  have hθ'' : ∀ x ∈ ball p ρ, fderiv ℝ (fderiv ℝ θ) x = 0 := fun x hx ↦ by
    rw [(eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) hθ').fderiv_eq]
    exact fderiv_const_apply _
  have hθd : Continuous (fderiv ℝ θ) := hθ.continuous_fderiv two_ne_zero
  have hθdd : Continuous (fderiv ℝ (fderiv ℝ θ)) :=
    (hθ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  refine ⟨hθ.continuous.mul (continuous_const.mul (continuous_finsetSum _ fun i _ ↦
      (continuous_const.mul ((continuous_apply i).sub continuous_const)).mul
        (hθd.clm_apply continuous_const))),
    hθ.continuous.mul (continuous_finsetSum _ fun i _ ↦
      (hθdd.clm_apply continuous_const).clm_apply continuous_const),
    fun x hx ↦ by simp [weight₁, hθ' x hx], fun x hx ↦ by simp [weight₀, hθ'' x hx]⟩

/-- The squared norm of the translated ground state is `κ⁻² e^{-t ∑ᵢ |aᵢ| (xᵢ - pᵢ)²}`. -/
private theorem sum_sq_wittenGroundState {a p : ι → ℝ} {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    ∑ s, diagonalQuadraticWittenEigenform a t 0 (Finset.univ.filter fun i ↦ a i < 0) (x - p) s ^ 2 =
      (gaussConst ι)⁻¹ ^ 2 * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2)) := by
  have h : diagonalQuadraticWittenEigenform a t 0 (Finset.univ.filter fun i ↦ a i < 0) (x - p) =
      ((gaussConst ι)⁻¹ * gauss a p t x) •
        (Pi.single (Finset.univ.filter fun i ↦ a i < 0) 1 : Finset ι → ℝ) :=
    congrFun (wittenGroundState_eq a p ht _) x
  simp [h, Pi.single_apply, mul_pow, gauss_sq]

/-- The pointwise energy of a cut-off ground state, in terms of the weights. -/
private theorem energy_eq {f θ : (ι → ℝ) → ℝ} {a p : ι → ℝ} {b t : ℝ} (ht : 0 ≤ t)
    (hθ : ContDiff ℝ 2 θ) (hf : ∀ x, θ x ≠ 0 → f =ᶠ[𝓝 x] fun y ↦ b + diagonalQuadratic a (y - p))
    (x : ι → ℝ) :
    ∑ s, euclideanWittenLaplacian f t (θ • fun y ↦ diagonalQuadraticWittenEigenform a t 0
        (Finset.univ.filter fun i ↦ a i < 0) (y - p)) x s *
      (θ • fun y ↦ diagonalQuadraticWittenEigenform a t 0
        (Finset.univ.filter fun i ↦ a i < 0) (y - p)) x s =
      (t * weight₁ a p θ x - weight₀ θ x) *
        ((gaussConst ι)⁻¹ ^ 2 * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2))) := by
  rw [sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_mul ht hθ hf x,
    sum_sq_wittenGroundState ht x, weight₁, weight₀]
  ring

/-- The pointwise squared norm of a cut-off ground state. -/
private theorem normSq_eq {a p : ι → ℝ} {t : ℝ} (ht : 0 ≤ t) (θ : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    ∑ s, (θ • fun y ↦ diagonalQuadraticWittenEigenform a t 0
        (Finset.univ.filter fun i ↦ a i < 0) (y - p)) x s ^ 2 =
      θ x ^ 2 * ((gaussConst ι)⁻¹ ^ 2 * Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2))) := by
  simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [sum_sq_wittenGroundState ht x]

/-- **A cut-off ground state is a quasimode.** Let `f` be the quadratic model
`y ↦ b + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` near every point where the compactly supported `C²` function `θ`
does not vanish, with every `aᵢ ≠ 0`, and let `θ = 1` on the ball of radius `ρ > 0` around `p`.
Let `Ψ_t(x) = Ψ_{0,s₀}(x - p)` be the Gaussian ground state of the model, with
`s₀ = {i | aᵢ < 0}`. Then for every `ε > 0` and all large `t`, the quadratic form of the Witten
Laplacian of `f` on `θ Ψ_t` is at most `ε` times its squared norm. -/
theorem exists_forall_integral_sum_euclideanWittenLaplacian_smul_mul_le {f θ : (ι → ℝ) → ℝ}
    {a p : ι → ℝ} {b ρ : ℝ} (ha : ∀ i, a i ≠ 0) (hρ : 0 < ρ) (hθ : ContDiff ℝ 2 θ)
    (hθc : HasCompactSupport θ) (hθ1 : ∀ x ∈ ball p ρ, θ x = 1)
    (hf : ∀ x, θ x ≠ 0 → f =ᶠ[𝓝 x] fun y ↦ b + diagonalQuadratic a (y - p)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T, ∀ t, T ≤ t →
      ∫ x, ∑ s, euclideanWittenLaplacian f t (θ • fun y ↦ diagonalQuadraticWittenEigenform a t 0
          (Finset.univ.filter fun i ↦ a i < 0) (y - p)) x s *
        (θ • fun y ↦ diagonalQuadraticWittenEigenform a t 0
          (Finset.univ.filter fun i ↦ a i < 0) (y - p)) x s ≤
      ε * ∫ x, ∑ s, (θ • fun y ↦ diagonalQuadraticWittenEigenform a t 0
          (Finset.univ.filter fun i ↦ a i < 0) (y - p)) x s ^ 2 := by
  obtain ⟨c, hc, hca⟩ := exists_pos_le_abs ha
  obtain ⟨δ, hδ, hδρ, hSδ⟩ :=
    exists_radius hc (Finset.sum_nonneg (s := Finset.univ) fun i _ ↦ abs_nonneg (a i)) hρ
  -- The weights of the pointwise energy vanish on `B(p, ρ)`, where `θ` is constant.
  obtain ⟨hw₁, hw₀, hw₁ρ, hw₀ρ⟩ := weights_spec (a := a) hθ hθ1
  set V := volume.real (ball p δ)
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume p hδ).ne' measure_ball_lt_top.ne
  set A := ∫ x, |weight₁ a p θ x|
  set B := ∫ x, |weight₀ θ x|
  have hγ : 0 < c * ρ ^ 2 / 2 := by positivity
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((tendsto_mul_add_mul_exp_neg A B hγ).eventually
    (gt_mem_nhds (mul_pos hε hV)))
  refine ⟨max T₀ 0, fun t ht ↦ ?_⟩
  have ht₀ : 0 ≤ t := (le_max_right _ _).trans ht
  have hsplit : Real.exp (-(t * (c * ρ ^ 2))) ≤
      Real.exp (-(t * ((∑ i, |a i|) * δ ^ 2))) * Real.exp (-(c * ρ ^ 2 / 2 * t)) := by
    rw [← Real.exp_add]
    have h := mul_le_mul_of_nonneg_left hSδ ht₀
    have h₁ : t * (c * ρ ^ 2) = 2 * (t * (c * ρ ^ 2 / 2)) := by ring
    have h₂ : c * ρ ^ 2 / 2 * t = t * (c * ρ ^ 2 / 2) := by ring
    exact Real.exp_le_exp.2 (by linarith [h, h₁, h₂])
  set K := (gaussConst ι)⁻¹ ^ 2
  rw [integral_congr_ae (Eventually.of_forall (energy_eq ht₀ hθ hf)),
    integral_congr_ae (Eventually.of_forall (normSq_eq (a := a) (p := p) ht₀ θ))]
  calc _ ≤ (t * A + B) * (K * Real.exp (-(t * (c * ρ ^ 2)))) :=
        integral_sub_mul_exp_le hρ hca ht₀ (by positivity) hw₁ hw₀ (hθc.mul_right) (hθc.mul_right)
          hw₁ρ hw₀ρ
    _ ≤ (t * A + B) * (K * (Real.exp (-(t * ((∑ i, |a i|) * δ ^ 2))) *
          Real.exp (-(c * ρ ^ 2 / 2 * t)))) := by gcongr
    _ = K * Real.exp (-(t * ((∑ i, |a i|) * δ ^ 2))) *
          ((t * A + B) * Real.exp (-(c * ρ ^ 2 / 2 * t))) := by ring
    _ ≤ K * Real.exp (-(t * ((∑ i, |a i|) * δ ^ 2))) * (ε * V) :=
          mul_le_mul_of_nonneg_left (hT₀ t ((le_max_left _ _).trans ht)).le (by positivity)
    _ = ε * (V * (K * Real.exp (-(t * ((∑ i, |a i|) * δ ^ 2))))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_integral_sq_mul_exp hδ hδρ ht₀ (by positivity) hθ.continuous hθc hθ1) hε.le

/-! ### Quasimodes with disjoint supports -/

section Disjoint

variable {κ : Type*} [Fintype κ] {v : κ → (ι → ℝ) → Finset ι → ℝ} {x : ι → ℝ}

omit [Fintype ι] [LinearOrder ι] in
/-- Near a point outside the supports of all `v j` with `j ≠ i`, a combination of the `v j` is
the multiple of `v i`. -/
private theorem eventuallyEq_sum_smul (c : κ → ℝ) {i : κ}
    (hi : ∀ j ≠ i, x ∉ tsupport (v j)) : (∑ j, c j • v j) =ᶠ[𝓝 x] c i • v i := by
  classical
  have h : ∀ᶠ y in 𝓝 x, ∀ j, j ≠ i → v j y = 0 := eventually_all.2 fun j ↦ by
    by_cases hj : j = i
    · exact Eventually.of_forall fun _ h ↦ absurd hj h
    · exact (notMem_tsupport_iff_eventuallyEq.1 (hi j hj)).mono fun y hy _ ↦ hy
  filter_upwards [h] with y hy
  rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj ↦ by simp [hy j hj]) (by simp)]

/-- **The energy of a combination of forms with disjoint supports.** If at most one of the forms
`v j` has `x` in its support, the pointwise energy of `∑ⱼ cⱼ vⱼ` at `x` is `∑ⱼ cⱼ²` times the
energies of the `v j`, and so is its squared norm: the Witten Laplacian is a local operator. -/
private theorem sum_euclideanWittenLaplacian_sum_smul_mul (f : (ι → ℝ) → ℝ) (t : ℝ) (c : κ → ℝ)
    (hv : ∀ i j, i ≠ j → x ∈ tsupport (v i) → x ∉ tsupport (v j)) :
    ∑ s, euclideanWittenLaplacian f t (∑ j, c j • v j) x s * (∑ j, c j • v j) x s =
        ∑ j, c j ^ 2 * ∑ s, euclideanWittenLaplacian f t (v j) x s * v j x s ∧
      ∑ s, (∑ j, c j • v j) x s ^ 2 = ∑ j, c j ^ 2 * ∑ s, v j x s ^ 2 := by
  classical
  have hzero : ∀ j, x ∉ tsupport (v j) → v j x = 0 := fun j hj ↦
    image_eq_zero_of_notMem_tsupport hj
  by_cases hx : ∃ i, x ∈ tsupport (v i)
  · obtain ⟨i, hi⟩ := hx
    have hi' : ∀ j ≠ i, x ∉ tsupport (v j) := fun j hj ↦ hv i j (Ne.symm hj) hi
    have hφ := eventuallyEq_sum_smul c hi'
    have hrest : ∀ (F : (Finset ι → ℝ) → ℝ), F 0 = 0 →
        ∑ j, c j ^ 2 * F (v j x) = c i ^ 2 * F (v i x) := fun F hF ↦
      Finset.sum_eq_single i (fun j _ hj ↦ by rw [hzero j (hi' j hj), hF, mul_zero]) (by simp)
    refine ⟨?_, ?_⟩
    · rw [((EventuallyEq.refl _ f).euclideanWittenLaplacian hφ t).eq_of_nhds, hφ.eq_of_nhds,
        euclideanWittenLaplacian_const_smul, Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)]
      · simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ ↦ by ring
      · rw [hzero j (hi' j hj)]
        simp
    · rw [hφ.eq_of_nhds, hrest (fun w ↦ ∑ s, w s ^ 2) (by simp)]
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  · push Not at hx
    have h₀ : (∑ j, c j • v j) x = 0 := by
      simp [Finset.sum_apply, hzero _ (hx _)]
    simp [h₀, hzero _ (hx _)]

omit [Fintype ι] [LinearOrder ι] [Fintype κ] in
/-- Forms each of which vanishes at the marked points of the others, but not at its own marked
point and multi-index, are linearly independent. -/
private theorem linearIndependent_of_apply_eq_zero [Finite κ] (z : κ → ι → ℝ) (σ : κ → Finset ι)
    (hz : ∀ i j, i ≠ j → v i (z j) = 0) (hne : ∀ j, v j (z j) (σ j) ≠ 0) :
    LinearIndependent ℝ v := by
  classical
  have := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrFun (congrFun hg (z q)) (σ q)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single q (fun p _ hpq ↦ by simp [hz p q hpq]) (by simp)] at h
  exact (mul_eq_zero.1 h).resolve_right (hne q)

/-- **The span of quasimodes with disjoint supports.** Let `v j` be linearly independent smooth
compactly supported forms of degree `m` with pairwise disjoint supports, on each of which the
quadratic form of `Δ_t` is at most `ε` times the squared norm. Then their span has dimension the
number of the `v j`, and on every element of it the quadratic form is at most `ε` times the
squared norm. -/
private theorem exists_finrank_eq_of_quasimodes {f : (ι → ℝ) → ℝ} {t ε : ℝ} {m : ℕ}
    (hli : LinearIndependent ℝ v) (hvC : ∀ j, ContDiff ℝ ∞ (v j))
    (hvc : ∀ j, HasCompactSupport (v j)) (hvm : ∀ j x s, v j x s ≠ 0 → s.card = m)
    (hdisj : ∀ x i j, i ≠ j → x ∈ tsupport (v i) → x ∉ tsupport (v j))
    (hE : ∀ j, Integrable fun x ↦ ∑ s, euclideanWittenLaplacian f t (v j) x s * v j x s)
    (hq : ∀ j, ∫ x, ∑ s, euclideanWittenLaplacian f t (v j) x s * v j x s ≤
      ε * ∫ x, ∑ s, v j x s ^ 2) :
    ∃ V : Submodule ℝ ((ι → ℝ) → Finset ι → ℝ), Module.finrank ℝ V = Fintype.card κ ∧
      ∀ φ ∈ V, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ (∀ x s, φ x s ≠ 0 → s.card = m) ∧
        ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ≤ ε * ∫ x, ∑ s, φ x s ^ 2 := by
  refine ⟨Submodule.span ℝ (Set.range v), finrank_span_eq_card hli, fun φ hφ ↦ ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hφ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (∑ j, c j • v j) = fun x ↦ ∑ j, c j • v j x := by
      ext x
      simp [Finset.sum_apply]
    rw [h]
    exact ContDiff.sum fun j _ ↦ (hvC j).const_smul (c j)
  · exact Finset.sum_induction _ HasCompactSupport (fun _ _ h₁ h₂ ↦ h₁.add h₂)
      HasCompactSupport.zero fun j _ ↦ (hvc j).mono (Function.support_const_smul_subset _ _)
  · intro x s hxs
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hxs
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxs
    exact hvm j x s (right_ne_zero_of_mul hj)
  · have hpt := fun x ↦ sum_euclideanWittenLaplacian_sum_smul_mul f t c (hdisj x)
    have hN : ∀ j, Integrable fun x ↦ c j ^ 2 * ∑ s, v j x s ^ 2 := fun j ↦
      (hvC j).continuous.integrable_mul_sum_sq_of_continuousOn (hvc j) subset_rfl
        continuousOn_const
    rw [integral_congr_ae (Eventually.of_forall fun x ↦ (hpt x).1),
      integral_congr_ae (Eventually.of_forall fun x ↦ (hpt x).2),
      integral_finsetSum _ fun j _ ↦ (hE j).const_mul _, integral_finsetSum _ fun j _ ↦ hN j,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [integral_const_mul, integral_const_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hq j) (sq_nonneg _)

end Disjoint

/-! ### The low-energy space in each degree -/

/-- The translated ground state is a positive multiple of `dx^{s}` at every point. -/
private theorem exists_pos_wittenGroundState_eq_smul (a p : ι → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (s : Finset ι) (y : ι → ℝ) :
    ∃ g : ℝ, 0 < g ∧ diagonalQuadraticWittenEigenform a t 0 s (y - p) =
      g • (Pi.single s 1 : Finset ι → ℝ) :=
  ⟨(gaussConst ι)⁻¹ * gauss a p t y, mul_pos (inv_pos.2 gaussConst_pos) (gauss_pos _ _ _ _),
    congrFun (wittenGroundState_eq a p ht s) y⟩

/-- A cut-off translated ground state has degree `s`. -/
private theorem eq_of_smul_wittenGroundState_apply_ne_zero {a p : ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    {s : Finset ι} (J : (ι → ℝ) → ℝ) {x : ι → ℝ} {s' : Finset ι}
    (h : (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 s (y - p)) x s' ≠ 0) : s' = s := by
  obtain ⟨g, -, hg⟩ := exists_pos_wittenGroundState_eq_smul a p ht s x
  by_contra hs
  simp [hg, hs] at h

/-- The pointwise energy of a `C²` compactly supported form supported in a ball on which `f` is a
quadratic model is integrable. -/
private theorem integrable_energy_of_eqOn {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}
    {a p : ι → ℝ} {b r : ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφr : tsupport φ ⊆ ball p r)
    (hfa : EqOn f (fun y ↦ b + diagonalQuadratic a (y - p)) (ball p r)) (t : ℝ) :
    Integrable fun x ↦ ∑ s, euclideanWittenLaplacian f t φ x s * φ x s :=
  hφ.continuous.integrable_sum_mul_of_continuousOn hφc hφr fun _ hx ↦
    (continuousAt_euclideanWittenLaplacian (((contDiff_const.add
      ((contDiff_diagonalQuadratic _).comp (contDiff_id.sub contDiff_const))).contDiffAt
        ).congr_of_eventuallyEq (eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) hfa))
      hφ.contDiffAt t).continuousWithinAt

omit [LinearOrder ι] in
/-- Smooth cutoffs equal to `1` on `ball p (r / 4)` with support `closedBall p (r / 2)`. -/
private theorem exists_cutoff {r : ℝ} (hr : 0 < r) :
    ∃ J : (ι → ℝ) → (ι → ℝ) → ℝ, (∀ p, ContDiff ℝ ∞ (J p)) ∧ (∀ p, HasCompactSupport (J p)) ∧
      (∀ p, ∀ x ∈ ball p (r / 4), J p x = 1) ∧ ∀ p, tsupport (J p) = closedBall p (r / 2) := by
  let θ : ∀ p : ι → ℝ, ContDiffBump p := fun p ↦ ⟨r / 4, r / 2, by positivity, by linarith⟩
  exact ⟨fun p ↦ θ p, fun p ↦ (θ p).contDiff, fun p ↦ (θ p).hasCompactSupport,
    fun p x hx ↦ (θ p).one_of_mem_closedBall (ball_subset_closedBall hx),
    fun p ↦ (θ p).tsupport_eq⟩

/-- **Quasimodes span a low-energy space of the dimension of the critical count.** Let `P` be a
finite set of points of `ℝ^ι` at mutual distance at least `2 r`, and suppose that on the ball of
radius `r` around each `p ∈ P` the function `f` is the quadratic model
`y ↦ f p + ∑ᵢ a p i (yᵢ - pᵢ)² / 2` with every `a p i ≠ 0`, so that `p` is a nondegenerate critical
point whose Morse index is the number of negative `a p i`. Then for every degree `m`, every
`ε > 0` and all large `t`, there is a space of smooth compactly supported forms of degree `m`,
whose dimension is the number of points of `P` of index `m`, on which the quadratic form of the
Witten Laplacian `Δ_t` of `f` is at most `ε` times the squared norm.

The space is spanned by the Gaussian ground states of the quadratic models, cut off near the
points of `P` of index `m`. Together with the gap of
`TauCeti.exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul` in degrees
that are no Morse index, this is the comparison of the low-lying spectrum of `Δ_t` with the
critical points in Witten's proof of the Morse inequalities. -/
theorem exists_forall_exists_finrank_eq_forall_integral_sum_euclideanWittenLaplacian_mul_le
    {f : (ι → ℝ) → ℝ} {P : Finset (ι → ℝ)} {r : ℝ} (hr : 0 < r)
    (hP : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * r ≤ dist p q) {a : (ι → ℝ) → ι → ℝ}
    (hfa : ∀ p ∈ P, EqOn f (fun y ↦ f p + diagonalQuadratic (a p) (y - p)) (ball p r))
    (ha : ∀ p ∈ P, ∀ i, a p i ≠ 0) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T, ∀ t, T ≤ t → ∃ V : Submodule ℝ ((ι → ℝ) → Finset ι → ℝ),
      Module.finrank ℝ V =
        (P.filter fun p ↦ (Finset.univ.filter fun i ↦ a p i < 0).card = m).card ∧
      ∀ φ ∈ V, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ (∀ x s, φ x s ≠ 0 → s.card = m) ∧
        ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ≤ ε * ∫ x, ∑ s, φ x s ^ 2 := by
  set Pm := P.filter fun p ↦ (Finset.univ.filter fun i ↦ a p i < 0).card = m
  set s₀ : (ι → ℝ) → Finset ι := fun p ↦ Finset.univ.filter fun i ↦ a p i < 0
  obtain ⟨J, hJ, hJc, hJ1, hJs⟩ := exists_cutoff (ι := ι) hr
  have hJr : ∀ p, tsupport (J p) ⊆ ball p r := fun p ↦ by
    rw [hJs]
    exact closedBall_subset_ball (by linarith)
  -- The cut-off ground states `J p Ψ_{p,t}` are quasimodes for large `t`.
  set Ψ : ℝ → (ι → ℝ) → (ι → ℝ) → Finset ι → ℝ := fun t p y ↦
    diagonalQuadraticWittenEigenform (a p) t 0 (s₀ p) (y - p)
  have hT : ∀ p ∈ Pm, ∃ T, ∀ t, T ≤ t →
      ∫ x, ∑ s, euclideanWittenLaplacian f t (J p • Ψ t p) x s * (J p • Ψ t p) x s ≤
        ε * ∫ x, ∑ s, (J p • Ψ t p) x s ^ 2 := fun p hp ↦
    have hpP := (Finset.mem_filter.1 hp).1
    exists_forall_integral_sum_euclideanWittenLaplacian_smul_mul_le (ha p hpP) (by positivity)
      ((hJ p).of_le (by simp)) (hJc p) (hJ1 p) (fun _ hx ↦ eventuallyEq_of_mem
        (isOpen_ball.mem_nhds (hJr p (subset_tsupport _ hx))) (hfa p hpP)) hε
  choose! T hT using hT
  obtain ⟨M, hM⟩ := Finset.exists_le (Pm.image T)
  refine ⟨max M 0, fun t ht ↦ ?_⟩
  have ht₀ : 0 ≤ t := (le_max_right _ _).trans ht
  set v : Pm → (ι → ℝ) → Finset ι → ℝ := fun p ↦ J p • Ψ t p
  have hvC : ∀ p, ContDiff ℝ ∞ (v p) := fun p ↦ (hJ p).smul
    ((contDiff_diagonalQuadraticWittenEigenform _ _ _ _).comp (contDiff_id.sub contDiff_const))
  have hdisj : ∀ p q : Pm, p ≠ q → ∀ x ∈ closedBall (p : ι → ℝ) (r / 2),
      x ∉ closedBall (q : ι → ℝ) (r / 2) := fun p q hpq ↦ by
    have h := hP p (Finset.mem_filter.1 p.2).1 q (Finset.mem_filter.1 q.2).1
      (Subtype.coe_injective.ne hpq)
    exact Set.disjoint_left.1 (closedBall_disjoint_closedBall (by linarith))
  have hvs : ∀ p, tsupport (v p) ⊆ closedBall (p : ι → ℝ) (r / 2) := fun p ↦
    (tsupport_smul_subset_left _ _).trans (hJs p).le
  -- `v p` vanishes at the other points of `P`, and not at `p` on the multi-index `s₀ p`.
  have hli : LinearIndependent ℝ v := linearIndependent_of_apply_eq_zero (fun p ↦ p)
    (fun p ↦ s₀ p) (fun p q hpq ↦ by
      have : (q : ι → ℝ) ∉ tsupport (J p) := by
        rw [hJs]
        exact hdisj q p hpq.symm _ (mem_closedBall_self (by positivity))
      simp [v, image_eq_zero_of_notMem_tsupport this]) fun q ↦ by
    obtain ⟨gq, hgq, hΨq⟩ : ∃ g : ℝ, 0 < g ∧ Ψ t q q = g • (Pi.single (s₀ q) 1 : Finset ι → ℝ) :=
      exists_pos_wittenGroundState_eq_smul (a q) q ht₀ (s₀ q) q
    simpa [v, hΨq, hJ1 q q (mem_ball_self (by positivity))] using hgq.ne'
  rw [← Fintype.card_coe]
  refine exists_finrank_eq_of_quasimodes hli hvC (fun p ↦ (hJc p).smul_right) (fun j x s hj ↦ ?_)
    (fun x p q hpq hxp hxq ↦ hdisj p q hpq x (hvs p hxp) (hvs q hxq))
    (fun p ↦ integrable_energy_of_eqOn ((hvC p).of_le (by simp)) ((hJc p).smul_right)
      ((tsupport_smul_subset_left _ _).trans (hJr p)) (hfa p (Finset.mem_filter.1 p.2).1) t)
    (fun p ↦ hT p p.2 t ((hM _ (Finset.mem_image_of_mem T p.2)).trans
      ((le_max_left _ _).trans ht)))
  rw [eq_of_smul_wittenGroundState_apply_ne_zero ht₀ (J j) hj]
  exact (Finset.mem_filter.1 j.2).2

end TauCeti
