/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
public import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Hölder continuity of the gradient for divergence-form equations

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in an open set `Ω ⊆ ℝ^{n+1}`,

that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ` on `Ω`, and let `0 < α < 1`.
This file proves the interior Schauder estimate in divergence form: `∇u` is as regular as the
coefficients and the data. If the open `R`-thickening `S_R` of a set `S` lies in `Ω`, the
coefficients `a` are `α`-Hölder on `S_R` with constant `K_a`, in the operator norm of the attached
bilinear forms, `G` is `α`-Hölder on `S_R` with constant `K_G`, and `a` is uniformly elliptic with
constants `0 < λ ≤ Λ` at the points of `S`, then the precise representative of `∇u` is `α`-Hölder
on `S` with constant

`C (K_G + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`,

where `C` depends only on `n`, `α`, `λ`, `Λ` and an upper bound for the dimensionless coefficient
modulus `K_a R^α`. No sign, symmetry or regularity of `a` is assumed beyond these. For the
Laplacian, `a = 1`, the coefficient modulus vanishes and `C` depends only on `n` and `α`.

## The argument

Fix a centre `x₀ ∈ S` and freeze the coefficients at `x₀`. On `B_r = ball x₀ r` let `w` solve the
frozen problem `-∂ᵢ(aⁱʲ(x₀) ∂ⱼw) = 0` with the boundary values of `u`. The comparison with the
frozen problem
(`TauCeti.PDE.UniformlyEllipticOn.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le`) bounds
`∫_{B_r} ‖∇u - ∇w‖²` by `2 λ⁻² r^{2α} (K_a² φ(r) + K_G² |B_r|)`, where `φ(t) = ∫_{B_t} ‖∇u‖²`,
while the gradient of `w` obeys the decay estimates of constant-coefficient equations
(`TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero` and
`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero`).
Unlike for the Laplacian, the error carries the energy `φ(r)` of `u` itself, so the estimate is
proved in three passes, each closed by the iteration lemma
`TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add`.

* **Morrey's estimate.** For radii `r` so small that `K_a² r^{2α}` is below the threshold of the
  iteration lemma, `φ(ρ) ≤ A ((ρ / r)^{n+1} + K_a² r^{2α}) φ(r) + B r^{n+1+2α}`, which gives
  `φ(ρ) = O(ρ^{n+1-α})`.
* **Campanato's estimate.** For the square mean oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²`,
  `ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + B r^{2α} φ(r) + B r^{n+1+2α}`. With `φ(r) = O(r^b)` this gives
  `ψ(ρ) = O(ρ^{b+2α})`. For `b = n + 1 - α` the mean oscillation of `∇u` is `O(ρ^{α/2})`, so the
  averages of `∇u` on small balls are bounded and in fact `φ(r) = O(r^{n+1})`. A second pass with
  `b = n + 1` gives `ψ(ρ) = O(ρ^{n+1+2α})`.
* **Hölder continuity.** By Jensen's inequality the mean oscillation of `∇u` on balls of radius
  `ρ` is then `O(ρ^α)`, and Campanato's theorem
  (`TauCeti.MeasureTheory.dist_preciseRepresentative_le_of_setAverage_norm_sub_le`) turns this
  into the Hölder estimate. Points farther apart than half the working radius are compared
  through the averages of `∇u` over balls of that radius.

The working radius is a fixed fraction of `R`, depending on the bound for `K_a R^α`, which is how
that bound enters the constant.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_of_uniformlyEllipticOn`: the
  interior Hölder estimate for `∇u` for divergence-form equations with Hölder coefficients.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`: the case of the Laplacian,
  `-Δu = -div G`, with a constant depending only on `n` and `α`.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Theorem 5.19 and its proof).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 3 (Theorem 3.13).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Comparison

/-- The constant `2^{d} (Λ / λ)^{d/2}` of the decay of the `L²` mass of the gradient of a solution
of a constant-coefficient equation on `ℝ^d`, `d = n + 1`. -/
private def massConst (n : ℕ) (lam Lam : ℝ) : ℝ := 2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)

/-- The constant `2^{3d+10} (d + 1)² (Λ / λ)^{(d+2)/2}` of the decay of the `L²` mean oscillation
of the gradient of a solution of a constant-coefficient equation on `ℝ^d`, `d = n + 1`. -/
private def oscConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  2 ^ (3 * (n + 1) + 10) * ((n : ℝ) + 1 + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2)

private theorem massConst_nonneg (n : ℕ) (lam Lam : ℝ) : 0 ≤ massConst n lam Lam := by
  unfold massConst
  positivity

private theorem oscConst_nonneg (n : ℕ) (lam Lam : ℝ) : 0 ≤ oscConst n lam Lam := by
  unfold oscConst
  positivity

/-- The exponent `n + 1 + 2α` splits as `t^{n+1} (t^α)²`. -/
private theorem rpow_add_two_mul_eq {t : ℝ} (ht : 0 < t) (a : ℝ) :
    t ^ ((n : ℝ) + 1 + 2 * a) = t ^ (n + 1) * (t ^ a) ^ 2 := by
  rw [Real.rpow_add ht, ← Real.rpow_natCast, mul_comm (2 : ℝ), Real.rpow_mul ht.le,
    Real.rpow_two, Nat.cast_add, Nat.cast_one]

/-- The volume of a ball of radius `t > 0` in `ℝ^{n+1}` is `t^{n+1}` times that of the unit
ball. -/
private theorem measureReal_ball_eq (x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : 0 < t) :
    volume.real (ball x t) =
      t ^ (n + 1) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  rw [Measure.addHaar_real_ball_of_pos _ _ ht, finrank_euclideanSpace_fin]

/-- The algebra of the energy error: `λ X ≤ k (p Y + q √V)` gives
`X² ≤ 2 λ⁻² k² (p² Y² + q² V)`. -/
private theorem sq_le_two_div_sq_mul_sq_mul_add {l X Y V k p q : ℝ} (hl : 0 < l) (hX : 0 ≤ X)
    (hV : 0 ≤ V) (h : l * X ≤ k * (p * Y + q * √V)) :
    X ^ 2 ≤ 2 / l ^ 2 * k ^ 2 * (p ^ 2 * Y ^ 2 + q ^ 2 * V) := by
  have h1 := pow_le_pow_left₀ (by positivity) h 2
  have h2 : (p * Y + q * √V) ^ 2 ≤ 2 * (p ^ 2 * Y ^ 2 + q ^ 2 * V) := by
    nlinarith [sq_nonneg (p * Y - q * √V), Real.sq_sqrt hV]
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg k)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rw [mul_pow, mul_pow] at h1
  linarith

/-- **The energy error of the frozen replacement.** Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `Ω ⊆ ℝ^{n+1}`, with `a` elliptic at `x₀` and `a`, `G`
`α`-Hölder with constants `K_a`, `K_G` on `B_r = ball x₀ r ⊆ Ω`. The replacement `w` frozen at
`x₀` satisfies `∫_{B_r} ‖∇u - ∇w‖² ≤ 2 λ⁻² r^{2α} (K_a² ∫_{B_r} ‖∇u‖² + K_G² |B_r|)`. -/
private theorem exists_setIntegral_norm_gradient_sub_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (h : UniformlyEllipticOn s a lam Lam)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} (hx₀ : x₀ ∈ s) {r : ℝ} (hr : 0 < r)
    {α Ka KG : ℝ≥0} (hα : 0 < α)
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGK : HolderOnWith KG α G (ball x₀ r)) (hball : ball x₀ r ⊆ Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) :
    ∃ w : W1p volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ v : W1p0 volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
        energyFormH1 (fun _ => a x₀) 0 0 w (v : W1p volume _ 2) = 0) ∧
      ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 ≤
        2 / lam ^ 2 * (r ^ (α : ℝ)) ^ 2 *
          (Ka ^ 2 * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
            KG ^ 2 *
              (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * r ^ (n + 1))) := by
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ r, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hlam : 0 < lam := h.pos
  obtain ⟨w, -, hw0, hest⟩ :=
    h.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le hx₀ hα haK hGK hB subset_rfl hu
  refine ⟨w, hw0, ?_⟩
  have hE : ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 =
      ‖W1p.gradient (W1p.restrictL hB u - w)‖ ^ 2 :=
    W1p.setIntegral_norm_gradient_sub_sq_eq hB u w
  have hY : ‖W1p.gradient (W1p.restrictL hB u)‖ ^ 2 =
      ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_restrictL_ae hB u] with x hx
    rw [hx]
  have hV : volume.real (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * r ^ (n + 1) := by
    simp only [B, Opens.coe_mk]
    rw [measureReal_ball_eq x₀ hr, mul_comm]
  have key := sq_le_two_div_sq_mul_sq_mul_add h.pos (norm_nonneg _) measureReal_nonneg hest
  rw [hY, hV] at key
  exact hE.trans_le key

/-- **The mass comparison.** Under the hypotheses of the energy error estimate, for
`0 < ρ ≤ r` the `L²` mass `φ(t) = ∫_{B_t} ‖∇u‖²` satisfies
`φ(ρ) ≤ 4 D₀ (ρ / r)^{n+1} φ(r) + (4 D₀ + 2) 2 λ⁻² r^{2α} (K_a² φ(r) + K_G² |B_r|)`. -/
private theorem setIntegral_ball_norm_gradient_sq_le_add
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (h : UniformlyEllipticOn s a lam Lam)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} (hx₀ : x₀ ∈ s) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    {α Ka KG : ℝ≥0} (hα : 0 < α)
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGK : HolderOnWith KG α G (ball x₀ r)) (hball : ball x₀ r ⊆ Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
      4 * massConst n lam Lam * (ρ / r) ^ (n + 1) * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
        (4 * massConst n lam Lam + 2) * (2 / lam ^ 2 * (r ^ (α : ℝ)) ^ 2 *
          (Ka ^ 2 * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
            KG ^ 2 * (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
              r ^ (n + 1)))) := by
  have hr : 0 < r := hρ.trans_le hρr
  obtain ⟨w, hw0, hE⟩ :=
    exists_setIntegral_norm_gradient_sub_sq_le h hx₀ hr hα haK hGK hball hu
  have hdec := setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero h.pos
    (h.lower_bound hx₀) (h.toQuadraticForm'_le hx₀) hw0 (x₀ := x₀)
    (R := r) subset_rfl hρ.le hρr
  simp only [Fintype.card_fin] at hdec
  have hfm : MemLp
      (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hHm : MemLp
      (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (ball x₀ r)) := Lp.memLp (W1p.gradient w)
  have hq : 0 ≤ (ρ / r) ^ (n + 1) := by positivity
  have hq1 : (ρ / r) ^ (n + 1) ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr)
  have hcomp := setIntegral_norm_sq_le_add_of_subset (ball_subset_ball hρr) hfm hHm
    (mul_nonneg (massConst_nonneg n lam Lam) hq) (by simpa [massConst, mul_assoc] using hdec)
  have hE0 : 0 ≤ ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  have hD := massConst_nonneg n lam Lam
  have h1 : (4 * (massConst n lam Lam * (ρ / r) ^ (n + 1)) + 2) *
      ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 ≤
      (4 * massConst n lam Lam + 2) *
        ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) hE0
  have h2 := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 4 * massConst n lam Lam + 2)
  linarith

/-- **The oscillation comparison.** Under the hypotheses of the energy error estimate, for
`0 < ρ ≤ r` the square mean oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` satisfies
`ψ(ρ) ≤ 4 D₁ (ρ / r)^{n+3} ψ(r) + (4 D₁ + 2) 2 λ⁻² r^{2α} (K_a² φ(r) + K_G² |B_r|)`. -/
private theorem setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (h : UniformlyEllipticOn s a lam Lam)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} (hx₀ : x₀ ∈ s) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    {α Ka KG : ℝ≥0} (hα : 0 < α)
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGK : HolderOnWith KG α G (ball x₀ r)) (hball : ball x₀ r ⊆ Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * oscConst n lam Lam * (ρ / r) ^ (n + 3) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
        (4 * oscConst n lam Lam + 2) * (2 / lam ^ 2 * (r ^ (α : ℝ)) ^ 2 *
          (Ka ^ 2 * (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
            KG ^ 2 * (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
              r ^ (n + 1)))) := by
  have hr : 0 < r := hρ.trans_le hρr
  obtain ⟨w, hw0, hE⟩ :=
    exists_setIntegral_norm_gradient_sub_sq_le h hx₀ hr hα haK hGK hball hu
  have hdec := setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero
    h.pos (h.lower_bound hx₀) (h.toQuadraticForm'_le hx₀) hw0 (x₀ := x₀)
    (R := r) subset_rfl (⨍ y in ball x₀ r, W1p.gradient u y) hρ.le hρr
  have hK : 2 ^ (3 * Fintype.card (Fin (n + 1)) + 10) *
      ((Fintype.card (Fin (n + 1)) : ℝ) + 1) ^ 2 *
        √(Lam / lam) ^ (Fintype.card (Fin (n + 1)) + 2) *
          (ρ / r) ^ (Fintype.card (Fin (n + 1)) + 2) =
      oscConst n lam Lam * (ρ / r) ^ (n + 3) := by
    simp only [oscConst, Fintype.card_fin]
    push_cast
    ring
  rw [hK] at hdec
  have hfm : MemLp
      (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hHm : MemLp
      (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (ball x₀ r)) := Lp.memLp (W1p.gradient w)
  have hq : 0 ≤ (ρ / r) ^ (n + 3) := by positivity
  have hq1 : (ρ / r) ^ (n + 3) ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr)
  have hcomp := setIntegral_norm_sub_setAverage_sq_le_add_of_subset (ball_subset_ball hρr)
    measure_ball_lt_top.ne hfm hHm (mul_nonneg (oscConst_nonneg n lam Lam) hq) hdec
  have hE0 : 0 ≤ ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  have hD := oscConst_nonneg n lam Lam
  have h1 : (4 * (oscConst n lam Lam * (ρ / r) ^ (n + 3)) + 2) *
      ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 ≤
      (4 * oscConst n lam Lam + 2) *
        ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) hE0
  have h2 := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 4 * oscConst n lam Lam + 2)
  linarith

end Comparison

section Decay

/-- The final algebra of the iteration: if `ψ(ρ) ≤ C ((ρ / R)^γ ψ(R) + B ρ^γ)`, `ψ(R) ≤ T R^e` and
`B ≤ B' T R^{e - γ}`, then `ψ(ρ) ≤ C (1 + B') T R^{e - γ} ρ^γ`. -/
private theorem le_mul_one_add_mul_rpow_of_le {C B B' T R ρ γ e ψρ ψR : ℝ} (hC : 0 ≤ C)
    (hR : 0 < R) (hρ : 0 < ρ) (hψR : ψR ≤ T * R ^ e) (hB : B ≤ B' * T * R ^ (e - γ))
    (hdec : ψρ ≤ C * ((ρ / R) ^ γ * ψR + B * ρ ^ γ)) :
    ψρ ≤ C * (1 + B') * T * R ^ (e - γ) * ρ ^ γ := by
  have hργ : 0 ≤ ρ ^ γ := by positivity
  have h1 : (ρ / R) ^ γ * ψR ≤ T * R ^ (e - γ) * ρ ^ γ := by
    calc (ρ / R) ^ γ * ψR ≤ (ρ / R) ^ γ * (T * R ^ e) :=
          mul_le_mul_of_nonneg_left hψR (by positivity)
      _ = T * R ^ (e - γ) * ρ ^ γ := by
          rw [Real.div_rpow hρ.le hR.le, Real.rpow_sub hR]
          field_simp
  have h2 : B * ρ ^ γ ≤ B' * T * R ^ (e - γ) * ρ ^ γ := mul_le_mul_of_nonneg_right hB hργ
  calc ψρ ≤ C * ((ρ / R) ^ γ * ψR + B * ρ ^ γ) := hdec
    _ ≤ C * (T * R ^ (e - γ) * ρ ^ γ + B' * T * R ^ (e - γ) * ρ ^ γ) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    _ = C * (1 + B') * T * R ^ (e - γ) * ρ ^ γ := by ring

/-- For `0 < r`, `r^{2a} r^{n+1} = r^{n+1+2a-c} r^c`. -/
private theorem rpow_sq_mul_pow_eq {r : ℝ} (hr : 0 < r) (a c : ℝ) :
    (r ^ a) ^ 2 * r ^ (n + 1) = r ^ ((n : ℝ) + 1 + 2 * a - c) * r ^ c := by
  rw [← Real.rpow_add hr, sub_add_cancel, rpow_add_two_mul_eq hr, mul_comm]

/-- **One step of Morrey's estimate.** Under the hypotheses of the energy error estimate on
`ball x₀ R`, for `0 < ρ ≤ r ≤ R` the `L²` mass `φ(t) = ∫_{B_t} ‖∇u‖²` satisfies
`φ(ρ) ≤ A ((ρ / r)^{n+1} + (K_a R^α)²) φ(r) + A K_G² ω R^{3α} r^{n+1-α}`, with
`A = 4 D₀ + (4 D₀ + 2) 2 λ⁻²`. -/
private theorem setIntegral_ball_norm_gradient_sq_le_mul_add_mul_rpow
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (h : UniformlyEllipticOn s a lam Lam)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} (hx₀ : x₀ ∈ s) {α Ka KG : ℝ≥0} (hα : 0 < α) {R : ℝ}
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ R))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGK : HolderOnWith KG α G (ball x₀ R)) (hball : ball x₀ R ⊆ Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ω : ℝ} (hωdef : ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    {A : ℝ} (hAdef : A = 4 * massConst n lam Lam + (4 * massConst n lam Lam + 2) * (2 / lam ^ 2))
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hrR : r ≤ R) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
      A * ((ρ / r) ^ ((n : ℝ) + 1) + (Ka * R ^ (α : ℝ)) ^ 2) *
        (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
      A * KG ^ 2 * ω * R ^ (3 * (α : ℝ)) * r ^ ((n : ℝ) + 1 - α) := by
  have hω : 0 ≤ ω := hωdef ▸ measureReal_nonneg
  have hD := massConst_nonneg n lam Lam
  have hR : 0 < R := hρ.trans_le (hρr.trans hrR)
  have hr : 0 < r := hρ.trans_le hρr
  have hc := setIntegral_ball_norm_gradient_sq_le_add h hx₀ hρ hρr hα
    (haK.mono (ball_subset_ball hrR)) (hGK.mono (ball_subset_ball hrR))
    ((ball_subset_ball hrR).trans hball) hu
  rw [← hωdef] at hc
  have hq : (ρ / r) ^ (n + 1) = (ρ / r) ^ ((n : ℝ) + 1) := by
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  have hrα : r ^ (α : ℝ) ≤ R ^ (α : ℝ) := Real.rpow_le_rpow hr.le hrR α.2
  have hKa' : (r ^ (α : ℝ)) ^ 2 * Ka ^ 2 ≤ (Ka * R ^ (α : ℝ)) ^ 2 := by
    rw [mul_pow, mul_comm]
    gcongr
  have hpow : (r ^ (α : ℝ)) ^ 2 * r ^ (n + 1) ≤ R ^ (3 * (α : ℝ)) * r ^ ((n : ℝ) + 1 - α) := by
    rw [rpow_sq_mul_pow_eq hr (α : ℝ) ((n : ℝ) + 1 - α)]
    have : (n : ℝ) + 1 + 2 * α - ((n : ℝ) + 1 - α) = 3 * α := by ring
    rw [this]
    gcongr
  rw [hq] at hc
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 := ⟨_, rfl⟩
  rw [← hΦ] at hc ⊢
  have hΦ0 : 0 ≤ Φ := hΦ ▸ setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hqn : 0 ≤ (ρ / r) ^ ((n : ℝ) + 1) := by positivity
  have hc₂ : 0 ≤ (4 * massConst n lam Lam + 2) * (2 / lam ^ 2) := by positivity
  have f1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKa' hΦ0) hc₂
  have f2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow
    (by positivity : (0 : ℝ) ≤ KG ^ 2 * ω)) hc₂
  have hε : 0 ≤ (Ka * R ^ (α : ℝ)) ^ 2 := sq_nonneg _
  have f3 : 4 * massConst n lam Lam * (ρ / r) ^ ((n : ℝ) + 1) * Φ ≤
      A * (ρ / r) ^ ((n : ℝ) + 1) * Φ := by
    gcongr
    rw [hAdef]
    nlinarith
  have f4 : (4 * massConst n lam Lam + 2) * (2 / lam ^ 2) * ((Ka * R ^ (α : ℝ)) ^ 2 * Φ) ≤
      A * ((Ka * R ^ (α : ℝ)) ^ 2 * Φ) := by
    gcongr
    rw [hAdef]
    linarith
  have f5 : (4 * massConst n lam Lam + 2) * (2 / lam ^ 2) *
      (KG ^ 2 * ω * (R ^ (3 * (α : ℝ)) * r ^ ((n : ℝ) + 1 - α))) ≤
      A * (KG ^ 2 * ω * (R ^ (3 * (α : ℝ)) * r ^ ((n : ℝ) + 1 - α))) := by
    gcongr
    rw [hAdef]
    linarith
  have hexp : (4 * massConst n lam Lam + 2) * (2 / lam ^ 2 * (r ^ (α : ℝ)) ^ 2 *
      (Ka ^ 2 * Φ + KG ^ 2 * (ω * r ^ (n + 1)))) =
      (4 * massConst n lam Lam + 2) * (2 / lam ^ 2) * ((r ^ (α : ℝ)) ^ 2 * Ka ^ 2 * Φ) +
        (4 * massConst n lam Lam + 2) * (2 / lam ^ 2) *
          (KG ^ 2 * ω * ((r ^ (α : ℝ)) ^ 2 * r ^ (n + 1))) := by ring
  rw [hexp] at hc
  linarith

/-- **Morrey's estimate.** For `α > 0` there are `ε₀ > 0` and `C`, depending only on `n`, `α`, `λ`
and `Λ`, such that the following holds. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on
`Ω ⊆ ℝ^{n+1}`, with `a` elliptic at `x₀`, and `a`, `G` `α`-Hölder with constants `K_a`, `K_G` on
`ball x₀ R ⊆ Ω`. If `(K_a R^α)² ≤ ε₀`, `‖∇u‖²_{L²(Ω)} ≤ T R^{n+1+2α}` and `K_G² ≤ T`, then
`∫_{B_ρ} ‖∇u‖² ≤ C T R^{3α} ρ^{n+1-α}` for `0 < ρ ≤ R`. -/
private theorem exists_setIntegral_ball_norm_gradient_sq_le {α : ℝ≥0} (hα : 0 < α)
    (lam Lam : ℝ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {Ka KG : ℝ≥0}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R T : ℝ},
      UniformlyEllipticOn s a lam Lam → x₀ ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ R) →
      HolderOnWith KG α G (ball x₀ R) → ball x₀ R ⊆ Omega →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      (Ka * R ^ (α : ℝ)) ^ 2 ≤ ε₀ → ‖W1p.gradient u‖ ^ 2 ≤ T * R ^ ((n : ℝ) + 1 + 2 * α) →
      (KG : ℝ) ^ 2 ≤ T → ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
          C * T * R ^ ((n : ℝ) + 1 + 2 * α - ((n : ℝ) + 1 - α)) * ρ ^ ((n : ℝ) + 1 - α) := by
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hω : 0 ≤ ω := hωdef ▸ measureReal_nonneg
  have hD := massConst_nonneg n lam Lam
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = 4 * massConst n lam Lam + (4 * massConst n lam Lam + 2) * (2 / lam ^ 2) := ⟨_, rfl⟩
  have hA : 0 ≤ A := hAdef ▸ by positivity
  have hα' : (0 : ℝ) < α := hα
  obtain ⟨ε₀, C, hε₀, hC, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add hA
    (α := (n : ℝ) + 1) (β := (n : ℝ) + 1 - α) (γ := (n : ℝ) + 1 - α) (by linarith)
    (by linarith)
  refine ⟨ε₀, C * (1 + A * ω), hε₀, by positivity, ?_⟩
  intro Omega u a G Ka KG s x₀ R T h hx₀ haK hGK hball hu hKa hN hKG ρ hρ hρR
  have hR : 0 < R := hρ.trans_le hρR
  have hT : 0 ≤ T := (sq_nonneg _).trans hKG
  have hint : ∀ t ≤ R, IntegrableOn (fun x => ‖W1p.gradient u x‖ ^ 2) (ball x₀ t) := fun t ht =>
    IntegrableOn.mono_set ((Lp.memLp (W1p.gradient u)).integrable_norm_pow two_ne_zero)
      ((ball_subset_ball ht).trans hball)
  have hmono : MonotoneOn (fun t => ∫ x in ball x₀ t, ‖W1p.gradient u x‖ ^ 2) (Ioc 0 R) :=
    fun s _ t ht hst => setIntegral_mono_set (hint t ht.2) (ae_of_all _ fun _ => by positivity)
      (ball_subset_ball hst).eventuallyLE
  have hstep : ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R →
      ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
        A * ((ρ / r) ^ ((n : ℝ) + 1) + (Ka * R ^ (α : ℝ)) ^ 2) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
        A * KG ^ 2 * ω * R ^ (3 * (α : ℝ)) * r ^ ((n : ℝ) + 1 - α) := fun ρ r hρ hρr hrR =>
    setIntegral_ball_norm_gradient_sq_le_mul_add_mul_rpow h hx₀ hα haK hGK hball hu hωdef hAdef
      hρ hρr hrR
  have hdec := hit (φ := fun t => ∫ x in ball x₀ t, ‖W1p.gradient u x‖ ^ 2) (R := R)
    (B := A * KG ^ 2 * ω * R ^ (3 * (α : ℝ))) (by positivity) hKa hmono
    (fun _ _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity) hstep ρ R hρ hρR
    le_rfl
  have hψR : ∫ x in ball x₀ R, ‖W1p.gradient u x‖ ^ 2 ≤ T * R ^ ((n : ℝ) + 1 + 2 * α) :=
    (Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient u) hball).trans hN
  refine le_mul_one_add_mul_rpow_of_le hC.le hR hρ hψR ?_ hdec
  have : (n : ℝ) + 1 + 2 * α - ((n : ℝ) + 1 - α) = 3 * α := by ring
  rw [this]
  have := mul_le_mul_of_nonneg_left hKG (by positivity : (0 : ℝ) ≤ A * ω * R ^ (3 * (α : ℝ)))
  linarith

/-- **One step of Campanato's estimate.** Under the hypotheses of the energy error estimate on
`ball x₀ R`, if `0 < ρ ≤ r ≤ R`, `(K_a R^α)² ≤ e`, `K_G² ≤ T`, `b ≤ n + 1` and
`∫_{B_r} ‖∇u‖² ≤ P T R^{n+1+2α-b} r^b`, then the square mean oscillation
`ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` satisfies
`ψ(ρ) ≤ 4 D₁ (ρ / r)^{n+3} ψ(r) + B T R^{n+1-b} r^{b+2α}`, with
`B = (4 D₁ + 2) 2 λ⁻² (e P + ω)`. -/
private theorem setIntegral_ball_norm_gradient_sub_setAverage_sq_le_mul_add_mul_rpow
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (h : UniformlyEllipticOn s a lam Lam)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} (hx₀ : x₀ ∈ s) {α Ka KG : ℝ≥0} (hα : 0 < α) {R : ℝ}
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ R))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGK : HolderOnWith KG α G (ball x₀ R)) (hball : ball x₀ R ⊆ Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ω : ℝ} (hωdef : ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    {b P e T Bc : ℝ} (hb : b ≤ (n : ℝ) + 1) (hP : 0 ≤ P) (hKa : (Ka * R ^ (α : ℝ)) ^ 2 ≤ e)
    (hKG : (KG : ℝ) ^ 2 ≤ T)
    (hBcdef : Bc = (4 * oscConst n lam Lam + 2) * (2 / lam ^ 2) * (e * P + ω))
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hrR : r ≤ R)
    (hφ : ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ≤
      P * T * R ^ ((n : ℝ) + 1 + 2 * α - b) * r ^ b) :
    ∫ y in ball x₀ ρ, ‖W1p.gradient u y - ⨍ z in ball x₀ ρ, W1p.gradient u z‖ ^ 2 ≤
      4 * oscConst n lam Lam * ((ρ / r) ^ ((n : ℝ) + 3) + 0) *
        (∫ y in ball x₀ r, ‖W1p.gradient u y - ⨍ z in ball x₀ r, W1p.gradient u z‖ ^ 2) +
      Bc * T * R ^ ((n : ℝ) + 1 - b) * r ^ (b + 2 * α) := by
  have hω : 0 ≤ ω := hωdef ▸ measureReal_nonneg
  have hT : 0 ≤ T := (sq_nonneg _).trans hKG
  have he : 0 ≤ e := (sq_nonneg _).trans hKa
  have hR : 0 < R := hρ.trans_le (hρr.trans hrR)
  have hD := oscConst_nonneg n lam Lam
  have hr : 0 < r := hρ.trans_le hρr
  have hc := setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add h hx₀ hρ hρr hα
    (haK.mono (ball_subset_ball hrR)) (hGK.mono (ball_subset_ball hrR))
    ((ball_subset_ball hrR).trans hball) hu
  rw [← hωdef] at hc
  have hq : (ρ / r) ^ (n + 3) = (ρ / r) ^ ((n : ℝ) + 3) := by
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [add_zero]
  rw [hq] at hc
  -- The two error terms are of order `r^{b + 2α}`.
  have hΦ := hφ
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ, Φ = ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 := ⟨_, rfl⟩
  rw [← hΦdef] at hc hΦ
  have hΦ0 : 0 ≤ Φ := hΦdef ▸ setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hRb : R ^ ((n : ℝ) + 1 + 2 * α - b) = (R ^ (α : ℝ)) ^ 2 * R ^ ((n : ℝ) + 1 - b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le, ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  have hrb : (r ^ (α : ℝ)) ^ 2 * r ^ b = r ^ (b + 2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  have hrd : (r ^ (α : ℝ)) ^ 2 * r ^ (n + 1) ≤ R ^ ((n : ℝ) + 1 - b) * r ^ (b + 2 * α) := by
    rw [rpow_sq_mul_pow_eq hr (α : ℝ) (b + 2 * α)]
    have : (n : ℝ) + 1 + 2 * α - (b + 2 * α) = (n : ℝ) + 1 - b := by ring
    rw [this]
    gcongr
  have h1 : (r ^ (α : ℝ)) ^ 2 * Ka ^ 2 * Φ ≤ e * P * T * R ^ ((n : ℝ) + 1 - b) *
      r ^ (b + 2 * α) := by
    calc (r ^ (α : ℝ)) ^ 2 * Ka ^ 2 * Φ
        ≤ (r ^ (α : ℝ)) ^ 2 * Ka ^ 2 * (P * T * R ^ ((n : ℝ) + 1 + 2 * α - b) * r ^ b) := by
          gcongr
      _ = (Ka * R ^ (α : ℝ)) ^ 2 * P * T * R ^ ((n : ℝ) + 1 - b) *
            ((r ^ (α : ℝ)) ^ 2 * r ^ b) := by
          rw [hRb]
          ring
      _ ≤ e * P * T * R ^ ((n : ℝ) + 1 - b) * ((r ^ (α : ℝ)) ^ 2 * r ^ b) := by
          gcongr
      _ = e * P * T * R ^ ((n : ℝ) + 1 - b) * r ^ (b + 2 * α) := by rw [hrb]
  have h2 : KG ^ 2 * ω * ((r ^ (α : ℝ)) ^ 2 * r ^ (n + 1)) ≤
      T * ω * (R ^ ((n : ℝ) + 1 - b) * r ^ (b + 2 * α)) := by
    gcongr
  have hc₂ : 0 ≤ (4 * oscConst n lam Lam + 2) * (2 / lam ^ 2) := by positivity
  have hexp : (4 * oscConst n lam Lam + 2) * (2 / lam ^ 2 * (r ^ (α : ℝ)) ^ 2 *
      (Ka ^ 2 * Φ + KG ^ 2 * (ω * r ^ (n + 1)))) =
      (4 * oscConst n lam Lam + 2) * (2 / lam ^ 2) * ((r ^ (α : ℝ)) ^ 2 * Ka ^ 2 * Φ +
        KG ^ 2 * ω * ((r ^ (α : ℝ)) ^ 2 * r ^ (n + 1))) := by ring
  rw [hexp] at hc
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hc₂
  have h4 : (4 * oscConst n lam Lam + 2) * (2 / lam ^ 2) *
      (e * P * T * R ^ ((n : ℝ) + 1 - b) * r ^ (b + 2 * α) +
        T * ω * (R ^ ((n : ℝ) + 1 - b) * r ^ (b + 2 * α))) =
      Bc * T * R ^ ((n : ℝ) + 1 - b) * r ^ (b + 2 * α) := by
    rw [hBcdef]
    ring
  linarith

/-- **Campanato's estimate.** For `0 < α < 1`, `b ≤ n + 1` and `P, e ≥ 0` there is `C`, depending
only on `n`, `α`, `λ`, `Λ`, `b`, `P` and `e`, such that the following holds. Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `Ω ⊆ ℝ^{n+1}`, with `a` elliptic at `x₀`, and `a`, `G` `α`-Hölder
with constants `K_a`, `K_G` on `ball x₀ R ⊆ Ω`. If `(K_a R^α)² ≤ e`,
`‖∇u‖²_{L²(Ω)} ≤ T R^{n+1+2α}`, `K_G² ≤ T` and `∫_{B_r} ‖∇u‖² ≤ P T R^{n+1+2α-b} r^b` for
`0 < r ≤ R`, then the square mean oscillation of `∇u` satisfies
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C T R^{n+1-b} ρ^{b+2α}` for `0 < ρ ≤ R`. -/
private theorem exists_setIntegral_ball_norm_gradient_sub_setAverage_sq_le {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) (lam Lam : ℝ) {b : ℝ} (hb : b ≤ (n : ℝ) + 1) {P e : ℝ}
    (hP : 0 ≤ P) (he : 0 ≤ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {Ka KG : ℝ≥0}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R T : ℝ},
      UniformlyEllipticOn s a lam Lam → x₀ ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ R) →
      HolderOnWith KG α G (ball x₀ R) → ball x₀ R ⊆ Omega →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      (Ka * R ^ (α : ℝ)) ^ 2 ≤ e → ‖W1p.gradient u‖ ^ 2 ≤ T * R ^ ((n : ℝ) + 1 + 2 * α) →
      (KG : ℝ) ^ 2 ≤ T →
      (∀ r, 0 < r → r ≤ R → ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ≤
        P * T * R ^ ((n : ℝ) + 1 + 2 * α - b) * r ^ b) →
      ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
          C * T * R ^ ((n : ℝ) + 1 - b) * ρ ^ (b + 2 * α) := by
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hω : 0 ≤ ω := hωdef ▸ measureReal_nonneg
  have hD := oscConst_nonneg n lam Lam
  have hα' : (0 : ℝ) < α := hα
  have hα1' : (α : ℝ) < 1 := hα1
  have hγ : b + 2 * α < (n : ℝ) + 3 := by linarith
  obtain ⟨ε₀, C, hε₀, hC, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add
    (by positivity : (0 : ℝ) ≤ 4 * oscConst n lam Lam) hγ hγ
  obtain ⟨Bc, hBcdef⟩ : ∃ Bc : ℝ,
      Bc = (4 * oscConst n lam Lam + 2) * (2 / lam ^ 2) * (e * P + ω) := ⟨_, rfl⟩
  have hBc : 0 ≤ Bc := hBcdef ▸ by positivity
  refine ⟨C * (1 + Bc), by positivity, ?_⟩
  intro Omega u a G Ka KG s x₀ R T h hx₀ haK hGK hball hu hKa hN hKG hφ ρ hρ hρR
  have hR : 0 < R := hρ.trans_le hρR
  have hT : 0 ≤ T := (sq_nonneg _).trans hKG
  set f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  have hfint : ∀ t ≤ R, IntegrableOn f (ball x₀ t) ∧
      ∀ c, IntegrableOn (fun y => ‖f y - c‖ ^ 2) (ball x₀ t) := fun t ht =>
    ⟨(Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two
      ((ball_subset_ball ht).trans hball) measure_ball_lt_top.ne,
      (Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
        ((ball_subset_ball ht).trans hball) measure_ball_lt_top.ne⟩
  -- The square mean oscillation is nondecreasing, since the average is the best constant.
  have hmono : MonotoneOn (fun t => ∫ y in ball x₀ t, ‖f y - ⨍ z in ball x₀ t, f z‖ ^ 2)
      (Ioc 0 R) := fun s hs t ht hst =>
    (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
      (hfint s hs.2).1 ((hfint s hs.2).2 _)).trans
      (setIntegral_mono_set ((hfint t ht.2).2 _) (ae_of_all _ fun _ => by positivity)
        (ball_subset_ball hst).eventuallyLE)
  have hstep : ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R →
      ∫ y in ball x₀ ρ, ‖f y - ⨍ z in ball x₀ ρ, f z‖ ^ 2 ≤
        4 * oscConst n lam Lam * ((ρ / r) ^ ((n : ℝ) + 3) + 0) *
          (∫ y in ball x₀ r, ‖f y - ⨍ z in ball x₀ r, f z‖ ^ 2) +
        Bc * T * R ^ ((n : ℝ) + 1 - b) * r ^ (b + 2 * α) := fun ρ r hρ hρr hrR =>
    setIntegral_ball_norm_gradient_sub_setAverage_sq_le_mul_add_mul_rpow h hx₀ hα haK hGK hball
      hu hωdef hb hP hKa hKG hBcdef hρ hρr hrR (hφ r (hρ.trans_le hρr) hrR)
  have hdec := hit (φ := fun t => ∫ y in ball x₀ t, ‖f y - ⨍ z in ball x₀ t, f z‖ ^ 2) (R := R)
    (B := Bc * T * R ^ ((n : ℝ) + 1 - b)) (ε := 0) (by positivity) (by positivity) hmono
    (fun _ _ => setIntegral_nonneg measurableSet_ball fun _ _ => by positivity) hstep ρ R hρ hρR
    le_rfl
  -- `ψ R ≤ ‖∇u‖²`.
  have hψR : ∫ y in ball x₀ R, ‖f y - ⨍ z in ball x₀ R, f z‖ ^ 2 ≤
      T * R ^ ((n : ℝ) + 1 + 2 * α) := by
    have h0 := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq
      measure_ball_lt_top.ne (hfint R le_rfl).1 ((hfint R le_rfl).2 0)
    simp only [sub_zero] at h0
    exact (h0.trans (Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient u) hball)).trans hN
  have hexp : (n : ℝ) + 1 + 2 * α - (b + 2 * α) = (n : ℝ) + 1 - b := by ring
  have := le_mul_one_add_mul_rpow_of_le hC.le hR hρ hψR (B' := Bc) (le_of_eq (by rw [hexp])) hdec
  rwa [hexp] at this

end Decay

section MeanOscillation

/-- **Mean oscillation from square mean oscillation.** If the square mean oscillation of `∇u` on
`ball x t ⊆ Ω` is at most `ω L² t^{n+1+2β}`, where `ω` is the measure of the unit ball and
`L ≥ 0`, then the mean oscillation of `∇u` on `closedBall x t` is at most `L t^β`. -/
private theorem setAverage_closedBall_norm_gradient_sub_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {x : EuclideanSpace ℝ (Fin (n + 1))} {t L β : ℝ} (ht : 0 < t) (hball : ball x t ⊆ Omega)
    (hL : 0 ≤ L)
    (hψ : ∫ y in ball x t, ‖W1p.gradient u y - ⨍ z in ball x t, W1p.gradient u z‖ ^ 2 ≤
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * L ^ 2 *
        t ^ ((n : ℝ) + 1 + 2 * β)) :
    ⨍ y in closedBall x t, ‖W1p.gradient u y - ⨍ z in closedBall x t, W1p.gradient u z‖ ≤
      L * t ^ β := by
  have hω : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    measureReal_ball_pos _ _ one_pos
  -- The averages over `closedBall x t` and `ball x t` agree.
  rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball x t)]
  -- Jensen's inequality bounds the mean oscillation by the square mean oscillation.
  have hJ : (⨍ y in ball x t, ‖W1p.gradient u y - ⨍ z in ball x t, W1p.gradient u z‖) ^ 2 ≤
      (∫ y in ball x t, ‖W1p.gradient u y - ⨍ z in ball x t, W1p.gradient u z‖ ^ 2) /
        volume.real (ball x t) := by
    rw [div_eq_inv_mul, ← smul_eq_mul, ← setAverage_eq]
    exact sq_setAverage_norm_le_setAverage_norm_sq (measure_ball_pos volume x ht).ne'
      measure_ball_lt_top.ne (((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball
        measure_ball_lt_top.ne).sub (integrableOn_const measure_ball_lt_top.ne))
      ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hball
        measure_ball_lt_top.ne (⨍ z in ball x t, W1p.gradient u z))
  rw [← pow_le_pow_iff_left₀ (average_nonneg fun _ => norm_nonneg _) (by positivity) two_ne_zero]
  refine hJ.trans ?_
  rw [measureReal_ball_eq x ht, div_le_iff₀ (by positivity)]
  refine hψ.trans (le_of_eq ?_)
  rw [rpow_add_two_mul_eq ht]
  ring

/-- The average of `∇u` over `closedBall z R`, for `ball z R ⊆ Ω`, is at most
`ω^{-1/2} R^{-(n+1)/2} ‖∇u‖_{L²(Ω)}` in norm, where `ω` is the measure of the unit ball. -/
private theorem norm_setAverage_closedBall_gradient_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 < R) (hball : ball z R ⊆ Omega) :
    ‖⨍ y in closedBall z R, W1p.gradient u y‖ ≤
      (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹ *
        (R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖) := by
  have hω : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    measureReal_ball_pos _ _ one_pos
  rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball z R)]
  -- Hölder's bound `‖⨍_B f‖ ≤ |B|^{-1/2} ‖f‖_{L²(B)}` on an average, with
  -- `‖f‖_{L²(B)} ≤ ‖f‖_{L²(Ω)}`.
  have h := (enorm_setAverage_le (f := W1p.gradient u) (mu := volume) (p := 2)
    one_le_two ENNReal.ofNat_ne_top).trans
    (mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)))
  replace h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero
    (measure_ball_pos volume z hR).ne' measure_ball_lt_top.ne) (Lp.eLpNorm_ne_top _)) h
  rw [toReal_enorm, ENNReal.toReal_mul, ← Lp.norm_def, ← ENNReal.toReal_rpow, ← measureReal_def,
    measureReal_ball_eq z hR] at h
  refine h.trans_eq ?_
  rw [ENNReal.toReal_ofNat, Real.mul_rpow (by positivity) hω.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hR.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hω.le]
  push_cast
  ring_nf

/-- If `∇u` lies in `L²(Ω)` and `ball z R ⊆ Ω`, then `∇u` is integrable on `closedBall z t` for
`t ≤ R`. -/
private theorem integrableOn_closedBall_gradient {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : W1p volume Omega 2) {z : EuclideanSpace ℝ (Fin (n + 1))} {R t : ℝ}
    (hball : ball z R ⊆ Omega) (ht : t ≤ R) :
    IntegrableOn (W1p.gradient u) (closedBall z t) := by
  rcases ht.lt_or_eq with ht | ht
  · exact (Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two
      ((closedBall_subset_ball ht).trans hball) measure_closedBall_lt_top.ne
  · -- `closedBall z R` and `ball z R` differ by a null set.
    rw [ht]
    exact ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball
      measure_ball_lt_top.ne).congr_set_ae (volume.addHaar_closedBall_ae_eq_ball z R)

/-- **Bounded averages.** If `ball x R ⊆ Ω` and the mean oscillation of `∇u` on `closedBall x s`
is at most `L s^β` for `0 < s ≤ R`, with `β > 0` and `L ≥ 0`, then for `0 < t ≤ R` the average of
`∇u` over `ball x t` is at most `2 · 2^{n+1} / (1 - 2^{-β}) · L R^β + ω^{-1/2} R^{-(n+1)/2}
‖∇u‖_{L²(Ω)}` in norm. -/
private theorem norm_setAverage_ball_gradient_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {x : EuclideanSpace ℝ (Fin (n + 1))} {R L β t : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hball : ball x R ⊆ Omega) (hL : 0 ≤ L)
    (hosc : ∀ s, 0 < s → s ≤ R →
      ⨍ y in closedBall x s, ‖W1p.gradient u y - ⨍ z in closedBall x s, W1p.gradient u z‖ ≤
        L * s ^ β)
    (ht : 0 < t) (htR : t ≤ R) :
    ‖⨍ y in ball x t, W1p.gradient u y‖ ≤
      2 * (2 ^ (n + 1) / (1 - 2 ^ (-β))) * (L * R ^ β) +
        (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹ *
          (R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖) := by
  have hint := integrableOn_closedBall_gradient u hball le_rfl
  have h1 := norm_setAverage_closedBall_sub_preciseRepresentative_le hβ hint hosc ht htR
  have h2 := norm_setAverage_closedBall_sub_preciseRepresentative_le hβ hint hosc hR le_rfl
  rw [finrank_euclideanSpace_fin] at h1 h2
  have h3 := norm_setAverage_closedBall_gradient_le u hR hball
  have hc : 0 ≤ 2 ^ (n + 1) / (1 - (2 : ℝ) ^ (-β)) :=
    div_nonneg (by positivity)
      (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hβ))).le
  have htβ : L * t ^ β ≤ L * R ^ β :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.le htR hβ.le) hL
  rw [← Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball x t)]
  set At := ⨍ y in closedBall x t, W1p.gradient u y
  set AR := ⨍ y in closedBall x R, W1p.gradient u y
  set p := preciseRepresentative volume
    (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x
  calc ‖At‖ = ‖(At - p) + (p - AR) + AR‖ := by abel_nf
    _ ≤ ‖At - p‖ + ‖p - AR‖ + ‖AR‖ := norm_add₃_le
    _ ≤ 2 ^ (n + 1) / (1 - 2 ^ (-β)) * (L * R ^ β) + 2 ^ (n + 1) / (1 - 2 ^ (-β)) * (L * R ^ β) +
        (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹ *
          (R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖) := by
        rw [norm_sub_rev p AR]
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left htβ hc)
    _ = _ := by ring

/-- The `L²` mass of `∇u` on a ball is controlled by its square mean oscillation and its
average there: `∫_{B_t} ‖∇u‖² ≤ 2 ∫_{B_t} ‖∇u - (∇u)_{B_t}‖² + 2 ω t^{n+1} ‖(∇u)_{B_t}‖²`. -/
private theorem setIntegral_ball_norm_gradient_sq_le_add_norm_setAverage
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {x : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (ht : 0 < t) (hball : ball x t ⊆ Omega) :
    ∫ y in ball x t, ‖W1p.gradient u y‖ ^ 2 ≤
      2 * (∫ y in ball x t, ‖W1p.gradient u y - ⨍ z in ball x t, W1p.gradient u z‖ ^ 2) +
        2 * (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * t ^ (n + 1)) *
          ‖⨍ y in ball x t, W1p.gradient u y‖ ^ 2 := by
  set c := ⨍ y in ball x t, W1p.gradient u y
  have h := MeasureTheory.setIntegral_norm_add_sq_le
    (g := fun y => W1p.gradient u y - c) (h := fun _ => c)
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hball
      measure_ball_lt_top.ne c) (integrableOn_const measure_ball_lt_top.ne)
  simp only [sub_add_cancel] at h
  rw [setIntegral_const, smul_eq_mul, measureReal_ball_eq x ht] at h
  linarith

end MeanOscillation

section Holder

/-- The precise representative of `∇u` at `z` is controlled by the mean oscillation of `∇u` near
`z` and by `‖∇u‖_{L²(Ω)}`. If `ball z R ⊆ Ω` and the mean oscillation of `∇u` on `closedBall z t`
is at most `M t^α` for `0 < t ≤ R`, then
`‖∇u*(z)‖ ≤ (2^{n+1} / (1 - 2^{-α}) M + ω^{-1/2} R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)}) R^α`, where `∇u*` is
the precise representative and `ω` is the measure of the unit ball. -/
private theorem norm_preciseRepresentative_gradient_le {α : ℝ≥0} (hα : 0 < α)
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R M : ℝ} (hR : 0 < R) (hball : ball z R ⊆ Omega)
    (hint : IntegrableOn (W1p.gradient u) (closedBall z R))
    (hM : ∀ t, 0 < t → t ≤ R →
      ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
        M * t ^ (α : ℝ)) :
    ‖preciseRepresentative volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) z‖ ≤
      (2 ^ (n + 1) / (1 - 2 ^ (-(α : ℝ))) * M +
        (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹ *
          (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)) * R ^ (α : ℝ) := by
  -- Compare the precise representative with the average over `closedBall z R`.
  have h1 := norm_setAverage_closedBall_sub_preciseRepresentative_le (α := (α : ℝ))
    (NNReal.coe_pos.2 hα) hint hM hR le_rfl
  rw [finrank_euclideanSpace_fin] at h1
  have h2 := norm_setAverage_closedBall_gradient_le u hR hball
  have haR : R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖ =
      R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ * R ^ (α : ℝ) := by
    rw [mul_right_comm, ← Real.rpow_add hR]
    congr 2
    ring
  rw [haR] at h2
  have h3 := norm_sub_le (⨍ y in closedBall z R, W1p.gradient u y)
    ((⨍ y in closedBall z R, W1p.gradient u y) - preciseRepresentative volume (W1p.gradient u) z)
  rw [sub_sub_cancel] at h3
  calc _ ≤ _ := h3
    _ ≤ _ := add_le_add h2 h1
    _ = _ := by ring

/-- For `0 ≤ a` and `0 < R ≤ 2 d`, two vectors of norm at most `A R^a` are at distance at most
`2 · 2^a A d^a`. -/
private theorem dist_le_two_mul_two_rpow_mul_rpow_of_norm_le {E : Type*}
    [SeminormedAddCommGroup E] {p q : E} {A R d a : ℝ} (ha : 0 ≤ a) (hR : 0 < R)
    (hd : R ≤ 2 * d) (hp : ‖p‖ ≤ A * R ^ a) (hq : ‖q‖ ≤ A * R ^ a) :
    dist p q ≤ 2 * 2 ^ a * A * d ^ a := by
  have hA : 0 ≤ A :=
    nonneg_of_mul_nonneg_left ((norm_nonneg p).trans hp) (Real.rpow_pos_of_pos hR a)
  have hRd : R ^ a ≤ 2 ^ a * d ^ a := by
    rw [← Real.mul_rpow zero_le_two (by linarith)]
    exact Real.rpow_le_rpow hR.le hd ha
  calc dist p q ≤ ‖p‖ + ‖q‖ := dist_le_norm_add_norm p q
    _ ≤ 2 * (A * R ^ a) := by linarith
    _ ≤ 2 * (A * (2 ^ a * d ^ a)) := by gcongr
    _ = 2 * 2 ^ a * A * d ^ a := by ring

/-- **Campanato's criterion for the gradient.** For `α > 0` there is `c`, depending only on `n` and
`α`, such that the following holds. If `ball z R ⊆ Ω` for every `z ∈ S` and the mean oscillation
of `∇u` on `closedBall z t` is at most `L t^α` for every `z ∈ S` and `0 < t ≤ R`, then the precise
representative of `∇u` is `α`-Hölder on `S` with constant
`c (L + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`. -/
private theorem exists_holderOnWith_preciseRepresentative_gradient_of_setAverage_le {α : ℝ≥0}
    (hα : 0 < α) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2} {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R L : ℝ},
      0 < R → 0 ≤ L → (∀ z ∈ S, ball z R ⊆ Omega) →
      (∀ z ∈ S, ∀ t, 0 < t → t ≤ R →
        ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
          L * t ^ (α : ℝ)) →
      HolderOnWith (c * (L + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal α
        (preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
        S := by
  obtain ⟨ω, hω⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hα' : (0 : ℝ) < α := hα
  obtain ⟨cα, hcαdef⟩ : ∃ cα : ℝ, cα = 2 ^ (n + 1) / (1 - 2 ^ (-(α : ℝ))) := ⟨_, rfl⟩
  have hcα0 : 0 ≤ cα := hcαdef ▸ div_nonneg (by positivity)
    (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα'))).le
  refine ⟨2 * 2 ^ (α : ℝ) * (cα + (√ω)⁻¹), by positivity, ?_⟩
  intro Omega u S R L hR hL hball hM
  have hint : ∀ z ∈ S, ∀ t ≤ R, IntegrableOn (W1p.gradient u) (closedBall z t) :=
    fun z hz t ht => integrableOn_closedBall_gradient u (hball z hz) ht
  obtain ⟨a, ha⟩ : ∃ a, a = R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ by positivity
  rw [← ha]
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  suffices h : dist (preciseRepresentative volume (W1p.gradient u) x)
      (preciseRepresentative volume (W1p.gradient u) y) ≤
      2 * 2 ^ (α : ℝ) * (cα + (√ω)⁻¹) * (L + a) * dist x y ^ (α : ℝ) from
    h.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  have hω0 : 0 ≤ (√ω)⁻¹ := by positivity
  rcases le_or_gt (2 * dist x y) R with hd | hd
  · -- Nearby points: Campanato's estimate.
    have h := dist_preciseRepresentative_le_of_setAverage_norm_sub_le hα' (hint x hx _ hd)
      (fun r hr hr' => hM x hx r hr (hr'.trans hd))
      (fun r hr hr' => hM y hy r hr (by linarith [dist_nonneg (x := x) (y := y)]))
    rw [finrank_euclideanSpace_fin, ← hcαdef] at h
    refine h.trans ?_
    have hd0 : 0 ≤ dist x y ^ (α : ℝ) := by positivity
    have h2α : (0 : ℝ) ≤ 2 * 2 ^ (α : ℝ) := by positivity
    calc 2 * 2 ^ (α : ℝ) * cα * (L * dist x y ^ (α : ℝ))
        = 2 * 2 ^ (α : ℝ) * (cα * L) * dist x y ^ (α : ℝ) := by ring
      _ ≤ 2 * 2 ^ (α : ℝ) * ((cα + (√ω)⁻¹) * (L + a)) * dist x y ^ (α : ℝ) := by
          gcongr <;> linarith
      _ = _ := by ring
  · -- Distant points: both values are controlled by averages over balls of radius `R`.
    have hbound : ∀ z ∈ S, ‖preciseRepresentative volume (W1p.gradient u) z‖ ≤
        ((cα + (√ω)⁻¹) * (L + a)) * R ^ (α : ℝ) := fun z hz => by
      refine (norm_preciseRepresentative_gradient_le hα u hR (hball z hz) (hint z hz R le_rfl)
        (hM z hz)).trans ?_
      rw [← hcαdef, ← hω, ← ha]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith
    have h := dist_le_two_mul_two_rpow_mul_rpow_of_norm_le hα'.le hR hd.le
      (hbound x hx) (hbound y hy)
    exact h.trans_eq (by ring)

end Holder

section PerCentre

/-- **Bounded averages after the first pass.** Let `ball x R ⊆ Ω`, `0 ≤ θ` with
`R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)} ≤ θ`, and suppose that the square mean oscillation of `∇u` on
`ball x t` is at most `C₁ θ² R^α t^{n+1+α}` for `0 < t ≤ R`. Then the averages of `∇u` over
`ball x t`, `0 < t ≤ R`, are at most `c₂ θ R^α` in norm, with
`c₂ = 2 · 2^{n+1} / (1 - 2^{-α/2}) · (C₁ / ω)^{1/2} + ω^{-1/2}`. -/
private theorem norm_setAverage_ball_gradient_le_of_setIntegral_le {α : ℝ≥0} (hα : 0 < α)
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {x : EuclideanSpace ℝ (Fin (n + 1))} {R θ C₁ : ℝ} (hR : 0 < R) (hball : ball x R ⊆ Omega)
    (hθ : 0 ≤ θ) (hC₁ : 0 ≤ C₁)
    (hNθ : R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ ≤ θ)
    (hψ : ∀ t, 0 < t → t ≤ R →
      ∫ y in ball x t, ‖W1p.gradient u y - ⨍ w in ball x t, W1p.gradient u w‖ ^ 2 ≤
        C₁ * θ ^ 2 * R ^ (α : ℝ) * t ^ ((n : ℝ) + 1 + 2 * ((α : ℝ) / 2)))
    {t : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    ‖⨍ y in ball x t, W1p.gradient u y‖ ≤
      (2 * (2 ^ (n + 1) / (1 - 2 ^ (-((α : ℝ) / 2)))) *
          √(C₁ / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) +
        (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹) *
        θ * R ^ (α : ℝ) := by
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ measureReal_ball_pos _ _ one_pos
  rw [← hωdef]
  have hα' : (0 : ℝ) < α := hα
  have hcβ : 0 ≤ 2 ^ (n + 1) / (1 - (2 : ℝ) ^ (-((α : ℝ) / 2))) := div_nonneg (by positivity)
    (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))).le
  -- The mean oscillation of `∇u` is `O(t^{α/2})`.
  have hL₁ : C₁ * θ ^ 2 * R ^ (α : ℝ) = ω * (√(C₁ / ω) * θ * R ^ ((α : ℝ) / 2)) ^ 2 := by
    have hh : (R ^ ((α : ℝ) / 2)) ^ 2 = R ^ (α : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
      norm_num
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hC₁ hω.le), hh]
    field_simp
  have hosc : ∀ s, 0 < s → s ≤ R →
      ⨍ y in closedBall x s, ‖W1p.gradient u y - ⨍ w in closedBall x s, W1p.gradient u w‖ ≤
        (√(C₁ / ω) * θ * R ^ ((α : ℝ) / 2)) * s ^ ((α : ℝ) / 2) := fun s hs hsR =>
    setAverage_closedBall_norm_gradient_sub_le u hs ((ball_subset_ball hsR).trans hball)
      (by positivity) (by rw [← hωdef, ← hL₁]; exact hψ s hs hsR)
  refine (norm_setAverage_ball_gradient_le u (by positivity) hR hball (by positivity) hosc ht
    htR).trans ?_
  rw [← hωdef]
  have h1 : √(C₁ / ω) * θ * R ^ ((α : ℝ) / 2) * R ^ ((α : ℝ) / 2) =
      √(C₁ / ω) * θ * R ^ (α : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hR, add_halves]
  have h2 : R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖ =
      R ^ (α : ℝ) * (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) := by
    rw [← mul_assoc, ← Real.rpow_add hR]
    congr 2
    ring
  rw [h1, h2]
  calc 2 * (2 ^ (n + 1) / (1 - 2 ^ (-((α : ℝ) / 2)))) * (√(C₁ / ω) * θ * R ^ (α : ℝ)) +
        (√ω)⁻¹ * (R ^ (α : ℝ) * (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖))
      ≤ 2 * (2 ^ (n + 1) / (1 - 2 ^ (-((α : ℝ) / 2)))) * (√(C₁ / ω) * θ * R ^ (α : ℝ)) +
        (√ω)⁻¹ * (R ^ (α : ℝ) * θ) := by gcongr
    _ = _ := by ring

/-- **Morrey's estimate with the full exponent.** Under the hypotheses of
`norm_setAverage_ball_gradient_le_of_setIntegral_le`, the `L²` mass of `∇u` on `ball x r` is at
most `(2 C₁ + 2 ω c₂²) θ² R^{2α} r^{n+1}` for `0 < r ≤ R`. -/
private theorem setIntegral_ball_norm_gradient_sq_le_of_setIntegral_le {α : ℝ≥0} (hα : 0 < α)
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {x : EuclideanSpace ℝ (Fin (n + 1))} {R θ C₁ : ℝ} (hR : 0 < R) (hball : ball x R ⊆ Omega)
    (hθ : 0 ≤ θ) (hC₁ : 0 ≤ C₁)
    (hNθ : R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ ≤ θ)
    (hψ : ∀ t, 0 < t → t ≤ R →
      ∫ y in ball x t, ‖W1p.gradient u y - ⨍ w in ball x t, W1p.gradient u w‖ ^ 2 ≤
        C₁ * θ ^ 2 * R ^ (α : ℝ) * t ^ ((n : ℝ) + 1 + 2 * ((α : ℝ) / 2)))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2 ≤
      (2 * C₁ + 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
        ((2 * (2 ^ (n + 1) / (1 - 2 ^ (-((α : ℝ) / 2)))) *
          √(C₁ / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) +
        (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹)) ^ 2) *
        θ ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α - ((n : ℝ) + 1)) * r ^ ((n : ℝ) + 1) := by
  have hav := norm_setAverage_ball_gradient_le_of_setIntegral_le hα u hR hball hθ hC₁ hNθ hψ hr
    hrR
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hω : 0 ≤ ω := hωdef ▸ measureReal_nonneg
  obtain ⟨c₂, hc₂def⟩ : ∃ c₂ : ℝ, c₂ = 2 * (2 ^ (n + 1) / (1 - 2 ^ (-((α : ℝ) / 2)))) *
      √(C₁ / ω) + (√ω)⁻¹ := ⟨_, rfl⟩
  rw [← hωdef, ← hc₂def] at hav ⊢
  have hm := setIntegral_ball_norm_gradient_sq_le_add_norm_setAverage u hr
    ((ball_subset_ball hrR).trans hball)
  rw [← hωdef] at hm
  have hpow : r ^ (n + 1) = r ^ ((n : ℝ) + 1) := by
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [hpow] at hm
  have he : (n : ℝ) + 1 + 2 * α - ((n : ℝ) + 1) = 2 * α := by ring
  rw [he, show (2 : ℝ) * α = α * 2 from mul_comm _ _, Real.rpow_mul hR.le, Real.rpow_two]
  have hr2 : r ^ ((n : ℝ) + 1 + 2 * ((α : ℝ) / 2)) ≤ R ^ (α : ℝ) * r ^ ((n : ℝ) + 1) := by
    rw [Real.rpow_add hr, mul_comm]
    gcongr
    rw [mul_div_cancel₀ _ two_ne_zero]
    exact Real.rpow_le_rpow hr.le hrR α.2
  have hψ' : ∫ y in ball x r, ‖W1p.gradient u y - ⨍ w in ball x r, W1p.gradient u w‖ ^ 2 ≤
      C₁ * θ ^ 2 * R ^ (α : ℝ) * (R ^ (α : ℝ) * r ^ ((n : ℝ) + 1)) :=
    (hψ r hr hrR).trans (mul_le_mul_of_nonneg_left hr2 (by positivity))
  have hav2 : ‖⨍ y in ball x r, W1p.gradient u y‖ ^ 2 ≤ (c₂ * θ * R ^ (α : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hav 2
  calc ∫ y in ball x r, ‖W1p.gradient u y‖ ^ 2
      ≤ 2 * (∫ y in ball x r, ‖W1p.gradient u y - ⨍ w in ball x r, W1p.gradient u w‖ ^ 2) +
          2 * (ω * r ^ ((n : ℝ) + 1)) * ‖⨍ y in ball x r, W1p.gradient u y‖ ^ 2 := hm
    _ ≤ 2 * (C₁ * θ ^ 2 * R ^ (α : ℝ) * (R ^ (α : ℝ) * r ^ ((n : ℝ) + 1))) +
          2 * (ω * r ^ ((n : ℝ) + 1)) * (c₂ * θ * R ^ (α : ℝ)) ^ 2 := by
        gcongr
    _ = (2 * C₁ + 2 * ω * c₂ ^ 2) * θ ^ 2 * (R ^ (α : ℝ)) ^ 2 * r ^ ((n : ℝ) + 1) := by ring

/-- **The mean oscillation of the gradient about one centre.** For `0 < α < 1` there are
`ε₀ > 0` and `C`, depending only on `n`, `α`, `λ` and `Λ`, such that the following holds. Let
`u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `Ω ⊆ ℝ^{n+1}`, with `a` elliptic at `x₀`,
and `a`, `G` `α`-Hölder with constants `K_a`, `K_G` on `ball x₀ R ⊆ Ω`. If
`(K_a R^α)² ≤ ε₀`, `K_G ≤ θ` and `R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)} ≤ θ`, then the mean oscillation of
`∇u` on `closedBall x₀ t` is at most `C θ t^α` for `0 < t ≤ R`. -/
private theorem exists_setAverage_closedBall_norm_gradient_sub_le {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) (lam Lam : ℝ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {Ka KG : ℝ≥0}
      {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
      {R θ : ℝ},
      UniformlyEllipticOn s a lam Lam → x₀ ∈ s →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ R) →
      HolderOnWith KG α G (ball x₀ R) → ball x₀ R ⊆ Omega →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      (Ka * R ^ (α : ℝ)) ^ 2 ≤ ε₀ → (KG : ℝ) ≤ θ →
      R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ ≤ θ → ∀ t, 0 < t → t ≤ R →
        ⨍ y in closedBall x₀ t, ‖W1p.gradient u y - ⨍ w in closedBall x₀ t, W1p.gradient u w‖ ≤
          C * θ * t ^ (α : ℝ) := by
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ measureReal_ball_pos _ _ one_pos
  have hα' : (0 : ℝ) < α := hα
  -- The constants of Morrey's estimate and of the two passes of Campanato's estimate.
  obtain ⟨ε₀, CM, hε₀, hCM, hmor⟩ := exists_setIntegral_ball_norm_gradient_sq_le hα lam Lam (n := n)
  obtain ⟨C₁, hC₁, hpass₁⟩ := exists_setIntegral_ball_norm_gradient_sub_setAverage_sq_le hα hα1
    lam Lam (n := n) (b := (n : ℝ) + 1 - α) (by linarith) hCM hε₀.le
  obtain ⟨C₂, hC₂, hpass₂⟩ := exists_setIntegral_ball_norm_gradient_sub_setAverage_sq_le hα hα1
    lam Lam (n := n) (b := (n : ℝ) + 1) le_rfl (P := 2 * C₁ + 2 * ω *
      ((2 * (2 ^ (n + 1) / (1 - 2 ^ (-((α : ℝ) / 2)))) * √(C₁ / ω) + (√ω)⁻¹)) ^ 2)
    (by positivity) hε₀.le
  refine ⟨ε₀, √(C₂ / ω), hε₀, by positivity, ?_⟩
  intro Omega u a G Ka KG s x₀ R θ h hx₀ haK hGK hball hu hKa hKGθ hNθ t ht htR
  have hR : 0 < R := ht.trans_le htR
  have hθ : 0 ≤ θ := KG.2.trans hKGθ
  have hN : ‖W1p.gradient u‖ ^ 2 ≤ θ ^ 2 * R ^ ((n : ℝ) + 1 + 2 * α) := by
    have hsplit : ‖W1p.gradient u‖ = R ^ (((n : ℝ) + 1) / 2 + α) *
        (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) := by
      rw [← mul_assoc, ← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, one_mul]
    have hsq : (R ^ (((n : ℝ) + 1) / 2 + α)) ^ 2 = R ^ ((n : ℝ) + 1 + 2 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
      congr 1
      push_cast
      ring
    rw [hsplit, mul_pow, hsq, mul_comm]
    gcongr
  have hKG : (KG : ℝ) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ KG.2 hKGθ 2
  -- First pass: Morrey's estimate, then Campanato's estimate with `b = n + 1 - α`.
  have hψ₁ := hpass₁ h hx₀ haK hGK hball hu hKa hN hKG (hmor h hx₀ haK hGK hball hu hKa hN hKG)
  have he₁ : (n : ℝ) + 1 - ((n : ℝ) + 1 - α) = α := by ring
  have he₂ : (n : ℝ) + 1 - α + 2 * α = (n : ℝ) + 1 + 2 * ((α : ℝ) / 2) := by ring
  simp only [he₁, he₂] at hψ₁
  -- Second pass: Campanato's estimate with `b = n + 1`.
  have hψ₂ := hpass₂ h hx₀ haK hGK hball hu hKa hN hKG fun r hr hrR => by
    have := setIntegral_ball_norm_gradient_sq_le_of_setIntegral_le hα u hR hball hθ hC₁ hNθ hψ₁
      hr hrR
    rwa [← hωdef] at this
  refine setAverage_closedBall_norm_gradient_sub_le u ht ((ball_subset_ball htR).trans hball)
    (by positivity) ((hψ₂ t ht htR).trans_eq ?_)
  rw [sub_self, Real.rpow_zero, mul_one, mul_pow, Real.sq_sqrt (div_nonneg hC₂ hω.le), ← hωdef]
  field_simp

end PerCentre

/-- **Interior Schauder estimate for divergence-form equations.** Let `0 < α < 1`, `0 < λ ≤ Λ`
and `M ≥ 0`. There is a constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `M`, such that the
following holds. Let `Ω ⊆ ℝ^{n+1}` be open and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `Ω`, that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function
`φ`. Suppose that the open `R`-thickening `S_R` of a set `S` lies in `Ω`, that the coefficients
`a` are uniformly elliptic with constants `λ`, `Λ` at the points of `S`, that `a` is `α`-Hölder on
`S_R` with constant `K_a`, in the operator norm of the attached bilinear forms, with
`K_a R^α ≤ M`, and that `G` is `α`-Hölder on `S_R` with constant `K_G`. Then the precise
representative of `∇u` is `α`-Hölder on `S`, with constant
`C (K_G + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`.

The precise representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). The exponent of the coefficients
and of `G` passes to `∇u` without loss; this is false for `α = 1`, which is why `α < 1` is
assumed. -/
theorem exists_holderOnWith_preciseRepresentative_gradient_of_uniformlyEllipticOn {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) (lam Lam : ℝ) (M : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {Ka KG : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      UniformlyEllipticOn S a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      HolderOnWith KG α G (thickening R S) → Ka * R ^ (α : ℝ) ≤ M →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (KG + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal α
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  obtain ⟨ε₀, C₀, hε₀, hC₀, hosc⟩ :=
    exists_setAverage_closedBall_norm_gradient_sub_le hα hα1 lam Lam (n := n)
  obtain ⟨c, hc, hasm⟩ := exists_holderOnWith_preciseRepresentative_gradient_of_setAverage_le hα
    (n := n)
  have hα' : (0 : ℝ) < α := hα
  -- The working radius is `κ R`, so that `(K_a (κ R)^α)² ≤ ε₀`.
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (1 + M / √ε₀) ^ (-(α : ℝ)⁻¹) := ⟨_, rfl⟩
  have hM1 : 1 ≤ 1 + (M : ℝ) / √ε₀ := le_add_of_nonneg_right (by positivity)
  have hκ0 : 0 < κ := hκdef ▸ by positivity
  have hκ1 : κ ≤ 1 := hκdef ▸ Real.rpow_le_one_of_one_le_of_nonpos hM1
    (neg_nonpos.2 (inv_nonneg.2 hα'.le))
  have hκα : κ ^ (α : ℝ) = (1 + M / √ε₀)⁻¹ := by
    rw [hκdef, ← Real.rpow_mul (by positivity), neg_mul, inv_mul_cancel₀ hα'.ne',
      Real.rpow_neg_one]
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = κ ^ (-(((n : ℝ) + 1) / 2 + α)) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := hmdef ▸ Real.one_le_rpow_of_pos_of_le_one_of_nonpos hκ0 hκ1 (by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith)
  refine ⟨c * (C₀ + 1) * m, by positivity, ?_⟩
  intro Omega u a G Ka KG S R h haK hGK hKaM hu hR hRS
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁, R₁ = κ * R := ⟨_, rfl⟩
  have hR₁ : 0 < R₁ := hR₁def ▸ mul_pos hκ0 hR
  have hR₁R : R₁ ≤ R := hR₁def ▸ mul_le_of_le_one_left hR.le hκ1
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ,
      θ = R₁ ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ + KG := ⟨_, rfl⟩
  have hθa : R₁ ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ ≤ θ :=
    hθdef ▸ le_add_of_nonneg_right KG.2
  have hθK : (KG : ℝ) ≤ θ := hθdef ▸ le_add_of_nonneg_left (by positivity)
  have hθ : 0 ≤ θ := KG.2.trans hθK
  have hKa₁ : (Ka * R₁ ^ (α : ℝ)) ^ 2 ≤ ε₀ := by
    have h1 : Ka * R₁ ^ (α : ℝ) ≤ √ε₀ := by
      rw [hR₁def, Real.mul_rpow hκ0.le hR.le, hκα, mul_left_comm]
      calc (1 + M / √ε₀)⁻¹ * (Ka * R ^ (α : ℝ)) ≤ (1 + M / √ε₀)⁻¹ * M := by gcongr
        _ ≤ √ε₀ := by
          rw [inv_mul_le_iff₀ (by positivity), add_mul, one_mul,
            div_mul_cancel₀ _ (Real.sqrt_pos.2 hε₀).ne']
          linarith [Real.sqrt_nonneg ε₀]
    calc (Ka * R₁ ^ (α : ℝ)) ^ 2 ≤ √ε₀ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = ε₀ := Real.sq_sqrt hε₀.le
  have hzball : ∀ z ∈ S, ball z R₁ ⊆ thickening R S := fun z hz =>
    (ball_subset_ball hR₁R).trans (ball_subset_thickening hz R)
  -- Campanato's criterion on the working radius `R₁`.
  have hH := hasm hR₁ (by positivity) (fun z hz => (hzball z hz).trans hRS)
    (fun z hz => hosc h hz (haK.mono (hzball z hz)) (hGK.mono (hzball z hz))
      ((hzball z hz).trans hRS) hu hKa₁ hθK hθa)
  refine hH.mono_const (Real.toNNReal_le_toNNReal ?_)
  -- The constant: `R₁^{-(n+1)/2-α} = m R^{-(n+1)/2-α}` with `m ≥ 1`.
  have hR₁m : R₁ ^ (-(((n : ℝ) + 1) / 2 + α)) = m * R ^ (-(((n : ℝ) + 1) / 2 + α)) := by
    rw [hR₁def, Real.mul_rpow hκ0.le hR.le, hmdef]
  have hθm : θ ≤ m * (KG + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) := by
    rw [hθdef, hR₁m]
    have : (KG : ℝ) ≤ m * KG := le_mul_of_one_le_left KG.2 hm1
    nlinarith
  calc c * (C₀ * θ + R₁ ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)
      ≤ c * (C₀ * θ + θ) := by gcongr
    _ = c * (C₀ + 1) * θ := by ring
    _ ≤ c * (C₀ + 1) * (m * (KG + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)) := by
        gcongr
    _ = c * (C₀ + 1) * m * (KG + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) := by ring

/-- **Interior Hölder continuity of the gradient for `-Δu = -div G`.** Let `0 < α < 1`. There is
a constant `C`, depending only on `n` and `α`, such that the following holds. Let `Ω ⊆ ℝ^{n+1}` be
open and let `u ∈ H¹(Ω)` be a weak solution of `-Δu = -div G` in `Ω`, that is
`∫_Ω ⟨∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`, where `G` is `α`-Hölder with constant
`K` on the open `R`-thickening of `S` (the points at distance less than `R` from `S`), which lies
in `Ω`. Then the precise representative of `∇u` is `α`-Hölder on `S`, with constant
`C (K + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`.

This is the case `a = 1` of
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_of_uniformlyEllipticOn`. -/
theorem exists_holderOnWith_preciseRepresentative_gradient {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      HolderOnWith K α G (thickening R S) →
      (∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      0 < R → thickening R S ⊆ Omega →
        HolderOnWith (C * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal α
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  obtain ⟨C, hC, h⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_uniformlyEllipticOn hα hα1 1 1 0 (n := n)
  exact ⟨C, hC, fun hG hu hR hRS => h (uniformlyEllipticOn_const_one_one _)
    ((HolderWith.const (C := 0)).holderOnWith _) hG (by simp) hu hR hRS⟩

end PDE

end TauCeti
