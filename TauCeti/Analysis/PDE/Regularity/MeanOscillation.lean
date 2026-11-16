/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
public import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# Mean oscillation of the gradient for divergence-form equations

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in an open set `Ω ⊆ ℝ^{n+1}`,

that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`, with a bounded measurable
coefficient matrix `a` that need be neither continuous nor symmetric. This file proves Krylov's
estimate for the mean oscillation of `∇u` on concentric balls `B_ρ ⊆ B_r ⊆ Ω`. Fix any constant
matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, and write
`θ(x) = ‖a(x) - A‖` for the deviation of the coefficients from `A`, measured in the operator norm
of the attached bilinear forms `TauCeti.PDE.matrixBilinearForm`, and
`ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²`. Then for `0 < ρ ≤ r` and every constant vector `c`

`ψ(ρ) ≤ 4 D (ρ / r)^(n + 3) ψ(r) + (2 (4 D + 2) / λ²) (∫_{B_r} θ² ‖∇u‖² + ∫_{B_r} ‖G - c‖²)`

with `D = 2^(3n + 13) (n + 2)² (Λ / λ)^((n + 3) / 2)`
(`setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_norm_matrixBilinearForm_sub_le`).
If `θ ≤ K` on `B_r` and `∇u ∈ L^{2q}(B_r)` for a pair of Hölder conjugate exponents `q, q'`,
Hölder's inequality turns the coefficient term into the mean deviation `⨍_{B_r} θ`, and dividing
by the volumes gives the scale-invariant form

`⨍_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ 4 D (ρ / r)² ⨍_{B_r} ‖∇u - (∇u)_{B_r}‖²`
`  + (2 (4 D + 2) / λ²) (r / ρ)^(n + 1) (⨍_{B_r} ‖G - c‖² + E)`

with `E = (K^(2q' - 1) ⨍_{B_r} θ)^(1/q') (⨍_{B_r} ‖∇u‖^(2q))^(1/q)`
(`setAverage_ball_norm_gradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le`; both
theorems are in the `TauCeti.PDE` namespace). The coefficients enter only through `⨍_{B_r} θ`,
which for `A` the average of `a` over `B_r` is a mean oscillation of `a`. So when `a` has small
mean oscillation the gradient oscillates on `B_ρ` like that of a solution of a constant-coefficient
equation, up to the data `G` and a small multiple of a higher average of `‖∇u‖`. Combined with
the Fefferman–Stein inequality for the sharp maximal function and the Hardy–Littlewood maximal
inequality, this is the estimate behind the `W^{1,p}` theory of divergence-form equations whose
coefficients have vanishing mean oscillation.

## The argument

On `B_r` let `w` solve the frozen problem `-∂ᵢ(Aⁱʲ ∂ⱼw) = 0` with the boundary values of `u`. The
mean oscillation of `∇w` decays from `B_r` to `B_ρ` with exponent `n + 3`, and this transfers to
`u` up to the energy distance `∫_{B_r} ‖∇u - ∇w‖²`
(`TauCeti.PDE.setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen`). Since `u` solves the
frozen equation with the field `G - c + (A - a) ∇u`, that distance is at most
`(2 / λ²) (∫_{B_r} θ² ‖∇u‖² + ∫_{B_r} ‖G - c‖²)`
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_norm_gradient_sub_sq_le`). For the averaged form,
Hölder's inequality with exponents `q'` and `q` bounds `∫ θ² ‖∇u‖²` by
`(∫ θ^(2q'))^(1/q') (∫ ‖∇u‖^(2q))^(1/q)`, and `θ^(2q') ≤ K^(2q' - 1) θ` because `0 ≤ θ ≤ K`
(`TauCeti.integral_sq_mul_norm_sq_le_of_ae_le`).

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475 (mean oscillation estimates for divergence-form
  equations with coefficients of vanishing mean oscillation).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, AMS, 2008.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.3 (comparison with the frozen problem).
-/

public section

open InnerProductSpace MeasureTheory Metric TopologicalSpace
open scoped Distributions Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {x₀ c : EuclideanSpace ℝ (Fin (n + 1))} {ρ r lam Lam K : ℝ}

/-- **Krylov's mean oscillation estimate for the gradient.** Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on an open set `Ω ⊆ ℝ^{n+1}`, that is
`∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`, let `ball x₀ r ⊆ Ω`, and let `A` be a
constant matrix, uniformly elliptic with constants `0 < λ ≤ Λ`. Suppose that `a` is measurable on
`B_r = ball x₀ r` and that the deviation `θ(x) = ‖a(x) - A‖`, in the operator norm of the attached
bilinear forms, is bounded there. Then for `0 < ρ ≤ r` and every constant vector `c` with
`G - c ∈ L²(B_r)`, the square mean oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` satisfies

`ψ(ρ) ≤ 4 D (ρ / r)^(n + 3) ψ(r) + (2 (4 D + 2) / λ²) (∫_{B_r} θ² ‖∇u‖² + ∫_{B_r} ‖G - c‖²)`,

with `D = 2^(3n + 13) (n + 2)² (Λ / λ)^((n + 3) / 2)`. For `a = A` this is
`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_forall_energyFormH1_eq`,
up to the factor `2`. -/
theorem setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_norm_matrixBilinearForm_sub_le
    (hA : UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (ball x₀ r)))
    (haK : ∀ x ∈ ball x₀ r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K)
    {u : W1p volume Omega 2}
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hball : ball x₀ r ⊆ Omega) (hGc : MemLp (fun x => G x - c) 2 (volume.restrict (ball x₀ r)))
    (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) * (ρ / r) ^ (n + 3) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
        2 * (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 *
          ((∫ x in ball x₀ r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ^ 2 *
              ‖W1p.gradient u x‖ ^ 2) +
            ∫ x in ball x₀ r, ‖G x - c‖ ^ 2) := by
  have hr : 0 < r := hρ.trans_le hρr
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hB : (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ≤ Omega := hball
  -- The replacement `w` of `u` on `B_r` for the frozen operator.
  obtain ⟨w, ⟨hwu, hw⟩, -⟩ :=
    UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (Omega := ⟨ball x₀ r, isOpen_ball⟩) (b := 0) (c := 0) hA aestronglyMeasurable_const
      aestronglyMeasurable_const aestronglyMeasurable_const (beta := 0) (fun _ _ => by simp)
      (gamma := 0) (fun _ _ => by simp) (fun _ _ => le_rfl) subset_rfl (by simpa using hA.pos) 0
      (W1p.restrictL hB u)
  have hw0 : ∀ v : W1p0 volume (⟨ball x₀ r, isOpen_ball⟩ : Opens _) 2,
      energyFormH1 (fun _ => A) 0 0 w (v : W1p volume _ 2) = 0 := fun v => by
    rw [hw v, zero_apply]
  have huw : W1p.restrictL hB u - w ∈ w1p0Submodule volume _ 2 := by
    have h := (ClosedSubmodule.mem_toSubmodule_iff (w - W1p.restrictL hB u)
      (w1p0Submodule volume _ 2)).2 hwu
    exact (ClosedSubmodule.mem_toSubmodule_iff _ _).1 (sub_mem_comm_iff.1 h)
  have hAu : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2 :=
    fun ξ => (le_abs_self _).trans
      (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le (hA.upper_bound hx₀) ξ)
  -- The mean oscillation of `∇u` decays up to the energy distance from `w`, and that distance is
  -- controlled by the coefficient deviation and the data.
  have hdec := setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen (u := u) hA.pos
    (hA.lower_bound hx₀) hAu hw0 hball hρ hρr
  have hcomp := UniformlyEllipticOn.setIntegral_norm_gradient_sub_sq_le
    (Omega := Omega) (B := ⟨ball x₀ r, isOpen_ball⟩) hA hB ha haK hu hGc huw hw0
  simp only [Opens.coe_mk] at hcomp
  have hD : (2 : ℝ) ^ (3 * (n + 1) + 10) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 *
      √(Lam / lam) ^ (n + 1 + 2) = 2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3) := by
    push_cast
    ring
  rw [hD] at hdec
  refine hdec.trans (le_of_le_of_eq (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hcomp (by positivity))) ?_)
  ring

/-- **Krylov's mean oscillation estimate for the gradient, averaged form.** Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on an open set `Ω ⊆ ℝ^{n+1}`, let `ball x₀ r ⊆ Ω`, and let `A` be a
constant matrix, uniformly elliptic with constants `0 < λ ≤ Λ`. Suppose that `a` is measurable on
`B_r = ball x₀ r` with `θ(x) = ‖a(x) - A‖ ≤ K` there, in the operator norm of the attached bilinear
forms, and that `∇u ∈ L^{2q}(B_r)` for a pair of Hölder conjugate exponents `q, q'`. Then for
`0 < ρ ≤ r` and every constant vector `c` with `G - c ∈ L²(B_r)`

`⨍_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ 4 D (ρ / r)² ⨍_{B_r} ‖∇u - (∇u)_{B_r}‖²`
`  + (2 (4 D + 2) / λ²) (r / ρ)^(n + 1) (⨍_{B_r} ‖G - c‖² + E)`

with `E = (K^(2q' - 1) ⨍_{B_r} θ)^(1/q') (⨍_{B_r} ‖∇u‖^(2q))^(1/q)` and
`D = 2^(3n + 13) (n + 2)² (Λ / λ)^((n + 3) / 2)`. Every average is invariant under dilations, and
the coefficients enter only through the mean deviation `⨍_{B_r} θ`. -/
theorem setAverage_ball_norm_gradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le
    (hA : UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (ball x₀ r)))
    (haK : ∀ x ∈ ball x₀ r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K)
    {u : W1p volume Omega 2}
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hball : ball x₀ r ⊆ Omega) (hGc : MemLp (fun x => G x - c) 2 (volume.restrict (ball x₀ r)))
    {q q' : ℝ} (hq : q.HolderConjugate q')
    (hgq : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      (ENNReal.ofReal (2 * q)) (volume.restrict (ball x₀ r)))
    (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ⨍ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) * (ρ / r) ^ 2 *
          (⨍ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
        2 * (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 *
          (r / ρ) ^ (n + 1) *
          ((⨍ x in ball x₀ r, ‖G x - c‖ ^ 2) +
            (K ^ (2 * q' - 1) *
                ⨍ x in ball x₀ r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖) ^ q'⁻¹ *
              (⨍ x in ball x₀ r, ‖W1p.gradient u x‖ ^ (2 * q)) ^ q⁻¹) := by
  have hr : 0 < r := hρ.trans_le hρr
  set μr := volume.restrict (ball x₀ r)
  set g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set θ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun x => ‖matrixBilinearForm (a x) - matrixBilinearForm A‖
  have : IsFiniteMeasure μr := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hK : 0 ≤ K :=
    (norm_nonneg (matrixBilinearForm (a x₀) - matrixBilinearForm A)).trans
      (haK x₀ (mem_ball_self hr))
  have hθm : AEStronglyMeasurable θ μr := by
    have h : Continuous
        fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => matrixBilinearForm (M - A) :=
      continuous_matrixBilinearForm.comp (continuous_sub_right A)
    simpa only [θ, matrixBilinearForm_sub] using
      (Continuous.norm (E := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) h).comp_aestronglyMeasurable ha
  have hθ : ∀ᵐ x ∂μr, 0 ≤ θ x ∧ θ x ≤ K :=
    (ae_restrict_mem measurableSet_ball).mono fun x hx =>
      ⟨norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A), haK x hx⟩
  -- Hölder's inequality with exponents `q'` and `q` bounds the coefficient term `∫ θ² ‖∇u‖²` of
  -- the frozen comparison.
  have hΘ := integral_sq_mul_norm_sq_le_of_ae_le hq hθm hθ hgq
  set Iθ := ∫ x in ball x₀ r, θ x
  set Ig := ∫ x in ball x₀ r, ‖g x‖ ^ (2 * q)
  have hIg : 0 ≤ Ig := integral_nonneg fun x => by positivity
  have key :=
    setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_norm_matrixBilinearForm_sub_le
      hA ha haK hu hball hGc hρ hρr
  -- Pass to averages, using `|B_ρ| = (ρ / r)^(n + 1) |B_r|`.
  set V : ℝ := volume.real (ball x₀ r)
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume x₀ hr).ne' measure_ball_lt_top.ne
  have hVρ : volume.real (ball x₀ ρ) = (ρ / r) ^ (n + 1) * V := by
    simp only [V, measureReal_def, Measure.addHaar_ball_of_pos volume x₀ hρ,
      Measure.addHaar_ball_of_pos volume x₀ hr, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ.le _), ENNReal.toReal_ofReal (pow_nonneg hr.le _),
      div_pow]
    field_simp
  have havg : ∀ (t : ℝ) (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
      ⨍ x in ball x₀ t, f x = (volume.real (ball x₀ t))⁻¹ * ∫ x in ball x₀ t, f x :=
    fun t f => by rw [setAverage_eq, smul_eq_mul]
  rw [havg ρ (fun x => ‖g x - ⨍ y in ball x₀ ρ, g y‖ ^ 2),
    havg r (fun x => ‖g x - ⨍ y in ball x₀ r, g y‖ ^ 2), havg r (fun x => ‖G x - c‖ ^ 2),
    havg r θ, havg r (fun x => ‖g x‖ ^ (2 * q)), hVρ]
  have hsplit : (K ^ (2 * q' - 1) * (V⁻¹ * Iθ)) ^ q'⁻¹ * (V⁻¹ * Ig) ^ q⁻¹ =
      V⁻¹ * ((K ^ (2 * q' - 1) * Iθ) ^ q'⁻¹ * Ig ^ q⁻¹) := by
    rw [mul_left_comm, Real.mul_rpow (inv_nonneg.2 hV.le)
        (mul_nonneg (Real.rpow_nonneg hK _) (integral_nonneg_of_ae (hθ.mono fun x hx => hx.1))),
      Real.mul_rpow (inv_nonneg.2 hV.le) hIg, mul_mul_mul_comm, ← Real.rpow_add (inv_pos.2 hV),
      hq.symm.inv_add_inv_eq_one, Real.rpow_one]
  rw [hsplit]
  have hs : 0 < ρ / r := div_pos hρ hr
  refine (mul_le_mul_of_nonneg_left (key.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add hΘ le_rfl) (by positivity)))) (by positivity)).trans_eq
    ?_
  have hlam : lam ≠ 0 := hA.pos.ne'
  have hV0 : V ≠ 0 := hV.ne'
  rw [← inv_div ρ r]
  simp only [g, V] at hV0 ⊢
  generalize ρ / r = s at hs ⊢
  rw [inv_pow]
  field_simp
  ring

end PDE

end TauCeti
