/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.PDE.UniformEllipticity
import TauCeti.Analysis.PDE.LowerOrder

/-!
# The pointwise integrand of a divergence-form energy bilinear form

For a divergence-form operator `L u = -∂ⱼ(aⁱʲ ∂ᵢ u) + bⁱ ∂ᵢ u + c u`, the weak (energy)
bilinear form is

`a(u, v) = ∫_Ω (aⁱʲ ∂ᵢu ∂ⱼv + bⁱ ∂ᵢu v + c u v)`,

whose integrand at a point `x` depends only on the *jets* `(u(x), ∇u(x))` and
`(v(x), ∇v(x))`, that is, on pairs in `ℝ × EuclideanSpace ℝ n`. This file assembles the
three pointwise coefficient forms already available

* the principal matrix form `matrixBilinearForm (a x)` (in
  `TauCeti.Analysis.PDE.UniformEllipticity`),
* the drift form `driftForm (b x)` and the mass form `massForm (c x)` (in
  `TauCeti.Analysis.PDE.LowerOrder`),

into a single bundled continuous bilinear form on jets, `energyIntegrand (a x) (b x) (c x)`,
matching `(U, V) ↦ ⟨a(x) U.2, V.2⟩ + ⟪b(x), U.2⟫ V.1 + c(x) U.1 V.1`, where `U.2 = ∇u`,
`U.1 = u`. Integrating this jet form over `Ω` against the jets of `u` and `v` recovers the
energy bilinear form, so this is the pointwise seed of Lane D's weak formulation.

The two estimates the energy method needs are proved pointwise, with their constants left
explicit (never hidden in a `∃ C`):

* **boundedness**: the operator norm of the jet form is at most `Λ + β + γ`, the sum of the
  ellipticity, drift, and mass constants;
* **Gårding's inequality (pointwise)**: with a sign condition `c ≥ 0` on the mass
  coefficient, the diagonal of the jet form is bounded below by
  `(λ/2)‖∇u‖² − (β²/2λ)|u|²`, the integrand-level version of Gårding's
  `a(u, u) ≥ α‖u‖²_{H¹} − K‖u‖²_{L²}`. The drift is absorbed by Young's inequality, paid
  for out of half of the ellipticity floor.

## Main declarations

* `TauCeti.PDE.energyIntegrand`: the bundled jet bilinear form of a divergence-form operator.
* `TauCeti.PDE.energyIntegrand_apply`, `TauCeti.PDE.energyIntegrand_self`: its value and its
  diagonal value.
* `TauCeti.PDE.energyIntegrand_one_zero_zero_apply`,
  `TauCeti.PDE.energyIntegrand_one_zero_zero_self`: the Laplacian model `−Δ`, whose jet form
  is the Dirichlet integrand `⟨∇u, ∇v⟩`, with diagonal `‖∇u‖²`.
* `TauCeti.PDE.UniformlyEllipticOn.norm_energyIntegrand_apply_le`,
  `TauCeti.PDE.UniformlyEllipticOn.opNorm_energyIntegrand_le`: boundedness with explicit
  constant `Λ + β + γ`.
* `TauCeti.PDE.UniformlyEllipticOn.garding_energyIntegrand_self`: the pointwise Gårding
  lower bound on the diagonal.
-/

namespace TauCeti

namespace PDE

open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- The pointwise weak-form (energy) integrand of a divergence-form operator
`L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u`, as a bundled continuous bilinear form on jets
`(value, gradient) ∈ ℝ × EuclideanSpace ℝ n`.

On jets `U = (u, ∇u)` and `V = (v, ∇v)` it evaluates to
`⟨a ∇u, ∇v⟩ + ⟪b, ∇u⟫ v + c u v`, the integrand of `a(u, v)`. Bundling it as a
`ContinuousLinearMap` lets it feed Mathlib's bounded-bilinear-form and Lax--Milgram APIs
once the energy form is integrated over the Sobolev space. -/
noncomputable def energyIntegrand (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ) :
    (ℝ × EuclideanSpace ℝ n) →L[ℝ] (ℝ × EuclideanSpace ℝ n) →L[ℝ] ℝ :=
  (matrixBilinearForm A).flip.bilinearComp
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ n))
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ n))
    + (driftForm b).flip.bilinearComp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ n))
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ n))
    + (massForm c).bilinearComp
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ n))
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ n))

/-- The jet form evaluates to `⟨a ∇u, ∇v⟩ + ⟪b, ∇u⟫ v + c u v` on jets `U`, `V`. -/
@[simp]
lemma energyIntegrand_apply (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ)
    (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand A b c U V
      = matrixBilinearForm A V.2 U.2 + driftForm b V.1 U.2 + massForm c U.1 V.1 := by
  simp [energyIntegrand]

/-- The diagonal of the jet form, the energy density `⟨a ∇u, ∇u⟩ + ⟪b, ∇u⟫ u + c u²`. -/
lemma energyIntegrand_self (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ)
    (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand A b c U U
      = A.toQuadraticForm' U.2 + ⟪b, U.2⟫_ℝ * U.1 + c * U.1 ^ 2 := by
  rw [energyIntegrand_apply, matrixBilinearForm_self, driftForm_apply, massForm_apply]
  ring

/-- The Laplacian model `−Δ` (`a = 1`, no drift, no mass) has jet form the Dirichlet
integrand `⟨∇u, ∇v⟩`. -/
@[simp]
lemma energyIntegrand_one_zero_zero_apply (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (1 : Matrix n n ℝ) 0 0 U V = V.2 ⬝ᵥ U.2 := by
  simp [energyIntegrand_apply]

/-- The diagonal of the Laplacian model's jet form is the Dirichlet energy density `‖∇u‖²`. -/
lemma energyIntegrand_one_zero_zero_self (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (1 : Matrix n n ℝ) 0 0 U U = ‖U.2‖ ^ 2 := by
  rw [energyIntegrand_self, toQuadraticForm'_one]
  simp

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {lam Lam beta gamma : ℝ}

/-- Pointwise boundedness of the jet form with explicit constant `Λ + β + γ`: at every
point of the domain, the principal, drift, and mass contributions are each controlled by
the corresponding constant times the jet norms. -/
lemma norm_energyIntegrand_apply_le (he : UniformlyEllipticOn Ω a lam Lam)
    (hbc : LowerOrderBoundedOn Ω b c beta gamma) {x : X} (hx : x ∈ Ω)
    (U V : ℝ × EuclideanSpace ℝ n) :
    ‖energyIntegrand (a x) (b x) (c x) U V‖ ≤ (Lam + beta + gamma) * ‖U‖ * ‖V‖ := by
  have step : ∀ {K p q : ℝ}, 0 ≤ K → 0 ≤ p → 0 ≤ q → p ≤ ‖U‖ → q ≤ ‖V‖ →
      K * p * q ≤ K * ‖U‖ * ‖V‖ := by
    intro K p q hK hp hq hpU hqV
    calc K * p * q = K * (p * q) := by ring
      _ ≤ K * (‖U‖ * ‖V‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hpU hqV hq (hp.trans hpU)) hK
      _ = K * ‖U‖ * ‖V‖ := by ring
  have hmat : ‖matrixBilinearForm (a x) V.2 U.2‖ ≤ Lam * ‖U‖ * ‖V‖ := by
    have h := he.norm_point_matrixBilinearForm_le hx V.2 U.2
    rw [mul_right_comm] at h
    exact h.trans (step he.upper_nonneg (norm_nonneg _) (norm_nonneg _)
      (norm_snd_le U) (norm_snd_le V))
  have hdrift : ‖driftForm (b x) V.1 U.2‖ ≤ beta * ‖U‖ * ‖V‖ := by
    have h := hbc.norm_driftForm_le hx V.1 U.2
    rw [mul_right_comm] at h
    exact h.trans (step hbc.beta_nonneg (norm_nonneg _) (norm_nonneg _)
      (norm_snd_le U) (norm_fst_le V))
  have hmass : ‖massForm (c x) U.1 V.1‖ ≤ gamma * ‖U‖ * ‖V‖ := by
    have h := hbc.norm_massForm_le hx U.1 V.1
    exact h.trans (step hbc.gamma_nonneg (norm_nonneg _) (norm_nonneg _)
      (norm_fst_le U) (norm_fst_le V))
  rw [energyIntegrand_apply]
  calc ‖matrixBilinearForm (a x) V.2 U.2 + driftForm (b x) V.1 U.2 + massForm (c x) U.1 V.1‖
      ≤ ‖matrixBilinearForm (a x) V.2 U.2 + driftForm (b x) V.1 U.2‖
          + ‖massForm (c x) U.1 V.1‖ := norm_add_le _ _
    _ ≤ ‖matrixBilinearForm (a x) V.2 U.2‖ + ‖driftForm (b x) V.1 U.2‖
          + ‖massForm (c x) U.1 V.1‖ := by gcongr; exact norm_add_le _ _
    _ ≤ Lam * ‖U‖ * ‖V‖ + beta * ‖U‖ * ‖V‖ + gamma * ‖U‖ * ‖V‖ :=
        add_le_add (add_le_add hmat hdrift) hmass
    _ = (Lam + beta + gamma) * ‖U‖ * ‖V‖ := by ring

/-- The operator norm of the jet form is at most `Λ + β + γ`. This is the boundedness
hypothesis of Lax--Milgram, with the constant explicit in the ellipticity, drift, and mass
bounds. -/
lemma opNorm_energyIntegrand_le (he : UniformlyEllipticOn Ω a lam Lam)
    (hbc : LowerOrderBoundedOn Ω b c beta gamma) {x : X} (hx : x ∈ Ω) :
    ‖energyIntegrand (a x) (b x) (c x)‖ ≤ Lam + beta + gamma := by
  refine (energyIntegrand (a x) (b x) (c x)).opNorm_le_bound₂
    (_root_.add_nonneg (_root_.add_nonneg he.upper_nonneg hbc.beta_nonneg) hbc.gamma_nonneg) ?_
  intro U V
  exact he.norm_energyIntegrand_apply_le hbc hx U V

/-- **Pointwise Gårding inequality.** With a nonnegative mass coefficient (`c ≥ 0`), the
diagonal of the jet form is bounded below by `(λ/2)‖∇u‖² − (β²/2λ)|u|²`. The ellipticity
floor `λ‖∇u‖²` pays for the drift term via Young's inequality, leaving half the floor and a
mass defect proportional to `β²/λ`. Integrating over `Ω` this is Gårding's inequality
`a(u, u) ≥ (λ/2)‖∇u‖²_{L²} − (β²/2λ)‖u‖²_{L²}`. -/
lemma garding_energyIntegrand_self (he : UniformlyEllipticOn Ω a lam Lam)
    (hb : DriftBoundedOn Ω b beta) (hc : NonnegMassOn Ω c gamma) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2
      ≤ energyIntegrand (a x) (b x) (c x) U U := by
  rw [energyIntegrand_self]
  have hlam := he.pos
  have hQ : lam * ‖U.2‖ ^ 2 ≤ (a x).toQuadraticForm' U.2 := he.lower_bound hx U.2
  have hM : 0 ≤ c x * U.1 ^ 2 := mul_nonneg (hc.nonneg hx) (sq_nonneg _)
  have hbip : |⟪b x, U.2⟫_ℝ| ≤ beta * ‖U.2‖ :=
    (abs_real_inner_le_norm (b x) U.2).trans
      (mul_le_mul_of_nonneg_right (hb.bound hx) (norm_nonneg _))
  have hD : -(beta * ‖U.2‖ * |U.1|) ≤ ⟪b x, U.2⟫_ℝ * U.1 := by
    have habs : |⟪b x, U.2⟫_ℝ * U.1| ≤ beta * ‖U.2‖ * |U.1| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hbip (abs_nonneg _)
    have := neg_abs_le (⟪b x, U.2⟫_ℝ * U.1)
    linarith
  have hYoung : beta * ‖U.2‖ * |U.1| ≤
      lam / 2 * ‖U.2‖ ^ 2 + beta ^ 2 / (2 * lam) * U.1 ^ 2 := by
    have hkey := two_mul_le_add_sq (lam * ‖U.2‖) (beta * |U.1|)
    rw [mul_pow, mul_pow, sq_abs] at hkey
    have h2lam : (0 : ℝ) < 2 * lam := mul_pos two_pos hlam
    rw [← sub_nonneg]
    have expand : lam / 2 * ‖U.2‖ ^ 2 + beta ^ 2 / (2 * lam) * U.1 ^ 2
        - beta * ‖U.2‖ * |U.1|
        = (lam ^ 2 * ‖U.2‖ ^ 2 + beta ^ 2 * U.1 ^ 2
            - 2 * lam * beta * ‖U.2‖ * |U.1|) / (2 * lam) := by
      field_simp
    rw [expand]
    apply div_nonneg _ h2lam.le
    nlinarith [hkey]
  nlinarith [hQ, hM, hD, hYoung]

end UniformlyEllipticOn

end PDE

end TauCeti
