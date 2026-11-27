/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Basic
import TauCeti.Analysis.PDE.DirichletProblem.LpEstimate
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.EnergyForm.SmallDrift
import TauCeti.Analysis.PDE.FundamentalSolution.Divergence
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball

/-!
# Krylov's whole-space `W^{1,p}` estimate with a zero-order shift

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants
`0 < λ ≤ Λ`, neither symmetric nor continuous in general, whose mean oscillation is small below a
radius `r₀`: on every ball `B` of radius at most `r₀` some constant elliptic matrix `A` has mean
deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Coefficients of vanishing mean oscillation satisfy this for
every `δ > 0` once `r₀` is small. This file proves, for `2 < p < ∞`, Krylov's whole-space estimate
for the equation with a zero-order shift `κ > 0`,

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G` in `ℝ^{n+1}`:

if `κ ≥ 16 / r₀²`, then every `u ∈ H¹(ℝ^{n+1})` solving it weakly, with `f, G ∈ L²` and
`∇u ∈ Lᵖ`, satisfies

`‖∇u‖_{Lᵖ} + √κ ‖u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + κ^{-1/2} ‖f‖_{Lᵖ})`

(`TauCeti.PDE.exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_setAverage_le`), with `C`
and the oscillation threshold `δ` depending only on `n`, `p`, `λ` and `Λ`. Both sides scale in
the same way under dilations, which is why the threshold for `κ` is a multiple of `r₀⁻²`. Unlike
the unshifted estimate `TauCeti.PDE.exists_eLpNorm_gradient_le_eLpNorm_value_of_setAverage_le`,
the right side does not contain `u`, and it admits a scalar datum `f`.

On the way it proves the interior estimate with a scalar datum: if `u ∈ H¹(Ω)` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly in `Ω`, `B(x₀, 2R) ⊆ Ω` and `4 R ≤ r₀`, then

`‖∇u‖_{Lᵖ(B_{R/2})} ≤ C (‖G‖_{Lᵖ(B_{2R})} + R ‖f‖_{Lᵖ(B_{2R})} + R⁻¹ ‖u‖_{Lᵖ(B_{2R})})`

(`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_scalar_forcing_of_setAverage_le`), where
`∇u ∈ Lᵖ(B_R)` is an a priori hypothesis.

## The argument

* **The scalar datum as a divergence.** On `B = B(x₀, 2R)` the datum `f` is minus the divergence
  of the gradient `H` of the Newtonian potential of `f 1_B`, with `‖H‖_{Lᵖ(B)} ≤ 4 (n + 1) R
  ‖f‖_{Lᵖ(B)}` (`TauCeti.exists_eLpNorm_restrict_le_and_integral_inner_gradient_eq`). So on `B`
  the restricted solution solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div (G + H)`, and the interior estimate in
  divergence form (`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_value_of_setAverage_le`)
  applies.
* **The whole space.** The shifted equation is the unshifted one with the scalar datum `f - κ u`.
  At the radius `R = κ^{-1/2}`, which satisfies `4 R ≤ r₀` exactly when `κ ≥ 16 / r₀²`, the
  interior estimates read `‖∇u‖_{Lᵖ(B_{R/2})} ≲ ‖G‖ + κ^{-1/2} ‖f‖ + √κ ‖u‖` on `B_{2R}`, with all
  three terms of the same scaling, and integrating them over all centres
  (`TauCeti.eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add`) gives the same bound on `ℝ^{n+1}`.
* **The zero-order term.** Testing the equation against a truncation of `|u|^{p-2} u` bounds
  `√κ ‖u‖_{Lᵖ} ≤ κ^{-1/2} ‖f‖_{Lᵖ} + √((p - 1) / (4 λ)) ‖G‖_{Lᵖ}`
  (`TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_forall_energyFormH1_eq`), which removes
  `u` from the right side.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.8.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set TopologicalSpace Matrix
open scoped ENNReal NNReal ContDiff Distributions Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The ball `B(x₀, r)` as an open set. -/
private def ballOpens (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) :
    Opens (EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨ball x₀ r, isOpen_ball⟩

/-- On a ball `B(x₀, r)`, a square-integrable `f` is minus the divergence of a field `H`, tested
against `C¹` functions supported in the ball, with `‖H‖_{Lᵖ(B(x₀, r))} ≤ 2 (n + 1) r
‖f‖_{Lᵖ(B(x₀, r))}` for every `1 ≤ p`. -/
private theorem exists_field_ball {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hr : 0 ≤ r)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : MemLp f 2 (volume.restrict (ball x₀ r))) :
    ∃ H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (∀ {p : ℝ≥0∞}, 1 ≤ p → eLpNorm H p (volume.restrict (ball x₀ r)) ≤
        ENNReal.ofReal (2 * (n + 1) * r) * eLpNorm f p (volume.restrict (ball x₀ r))) ∧
      ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ ball x₀ r →
          ∫ x in ball x₀ r, f x * φ x = ∫ x in ball x₀ r, ⟪H x, ∇ φ x⟫_ℝ := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- The datum cut off outside the ball is integrable with compact support.
  have hhi : Integrable ((ball x₀ r).indicator f) volume :=
    (integrable_indicator_iff measurableSet_ball).2 (hf.integrable one_le_two)
  have hhc : HasCompactSupport ((ball x₀ r).indicator f) :=
    HasCompactSupport.intro (isCompact_closedBall x₀ r) fun x hx =>
      indicator_of_notMem (fun hxB => hx (ball_subset_closedBall hxB)) f
  obtain ⟨H, -, hHle, hHeq⟩ := exists_eLpNorm_restrict_le_and_integral_inner_gradient_eq
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) hhi hhc
  refine ⟨H, fun {p} hp => ?_, fun φ hφ1 hφc hφs => ?_⟩
  · refine (hHle isBounded_ball (fun x hx => indicator_of_notMem hx f) hp).trans ?_
    rw [eLpNorm_congr_ae (indicator_ae_eq_restrict measurableSet_ball.nullMeasurableSet)]
    gcongr ENNReal.ofReal ?_ * _
    rw [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_left (Metric.diam_ball (x := x₀) hr)
      (by positivity : (0 : ℝ) ≤ n + 1)]
  calc ∫ x in ball x₀ r, f x * φ x
      = ∫ x, (ball x₀ r).indicator f x * φ x := by
        rw [← integral_indicator measurableSet_ball]
        exact integral_congr_ae (ae_of_all _ fun x => indicator_mul_left _ _ _)
    _ = ∫ x, ⟪H x, ∇ φ x⟫_ℝ := (hHeq φ hφ1 hφc).symm
    _ = ∫ x in ball x₀ r, ⟪H x, ∇ φ x⟫_ℝ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [gradient_of_notMem_tsupport fun h => hx (hφs h), inner_zero_right]).symm

/-- On the ball `B(x₀, 2R) ⊆ Ω`, a solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` on `Ω` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div (G + H)` for a field `H` with `‖H‖_{Lᵖ(B(x₀, 2R))} ≤ 4 (n + 1) R
‖f‖_{Lᵖ(B(x₀, 2R))}` for every `1 ≤ p`. -/
private theorem exists_field_forall_energyFormH1_restrictL_eq
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hR : 0 < R) (hΩ : ballOpens x₀ (2 * R) ≤ Ω)
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict (ball x₀ (2 * R))))
    {u : W1p volume Ω 2} {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : MemLp G 2 (volume.restrict (ball x₀ (2 * R))))
    (hf : MemLp f 2 (volume.restrict (ball x₀ (2 * R))))
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume +
        ∫ x in Ω, f x * φ x ∂volume) :
    ∃ H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (∀ {p : ℝ≥0∞}, 1 ≤ p → eLpNorm H p (volume.restrict (ball x₀ (2 * R))) ≤
        ENNReal.ofReal (4 * (n + 1) * R) * eLpNorm f p (volume.restrict (ball x₀ (2 * R)))) ∧
      ∀ φ : 𝓓(ballOpens x₀ (2 * R), ℝ),
        energyFormH1 a 0 0 (W1p.restrictL hΩ u)
            (W1p.ofTestFunctionₗ volume (ballOpens x₀ (2 * R)) 2 φ) =
          ∫ x in ballOpens x₀ (2 * R),
            ⟪G x + H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  set B := ball x₀ (2 * R)
  have hBc : (ballOpens x₀ (2 * R) : Set (EuclideanSpace ℝ (Fin (n + 1)))) = B := rfl
  have : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨H, hHle, hHφ⟩ := exists_field_ball (by positivity : 0 ≤ 2 * R) hf
  have hc : (2 * ((n : ℝ) + 1) * (2 * R)) = 4 * (n + 1) * R := by ring
  refine ⟨H, fun {p} hp => hc ▸ hHle hp, fun φ => ?_⟩
  have hH1 : MemLp H 1 (volume.restrict B) := (hHle le_rfl).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_one_iff_integrable.2
      (hf.integrable one_le_two)).eLpNorm_lt_top)
  -- The weak equation on the ball, tested against `φ`.
  have hres := forall_energyFormH1_restrictL_eq_setIntegral_sub_setIntegral_neg_inner hΩ ha hu hG
    hf ⟨W1p.ofTestFunctionₗ volume (ballOpens x₀ (2 * R)) 2 φ,
      W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  have h1 : ∫ x in (ballOpens x₀ (2 * R) : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      f x * W1p.value (W1p.ofTestFunctionₗ volume (ballOpens x₀ (2 * R)) 2 φ) x =
      ∫ x in B, f x * φ x :=
    integral_congr_ae ((W1p.value_ofTestFunctionₗ_ae (p := 2) φ).mono
      fun x hx => congrArg (f x * ·) hx)
  have h2 : ∫ x in (ballOpens x₀ (2 * R) : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ⟪-G x, W1p.gradient (W1p.ofTestFunctionₗ volume (ballOpens x₀ (2 * R)) 2 φ) x⟫_ℝ =
      -∫ x in B, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
    rw [← integral_neg]
    exact integral_congr_ae ((gradientTestFunctionLp_apply_ae (mu := volume) 2 φ).mono
      fun x hx => by dsimp only; rw [W1p.gradient_ofTestFunctionₗ, hx, inner_neg_left])
  rw [hres, h1, h2, sub_neg_eq_add, add_comm, hBc]
  simp only [inner_add_left]
  rw [integral_add (integrable_inner_gradient_testFunction hG φ)
    (integrable_inner_gradient_testFunction hH1 φ)]
  -- The scalar datum is replaced by the pairing with `H`.
  rw [hHφ φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset]

/-- **The interior `W^{1,p}` estimate with a scalar datum, for coefficients of small mean
oscillation.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only
on `n`, `p`, `λ` and `Λ`, with the following property. Let `a` be a measurable coefficient matrix
on `ℝ^{n+1}`, bounded by `Λ`, such that on every ball `B` of radius at most `r₀` some constant
matrix `A`, uniformly elliptic with constants `λ, Λ`, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from
`a`. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly in `Ω`, let `B(x₀, 2R) ⊆ Ω` with
`4 R ≤ r₀`, let `a` be uniformly elliptic with constants `λ, Λ` on `B(x₀, 2R)`, let `f` and `G` be
square integrable on `B(x₀, 2R)`, and let `∇u` lie in `Lᵖ(B(x₀, R))`. Then

`‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C (‖G‖_{Lᵖ(B(x₀, 2R))} + R ‖f‖_{Lᵖ(B(x₀, 2R))} +
  R⁻¹ ‖u‖_{Lᵖ(B(x₀, 2R))})`.

The membership `∇u ∈ Lᵖ(B(x₀, R))` is an a priori assumption. The scalar datum enters with the
factor `R`, the scaling of one derivative. -/
theorem exists_eLpNorm_gradient_ball_le_of_scalar_forcing_of_setAverage_le {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
          {R : ℝ}, UniformlyEllipticOn (ball x₀ (2 * R)) a lam Lam →
          4 * R ≤ r₀ → ball x₀ (2 * R) ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
        ∀ (u : W1p volume Ω 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
          MemLp G 2 (volume.restrict (ball x₀ (2 * R))) →
          MemLp f 2 (volume.restrict (ball x₀ (2 * R))) →
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume +
              ∫ x in Ω, f x * φ x ∂volume) →
          MemLp (W1p.gradient u) p (volume.restrict (ball x₀ R)) →
          eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ≤
            C * (eLpNorm G p (volume.restrict (ball x₀ (2 * R))) +
              ENNReal.ofReal R * eLpNorm f p (volume.restrict (ball x₀ (2 * R))) +
              ENNReal.ofReal R⁻¹ *
                eLpNorm (W1p.value u) p (volume.restrict (ball x₀ (2 * R)))) := by
  obtain ⟨C₁, δ, hδ, h₁⟩ :=
    exists_eLpNorm_gradient_ball_le_eLpNorm_value_of_setAverage_le (n := n) hp hp_top lam Lam
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  refine ⟨C₁ * (4 * (n + 1)), δ, hδ,
    fun {a r₀} ham hbd hosc {Ω x₀ R} hell hRr hball u G f hG hf hu hgrad => ?_⟩
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 (by linarith), Measure.restrict_empty, eLpNorm_measure_zero]
    exact zero_le
  have hΩ : ballOpens x₀ (2 * R) ≤ Ω := hball
  have ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict (ball x₀ (2 * R))) :=
    memLp_energyIntegrand_of_bounds (Omega := ballOpens x₀ (2 * R)) (beta := 0) (gamma := 0)
      hell.upper_nonneg ham.restrict aestronglyMeasurable_const
      aestronglyMeasurable_const (fun x hx => hell.upper_bound hx) (fun _ _ => by simp)
      (fun _ _ => by simp)
  obtain ⟨H, hHle, hHeq⟩ := exists_field_forall_energyFormH1_restrictL_eq hR hΩ ha hG hf hu
  have hsub : ∀ {ρ : ℝ}, ρ ≤ 2 * R → ∀ {F : Type _} [NormedAddCommGroup F]
      {g g' : EuclideanSpace ℝ (Fin (n + 1)) → F},
      g =ᵐ[volume.restrict (ballOpens x₀ (2 * R) : Set (EuclideanSpace ℝ (Fin (n + 1))))] g' →
        g =ᵐ[volume.restrict (ball x₀ ρ)] g' :=
    fun hρ _ _ _ _ h => ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρ) h
  have hgradR := hsub (ρ := R) (by linarith) (W1p.gradient_restrictL_ae hΩ u)
  have key := h₁ ham hbd hosc (Ω := ballOpens x₀ (2 * R)) hell hRr subset_rfl
    (W1p.restrictL hΩ u) (fun x => G x + H x) hHeq ((hgrad.ae_eq hgradR.symm))
  rw [eLpNorm_congr_ae (hsub (ρ := R / 2) (by linarith) (W1p.gradient_restrictL_ae hΩ u)),
    eLpNorm_congr_ae (hsub (ρ := 2 * R) le_rfl (W1p.value_restrictL_ae hΩ u))] at key
  refine key.trans ?_
  set c : ℝ≥0∞ := ((4 * (n + 1) : ℝ≥0) : ℝ≥0∞)
  have hc1 : 1 ≤ c := by
    simp only [c, ENNReal.one_le_coe_iff]
    exact one_le_mul_of_one_le_of_one_le (by norm_num) le_add_self
  have hcR : ENNReal.ofReal (4 * (n + 1) * R) = c * ENNReal.ofReal R := by
    rw [ENNReal.ofReal_mul (by positivity), show (4 * ((n : ℝ) + 1)) = ((4 * (n + 1) : ℝ≥0) : ℝ)
      by push_cast; ring, ENNReal.ofReal_coe_nnreal]
  calc (C₁ : ℝ≥0∞) * (eLpNorm (fun x => G x + H x) p (volume.restrict (ball x₀ (2 * R))) +
        ENNReal.ofReal R⁻¹ * eLpNorm (W1p.value u) p (volume.restrict (ball x₀ (2 * R))))
      ≤ C₁ * (c * eLpNorm G p (volume.restrict (ball x₀ (2 * R))) +
          c * (ENNReal.ofReal R * eLpNorm f p (volume.restrict (ball x₀ (2 * R)))) +
          c * (ENNReal.ofReal R⁻¹ *
            eLpNorm (W1p.value u) p (volume.restrict (ball x₀ (2 * R))))) := by
        refine mul_le_mul_right (add_le_add ?_ (le_mul_of_one_le_left' hc1)) _
        refine (eLpNorm_add_le (f := G) (g := H) hp1).trans ?_
        rw [← mul_assoc, ← hcR]
        exact add_le_add (le_mul_of_one_le_left' hc1) (hHle hp1)
    _ = ((C₁ * (4 * (n + 1)) : ℝ≥0) : ℝ≥0∞) *
          (eLpNorm G p (volume.restrict (ball x₀ (2 * R))) +
            ENNReal.ofReal R * eLpNorm f p (volume.restrict (ball x₀ (2 * R))) +
            ENNReal.ofReal R⁻¹ *
              eLpNorm (W1p.value u) p (volume.restrict (ball x₀ (2 * R)))) := by
        rw [ENNReal.coe_mul]
        ring


/-- The radius `κ^{-1/2}` is admissible for the oscillation radius `r₀` once `κ ≥ 16 / r₀²`. -/
private theorem four_mul_inv_sqrt_le {r₀ κ : ℝ} (hr₀ : 0 < r₀) (hκ : 16 / r₀ ^ 2 ≤ κ) :
    4 * (√κ)⁻¹ ≤ r₀ := by
  have hκ0 : 0 < κ := (by positivity : (0 : ℝ) < 16 / r₀ ^ 2).trans_le hκ
  have h16 : (4 : ℝ) ^ 2 ≤ r₀ ^ 2 * κ := by
    rw [div_le_iff₀ (by positivity)] at hκ
    linarith
  have h4 := (Real.le_sqrt (by norm_num) (by positivity)).2 h16
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr₀.le] at h4
  rw [← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.2 hκ0)]
  exact h4

/-! ### The whole space with a zero-order shift -/

section Shift

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} {κ : ℝ}

/-- `R ‖f - κ v‖ + R⁻¹ ‖v‖ ≤ 2 ‖g‖` for `R = κ^{-1/2}` and `g = R |f| + 2 √κ |v|`, so the three
terms of the interior estimate with the shifted datum combine into one function. -/
private theorem mul_add_le_of_sub_mul (hp1 : 1 ≤ p) (hκ0 : 0 < κ) (C : ℝ≥0)
    {F : Type*} [NormedAddCommGroup F] (G : α → F) {f v : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hv : AEStronglyMeasurable v μ) :
    (C : ℝ≥0∞) * (eLpNorm G p μ + ENNReal.ofReal (√κ)⁻¹ * eLpNorm (fun x => f x - κ * v x) p μ +
        ENNReal.ofReal (√κ)⁻¹⁻¹ * eLpNorm v p μ) ≤
      ENNReal.ofReal C * eLpNorm G p μ +
        ENNReal.ofReal (2 * C) * eLpNorm (fun x => (√κ)⁻¹ * ‖f x‖ + 2 * √κ * ‖v x‖) p μ := by
  have hsκ : 0 < √κ := Real.sqrt_pos.2 hκ0
  set R := (√κ)⁻¹ with hR_def
  have hR : 0 < R := inv_pos.2 hsκ
  set g := fun x => R * ‖f x‖ + 2 * √κ * ‖v x‖ with hg_def
  have hRκ : R * κ = √κ := by
    have hκs : κ = √κ * √κ := (Real.mul_self_sqrt hκ0.le).symm
    calc R * κ = (√κ)⁻¹ * √κ * √κ := by rw [hR_def, mul_assoc, ← hκs]
      _ = √κ := by rw [inv_mul_cancel₀ hsκ.ne', one_mul]
  -- Each of `R ‖f‖` and `2 √κ ‖v‖` is at most `‖g‖`.
  have hfg : ENNReal.ofReal R * eLpNorm f p μ ≤ eLpNorm g p μ := by
    rw [← Real.eNorm_of_nonneg hR.le, ← eLpNorm_const_smul]
    refine eLpNorm_mono_real (hf.const_smul R) fun x => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hR.le, hg_def]
    exact le_add_of_nonneg_right (by positivity)
  have hvg : 2 * (ENNReal.ofReal √κ * eLpNorm v p μ) ≤ eLpNorm g p μ := by
    rw [← mul_assoc, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two,
      ← Real.eNorm_of_nonneg (by positivity), ← eLpNorm_const_smul]
    refine eLpNorm_mono_real (hv.const_smul _) fun x => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul,
      Real.norm_of_nonneg (by positivity : 0 ≤ 2 * √κ), hg_def]
    exact le_add_of_nonneg_left (by positivity)
  have hsub : eLpNorm (fun x => f x - κ * v x) p μ ≤
      eLpNorm f p μ + ENNReal.ofReal κ * eLpNorm v p μ := by
    refine (eLpNorm_sub_le hp1).trans_eq ?_
    rw [← Real.eNorm_of_nonneg hκ0.le, ← eLpNorm_const_smul]
    rfl
  calc (C : ℝ≥0∞) * (eLpNorm G p μ + ENNReal.ofReal R * eLpNorm (fun x => f x - κ * v x) p μ +
        ENNReal.ofReal R⁻¹ * eLpNorm v p μ)
      ≤ C * (eLpNorm G p μ + (ENNReal.ofReal R * eLpNorm f p μ +
          ENNReal.ofReal √κ * eLpNorm v p μ) + ENNReal.ofReal √κ * eLpNorm v p μ) := by
        rw [hR_def, inv_inv, ← hR_def]
        gcongr
        refine (mul_le_mul_right hsub _).trans_eq ?_
        rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hR.le, hRκ]
    _ = C * eLpNorm G p μ +
          C * (ENNReal.ofReal R * eLpNorm f p μ + 2 * (ENNReal.ofReal √κ * eLpNorm v p μ)) := by
        ring
    _ ≤ C * eLpNorm G p μ + C * (eLpNorm g p μ + eLpNorm g p μ) := by gcongr
    _ = ENNReal.ofReal C * eLpNorm G p μ + ENNReal.ofReal (2 * C) * eLpNorm g p μ := by
        rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
          ENNReal.ofReal_coe_nnreal]
        ring

/-- The `Lᵖ` norm of `g = R |f| + c |v|` is at most `R ‖f‖ + c ‖v‖`. -/
private theorem eLpNorm_mul_norm_add_mul_norm_le (hp1 : 1 ≤ p) {R c : ℝ} (hR : 0 ≤ R)
    (hc : 0 ≤ c) {f v : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hv : AEStronglyMeasurable v μ) :
    eLpNorm (fun x => R * ‖f x‖ + c * ‖v x‖) p μ ≤
      ENNReal.ofReal R * eLpNorm f p μ + ENNReal.ofReal c * eLpNorm v p μ := by
  refine (eLpNorm_add_le hp1).trans (add_le_add ?_ ?_)
  · calc eLpNorm (fun x => R * ‖f x‖) p μ ≤ eLpNorm (R • f) p μ :=
          eLpNorm_mono (hf.norm.const_mul R) fun x => by
            simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_norm, le_refl]
      _ = ENNReal.ofReal R * eLpNorm f p μ := by
          rw [eLpNorm_const_smul, Real.eNorm_of_nonneg hR]
  · calc eLpNorm (fun x => c * ‖v x‖) p μ ≤ eLpNorm (c • v) p μ :=
          eLpNorm_mono (hv.norm.const_mul c) fun x => by
            simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_norm, le_refl]
      _ = ENNReal.ofReal c * eLpNorm v p μ := by
          rw [eLpNorm_const_smul, Real.eNorm_of_nonneg hc]

/-- The final bookkeeping: from `X ≤ A G + 2 A g`, `g ≤ F + 2 U` and `U ≤ F + K G`, the sum
`X + U` is at most a constant times `G + F`. -/
private theorem add_le_mul_add_of_le {A K : ℝ≥0} {X U Gn Fn gn : ℝ≥0∞}
    (hX : X ≤ A * Gn + 2 * A * gn) (hg : gn ≤ Fn + 2 * U) (hU : U ≤ Fn + K * Gn) :
    X + U ≤ ((A + (4 * A + 1) * K + (6 * A + 1) : ℝ≥0) : ℝ≥0∞) * (Gn + Fn) := by
  calc X + U ≤ A * Gn + 2 * A * (Fn + 2 * U) + U := by gcongr; exact hX.trans (by gcongr)
    _ = A * Gn + 2 * A * Fn + (4 * A + 1) * U := by ring
    _ ≤ A * Gn + 2 * A * Fn + (4 * A + 1) * (Fn + K * Gn) := by gcongr
    _ = (A + (4 * A + 1) * K) * Gn + (6 * A + 1) * Fn := by ring
    _ ≤ ((A + (4 * A + 1) * K + (6 * A + 1) : ℝ≥0) : ℝ≥0∞) * Gn +
          ((A + (4 * A + 1) * K + (6 * A + 1) : ℝ≥0) : ℝ≥0∞) * Fn := by
        gcongr ?_ * Gn + ?_ * Fn
        · push_cast
          exact le_self_add
        · push_cast
          exact le_add_self
    _ = _ := by rw [← mul_add]

end Shift

/-- The shifted equation `-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G` on `ℝ^{n+1}`, tested against test
functions, is the unshifted equation with the scalar datum `f - κ u`. -/
private theorem forall_energyFormH1_zero_zero_eq_of_shift
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {κ : ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : MemLp f 2 volume)
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, f x * φ x ∂volume +
          ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
      ∫ x in (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
          ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume +
        ∫ x in (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
          (f x - κ * W1p.value u x) * φ x ∂volume := by
  have hu2 : MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (W1p.value u)
  have hφ2 : MemLp (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) 2 volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hsplit := energyFormH1_eq_energyFormH1_zero_add_setIntegral (b := 0) hcoeff
    (memLp_top_const κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ)
  have hval : ∫ x in (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
      κ * W1p.value u x * W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) x =
        ∫ x, κ * W1p.value u x * φ x := by
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact integral_congr_ae ((W1p.value_ofTestFunctionₗ_top_ae φ).mono
      fun x hx => congrArg (κ * W1p.value u x * ·) hx)
  have hsub : ∫ x, (f x - κ * W1p.value u x) * φ x =
      (∫ x, f x * φ x) - ∫ x, κ * W1p.value u x * φ x :=
    (integral_congr_ae (ae_of_all _ fun x => sub_mul _ _ _)).trans
      (integral_sub (hf.integrable_mul hφ2) ((hu2.const_mul κ).integrable_mul hφ2))
  have h := hu φ
  simp only [Opens.coe_top, Measure.restrict_univ] at hsplit hval ⊢
  rw [hsub]
  linarith

/-- The shifted equation tested against test functions holds against all of `H¹(ℝ^{n+1})`, in
the form of `TauCeti.PDE.UniformlyEllipticOn.eLpNorm_value_le_of_forall_energyFormH1_eq`. -/
private theorem forall_energyFormH1_eq_dirichletForcing_add_divergenceForcing
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {κ : ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hfT : MemLp f 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hκuT : MemLp (fun x => κ * W1p.value u x) 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hGT : MemLp (fun x => G x - 0) 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hu' : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x in (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
            ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume +
          ∫ x in (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
            (f x - κ * W1p.value u x) * φ x ∂volume)
    (v : W1p0 volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2) :
    energyFormH1 a 0 (fun _ => κ) u (v : W1p volume ⊤ 2) =
      dirichletForcing hfT.toLp v + divergenceForcing (-hGT.toLp) v := by
  have h1 := forall_energyFormH1_restrictL_eq_inner_add_inner le_rfl hcoeff hu' hGT
    (hfT.sub hκuT) v
  rw [W1p.restrictL_self] at h1
  have hsubLp : MemLp.toLp (fun x => f x - κ * W1p.value u x) (hfT.sub hκuT) =
      hfT.toLp - hκuT.toLp := MemLp.toLp_sub hfT hκuT
  have hκint : ⟪hκuT.toLp, W1p.value (v : W1p volume ⊤ 2)⟫_ℝ =
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))),
        κ * W1p.value u x * W1p.value (v : W1p volume ⊤ 2) x := by
    rw [L2.inner_def]
    exact integral_congr_ae (hκuT.coeFn_toLp.mono fun x hx => by
      dsimp only
      rw [hx, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
        mul_comm])
  rw [energyFormH1_eq_energyFormH1_zero_add_setIntegral (b := 0) hcoeff (memLp_top_const κ), h1,
    dirichletForcing_apply, divergenceForcing_apply, inner_neg_left, neg_neg, hsubLp,
    inner_sub_left, hκint]
  ring

/-- **The zero-order bound** for the shifted equation on `ℝ^{n+1}`:
`√κ ‖u‖_{Lᵖ} ≤ κ^{-1/2} ‖f‖_{Lᵖ} + √((p - 1) / (4 λ)) ‖G‖_{Lᵖ}`. -/
private theorem sqrt_mul_eLpNorm_value_le_of_shift {p : ℝ≥0∞} (hp : 2 ≤ p) (hp_top : p ≠ ⊤)
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    {κ : ℝ} (hκ0 : 0 < κ)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : MemLp G 2 volume) (hf : MemLp f 2 volume)
    (hu' : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x in (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
            ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume +
          ∫ x in (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
            (f x - κ * W1p.value u x) * φ x ∂volume) :
    ENNReal.ofReal √κ * eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ≤
      ENNReal.ofReal (√κ)⁻¹ * eLpNorm f p volume +
        ENNReal.ofReal √((p.toReal - 1) / (4 * lam)) * eLpNorm G p volume := by
  have hsκ : 0 < √κ := Real.sqrt_pos.2 hκ0
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hell.upper_nonneg ham.restrict
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x _ => hell.upper_bound (mem_univ x)) (fun _ _ => by simp) (fun _ _ => by simp)
  have hu2 : MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (W1p.value u)
  have hfT : MemLp f 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hf
  have hκuT : MemLp (fun x => κ * W1p.value u x) 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hu2.const_mul κ
  have hGT : MemLp (fun x => G x - 0) 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ, sub_zero] using hG
  have hZ := (hell.mono_set (subset_univ _)).eLpNorm_value_le_of_forall_energyFormH1_eq
    (Omega := ⊤) (mu := volume) ham.restrict aestronglyMeasurable_const (gamma := κ)
    (fun _ _ => by rw [Real.norm_of_nonneg hκ0.le]) (ae_of_all _ fun _ => le_rfl) hκ0 hp hp_top
    (u := ⟨u, W1p.mem_w1p0Submodule_top (by norm_num) u⟩)
    (forall_energyFormH1_eq_dirichletForcing_add_divergenceForcing hcoeff hfT hκuT hGT hu')
  have hf1 : (hfT.toLp : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[volume] f := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hfT.coeFn_toLp
  have hG1 : ((-hGT.toLp : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2 _) :
      EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume] -G := by
    simpa only [Opens.coe_top, Measure.restrict_univ, sub_zero] using
      (Lp.coeFn_neg hGT.toLp).trans hGT.coeFn_toLp.neg
  simp only [Opens.coe_top, Measure.restrict_univ] at hZ
  rw [eLpNorm_congr_ae hf1, eLpNorm_congr_ae hG1, eLpNorm_neg] at hZ
  have h1 : √κ * κ⁻¹ = (√κ)⁻¹ :=
    calc √κ * κ⁻¹ = √κ * (√κ * √κ)⁻¹ := by rw [Real.mul_self_sqrt hκ0.le]
      _ = (√κ)⁻¹ := by rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hsκ.ne', one_mul]
  have h2 : √κ * √((p.toReal - 1) / (4 * lam * κ)) = √((p.toReal - 1) / (4 * lam)) := by
    have hlam := hell.pos
    rw [← Real.sqrt_mul hκ0.le]
    congr 1
    field_simp
  calc ENNReal.ofReal √κ * eLpNorm (W1p.value u) p volume
      ≤ ENNReal.ofReal √κ * (ENNReal.ofReal κ⁻¹ * eLpNorm f p volume +
          ENNReal.ofReal √((p.toReal - 1) / (4 * lam * κ)) * eLpNorm G p volume) := by
        gcongr
    _ = _ := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hsκ.le,
          ← ENNReal.ofReal_mul hsκ.le, h1, h2]

/-- **Krylov's whole-space `W^{1,p}` estimate with a zero-order shift.** Let `2 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the
following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic
with constants `λ, Λ`, such that on every ball `B` of radius at most `r₀` some constant matrix `A`,
uniformly elliptic with the same constants, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Let
`κ ≥ 16 / r₀²` and let `u ∈ H¹(ℝ^{n+1})` solve

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G`

weakly, with `f, G ∈ L²` and `∇u ∈ Lᵖ`. Then

`‖∇u‖_{Lᵖ} + √κ ‖u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + κ^{-1/2} ‖f‖_{Lᵖ})`.

The membership `∇u ∈ Lᵖ` is an a priori assumption; `u ∈ Lᵖ` is part of the conclusion when
`f, G ∈ Lᵖ`. This is N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*,
Theorem 2.8, in the a priori form for `2 < p < ∞`, with the threshold `κ₀ = 16 / r₀²` explicit. -/
theorem exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_setAverage_le {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {r₀ κ : ℝ}, 0 < r₀ → 16 / r₀ ^ 2 ≤ κ → AEStronglyMeasurable a volume →
        UniformlyEllipticOn univ a lam Lam →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G 2 volume → MemLp f 2 volume →
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
              ∫ x, f x * φ x ∂volume +
                ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume) →
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            p volume →
          eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1))) p volume +
            ENNReal.ofReal √κ *
              eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ≤
            C * (eLpNorm G p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm f p volume) := by
  obtain ⟨C₁, δ, hδ, h₁⟩ :=
    exists_eLpNorm_gradient_ball_le_of_scalar_forcing_of_setAverage_le (n := n) hp hp_top lam Lam
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  set A : ℝ≥0 := 2 * 4 ^ (n + 1) * C₁ with hA_def
  set K : ℝ≥0 := (√((p.toReal - 1) / (4 * lam))).toNNReal
  refine ⟨A + (4 * A + 1) * K + (6 * A + 1), δ, hδ,
    fun {a r₀ κ} hr₀ hκ ham hell hosc u G f hG hf hu hgrad => ?_⟩
  have hκ0 : 0 < κ := (by positivity : (0 : ℝ) < 16 / r₀ ^ 2).trans_le hκ
  have hsκ : 0 < √κ := Real.sqrt_pos.2 hκ0
  set R := (√κ)⁻¹
  have hR : 0 < R := inv_pos.2 hsκ
  have h4R : 4 * R ≤ r₀ := four_mul_inv_sqrt_le hr₀ hκ
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hell.upper_nonneg ham.restrict
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x _ => hell.upper_bound (mem_univ x)) (fun _ _ => by simp) (fun _ _ => by simp)
  have hu2 : MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (W1p.value u)
  have hu' := forall_energyFormH1_zero_zero_eq_of_shift hcoeff hf hu
  -- The interior estimates at the radius `R`, on every ball `B(y, 2R)`.
  have hlocal : ∀ y, eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) p (volume.restrict (ball y (R / 2))) ≤
      ENNReal.ofReal C₁ * eLpNorm G p (volume.restrict (ball y (4 * (R / 2)))) +
        ENNReal.ofReal (2 * C₁) * eLpNorm (fun x => R * ‖f x‖ + 2 * √κ * ‖W1p.value u x‖) p
          (volume.restrict (ball y (4 * (R / 2)))) := fun y => by
    rw [show 4 * (R / 2) = 2 * R by ring]
    exact (h₁ ham (fun x => hell.opNorm_matrixBilinearForm_le (mem_univ x)) hosc (Ω := ⊤)
      (x₀ := y) (R := R) (hell.mono_set (subset_univ _)) h4R (subset_univ _) u G _
      (hG.restrict _) ((hf.sub (hu2.const_mul κ)).restrict _) hu' (hgrad.restrict _)).trans
      (mul_add_le_of_sub_mul hp1 hκ0 C₁ G hf.aestronglyMeasurable.restrict
        hu2.aestronglyMeasurable.restrict)
  -- Integrating the interior estimates over all centres.
  have hgm : AEStronglyMeasurable (fun x => R * ‖f x‖ + 2 * √κ * ‖W1p.value u x‖) volume :=
    (hf.aestronglyMeasurable.norm.const_mul R).add (hu2.aestronglyMeasurable.norm.const_mul _)
  have hglob := eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add hp1 hp_top
    hgrad.aestronglyMeasurable hG.aestronglyMeasurable hgm (by norm_num : (1 : ℝ) ≤ 4)
    (half_pos hR) (Eventually.of_forall hlocal)
  refine add_le_mul_add_of_le (hglob.trans_eq ?_)
    ((eLpNorm_mul_norm_add_mul_norm_le (c := 2 * √κ) hp1 hR.le (by positivity)
      hf.aestronglyMeasurable hu2.aestronglyMeasurable).trans_eq ?_)
    (sqrt_mul_eLpNorm_value_le_of_shift hp.le hp_top ham hell hκ0 hG hf hu')
  · rw [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal, hA_def]
    push_cast
    ring
  · rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_assoc]

end PDE

end TauCeti
