/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Basic
public import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Regularity
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.PDE.DirichletProblem.LpEstimate
import TauCeti.Analysis.PDE.DirichletProblem.WholeSpace
import TauCeti.Analysis.PDE.Ellipticity.Integral
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.FundamentalSolution.Divergence
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball
import TauCeti.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Krylov's whole-space `W^{1,p}` theorem with a zero-order shift

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

Both a priori hypotheses can be dropped when the oscillation is measured by the VMO modulus
(`TauCeti.vmoModulus`):

* `TauCeti.PDE.exists_memLp_gradient_ball_of_scalar_forcing_of_vmoModulus_le`: interior
  regularity with a scalar datum, `∇u ∈ Lᵖ(B_R)` whenever `f, G ∈ Lᵖ(B_{2R})` and `8 R ≤ r₀`.
* `TauCeti.PDE.exists_memLp_gradient_and_memLp_value_of_vmoModulus_le`: for every `κ > 0`, an
  `H¹(ℝ^{n+1})` solution of the shifted equation with `f, G ∈ L² ∩ Lᵖ` lies in `W^{1,p}(ℝ^{n+1})`.
* `TauCeti.PDE.exists_memLp_and_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_vmoModulus_le`
  and its form for coefficients of vanishing mean oscillation,
  `TauCeti.PDE.exists_memLp_and_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_memVMO`: the
  estimate above for every such solution, with no a priori hypothesis.

For every `κ > 0` and `f, G ∈ L²` the shifted equation has exactly one solution in
`H¹(ℝ^{n+1})`, by Lax–Milgram
(`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_of_pos`, in
`TauCeti/Analysis/PDE/DirichletProblem/WholeSpace.lean`). Together these are Krylov's theorem for
`2 < p < ∞` and data in `L² ∩ Lᵖ`: the shifted equation has exactly one solution in
`H¹(ℝ^{n+1})`, it lies in `W^{1,p}(ℝ^{n+1})`, and it satisfies the estimate.

## The argument

* **The scalar datum as a divergence.** On `B = B(x₀, 2R)` the datum `f` is minus the divergence
  of the gradient `H` of the Newtonian potential of `f 1_B`, with `‖H‖_{Lᵖ(B)} ≤ 4 (n + 1) R
  ‖f‖_{Lᵖ(B)}`
  (`TauCeti.exists_eLpNorm_restrict_ball_le_and_setIntegral_inner_gradient_eq`). So on `B`
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
* **Regularity.** The interior regularity theorem in divergence form
  (`TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le`), applied to
  `-div (G + H)` on `B(x₀, 2R)`, supplies the a priori hypothesis of the interior estimate on every
  ball of radius `r₀ / 8`, and integrating those interior estimates over all centres shows
  `∇u ∈ Lᵖ(ℝ^{n+1})`. The value lies in `Lᵖ` by the zero-order bound.

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
  obtain ⟨H, -, hHle, hHφ⟩ := exists_eLpNorm_restrict_ball_le_and_setIntegral_inner_gradient_eq
    volume (by positivity : 0 ≤ 2 * R) (hf.integrable one_le_two)
  have hc : (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) : ℝ) * (2 * (2 * R)) =
      4 * (n + 1) * R := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    push_cast
    ring
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
  rw [← hHφ φ (φ.contDiff.of_le (by simp)) φ.tsupport_subset]

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
    hell.memLp_energyIntegrand_zero_zero (Omega := ballOpens x₀ (2 * R)) ham.restrict
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

/-- `C (‖G‖ + R ‖g‖ + R⁻¹ ‖v‖) ≤ C ‖G‖ + 2 C ‖R |g| + R⁻¹ |v|‖` for `R > 0`, so the three terms
of the interior estimate with a scalar datum combine into one function. -/
private theorem mul_add_add_le_of_pos {R : ℝ} (hR : 0 < R) (C : ℝ≥0) {F : Type*}
    [NormedAddCommGroup F] (G : α → F) {g v : α → ℝ} (hg : AEStronglyMeasurable g μ)
    (hv : AEStronglyMeasurable v μ) :
    (C : ℝ≥0∞) * (eLpNorm G p μ + ENNReal.ofReal R * eLpNorm g p μ +
        ENNReal.ofReal R⁻¹ * eLpNorm v p μ) ≤
      ENNReal.ofReal C * eLpNorm G p μ +
        ENNReal.ofReal (2 * C) * eLpNorm (fun x => R * ‖g x‖ + R⁻¹ * ‖v x‖) p μ := by
  set k := fun x => R * ‖g x‖ + R⁻¹ * ‖v x‖
  have hgk : ENNReal.ofReal R * eLpNorm g p μ ≤ eLpNorm k p μ := by
    rw [← eLpNorm_const_mul_norm hR.le hg]
    refine eLpNorm_mono_real (hg.norm.const_mul R) fun x => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact le_add_of_nonneg_right (by positivity)
  have hvk : ENNReal.ofReal R⁻¹ * eLpNorm v p μ ≤ eLpNorm k p μ := by
    rw [← eLpNorm_const_mul_norm (inv_pos.2 hR).le hv]
    refine eLpNorm_mono_real (hv.norm.const_mul R⁻¹) fun x => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact le_add_of_nonneg_left (by positivity)
  calc (C : ℝ≥0∞) * (eLpNorm G p μ + ENNReal.ofReal R * eLpNorm g p μ +
        ENNReal.ofReal R⁻¹ * eLpNorm v p μ)
      ≤ C * (eLpNorm G p μ + eLpNorm k p μ + eLpNorm k p μ) := by gcongr
    _ = ENNReal.ofReal C * eLpNorm G p μ + ENNReal.ofReal (2 * C) * eLpNorm k p μ := by
        rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
          ENNReal.ofReal_coe_nnreal]
        ring

/-- `R ‖f - κ v‖ + R⁻¹ ‖v‖ ≤ 2 ‖g‖` for `R = κ^{-1/2}` and `g = R |f| + 2 √κ |v|`, so the three
terms of the interior estimate with the shifted datum combine into one function. -/
private theorem mul_add_le_of_sub_mul (hκ0 : 0 < κ) (C : ℝ≥0)
    {F : Type*} [NormedAddCommGroup F] (G : α → F) {f v : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hv : AEStronglyMeasurable v μ) :
    (C : ℝ≥0∞) * (eLpNorm G p μ + ENNReal.ofReal (√κ)⁻¹ * eLpNorm (fun x => f x - κ * v x) p μ +
        ENNReal.ofReal (√κ)⁻¹⁻¹ * eLpNorm v p μ) ≤
      ENNReal.ofReal C * eLpNorm G p μ +
        ENNReal.ofReal (2 * C) * eLpNorm (fun x => (√κ)⁻¹ * ‖f x‖ + 2 * √κ * ‖v x‖) p μ := by
  have hsκ : 0 < √κ := Real.sqrt_pos.2 hκ0
  have hRκ : (√κ)⁻¹ * κ = √κ := by
    rw [inv_mul_eq_iff_eq_mul₀ hsκ.ne', Real.mul_self_sqrt hκ0.le]
  refine (mul_add_add_le_of_pos (inv_pos.2 hsκ) C G (hf.sub (hv.const_mul κ)) hv).trans ?_
  gcongr
  refine eLpNorm_mono_real
    (((hf.sub (hv.const_mul κ)).norm.const_mul _).add (hv.norm.const_mul _)) fun x => ?_
  rw [inv_inv, Pi.sub_apply, Real.norm_of_nonneg (by positivity)]
  have h := norm_sub_le (f x) (κ * v x)
  rw [norm_mul, Real.norm_of_nonneg hκ0.le] at h
  have h' := mul_le_mul_of_nonneg_left h (inv_pos.2 hsκ).le
  rw [mul_add, ← mul_assoc, hRκ] at h'
  linarith

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

/-- **The zero-order bound** for the shifted equation on `ℝ^{n+1}`:
`√κ ‖u‖_{Lᵖ} ≤ κ^{-1/2} ‖f‖_{Lᵖ} + √((p - 1) / (4 λ)) ‖G‖_{Lᵖ}`. -/
private theorem sqrt_mul_eLpNorm_value_le_of_shift {p : ℝ≥0∞} (hp : 2 ≤ p) (hp_top : p ≠ ⊤)
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))))
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
  have hfT : MemLp f 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hf
  have hGT : MemLp G 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hG
  have hZ := (hell.mono_set (subset_univ _)).eLpNorm_value_le_of_forall_energyFormH1_eq
    (Omega := ⊤) (mu := volume) ham.restrict aestronglyMeasurable_const (gamma := κ)
    (fun _ _ => by rw [Real.norm_of_nonneg hκ0.le]) (ae_of_all _ fun _ => le_rfl) hκ0 hp hp_top
    (u := ⟨u, W1p.mem_w1p0Submodule_top (by norm_num) u⟩)
    (forall_energyFormH1_eq_dirichletForcing_add_divergenceForcing hcoeff hfT hGT hu')
  have hf1 : (hfT.toLp : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[volume] f := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hfT.coeFn_toLp
  have hG1 : ((-hGT.toLp : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2 _) :
      EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume] -G := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
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
  have hcoeff := (hell.mono_set (subset_univ _)).memLp_energyIntegrand_zero_zero
    (Omega := (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) ham.restrict
  have hu2 := W1p.memLp_value u
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
      (mul_add_le_of_sub_mul hκ0 C₁ G hf.aestronglyMeasurable.restrict
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
    (sqrt_mul_eLpNorm_value_le_of_shift hp.le hp_top ham hell hcoeff hκ0 hG hf hu')
  · simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_mul zero_le_two, hA_def]
    push_cast
    ring
  · rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_assoc]

/-! ### Regularity and solvability -/

/-- If the VMO modulus of a uniformly elliptic field `a` at the scale `r₀` is at most `δ`, then on
every ball of radius at most `r₀` some constant matrix, uniformly elliptic with the same constants
(the average of `a` over the ball), has mean deviation at most `δ` from `a`. This is the oscillation
hypothesis of the a priori estimates above. -/
theorem exists_uniformlyEllipticOn_const_and_setAverage_le_of_vmoModulus_le {lam Lam : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam) {r₀ δ : ℝ}
    (hδ : 0 ≤ δ)
    (hη : vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume r₀ ≤ ENNReal.ofReal δ)
    (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) (hr : 0 < r) (hrr : r ≤ r₀) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
        ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ :=
  (hell.mono_set (subset_univ _)).exists_uniformlyEllipticOn_const_and_setAverage_le
    measurableSet_ball ham.restrict (measure_ball_pos volume c hr).ne' measure_ball_lt_top.ne hδ
    ((setLAverage_enorm_sub_setAverage_le_vmoModulus _ volume c hrr).trans hη)

/-- **Interior `W^{1,p}` regularity with a scalar datum, for coefficients of small mean
oscillation.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There is a threshold `δ > 0`, depending only on
`n`, `p`, `λ` and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on
`ℝ^{n+1}`, uniformly elliptic with constants `λ, Λ`, whose VMO modulus at the scale `r₀` is at
most `δ`. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly in `Ω`, let `B(x₀, 2R) ⊆ Ω` with
`8 R ≤ r₀`, and let `f` and `G` lie in `Lᵖ(B(x₀, 2R))`. Then `∇u ∈ Lᵖ(B(x₀, R))`.

Nothing is assumed about the integrability of `∇u` beyond `L²`. This is the regularity counterpart
of the a priori estimate
`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_scalar_forcing_of_setAverage_le`, and the case of a
scalar datum of `TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le`: on
`B(x₀, 2R)` the datum `f` is `-div H` for a field `H ∈ Lᵖ(B(x₀, 2R))`. -/
theorem exists_memLp_gradient_ball_of_scalar_forcing_of_vmoModulus_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume r₀ ≤ ENNReal.ofReal δ →
        ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
          {R : ℝ}, 8 * R ≤ r₀ → ball x₀ (2 * R) ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
        ∀ (u : W1p volume Ω 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
          MemLp G p (volume.restrict (ball x₀ (2 * R))) →
          MemLp f p (volume.restrict (ball x₀ (2 * R))) →
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume +
              ∫ x in Ω, f x * φ x ∂volume) →
          MemLp (W1p.gradient u) p (volume.restrict (ball x₀ R)) := by
  obtain ⟨_, δ, hδ, hreg⟩ :=
    exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le (n := n) hp hp_top lam Lam
  refine ⟨δ, hδ, fun {a r₀} ham hell hη {Ω x₀ R} hRr hball u G f hG hf hu => ?_⟩
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 hR, Measure.restrict_empty]
    exact memLp_measure_zero
  have : IsFiniteMeasure (volume.restrict (ball x₀ (2 * R))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hΩ : ballOpens x₀ (2 * R) ≤ Ω := hball
  have ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict (ball x₀ (2 * R))) :=
    (hell.mono_set (subset_univ _)).memLp_energyIntegrand_zero_zero
      (Omega := ballOpens x₀ (2 * R)) ham.restrict
  -- On `B(x₀, 2R)` the scalar datum is `-div H` for a field `H ∈ Lᵖ(B(x₀, 2R))`.
  obtain ⟨H, hHle, hHeq⟩ := exists_field_forall_energyFormH1_restrictL_eq hR hΩ ha
    (hG.mono_exponent hp.le) (hf.mono_exponent hp.le) hu
  have hH : MemLp H p (volume.restrict (ball x₀ (2 * R))) :=
    memLp_iff.2 ((hHle (one_le_two.trans hp.le)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top))
  have h := (hreg ham hell hη (Ω := ballOpens x₀ (2 * R)) (x₀ := x₀) (R := 2 * R)
    (by positivity) (by linarith) subset_rfl (W1p.restrictL hΩ u) (fun x => G x + H x) hHeq
    (hG.add hH)).1
  rw [show 2 * R / 2 = R by ring] at h
  exact h.ae_eq (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith))
    (W1p.gradient_restrictL_ae hΩ u))

/-- **`W^{1,p}` regularity for the whole-space equation with a zero-order shift.** Let
`2 < p < ∞` and `0 < λ ≤ Λ`. There is a threshold `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`,
with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly
elliptic with constants `λ, Λ`, whose VMO modulus at a scale `r₀ > 0` is at most `δ`, and let
`κ > 0`. If `u ∈ H¹(ℝ^{n+1})` solves

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G`

weakly, with `f, G ∈ L² ∩ Lᵖ`, then `∇u ∈ Lᵖ` and `u ∈ Lᵖ`, so `u ∈ W^{1,p}(ℝ^{n+1})`.

No relation between `κ` and `r₀` is needed here. The value lies in `Lᵖ` by the zero-order bound,
and the gradient by the interior regularity and estimates on all balls of radius `r₀ / 8`, which
are integrated over all centres. -/
theorem exists_memLp_gradient_and_memLp_value_of_vmoModulus_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {r₀ κ : ℝ}, 0 < r₀ → 0 < κ → AEStronglyMeasurable a volume →
        UniformlyEllipticOn univ a lam Lam →
        vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume r₀ ≤ ENNReal.ofReal δ →
        ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G 2 volume → MemLp f 2 volume →
          MemLp G p volume → MemLp f p volume →
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
              ∫ x, f x * φ x ∂volume +
                ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume) →
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
              p volume ∧
            MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume := by
  obtain ⟨δ₁, hδ₁, hloc⟩ :=
    exists_memLp_gradient_ball_of_scalar_forcing_of_vmoModulus_le (n := n) hp hp_top lam Lam
  obtain ⟨C, δ₂, hδ₂, hap⟩ :=
    exists_eLpNorm_gradient_ball_le_of_scalar_forcing_of_setAverage_le (n := n) hp hp_top lam Lam
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂,
    fun {a r₀ κ} hr₀ hκ ham hell hη u G f hG hf hGp hfp hu => ?_⟩
  have hcoeff := (hell.mono_set (subset_univ _)).memLp_energyIntegrand_zero_zero
    (Omega := (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) ham.restrict
  have hu2 := W1p.memLp_value u
  have hu' := forall_energyFormH1_zero_zero_eq_of_shift hcoeff hf hu
  -- The value lies in `Lᵖ` by the zero-order bound.
  have hup : MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume := by
    refine memLp_iff.2 (ENNReal.lt_top_of_mul_ne_top_right ?_
      (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hκ)).ne')
    exact ((sqrt_mul_eLpNorm_value_le_of_shift hp.le hp_top ham hell hcoeff hκ hG hf hu').trans_lt
      (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfp.eLpNorm_lt_top,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGp.eLpNorm_lt_top⟩)).ne
  refine ⟨?_, hup⟩
  set R := r₀ / 8
  have hR : 0 < R := by positivity
  have h8R : 8 * R = r₀ := by simp only [R]; ring
  have hFp := hfp.sub (hup.const_mul κ)
  -- On every ball of radius `R / 2`, the gradient is bounded by the data on the ball of
  -- radius `2 R`; the interior regularity theorem supplies the a priori integrability.
  have hlocal : ∀ y, eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) p (volume.restrict (ball y (R / 2))) ≤
      ENNReal.ofReal C * eLpNorm G p (volume.restrict (ball y (4 * (R / 2)))) +
        ENNReal.ofReal (2 * C) * eLpNorm (fun x => R * ‖f x - κ * W1p.value u x‖ +
          R⁻¹ * ‖W1p.value u x‖) p (volume.restrict (ball y (4 * (R / 2)))) := fun y => by
    rw [show 4 * (R / 2) = 2 * R by ring]
    have hgradR := hloc ham hell (hη.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
      (Ω := ⊤) (x₀ := y) (R := R) h8R.le (subset_univ _) u G _ (hGp.restrict _)
      (hFp.restrict _) hu'
    exact (hap ham (fun x => hell.opNorm_matrixBilinearForm_le (mem_univ x))
      (fun c r hr hrr => exists_uniformlyEllipticOn_const_and_setAverage_le_of_vmoModulus_le ham
        hell hδ₂.le (hη.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))) c r hr hrr)
      (Ω := ⊤) (x₀ := y) (R := R) (hell.mono_set (subset_univ _)) (by linarith) (subset_univ _)
      u G _ (hG.restrict _) ((hf.sub (hu2.const_mul κ)).restrict _) hu' hgradR).trans
      (mul_add_add_le_of_pos hR C G (hf.sub (hu2.const_mul κ)).aestronglyMeasurable.restrict
        hu2.aestronglyMeasurable.restrict)
  -- Integrating the local bounds over all centres.
  have hk : MemLp (fun x => R * ‖f x - κ * W1p.value u x‖ + R⁻¹ * ‖W1p.value u x‖) p volume :=
    (hFp.norm.const_mul R).add (hup.norm.const_mul R⁻¹)
  have hglob := eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add (one_le_two.trans hp.le) hp_top
    (W1p.memLp_gradient u).aestronglyMeasurable hG.aestronglyMeasurable hk.aestronglyMeasurable
    (by norm_num : (1 : ℝ) ≤ 4) (half_pos hR) (Eventually.of_forall hlocal)
  exact memLp_iff.2 (hglob.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGp.eLpNorm_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk.eLpNorm_lt_top⟩)))

/-- **Krylov's whole-space `W^{1,p}` theorem with a zero-order shift, for coefficients of small
mean oscillation.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`,
depending only on `n`, `p`, `λ` and `Λ`, with the following property. Let `a` be a measurable
coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants `λ, Λ`, not necessarily
symmetric, whose VMO modulus at a scale `r₀ > 0` is at most `δ`, and let `κ ≥ 16 / r₀²`. If
`u ∈ H¹(ℝ^{n+1})` solves

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G`

weakly, with `f, G ∈ L² ∩ Lᵖ`, then `u ∈ W^{1,p}(ℝ^{n+1})` and

`‖∇u‖_{Lᵖ} + √κ ‖u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + κ^{-1/2} ‖f‖_{Lᵖ})`.

Unlike `TauCeti.PDE.exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_setAverage_le`,
nothing is assumed about the integrability of `∇u` beyond `L²`. Such a solution exists and is
unique for every `κ > 0`
(`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_of_pos`). This is
N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Theorem 2.8, for
`2 < p < ∞` and data in `L² ∩ Lᵖ`. -/
theorem exists_memLp_and_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_vmoModulus_le
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {r₀ κ : ℝ}, 0 < r₀ → 16 / r₀ ^ 2 ≤ κ → AEStronglyMeasurable a volume →
        UniformlyEllipticOn univ a lam Lam →
        vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume r₀ ≤ ENNReal.ofReal δ →
        ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G 2 volume → MemLp f 2 volume →
          MemLp G p volume → MemLp f p volume →
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
              ∫ x, f x * φ x ∂volume +
                ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume) →
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
              p volume ∧
            MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ∧
            eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
                EuclideanSpace ℝ (Fin (n + 1))) p volume +
              ENNReal.ofReal √κ *
                eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ≤
              C * (eLpNorm G p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm f p volume) := by
  obtain ⟨δ₁, hδ₁, hreg⟩ :=
    exists_memLp_gradient_and_memLp_value_of_vmoModulus_le (n := n) hp hp_top lam Lam
  obtain ⟨C, δ₂, hδ₂, hest⟩ :=
    exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_setAverage_le (n := n) hp hp_top
      lam Lam
  refine ⟨C, min δ₁ δ₂, lt_min hδ₁ hδ₂,
    fun {a r₀ κ} hr₀ hκ ham hell hη u G f hG hf hGp hfp hu => ?_⟩
  have hκ0 : 0 < κ := (by positivity : (0 : ℝ) < 16 / r₀ ^ 2).trans_le hκ
  obtain ⟨hgrad, hval⟩ := hreg hr₀ hκ0 ham hell
    (hη.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))) u G f hG hf hGp hfp hu
  exact ⟨hgrad, hval, hest hr₀ hκ ham hell
    (fun c r hr hrr => exists_uniformlyEllipticOn_const_and_setAverage_le_of_vmoModulus_le ham hell
      hδ₂.le (hη.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))) c r hr hrr)
    u G f hG hf hu hgrad⟩

/-- **Krylov's whole-space `W^{1,p}` theorem with a zero-order shift, for coefficients of vanishing
mean oscillation.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There is a constant `C`, depending only on
`n`, `p`, `λ` and `Λ`, with the following property. Let `a` be a coefficient matrix on `ℝ^{n+1}`,
uniformly elliptic with constants `λ, Λ`, not necessarily symmetric, whose operators `a(x)` have
vanishing mean oscillation. Then there is a threshold `κ₀ > 0` such that for every `κ ≥ κ₀`, every
`u ∈ H¹(ℝ^{n+1})` solving `-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G` weakly, with `f, G ∈ L² ∩ Lᵖ`, lies in
`W^{1,p}(ℝ^{n+1})` and satisfies

`‖∇u‖_{Lᵖ} + √κ ‖u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + κ^{-1/2} ‖f‖_{Lᵖ})`.

The threshold `κ₀` depends on `a` only through its VMO modulus; see
`TauCeti.PDE.exists_memLp_and_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_vmoModulus_le`. -/
theorem exists_memLp_and_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_memVMO {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      MemVMO (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
      UniformlyEllipticOn univ a lam Lam →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ {κ : ℝ}, κ₀ ≤ κ →
        ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G 2 volume → MemLp f 2 volume →
          MemLp G p volume → MemLp f p volume →
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
              ∫ x, f x * φ x ∂volume +
                ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume) →
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
              p volume ∧
            MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ∧
            eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
                EuclideanSpace ℝ (Fin (n + 1))) p volume +
              ENNReal.ofReal √κ *
                eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ≤
              C * (eLpNorm G p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm f p volume) := by
  obtain ⟨C, δ, hδ, hmain⟩ :=
    exists_memLp_and_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_vmoModulus_le (n := n) hp
      hp_top lam Lam
  refine ⟨C, fun {a} hvmo hell => ?_⟩
  obtain ⟨hbmo, hlim⟩ := memVMO_iff_tendsto.1 hvmo
  -- The VMO modulus is below `δ` on `(0, r₁)`.
  obtain ⟨r₁, hr₁, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ)))
  have hr₁' : 0 < r₁ := hr₁
  refine ⟨16 / (r₁ / 2) ^ 2, by positivity, fun {κ} hκ => ?_⟩
  exact hmain (by positivity) hκ (Matrix.aestronglyMeasurable_toEuclideanCLM_iff.1
    hbmo.locallyIntegrable.aestronglyMeasurable) hell (hsub ⟨by positivity, by linarith⟩).le

end PDE

end TauCeti
