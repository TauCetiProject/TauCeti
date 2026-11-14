/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Hessian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian

/-!
# The squared norm of a section and the maximum principle for the rough Laplacian

Let `∇` be a metric connection on a Riemannian vector bundle `V` over a Riemannian manifold `M`,
and let `∇*∇` be its rough Laplacian (`CovariantDerivative.roughLaplacian`), built with the
Levi-Civita connection on the tangent bundle. For a smooth section `σ`, tracing the Hessian of
`|σ|²` (`CovariantDerivative.IsMetricCompatible.hessian_norm_sq`) gives

`Δ |σ|² = 2 |∇σ|² - 2 ⟪∇*∇σ, σ⟫`,   `|∇σ|² = ∑ᵢ |∇_{eᵢ} σ|²`

for every orthonormal basis `eᵢ` of the tangent space, where `Δ = div ∘ grad` is
`TauCeti.Manifold.laplaceBeltrami`. With the nonnegative Laplacian `d*d = -Δ` this reads
`(1/2) d*d |σ|² + |∇σ|² = ⟪∇*∇σ, σ⟫`, the form in which Weitzenböck formulas are paired with a
section.

At a local maximum of `|σ|` on a boundaryless manifold `Δ |σ|² ≤ 0`, so
`|∇σ|² ≤ ⟪∇*∇σ, σ⟫` there. On a compact boundaryless manifold this bounds every section obeying a
pointwise inequality of the form

`⟪∇*∇σ, σ⟫ + c |σ|⁴ ≤ K |σ|²`,   `c > 0`,

by `|σ|² ≤ max 0 (K / c)`: at a maximum point of `|σ|²` the left side is at least `c |σ|⁴`. This
is the a priori `C⁰` bound for the spinor of a solution of the Seiberg–Witten equations. There the
Weitzenböck formula `D_A* D_A = ∇_A*∇_A + s / 4 + c(F_A⁺) / 2` and the curvature equation turn
`D_A ψ = 0` into such an inequality, with `c = 1 / 4` and `K` controlled by the scalar curvature
`s` and the perturbation.

For Taubes's large-parameter equations on a symplectic four-manifold the normalized spinor
`ψ = α u₀ + β` satisfies an equation of Ginzburg–Landau type,

`∇*∇ψ + (r / 4) (|ψ|² - 1) ψ + τ = 0`,   `τ = (r / 2) β + R ψ`,

where `R` collects the scalar curvature and curvature terms, bounded independently of `r`. Since
`⟪β, ψ⟫ = |β|² ≥ 0`, the remaining term satisfies `⟪τ, ψ⟫ ≥ -K |ψ|²` with `K` independent of `r`,
and the maximum principle gives `|α|² + |β|² ≤ 1 + 4 K / r` for `K ≥ 0`.

## Main results

* `CovariantDerivative.IsMetricCompatible.laplaceBeltrami_norm_sq`:
  `Δ |σ|² = 2 ∑ᵢ |∇_{eᵢ} σ|² - 2 ⟪∇*∇σ, σ⟫`.
* `CovariantDerivative.IsMetricCompatible.sum_norm_sq_le_inner_roughLaplacian_of_isLocalMax`: at a
  local maximum of `|σ|`, `∑ᵢ |∇_{eᵢ} σ|² ≤ ⟪∇*∇σ, σ⟫`.
* `CovariantDerivative.IsMetricCompatible.norm_sq_le_max_of_inner_roughLaplacian_add_le`: on a
  compact boundaryless manifold, `⟪∇*∇σ, σ⟫ + c |σ|⁴ ≤ K |σ|²` everywhere implies
  `|σ|² ≤ max 0 (K / c)` everywhere.
* `CovariantDerivative.IsMetricCompatible.norm_sq_le_max_of_roughLaplacian_add_eq_zero`: the same
  bound `|σ|² ≤ max 0 (1 + K / c)` for a solution of `∇*∇σ + c (|σ|² - 1) σ + τ = 0` whose
  remaining term satisfies `⟪τ, σ⟫ ≥ -K |σ|²`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 9 (the Bochner
  technique).
* P. B. Kronheimer and T. S. Mrowka, *The genus of embedded surfaces in the projective plane*,
  Math. Res. Lett. 1 (1994), 797–808 (the pointwise bound on the spinor).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Princeton University Press (1996), Chapter 5 (compactness of the moduli space).
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative.IsMetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  {σ : Π x : M, V x}

/-- **The Laplacian of the squared norm of a section.** For a metric connection `∇`, a smooth
section `σ` and an orthonormal basis `eᵢ` of the tangent space at `x`,
`Δ |σ|² = 2 ∑ᵢ |∇_{eᵢ} σ|² - 2 ⟪∇*∇σ, σ⟫`, where `Δ = div ∘ grad` is the Laplace–Beltrami operator
and `∇*∇` is the rough Laplacian built with the Levi-Civita connection. -/
theorem laplaceBeltrami_norm_sq (hcov : cov.IsMetricCompatible) (hσ : CMDiff ∞ (T% σ)) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    TauCeti.Manifold.laplaceBeltrami I (fun y ↦ ‖σ y‖ ^ 2) x =
      2 * ∑ i, ‖cov σ x (b i)‖ ^ 2 -
        2 * ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫ := by
  rw [TauCeti.Manifold.laplaceBeltrami_eq_sum_hessian I _ x b,
    cov.roughLaplacian_eq_sum (leviCivitaConnection I M) σ x b]
  simp only [hcov.hessian_norm_sq hσ x, real_inner_self_eq_norm_sq, inner_neg_left,
    sum_inner, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

variable [I.Boundaryless]

/-- **The rough Laplacian at a maximum of the norm.** At a local maximum of `|σ|` on a
boundaryless manifold, `∑ᵢ |∇_{eᵢ} σ|² ≤ ⟪∇*∇σ, σ⟫` for every orthonormal basis `eᵢ` of the
tangent space; in particular `⟪∇*∇σ, σ⟫ ≥ 0` there. -/
theorem sum_norm_sq_le_inner_roughLaplacian_of_isLocalMax (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) {x : M} (hmax : IsLocalMax (fun y ↦ ‖σ y‖) x)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ i, ‖cov σ x (b i)‖ ^ 2 ≤ ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫ := by
  have hsq : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖σ y‖ ^ 2) x := by
    simp_rw [← real_inner_self_eq_norm_sq]
    exact ((hσ.inner_bundle hσ).of_le (by simp)).contMDiffAt
  have hmax2 : IsLocalMax (fun y ↦ ‖σ y‖ ^ 2) x :=
    Filter.Eventually.mono hmax fun _ hy ↦ pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hlap := TauCeti.Manifold.laplaceBeltrami_nonpos_of_isLocalMax hsq hmax2
  rw [hcov.laplaceBeltrami_norm_sq hσ x b] at hlap
  linarith

/-- **The maximum principle bound for a section.** On a compact boundaryless manifold, if a smooth
section `σ` satisfies `⟪∇*∇σ, σ⟫ + c |σ|⁴ ≤ K |σ|²` everywhere, with `c > 0`, then
`|σ|² ≤ max 0 (K / c)` everywhere. For the spinor of a Seiberg–Witten solution the inequality is
the Weitzenböck formula paired with the spinor. -/
theorem norm_sq_le_max_of_inner_roughLaplacian_add_le [CompactSpace M]
    (hcov : cov.IsMetricCompatible) (hσ : CMDiff ∞ (T% σ)) {c K : ℝ} (hc : 0 < c)
    (h : ∀ y, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ y, σ y⟫ + c * ‖σ y‖ ^ 4 ≤
      K * ‖σ y‖ ^ 2) (x : M) :
    ‖σ x‖ ^ 2 ≤ max 0 (K / c) := by
  -- `|σ|` attains its maximum at some point `x₀`.
  have hcont : Continuous fun y ↦ ‖σ y‖ := by
    have h2 : Continuous fun y ↦ ‖σ y‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq] using (hσ.inner_bundle hσ).continuous
    simpa only [Real.sqrt_sq (norm_nonneg _)] using h2.sqrt
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩ hcont.continuousOn
  have hmax : IsLocalMax (fun y ↦ ‖σ y‖) x₀ := hx₀.isLocalMax Filter.univ_mem
  -- There `⟪∇*∇σ, σ⟫ ≥ 0`, so `c |σ(x₀)|⁴ ≤ K |σ(x₀)|²`.
  have hlap := hcov.sum_norm_sq_le_inner_roughLaplacian_of_isLocalMax hσ hmax
    (stdOrthonormalBasis ℝ (TangentSpace I x₀))
  have hpos : 0 ≤ ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x₀, σ x₀⟫ :=
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg _).trans hlap
  have hx₀' : c * (‖σ x₀‖ ^ 2) ^ 2 ≤ K * ‖σ x₀‖ ^ 2 := by
    have := h x₀
    nlinarith
  have hle : ‖σ x‖ ^ 2 ≤ ‖σ x₀‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hx₀ (Set.mem_univ x)) 2
  refine hle.trans ?_
  rcases (sq_nonneg ‖σ x₀‖).eq_or_lt with h0 | h0
  · rw [← h0]
    exact le_max_left _ _
  · refine le_max_of_le_right ((le_div_iff₀ hc).2 ?_)
    nlinarith

/-- **The maximum principle bound for a Ginzburg–Landau type equation.** On a compact
boundaryless manifold, let a smooth section `σ` satisfy
`∇*∇σ + c (|σ|² - 1) σ + τ = 0` with `c > 0`, where the remaining term `τ` obeys
`⟪τ, σ⟫ ≥ -K |σ|²`. Then `|σ|² ≤ max 0 (1 + K / c)` everywhere. For Taubes's large-parameter
Seiberg–Witten equations `c = r / 4`, and `τ` collects the curvature terms of the Weitzenböck
formula and the term `(r / 2) β`, whose pairing with the spinor is nonnegative. -/
theorem norm_sq_le_max_of_roughLaplacian_add_eq_zero [CompactSpace M]
    (hcov : cov.IsMetricCompatible) (hσ : CMDiff ∞ (T% σ)) {τ : Π x : M, V x} {c K : ℝ}
    (hc : 0 < c) (hτ : ∀ y, -K * ‖σ y‖ ^ 2 ≤ ⟪τ y, σ y⟫)
    (h : ∀ y, cov.roughLaplacian (leviCivitaConnection I M) σ y +
      (c * (‖σ y‖ ^ 2 - 1)) • σ y + τ y = 0) (x : M) :
    ‖σ x‖ ^ 2 ≤ max 0 (1 + K / c) := by
  have hle : ∀ y, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ y, σ y⟫ + c * ‖σ y‖ ^ 4 ≤
      (c + K) * ‖σ y‖ ^ 2 := fun y ↦ by
    have hy := congrArg (⟪·, σ y⟫) (h y)
    simp only [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, inner_zero_left,
      RCLike.conj_to_real] at hy
    nlinarith [hτ y]
  simpa only [add_div, div_self hc.ne'] using
    hcov.norm_sq_le_max_of_inner_roughLaplacian_add_le hσ hc hle x

end CovariantDerivative.IsMetricCompatible
