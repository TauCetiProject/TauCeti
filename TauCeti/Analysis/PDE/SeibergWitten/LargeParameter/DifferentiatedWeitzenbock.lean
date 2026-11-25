/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.GradientBound
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Bochner
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.MaximumPrinciple
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Norm

/-!
# The differentiated Weitzenböck inequalities and the gradient bound at large parameter

On a symplectic four-manifold Taubes writes the normalized spinor of a solution of the
large-parameter Seiberg–Witten equations through two components: a section `α` of the twisting
line and a section `β` of the complementary line. Projecting the Weitzenböck formula gives a
coupled system of Ginzburg–Landau type,

`∇*∇α = (r / 4) (1 - |α|² - |β|²) α + 𝔞`,   `∇*∇β + (r / 4) (1 + |α|² + |β|²) β = 𝔟`,

where `𝔞` and `𝔟` collect the terms of lower order: the coupling through the derivatives of the
canonical spinor, the curvature of the background connection and the forcing. The gradient bound
`|∇α|² + r |∇β|² ≤ C' r w₊ + C'`, `w₊ = max (1 - |α|²) 0`, follows from four scalar differential
inequalities by the maximum principle (`TauCeti.SeibergWitten.norm_sq_add_mul_norm_sq_le`). This
file derives those four inequalities from the system, for sections `α`, `β` of arbitrary
Riemannian vector bundles with metric connections over a Riemannian manifold, and concludes the
gradient bound for solutions of the system on a compact boundaryless manifold.

* **First order.** Pairing the equations with `α` and `β` gives the identities
  `-Δ|α|² / 2 + |∇α|² + (r / 4) (|α|² + |β|² - 1) |α|² = ⟪𝔞, α⟫` and its analogue for `β`
  (`neg_laplaceBeltrami_norm_sq_div_two_add_eq_inner_of_roughLaplacian_eq`,
  `neg_laplaceBeltrami_norm_sq_div_two_add_eq_inner_of_roughLaplacian_add_eq`, in the namespace
  `TauCeti.SeibergWitten`).
* **Second order.** Differentiating an equation once,
  `∇_v (∇*∇α) = (r / 4) (1 - |α|² - |β|²) ∇_v α - (r / 2) (⟪∇_v α, α⟫ + ⟪∇_v β, β⟫) α + ∇_v 𝔞`,
  and pairing with `∇_v α` bounds the first term of the Bochner inequality
  `IsMetricCompatible.neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le`
  (in the namespace `CovariantDerivative`).
  Its curvature terms involve the curvature `R` of the connection, of size `O(r)` in Taubes's
  setting, the Riemann curvature and the divergence `∑ᵢ (∇_{eᵢ}R)(·, eᵢ)` of `R`, which the
  curvature equation controls although `∇R` itself is not bounded
  (`neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le_of_roughLaplacian_eq`
  and its analogue for `β`). For `β` the derivative of the potential `(r / 4) (1 + |α|² + |β|²)`
  has a good sign, and the remaining derivative of the potential carries a factor `|β|`.
* **The gradient bound.** Under the bounds of Taubes's setting, `|𝔞| ≤ c (|∇β| + |α| + |β|)`,
  `|∇𝔞| ≤ c (|∇²β| + |∇α| + |∇β| + 1)`, the analogues for `𝔟`, `|R| ≤ c r` for both
  connections, `|Rᵀ| ≤ c`, the divergence bounds `c r (|∇α| + |∇β| + 1)` and
  `c r |β| (|∇α| + |∇β| + 1)`, and the coarse bounds `|α|² + |β|² ≤ 1 + C / r` and
  `|β|² ≤ (C / r) w₊ + C / r²`, the four inequalities hold with a constant depending only on `c`,
  `C` and the dimension, and so
  `|∇α|² + r |∇β|² ≤ C' r w₊ + C'` with `C'` independent of `r` and of the solution
  (`TauCeti.SeibergWitten.innerCovariantDerivative_self_add_mul_innerCovariantDerivative_self_le`).

Here `|∇α|` is the Hilbert–Schmidt norm `√⟪∇α, ∇α⟫` (`CovariantDerivative.innerCovariantDerivative`)
and `|∇²α|² = ∑ᵢⱼ |∇²α(eᵢ, eⱼ)|²` in an orthonormal basis `eᵢ`. The derivation of the projected
system and of the bounds on `𝔞`, `𝔟` and on the curvature from the Seiberg–Witten equations on a
symplectic four-manifold is not done here.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *The Seiberg–Witten equations and the Weinstein conjecture*, Geom. Topol. 11
  (2007), 2117–2202, Section 2.
-/

public section

open Bundle CovariantDerivative Module TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  [IsContMDiffRiemannianBundle I ∞ F₁ V₁]
  {cov₁ : _root_.CovariantDerivative I F₁ V₁} [ContMDiffCovariantDerivative cov₁ ∞]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  [IsContMDiffRiemannianBundle I ∞ F₂ V₂]
  {cov₂ : _root_.CovariantDerivative I F₂ V₂} [ContMDiffCovariantDerivative cov₂ ∞]
  {α 𝔞 : Π x : M, V₁ x} {β 𝔟 : Π x : M, V₂ x} {r κ : ℝ}

local notation "∇ᵀ" => CovariantDerivative.leviCivitaConnection I M

omit [ContMDiffCovariantDerivative cov₂ ∞] in
/-- **The differentiated projected equation.** If
`∇*∇α = (r / 4) (κ - |α|² - |β|²) α + 𝔞`, then
`∇_v (∇*∇α) = (r / 4) (κ - |α|² - |β|²) ∇_v α - (r / 2) (⟪∇_v α, α⟫ + ⟪∇_v β, β⟫) α + ∇_v 𝔞`. -/
private theorem covariantDerivative_roughLaplacian_apply (hcov₁ : cov₁.IsMetricCompatible)
    (hcov₂ : cov₂.IsMetricCompatible) (hα : CMDiff ∞ (T% α)) (hβ : CMDiff ∞ (T% β))
    (h𝔞 : CMDiff ∞ (T% 𝔞))
    (heq : ∀ y, cov₁.roughLaplacian (∇ᵀ) α y =
      (r / 4 * (κ - ‖α y‖ ^ 2 - ‖β y‖ ^ 2)) • α y + 𝔞 y) (x : M) (v : TangentSpace I x) :
    cov₁ (cov₁.roughLaplacian (∇ᵀ) α) x v =
      (r / 4 * (κ - ‖α x‖ ^ 2 - ‖β x‖ ^ 2)) • cov₁ α x v -
        (r / 2 * (⟪cov₁ α x v, α x⟫ + ⟪cov₂ β x v, β x⟫)) • α x + cov₁ 𝔞 x v := by
  have hfun : cov₁.roughLaplacian (∇ᵀ) α = (r / 4 * κ) • α -
      (r / 4) • ((fun y ↦ ‖α y‖ ^ 2) • α) - (r / 4) • ((fun y ↦ ‖β y‖ ^ 2) • α) + 𝔞 := by
    funext y
    rw [heq y]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply']
    module
  have hC := cov₁.isCovariantDerivativeOnUniv
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hsα : CMDiff ∞ (fun y ↦ ‖α y‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using hα.inner_bundle hα
  have hsβ : CMDiff ∞ (fun y ↦ ‖β y‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using hβ.inner_bundle hβ
  have h1 : CMDiff ∞ (T% ((r / 4 * κ) • α)) := hα.const_smul_section
  have h2 : CMDiff ∞ (T% ((r / 4) • ((fun y ↦ ‖α y‖ ^ 2) • α))) :=
    (hsα.smul_section hα).const_smul_section
  have h3 : CMDiff ∞ (T% ((r / 4) • ((fun y ↦ ‖β y‖ ^ 2) • α))) :=
    (hsβ.smul_section hα).const_smul_section
  have hαd := hα.mdifferentiableAt (x := x) hn
  rw [hfun, hC.add (((h1.sub_section h2).sub_section h3).mdifferentiableAt hn)
      (h𝔞.mdifferentiableAt hn), hC.sub ((h1.sub_section h2).mdifferentiableAt hn)
      (h3.mdifferentiableAt hn), hC.sub (h1.mdifferentiableAt hn) (h2.mdifferentiableAt hn),
    hC.smul_const _ hαd, hC.smul_const _ ((hsα.smul_section hα).mdifferentiableAt hn),
    hC.smul_const _ ((hsβ.smul_section hα).mdifferentiableAt hn)]
  simp only [add_apply, sub_apply, smul_apply]
  rw [hC.leibniz_apply hαd (hsα.mdifferentiableAt hn),
    hC.leibniz_apply hαd (hsβ.mdifferentiableAt hn),
    hcov₁.mvfderiv_norm_sq hαd, hcov₂.mvfderiv_norm_sq (hβ.mdifferentiableAt hn)]
  module


omit [ContMDiffCovariantDerivative cov₂ ∞] in
/-- The pairing of the differentiated projected equation with `∇α`, term by term in an orthonormal
basis `eⱼ`, bounded by the Cauchy–Schwarz inequality. -/
private theorem sum_inner_covariantDerivative_roughLaplacian_le (hcov₁ : cov₁.IsMetricCompatible)
    (hcov₂ : cov₂.IsMetricCompatible) (hα : CMDiff ∞ (T% α)) (hβ : CMDiff ∞ (T% β))
    (h𝔞 : CMDiff ∞ (T% 𝔞))
    (heq : ∀ y, cov₁.roughLaplacian (∇ᵀ) α y =
      (r / 4 * (κ - ‖α y‖ ^ 2 - ‖β y‖ ^ 2)) • α y + 𝔞 y) (hr : 0 ≤ r) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ j, ⟪cov₁ (cov₁.roughLaplacian (∇ᵀ) α) x (b j), cov₁ α x (b j)⟫ ≤
      ∑ j, (r / 4 * (κ - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) * ‖cov₁ α x (b j)‖ ^ 2 +
        r / 2 * ((‖cov₁ α x (b j)‖ * ‖α x‖ + ‖cov₂ β x (b j)‖ * ‖β x‖) *
          (‖α x‖ * ‖cov₁ α x (b j)‖)) + ‖cov₁ 𝔞 x (b j)‖ * ‖cov₁ α x (b j)‖) := by
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [covariantDerivative_roughLaplacian_apply hcov₁ hcov₂ hα hβ h𝔞 heq, inner_add_left,
    inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hp : |⟪cov₁ α x (b j), α x⟫ + ⟪cov₂ β x (b j), β x⟫| ≤
      ‖cov₁ α x (b j)‖ * ‖α x‖ + ‖cov₂ β x (b j)‖ * ‖β x‖ :=
    (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
  have hpq : -((⟪cov₁ α x (b j), α x⟫ + ⟪cov₂ β x (b j), β x⟫) * ⟪α x, cov₁ α x (b j)⟫) ≤
      (‖cov₁ α x (b j)‖ * ‖α x‖ + ‖cov₂ β x (b j)‖ * ‖β x‖) * (‖α x‖ * ‖cov₁ α x (b j)‖) := by
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul hp (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hpq (by positivity : 0 ≤ r / 2),
    real_inner_le_norm (cov₁ 𝔞 x (b j)) (cov₁ α x (b j))]


omit [ContMDiffCovariantDerivative cov₂ ∞] in
/-- **The differentiated Weitzenböck inequality for the first component.** Let `α` and `β` be
smooth sections of Riemannian bundles with metric connections, with
`∇*∇α = (r / 4) (1 - |α|² - |β|²) α + 𝔞` and `r ≥ 0`. At a point `x`, with an orthonormal basis
`eᵢ` of `n` elements, suppose `|α|, |β| ≤ B`, `|R(u, v) s| ≤ c_R |u| |v| |s|` for the curvature
of the connection on `α`, `|Rᵀ(u, v) w| ≤ c_T |u| |v| |w|` for the Riemann curvature,
`|∑ᵢ (∇_{eᵢ}R)(eⱼ, eᵢ) α| ≤ D` and `|∇_{eⱼ} 𝔞| ≤ D_𝔞` for every `j`. Then, with the Hilbert–Schmidt
norms `|∇α|`, `|∇β|`,

`-Δ|∇α|² / 2 + ∑ᵢⱼ |∇²α(eᵢ, eⱼ)|² ≤ n (r |∇α|² / 4 + (r / 2) B² (|∇α| + |∇β|) |∇α| +`
`  D_𝔞 |∇α|) + n (n (2 c_R + c_T) |∇α| + D) |∇α|`. -/
theorem neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le_of_roughLaplacian_eq
    (hcov₁ : cov₁.IsMetricCompatible) (hcov₂ : cov₂.IsMetricCompatible) (hα : CMDiff ∞ (T% α))
    (hβ : CMDiff ∞ (T% β)) (h𝔞 : CMDiff ∞ (T% 𝔞))
    (heq : ∀ y, cov₁.roughLaplacian (∇ᵀ) α y =
      (r / 4 * (1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2)) • α y + 𝔞 y) (hr : 0 ≤ r) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) {B cR cT D Da : ℝ}
    (hαB : ‖α x‖ ≤ B) (hβB : ‖β x‖ ≤ B)
    (hR : ∀ u v s, ‖cov₁.curvatureTensor x u v s‖ ≤ cR * ‖u‖ * ‖v‖ * ‖s‖)
    (hRT : ∀ u v w, ‖(∇ᵀ).curvatureTensor x u v w‖ ≤ cT * ‖u‖ * ‖v‖ * ‖w‖)
    (hD : ∀ j, ‖∑ i, cov₁.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (α x)‖ ≤ D)
    (hd𝔞 : ∀ j, ‖cov₁ 𝔞 x (b j)‖ ≤ Da) :
    -(laplaceBeltrami I (cov₁.innerCovariantDerivative α α) x / 2) +
        ∑ i, ∑ j, ‖cov₁.secondCovariantDerivative (∇ᵀ) α x (b i) (b j)‖ ^ 2 ≤
      Fintype.card ι * (r / 4 * √(cov₁.innerCovariantDerivative α α x) ^ 2 +
          r / 2 * B ^ 2 * (√(cov₁.innerCovariantDerivative α α x) +
            √(cov₂.innerCovariantDerivative β β x)) * √(cov₁.innerCovariantDerivative α α x) +
          Da * √(cov₁.innerCovariantDerivative α α x)) +
        Fintype.card ι * (Fintype.card ι * (2 * cR + cT) * √(cov₁.innerCovariantDerivative α α x) +
          D) * √(cov₁.innerCovariantDerivative α α x) := by
  refine (hcov₁.neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le hα x b hR hRT
    hD).trans (add_le_add ?_ le_rfl)
  refine (sum_inner_covariantDerivative_roughLaplacian_le hcov₁ hcov₂ hα hβ h𝔞 heq hr x b).trans ?_
  set A := √(cov₁.innerCovariantDerivative α α x)
  set G := √(cov₂.innerCovariantDerivative β β x)
  refine (Finset.sum_le_card_nsmul _ _ (r / 4 * A ^ 2 + r / 2 * B ^ 2 * (A + G) * A + Da * A)
    fun j _ ↦ ?_).trans_eq (by simp [mul_add])
  have ha : ‖cov₁ α x (b j)‖ ≤ A :=
    cov₁.norm_apply_orthonormalBasis_le_sqrt_innerCovariantDerivative α x b j
  have hg : ‖cov₂ β x (b j)‖ ≤ G :=
    cov₂.norm_apply_orthonormalBasis_le_sqrt_innerCovariantDerivative β x b j
  have hB : 0 ≤ B := (norm_nonneg _).trans hαB
  have h1 : r / 4 * (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) * ‖cov₁ α x (b j)‖ ^ 2 ≤ r / 4 * A ^ 2 := by
    have : 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (α x), norm_nonneg (β x)]
    calc _ ≤ r / 4 * 1 * ‖cov₁ α x (b j)‖ ^ 2 := by gcongr
      _ ≤ r / 4 * A ^ 2 := by rw [mul_one]; gcongr
  have h2 : (‖cov₁ α x (b j)‖ * ‖α x‖ + ‖cov₂ β x (b j)‖ * ‖β x‖) *
      (‖α x‖ * ‖cov₁ α x (b j)‖) ≤ B ^ 2 * (A + G) * A := by
    calc _ ≤ (A * B + G * B) * (B * A) := by gcongr
      _ = B ^ 2 * (A + G) * A := by ring
  have h3 : ‖cov₁ 𝔞 x (b j)‖ * ‖cov₁ α x (b j)‖ ≤ Da * A :=
    mul_le_mul (hd𝔞 j) ha (norm_nonneg _) ((norm_nonneg _).trans (hd𝔞 j))
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ r / 2)]


omit [ContMDiffCovariantDerivative cov₁ ∞] in
/-- **The differentiated Weitzenböck inequality for the second component.** Let `α` and `β` be
smooth sections of Riemannian bundles with metric connections, with
`∇*∇β + (r / 4) (1 + |α|² + |β|²) β = 𝔟` and `r ≥ 0`. At a point `x`, with an orthonormal basis
`eᵢ` of `n` elements, suppose `|α|, |β| ≤ B`, `|R(u, v) s| ≤ c_R |u| |v| |s|` for the curvature
of the connection on `β`, `|Rᵀ(u, v) w| ≤ c_T |u| |v| |w|` for the Riemann curvature,
`|∑ᵢ (∇_{eᵢ}R)(eⱼ, eᵢ) β| ≤ D` and `|∇_{eⱼ} 𝔟| ≤ D_𝔟` for every `j`. Then, with the Hilbert–Schmidt
norms `|∇α|`, `|∇β|`, the potential term has a good sign and

`-Δ|∇β|² / 2 + ∑ᵢⱼ |∇²β(eᵢ, eⱼ)|² ≤ n ((r / 2) B |β| (|∇α| + |∇β|) |∇β| + D_𝔟 |∇β|) +`
`  n (n (2 c_R + c_T) |∇β| + D) |∇β|`. -/
theorem neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le_of_roughLaplacian_add_eq
    (hcov₁ : cov₁.IsMetricCompatible) (hcov₂ : cov₂.IsMetricCompatible) (hα : CMDiff ∞ (T% α))
    (hβ : CMDiff ∞ (T% β)) (h𝔟 : CMDiff ∞ (T% 𝔟))
    (heq : ∀ y, cov₂.roughLaplacian (∇ᵀ) β y +
      (r / 4 * (1 + ‖α y‖ ^ 2 + ‖β y‖ ^ 2)) • β y = 𝔟 y) (hr : 0 ≤ r) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) {B cR cT D Db : ℝ}
    (hαB : ‖α x‖ ≤ B) (hβB : ‖β x‖ ≤ B)
    (hR : ∀ u v s, ‖cov₂.curvatureTensor x u v s‖ ≤ cR * ‖u‖ * ‖v‖ * ‖s‖)
    (hRT : ∀ u v w, ‖(∇ᵀ).curvatureTensor x u v w‖ ≤ cT * ‖u‖ * ‖v‖ * ‖w‖)
    (hD : ∀ j, ‖∑ i, cov₂.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (β x)‖ ≤ D)
    (hd𝔟 : ∀ j, ‖cov₂ 𝔟 x (b j)‖ ≤ Db) :
    -(laplaceBeltrami I (cov₂.innerCovariantDerivative β β) x / 2) +
        ∑ i, ∑ j, ‖cov₂.secondCovariantDerivative (∇ᵀ) β x (b i) (b j)‖ ^ 2 ≤
      Fintype.card ι * (r / 2 * B * ‖β x‖ * (√(cov₁.innerCovariantDerivative α α x) +
            √(cov₂.innerCovariantDerivative β β x)) * √(cov₂.innerCovariantDerivative β β x) +
          Db * √(cov₂.innerCovariantDerivative β β x)) +
        Fintype.card ι * (Fintype.card ι * (2 * cR + cT) * √(cov₂.innerCovariantDerivative β β x) +
          D) * √(cov₂.innerCovariantDerivative β β x) := by
  have heq' (y : M) : cov₂.roughLaplacian (∇ᵀ) β y =
      (r / 4 * (-1 - ‖β y‖ ^ 2 - ‖α y‖ ^ 2)) • β y + 𝔟 y := by
    rw [← heq y]
    module
  refine (hcov₂.neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le hβ x b hR hRT
    hD).trans (add_le_add ?_ le_rfl)
  refine (sum_inner_covariantDerivative_roughLaplacian_le hcov₂ hcov₁ hβ hα h𝔟 heq' hr x b).trans ?_
  set A := √(cov₁.innerCovariantDerivative α α x)
  set G := √(cov₂.innerCovariantDerivative β β x)
  refine (Finset.sum_le_card_nsmul _ _ (r / 2 * B * ‖β x‖ * (A + G) * G + Db * G)
    fun j _ ↦ ?_).trans_eq (by simp [mul_add])
  have ha : ‖cov₁ α x (b j)‖ ≤ A :=
    cov₁.norm_apply_orthonormalBasis_le_sqrt_innerCovariantDerivative α x b j
  have hg : ‖cov₂ β x (b j)‖ ≤ G :=
    cov₂.norm_apply_orthonormalBasis_le_sqrt_innerCovariantDerivative β x b j
  have hB : 0 ≤ B := (norm_nonneg _).trans hαB
  have h1 : r / 4 * (-1 - ‖β x‖ ^ 2 - ‖α x‖ ^ 2) * ‖cov₂ β x (b j)‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (by nlinarith [norm_nonneg (α x), norm_nonneg (β x)])) (sq_nonneg _)
  have h2 : (‖cov₂ β x (b j)‖ * ‖β x‖ + ‖cov₁ α x (b j)‖ * ‖α x‖) *
      (‖β x‖ * ‖cov₂ β x (b j)‖) ≤ B * ‖β x‖ * (A + G) * G := by
    calc _ ≤ (G * B + A * B) * (‖β x‖ * G) := by gcongr
      _ = B * ‖β x‖ * (A + G) * G := by ring
  have h3 : ‖cov₂ 𝔟 x (b j)‖ * ‖cov₂ β x (b j)‖ ≤ Db * G :=
    mul_le_mul (hd𝔟 j) hg (norm_nonneg _) ((norm_nonneg _).trans (hd𝔟 j))
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ r / 2)]

omit [∀ x, InnerProductSpace ℝ (V₂ x)] in
/-- **The Weitzenböck identity for the first component.** If
`∇*∇α = (r / 4) (1 - |α|² - |β|²) α + 𝔞`, then
`-Δ|α|² / 2 + |∇α|² + (r / 4) (|α|² + |β|² - 1) |α|² = ⟪𝔞, α⟫`, with the Hilbert–Schmidt norm
`|∇α|² = ⟪∇α, ∇α⟫`. -/
theorem neg_laplaceBeltrami_norm_sq_div_two_add_eq_inner_of_roughLaplacian_eq
    (hcov₁ : cov₁.IsMetricCompatible) (hα : CMDiff ∞ (T% α))
    (heq : ∀ y, cov₁.roughLaplacian (∇ᵀ) α y =
      (r / 4 * (1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2)) • α y + 𝔞 y) (x : M) :
    -(laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) x / 2) + cov₁.innerCovariantDerivative α α x +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖α x‖ ^ 2 = ⟪𝔞 x, α x⟫ := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [hcov₁.laplaceBeltrami_norm_sq hα x b, cov₁.innerCovariantDerivative_eq_sum α α x b, heq x,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [real_inner_self_eq_norm_sq]
  ring

omit [∀ x, InnerProductSpace ℝ (V₁ x)] in
/-- **The Weitzenböck identity for the second component.** If
`∇*∇β + (r / 4) (1 + |α|² + |β|²) β = 𝔟`, then
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² = ⟪𝔟, β⟫`, with the Hilbert–Schmidt norm
`|∇β|² = ⟪∇β, ∇β⟫`. -/
theorem neg_laplaceBeltrami_norm_sq_div_two_add_eq_inner_of_roughLaplacian_add_eq
    (hcov₂ : cov₂.IsMetricCompatible) (hβ : CMDiff ∞ (T% β))
    (heq : ∀ y, cov₂.roughLaplacian (∇ᵀ) β y +
      (r / 4 * (1 + ‖α y‖ ^ 2 + ‖β y‖ ^ 2)) • β y = 𝔟 y) (x : M) :
    -(laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) x / 2) + cov₂.innerCovariantDerivative β β x +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 = ⟪𝔟 x, β x⟫ := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [hcov₂.laplaceBeltrami_norm_sq hβ x b, cov₂.innerCovariantDerivative_eq_sum β β x b, ← heq x,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [real_inner_self_eq_norm_sq]
  ring


/-- Comparison of coefficients: if `0 ≤ X, Y, Z, W` then
`(1/4 + B²/2 + 4c) X + (B²/2 + c) Y + c Z + c W ≤ 4 (1 + c) (1 + B²) (X + Y + Z + W)`. -/
private theorem coeff_le {c B X Y Z W : ℝ} (hc : 0 ≤ c) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hW : 0 ≤ W) :
    (1 / 4 + B ^ 2 / 2 + 4 * c) * X + (B ^ 2 / 2 + c) * Y + c * Z + c * W ≤
      4 * (1 + c) * (1 + B ^ 2) * (X + Y + Z + W) := by
  have hB := sq_nonneg B
  have hcB := mul_nonneg hc hB
  nlinarith [mul_nonneg hcB hX, mul_nonneg hcB hY, mul_nonneg hcB hZ, mul_nonneg hcB hW,
    mul_nonneg hB hX, mul_nonneg hB hY, mul_nonneg hB hZ, mul_nonneg hB hW, mul_nonneg hc hX,
    mul_nonneg hc hY, mul_nonneg hc hZ, mul_nonneg hc hW]

/-- The arithmetic of the second-order inequality for the first component. -/
private theorem canonical_arith_le {n r c B A G N : ℝ} (hn : n ≤ n ^ 2)
    (hr : 1 ≤ r) (hc : 0 ≤ c) (hA : 0 ≤ A) (hG : 0 ≤ G) (hN : 0 ≤ N) :
    n * (r / 4 * A ^ 2 + r / 2 * B ^ 2 * (A + G) * A + c * (N + A + G + 1) * A) +
        n * (n * (2 * (c * r) + c) * A + c * r * (A + G + 1)) * A ≤
      n ^ 2 * (4 * (1 + c) * (1 + B ^ 2)) *
        (r * (A ^ 2 + A * G + A) + (N + A + G + 1) * A) := by
  have hX : 0 ≤ r * A ^ 2 := by positivity
  have hY : 0 ≤ r * (A * G) := by positivity
  have hZ : 0 ≤ r * A := by positivity
  have hW : 0 ≤ (N + A + G + 1) * A := by positivity
  have hA2 : n ^ 2 * c * A ^ 2 ≤ n ^ 2 * c * (r * A ^ 2) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (sq_nonneg A) hr) (by positivity)
  have hdiff : 0 ≤ n ^ 2 - n := sub_nonneg.2 hn
  have hB := sq_nonneg B
  -- Bound `n` by `n²` in every term, then compare coefficients.
  have h1 : n * (r / 4 * A ^ 2 + r / 2 * B ^ 2 * (A + G) * A + c * (N + A + G + 1) * A) +
      n * (n * (2 * (c * r) + c) * A + c * r * (A + G + 1)) * A ≤
      n ^ 2 * ((1 / 4 + B ^ 2 / 2 + 4 * c) * (r * A ^ 2) + (B ^ 2 / 2 + c) * (r * (A * G)) +
        c * (r * A) + c * ((N + A + G + 1) * A)) := by
    nlinarith [mul_nonneg hdiff hX, mul_nonneg hdiff hY, mul_nonneg hdiff hZ, mul_nonneg hdiff hW,
      mul_nonneg (mul_nonneg hdiff hB) hX, mul_nonneg (mul_nonneg hdiff hB) hY,
      mul_nonneg (mul_nonneg hdiff hc) hX, mul_nonneg (mul_nonneg hdiff hc) hY,
      mul_nonneg (mul_nonneg hdiff hc) hZ, mul_nonneg (mul_nonneg hdiff hc) hW]
  refine h1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((coeff_le hc hX hY hZ hW).trans_eq ?_) (sq_nonneg n)
  ring


/-- The arithmetic of the second-order inequality for the second component. -/
private theorem complement_arith_le {n r c B b A G N : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ n ^ 2)
    (hr : 1 ≤ r)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hb : 0 ≤ b) (hA : 0 ≤ A) (hG : 0 ≤ G) (hN : 0 ≤ N) :
    n * (r / 2 * B * b * (A + G) * G + c * (N + A + G + 1) * G) +
        n * (n * (2 * (c * r) + c) * G + c * r * b * (A + G + 1)) * G ≤
      n ^ 2 * (4 * (1 + c) * (1 + B ^ 2)) *
        (r * (G ^ 2 + b * (A + G + 1) * G) + (N + A + G + 1) * G) := by
  have hP : 0 ≤ r * (b * (A + G + 1) * G) := by positivity
  have hX : 0 ≤ r * G ^ 2 := by positivity
  have hW : 0 ≤ (N + A + G + 1) * G := by positivity
  have hdiff : 0 ≤ n ^ 2 - n := sub_nonneg.2 hn
  have hG2 : n ^ 2 * c * G ^ 2 ≤ n ^ 2 * c * (r * G ^ 2) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (sq_nonneg G) hr) (by positivity)
  have hPG : r * B * b * (A + G) * G ≤ B * (r * (b * (A + G + 1) * G)) := by
    have : 0 ≤ r * B * b * G := by positivity
    nlinarith
  have h1 : n * (r / 2 * B * b * (A + G) * G + c * (N + A + G + 1) * G) +
      n * (n * (2 * (c * r) + c) * G + c * r * b * (A + G + 1)) * G ≤
      n ^ 2 * ((B / 2 + c) * (r * (b * (A + G + 1) * G)) + 3 * c * (r * G ^ 2) +
        c * ((N + A + G + 1) * G)) := by
    nlinarith [mul_nonneg hdiff hP, mul_nonneg hdiff hW, mul_nonneg (mul_nonneg hdiff hB) hP,
      mul_nonneg (mul_nonneg hdiff hc) hP, mul_nonneg (mul_nonneg hdiff hc) hW,
      mul_le_mul_of_nonneg_left hPG (by positivity : 0 ≤ n / 2)]
  refine h1.trans ?_
  rw [mul_assoc (n ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg n)
  have hB1 : B / 2 + c ≤ 4 * (1 + c) * (1 + B ^ 2) := by nlinarith [sq_nonneg (B - 1)]
  have h3 : 3 * c ≤ 4 * (1 + c) * (1 + B ^ 2) := by nlinarith [sq_nonneg B]
  have h4 : c ≤ 4 * (1 + c) * (1 + B ^ 2) := by nlinarith [sq_nonneg B]
  nlinarith [mul_le_mul_of_nonneg_right hB1 hP, mul_le_mul_of_nonneg_right h3 hX,
    mul_le_mul_of_nonneg_right h4 hW]


/-- The bound `a² + b² ≤ 1 + C / r` with `C ≥ 0` and `r ≥ 1` gives `a ≤ 1 + C`. -/
private theorem le_one_add_of_sq_add_sq_le {r C a b : ℝ} (hr : 1 ≤ r) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (h : a ^ 2 + b ^ 2 ≤ 1 + C / r) : a ≤ 1 + C := by
  have hCr : C / r ≤ C := div_le_self hC hr
  nlinarith [sq_nonneg b]

omit [FiniteDimensional ℝ F₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  [IsContMDiffRiemannianBundle I ∞ F₂ V₂] [ContMDiffCovariantDerivative cov₂ ∞] in
/-- The first-order inequality for `α`, with the constant of the gradient bound. -/
private theorem firstOrder_canonical_le (hcov₁ : cov₁.IsMetricCompatible) (hα : CMDiff ∞ (T% α))
    (heqα : ∀ y, cov₁.roughLaplacian (∇ᵀ) α y =
      (r / 4 * (1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2)) • α y + 𝔞 y) {c K : ℝ} (hK : 0 ≤ K) (y : M)
    (h𝔞₀ : ‖𝔞 y‖ ≤ c * (√(cov₂.innerCovariantDerivative β β y) + ‖α y‖ + ‖β y‖)) :
    -laplaceBeltrami I (fun x ↦ ‖α x‖ ^ 2) y / 2 + √(cov₁.innerCovariantDerivative α α y) ^ 2 +
        r / 4 * (‖α y‖ ^ 2 + ‖β y‖ ^ 2 - 1) * ‖α y‖ ^ 2 ≤
      (c + K) * ‖α y‖ * (√(cov₂.innerCovariantDerivative β β y) + ‖α y‖ + ‖β y‖) := by
  have h := neg_laplaceBeltrami_norm_sq_div_two_add_eq_inner_of_roughLaplacian_eq hcov₁ hα heqα y
  have h1 := (real_inner_le_norm (𝔞 y) (α y)).trans
    (mul_le_mul_of_nonneg_right h𝔞₀ (norm_nonneg (α y)))
  rw [Real.sq_sqrt (cov₁.innerCovariantDerivative_self_nonneg α y)]
  have h2 : 0 ≤ ‖α y‖ * (√(cov₂.innerCovariantDerivative β β y) + ‖α y‖ + ‖β y‖) := by
    positivity
  nlinarith [mul_nonneg hK h2]

omit [FiniteDimensional ℝ F₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  [IsContMDiffRiemannianBundle I ∞ F₁ V₁] [ContMDiffCovariantDerivative cov₁ ∞] in
/-- The first-order inequality for `β`, with the constant of the gradient bound. -/
private theorem firstOrder_complement_le (hcov₂ : cov₂.IsMetricCompatible) (hβ : CMDiff ∞ (T% β))
    (heqβ : ∀ y, cov₂.roughLaplacian (∇ᵀ) β y +
      (r / 4 * (1 + ‖α y‖ ^ 2 + ‖β y‖ ^ 2)) • β y = 𝔟 y) {c K : ℝ} (hK : 0 ≤ K) (y : M)
    (h𝔟₀ : ‖𝔟 y‖ ≤ c * (√(cov₁.innerCovariantDerivative α α y) + ‖α y‖ + ‖β y‖)) :
    -laplaceBeltrami I (fun x ↦ ‖β x‖ ^ 2) y / 2 + √(cov₂.innerCovariantDerivative β β y) ^ 2 +
        r / 4 * (‖α y‖ ^ 2 + ‖β y‖ ^ 2 + 1) * ‖β y‖ ^ 2 ≤
      (c + K) * ‖β y‖ * (√(cov₁.innerCovariantDerivative α α y) + ‖α y‖ + ‖β y‖) := by
  have h := neg_laplaceBeltrami_norm_sq_div_two_add_eq_inner_of_roughLaplacian_add_eq hcov₂ hβ
    heqβ y
  have h1 := (real_inner_le_norm (𝔟 y) (β y)).trans
    (mul_le_mul_of_nonneg_right h𝔟₀ (norm_nonneg (β y)))
  rw [Real.sq_sqrt (cov₂.innerCovariantDerivative_self_nonneg β y)]
  have h2 : 0 ≤ ‖β y‖ * (√(cov₁.innerCovariantDerivative α α y) + ‖α y‖ + ‖β y‖) := by
    positivity
  nlinarith [mul_nonneg hK h2]

/-- The second-order inequality for `α`, with the constant of the gradient bound, in the standard
orthonormal basis `b` at `y`, for `A = |∇α|`, `G = |∇β|` and `N = |∇²β|`. -/
private theorem secondOrder_canonical_le (hcov₁ : cov₁.IsMetricCompatible)
    (hcov₂ : cov₂.IsMetricCompatible) (hα : CMDiff ∞ (T% α)) (hβ : CMDiff ∞ (T% β))
    (h𝔞 : CMDiff ∞ (T% 𝔞))
    (heqα : ∀ y, cov₁.roughLaplacian (∇ᵀ) α y =
      (r / 4 * (1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2)) • α y + 𝔞 y)
    {c B A G N : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) (y : M) (hαB : ‖α y‖ ≤ B) (hβB : ‖β y‖ ≤ B)
    (hA : √(cov₁.innerCovariantDerivative α α y) = A)
    (hG : √(cov₂.innerCovariantDerivative β β y) = G)
    (hN : √(∑ i, ∑ j, ‖cov₂.secondCovariantDerivative (∇ᵀ) β y
      (stdOrthonormalBasis ℝ (TangentSpace I y) i)
      (stdOrthonormalBasis ℝ (TangentSpace I y) j)‖ ^ 2) = N)
    (h𝔞₁ : ‖cov₁ 𝔞 y‖ ≤ c * (N + A + G + 1))
    (hR₁ : ∀ u v s, ‖cov₁.curvatureTensor y u v s‖ ≤ c * r * ‖u‖ * ‖v‖ * ‖s‖)
    (hRT : ∀ u v w, ‖(∇ᵀ).curvatureTensor y u v w‖ ≤ c * ‖u‖ * ‖v‖ * ‖w‖)
    (hD₁ : ∀ j, ‖∑ i, cov₁.derivCurvatureTensor (∇ᵀ) y
      (stdOrthonormalBasis ℝ (TangentSpace I y) i) (stdOrthonormalBasis ℝ (TangentSpace I y) j)
      (stdOrthonormalBasis ℝ (TangentSpace I y) i) (α y)‖ ≤ c * r * (A + G + 1)) :
    -laplaceBeltrami I (cov₁.innerCovariantDerivative α α) y / 2 +
        ∑ i, ∑ j, ‖cov₁.secondCovariantDerivative (∇ᵀ) α y
          (stdOrthonormalBasis ℝ (TangentSpace I y) i)
          (stdOrthonormalBasis ℝ (TangentSpace I y) j)‖ ^ 2 ≤
      (c + 4 * (finrank ℝ E : ℝ) ^ 2 * (1 + c) * (1 + B ^ 2)) *
        (r * (A ^ 2 + A * G + A) + (N + A + G + 1) * A) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I y)
  have h := neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le_of_roughLaplacian_eq
    hcov₁ hcov₂ hα hβ h𝔞 heqα (by linarith) y b hαB hβB hR₁ hRT (hA ▸ hG ▸ hD₁)
    (Da := c * (N + A + G + 1)) fun j ↦ ((cov₁ 𝔞 y).le_opNorm (b j)).trans
      (by rw [b.orthonormal.1 j, mul_one]; exact h𝔞₁)
  -- The tangent space `TangentSpace I y` is the model space `E`, with the same dimension.
  simp only [Fintype.card_fin, finrank_tangentSpace, hA, hG] at h
  have h2 := canonical_arith_le (n := finrank ℝ E) (B := B) (A := A) (G := G) (N := N)
    (by exact_mod_cast Nat.le_self_pow two_ne_zero (finrank ℝ E)) hr hc
    (hA ▸ Real.sqrt_nonneg _) (hG ▸ Real.sqrt_nonneg _) (hN ▸ Real.sqrt_nonneg _)
  have hX : 0 ≤ r * (A ^ 2 + A * G + A) + (N + A + G + 1) * A := by
    have : 0 ≤ r := by linarith
    have : 0 ≤ A := hA ▸ Real.sqrt_nonneg _
    have : 0 ≤ G := hG ▸ Real.sqrt_nonneg _
    have : 0 ≤ N := hN ▸ Real.sqrt_nonneg _
    positivity
  nlinarith [mul_nonneg hc hX]

/-- The second-order inequality for `β`, with the constant of the gradient bound, in the standard
orthonormal basis `b` at `y`, for `A = |∇α|`, `G = |∇β|` and `N = |∇²α|`. -/
private theorem secondOrder_complement_le (hcov₁ : cov₁.IsMetricCompatible)
    (hcov₂ : cov₂.IsMetricCompatible) (hα : CMDiff ∞ (T% α)) (hβ : CMDiff ∞ (T% β))
    (h𝔟 : CMDiff ∞ (T% 𝔟))
    (heqβ : ∀ y, cov₂.roughLaplacian (∇ᵀ) β y +
      (r / 4 * (1 + ‖α y‖ ^ 2 + ‖β y‖ ^ 2)) • β y = 𝔟 y)
    {c B A G N : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) (y : M) (hαB : ‖α y‖ ≤ B) (hβB : ‖β y‖ ≤ B)
    (hA : √(cov₁.innerCovariantDerivative α α y) = A)
    (hG : √(cov₂.innerCovariantDerivative β β y) = G)
    (hN : √(∑ i, ∑ j, ‖cov₁.secondCovariantDerivative (∇ᵀ) α y
      (stdOrthonormalBasis ℝ (TangentSpace I y) i)
      (stdOrthonormalBasis ℝ (TangentSpace I y) j)‖ ^ 2) = N)
    (h𝔟₁ : ‖cov₂ 𝔟 y‖ ≤ c * (N + A + G + 1))
    (hR₂ : ∀ u v s, ‖cov₂.curvatureTensor y u v s‖ ≤ c * r * ‖u‖ * ‖v‖ * ‖s‖)
    (hRT : ∀ u v w, ‖(∇ᵀ).curvatureTensor y u v w‖ ≤ c * ‖u‖ * ‖v‖ * ‖w‖)
    (hD₂ : ∀ j, ‖∑ i, cov₂.derivCurvatureTensor (∇ᵀ) y
      (stdOrthonormalBasis ℝ (TangentSpace I y) i) (stdOrthonormalBasis ℝ (TangentSpace I y) j)
      (stdOrthonormalBasis ℝ (TangentSpace I y) i) (β y)‖ ≤ c * r * ‖β y‖ * (A + G + 1)) :
    -laplaceBeltrami I (cov₂.innerCovariantDerivative β β) y / 2 +
        ∑ i, ∑ j, ‖cov₂.secondCovariantDerivative (∇ᵀ) β y
          (stdOrthonormalBasis ℝ (TangentSpace I y) i)
          (stdOrthonormalBasis ℝ (TangentSpace I y) j)‖ ^ 2 ≤
      (c + 4 * (finrank ℝ E : ℝ) ^ 2 * (1 + c) * (1 + B ^ 2)) *
        (r * (G ^ 2 + ‖β y‖ * (A + G + 1) * G) + (N + A + G + 1) * G) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I y)
  have h :=
    neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le_of_roughLaplacian_add_eq
    hcov₁ hcov₂ hα hβ h𝔟 heqβ (by linarith) y b hαB hβB hR₂ hRT (hA ▸ hG ▸ hD₂)
    (Db := c * (N + A + G + 1)) fun j ↦ ((cov₂ 𝔟 y).le_opNorm (b j)).trans
      (by rw [b.orthonormal.1 j, mul_one]; exact h𝔟₁)
  -- The tangent space `TangentSpace I y` is the model space `E`, with the same dimension.
  simp only [Fintype.card_fin, finrank_tangentSpace, hA, hG] at h
  have h2 := complement_arith_le (n := finrank ℝ E) (B := B) (A := A) (G := G) (N := N)
    (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_self_pow two_ne_zero (finrank ℝ E)) hr hc
    ((norm_nonneg _).trans hαB) (norm_nonneg (β y)) (hA ▸ Real.sqrt_nonneg _)
    (hG ▸ Real.sqrt_nonneg _) (hN ▸ Real.sqrt_nonneg _)
  have hX : 0 ≤ r * (G ^ 2 + ‖β y‖ * (A + G + 1) * G) + (N + A + G + 1) * G := by
    have : 0 ≤ r := by linarith
    have : 0 ≤ A := hA ▸ Real.sqrt_nonneg _
    have : 0 ≤ G := hG ▸ Real.sqrt_nonneg _
    have : 0 ≤ N := hN ▸ Real.sqrt_nonneg _
    positivity
  nlinarith [mul_nonneg hc hX]

/-- **Taubes's gradient bound for the projected Weitzenböck system.** On a compact boundaryless
Riemannian manifold of dimension `n`, let `α` and `β` be smooth sections of Riemannian bundles with
metric connections solving

`∇*∇α = (r / 4) (1 - |α|² - |β|²) α + 𝔞`,   `∇*∇β + (r / 4) (1 + |α|² + |β|²) β = 𝔟`,

with `r ≥ 1`. Suppose that for a constant `c ≥ 0`, with the Hilbert–Schmidt norms `|∇α|`, `|∇β|`
and `|∇²α|² = ∑ᵢⱼ |∇²α(eᵢ, eⱼ)|²` in the standard orthonormal basis `eᵢ` at each point:

* `|𝔞| ≤ c (|∇β| + |α| + |β|)`, `|𝔟| ≤ c (|∇α| + |α| + |β|)`, and the operator norms
  `|∇𝔞| ≤ c (|∇²β| + |∇α| + |∇β| + 1)`, `|∇𝔟| ≤ c (|∇²α| + |∇α| + |∇β| + 1)`;
* the curvatures of both connections are at most `c r` and the Riemann curvature at most `c`;
* the divergences of the curvatures satisfy
  `|∑ᵢ (∇_{eᵢ}R₁)(eⱼ, eᵢ) α| ≤ c r (|∇α| + |∇β| + 1)` and
  `|∑ᵢ (∇_{eᵢ}R₂)(eⱼ, eᵢ) β| ≤ c r |β| (|∇α| + |∇β| + 1)`;
* the coarse bounds `|α|² + |β|² ≤ 1 + C / r` and `|β|² ≤ (C / r) w₊ + C / r²` hold, with
  `w₊ = max (1 - |α|²) 0`.

Then `|∇α|² + r |∇β|² ≤ C' r w₊ + C'` everywhere, with `C' = 150 (1 + c' + C)⁵` and
`c' = c + 4 n² (1 + c) (1 + (1 + C)²)`, independent of `r` and of the solution. -/
theorem innerCovariantDerivative_self_add_mul_innerCovariantDerivative_self_le [CompactSpace M]
    [I.Boundaryless] (hcov₁ : cov₁.IsMetricCompatible) (hcov₂ : cov₂.IsMetricCompatible)
    (hα : CMDiff ∞ (T% α)) (hβ : CMDiff ∞ (T% β)) (h𝔞 : CMDiff ∞ (T% 𝔞))
    (h𝔟 : CMDiff ∞ (T% 𝔟))
    (heqα : ∀ y, cov₁.roughLaplacian (∇ᵀ) α y =
      (r / 4 * (1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2)) • α y + 𝔞 y)
    (heqβ : ∀ y, cov₂.roughLaplacian (∇ᵀ) β y +
      (r / 4 * (1 + ‖α y‖ ^ 2 + ‖β y‖ ^ 2)) • β y = 𝔟 y)
    {c C : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r)
    (hs : ∀ x, ‖α x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + C / r)
    (ht : ∀ x, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2)
    (h𝔞₀ : ∀ x, ‖𝔞 x‖ ≤ c * (√(cov₂.innerCovariantDerivative β β x) + ‖α x‖ + ‖β x‖))
    (h𝔟₀ : ∀ x, ‖𝔟 x‖ ≤ c * (√(cov₁.innerCovariantDerivative α α x) + ‖α x‖ + ‖β x‖))
    (h𝔞₁ : ∀ x, ‖cov₁ 𝔞 x‖ ≤ c * (√(∑ i, ∑ j, ‖cov₂.secondCovariantDerivative (∇ᵀ) β x
        (stdOrthonormalBasis ℝ (TangentSpace I x) i)
        (stdOrthonormalBasis ℝ (TangentSpace I x) j)‖ ^ 2) +
      √(cov₁.innerCovariantDerivative α α x) + √(cov₂.innerCovariantDerivative β β x) + 1))
    (h𝔟₁ : ∀ x, ‖cov₂ 𝔟 x‖ ≤ c * (√(∑ i, ∑ j, ‖cov₁.secondCovariantDerivative (∇ᵀ) α x
        (stdOrthonormalBasis ℝ (TangentSpace I x) i)
        (stdOrthonormalBasis ℝ (TangentSpace I x) j)‖ ^ 2) +
      √(cov₁.innerCovariantDerivative α α x) + √(cov₂.innerCovariantDerivative β β x) + 1))
    (hR₁ : ∀ x u v s, ‖cov₁.curvatureTensor x u v s‖ ≤ c * r * ‖u‖ * ‖v‖ * ‖s‖)
    (hR₂ : ∀ x u v s, ‖cov₂.curvatureTensor x u v s‖ ≤ c * r * ‖u‖ * ‖v‖ * ‖s‖)
    (hRT : ∀ x u v w, ‖(∇ᵀ).curvatureTensor x u v w‖ ≤ c * ‖u‖ * ‖v‖ * ‖w‖)
    (hD₁ : ∀ x j, ‖∑ i, cov₁.derivCurvatureTensor (∇ᵀ) x
        (stdOrthonormalBasis ℝ (TangentSpace I x) i) (stdOrthonormalBasis ℝ (TangentSpace I x) j)
        (stdOrthonormalBasis ℝ (TangentSpace I x) i) (α x)‖ ≤
      c * r * (√(cov₁.innerCovariantDerivative α α x) + √(cov₂.innerCovariantDerivative β β x) + 1))
    (hD₂ : ∀ x j, ‖∑ i, cov₂.derivCurvatureTensor (∇ᵀ) x
        (stdOrthonormalBasis ℝ (TangentSpace I x) i) (stdOrthonormalBasis ℝ (TangentSpace I x) j)
        (stdOrthonormalBasis ℝ (TangentSpace I x) i) (β x)‖ ≤
      c * r * ‖β x‖ *
        (√(cov₁.innerCovariantDerivative α α x) + √(cov₂.innerCovariantDerivative β β x) + 1))
    (x : M) :
    cov₁.innerCovariantDerivative α α x + r * cov₂.innerCovariantDerivative β β x ≤
      150 * (1 + (c + 4 * finrank ℝ E ^ 2 * (1 + c) * (1 + (1 + C) ^ 2)) + C) ^ 5 * r *
          max (1 - ‖α x‖ ^ 2) 0 +
        150 * (1 + (c + 4 * finrank ℝ E ^ 2 * (1 + c) * (1 + (1 + C) ^ 2)) + C) ^ 5 := by
  have hC : 0 ≤ C := nonneg_of_sq_le hr (ht x)
  have hB (y : M) : ‖α y‖ ≤ 1 + C ∧ ‖β y‖ ≤ 1 + C :=
    ⟨le_one_add_of_sq_add_sq_le hr hC (norm_nonneg _) (hs y),
      le_one_add_of_sq_add_sq_le hr hC (norm_nonneg _) ((add_comm _ _).trans_le (hs y))⟩
  have hK0 : 0 ≤ 4 * (finrank ℝ E : ℝ) ^ 2 * (1 + c) * (1 + (1 + C) ^ 2) := by positivity
  have hsq {t : ℝ} (h : 0 ≤ t) : ‖√t‖ ^ 2 = t := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt h]
  have hnorm (t : ℝ) : ‖√t‖ = √t := Real.norm_of_nonneg (Real.sqrt_nonneg _)
  have hα₂ : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖α y‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using (hα.inner_bundle hα).of_le (by simp)
  have hβ₂ : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖β y‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using (hβ.inner_bundle hβ).of_le (by simp)
  have hfα : (fun y ↦ ‖√(cov₁.innerCovariantDerivative α α y)‖ ^ 2) =
      cov₁.innerCovariantDerivative α α :=
    funext fun y ↦ hsq (cov₁.innerCovariantDerivative_self_nonneg α y)
  have hfβ : (fun y ↦ ‖√(cov₂.innerCovariantDerivative β β y)‖ ^ 2) =
      cov₂.innerCovariantDerivative β β :=
    funext fun y ↦ hsq (cov₂.innerCovariantDerivative_self_nonneg β y)
  -- Apply the maximum-principle bound with `Dα = |∇α|`, `Dβ = |∇β|` and the norms of the
  -- second covariant derivatives in the standard orthonormal basis.
  have key := norm_sq_add_mul_norm_sq_le
    (c := c + 4 * (finrank ℝ E : ℝ) ^ 2 * (1 + c) * (1 + (1 + C) ^ 2)) (by positivity) hr hα₂ hβ₂
    (Dα := fun y ↦ √(cov₁.innerCovariantDerivative α α y))
    (Dβ := fun y ↦ √(cov₂.innerCovariantDerivative β β y))
    (D2α := fun y ↦ √(∑ i, ∑ j, ‖cov₁.secondCovariantDerivative (∇ᵀ) α y
        (stdOrthonormalBasis ℝ (TangentSpace I y) i)
        (stdOrthonormalBasis ℝ (TangentSpace I y) j)‖ ^ 2))
    (D2β := fun y ↦ √(∑ i, ∑ j, ‖cov₂.secondCovariantDerivative (∇ᵀ) β y
        (stdOrthonormalBasis ℝ (TangentSpace I y) i)
        (stdOrthonormalBasis ℝ (TangentSpace I y) j)‖ ^ 2))
    (by rw [hfα]; exact (cov₁.contMDiff_innerCovariantDerivative hα hα).of_le (by simp))
    (by rw [hfβ]; exact (cov₂.contMDiff_innerCovariantDerivative hβ hβ).of_le (by simp))
    (fun y ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_) hs ht x
  rotate_left
  · simp only [hnorm]
    exact firstOrder_canonical_le hcov₁ hα heqα hK0 y (h𝔞₀ y)
  · simp only [hnorm]
    exact firstOrder_complement_le hcov₂ hβ heqβ hK0 y (h𝔟₀ y)
  · rw [hfα, hsq (by positivity)]
    simp only [hnorm]
    exact secondOrder_canonical_le hcov₁ hcov₂ hα hβ h𝔞 heqα hc hr y (hB y).1 (hB y).2 rfl rfl rfl
      (h𝔞₁ y) (hR₁ y) (hRT y) (hD₁ y)
  · rw [hfβ, hsq (by positivity)]
    simp only [hnorm]
    exact secondOrder_complement_le hcov₁ hcov₂ hα hβ h𝔟 heqβ hc hr y (hB y).1 (hB y).2 rfl rfl
      rfl (h𝔟₁ y) (hR₂ y) (hRT y) (hD₂ y)
  simpa only [hsq (cov₁.innerCovariantDerivative_self_nonneg α x),
    hsq (cov₂.innerCovariantDerivative_self_nonneg β x)] using key

end TauCeti.SeibergWitten
