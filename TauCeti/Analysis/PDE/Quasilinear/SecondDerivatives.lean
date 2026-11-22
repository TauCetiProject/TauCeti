/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.DivergenceForm
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Quasilinear.Regularity
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Holder

/-!
# Interior `C^{2,α}` regularity for quasilinear divergence-form equations

Let `Ω ⊆ ℝⁿ⁺¹` be open, let `0 < α < 1`, and consider the quasilinear divergence-form equation

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f` in `Ω`,

whose coefficient matrix depends on the solution. Suppose that `A(·, s)` is uniformly elliptic
with constants `λ, Λ` for every `s`, that the entries of `A` are `C¹` jointly in `(x, s)` on
`Ω × ℝ` with locally `α`-Hölder derivatives, and that `f` is locally `α`-Hölder on `Ω`. This file
proves that the second derivatives of every weak solution `u ∈ H¹(Ω)` are locally `α`-Hölder
(`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_quasilinear_eq`,
in the `TauCeti.PDE` namespace): on every open `V` whose closure is compact and contained in `Ω`,
each weak derivative `∂ₑu` lies in `H¹(V)`, and the precise representative of its gradient is
`α`-Hölder on every compact subset of `V`. This is interior `C^{2,α}` regularity, the same
conclusion as for the linear equation with `C^{1,α}` coefficients
(`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_contDiffOn`).

No bound on `A` or on its derivatives that is uniform in `s` is assumed, and no integrability of
`f` on `Ω`: only the values of `A` on compact subsets of `Ω × ℝ` and of `f` on compact subsets of
`Ω` enter. The equation is tested against test functions, so `f` need only be locally integrable.

## The bootstrap

* **Continuity.** A weak solution `u` solves the linear equation with the frozen coefficient
  `a(x) = A(x, u(x))`, which is measurable and uniformly elliptic, so De Giorgi's theorem makes the
  precise representative `ū` of `u` continuous on `Ω`
  (`TauCeti.PDE.continuousOn_preciseRepresentative_of_forall_memLp`).
* **The gradient is `α`-Hölder.** On a ball `B` with closure in `Ω`, `ū` is bounded by some `M`.
  Replacing `A(x, s)` by `A(x, max (-M) (min M s))` does not change the equation on `B`, and the
  truncated coefficient is Lipschitz in `(x, s)` on `B × ℝ`, since `A` is `C¹` on the compact
  convex set `closure B × [-M, M]`. The interior `C^{1,β}` theorem for quasilinear equations
  (`exists_holderOnWith_preciseRepresentative_gradient_of_forall_energyFormH1_quasilinear_eq`)
  then makes the precise representative of `∇u` `α`-Hölder near the centre of `B`.
* **`ū` is `C¹`.** A continuous function with a continuous weak derivative is `C¹`
  (`TauCeti.HasWeakFDerivOn.hasFDerivAt_of_continuousOn`), so `ū` is `C¹` on `Ω` and its
  derivative is the precise representative of `∇u`.
* **The frozen coefficient is `C^{1,α}`.** By the chain rule, the derivative of
  `x ↦ A(x, ū(x))` is `DA(x, ū(x)) ∘ (id, Dū(x))`, a product of two locally `α`-Hölder fields.
* **Linear `C^{2,α}` regularity.** On an open neighbourhood of the closure of `V` with compact
  closure in `Ω`, `u` solves the linear equation with the `C^{1,α}` coefficient
  `x ↦ A(x, ū(x))` and the bounded datum `f`, and the linear theorem applies.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.32 and 8.10, and the regularity of quasilinear equations in Chapter 13.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

variable {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
  {α : ℝ≥0} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {u : W1p volume Omega 2}

/-- The entries of `A(x, s)` for fixed `x ∈ Ω`, as functions of `s`, and for fixed `s`, as
functions of `x ∈ Ω`, are continuous. -/
private theorem continuous_apply_and_continuousOn_apply
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ)) :
    (∀ x ∈ Omega, Continuous (A x)) ∧ ∀ s, ContinuousOn (fun x => A x s) Omega := by
  constructor
  · intro x hx
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (hAC i j).continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨hx, trivial⟩
  · intro s
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact (hAC i j).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      fun _ hx => ⟨hx, trivial⟩

/-- A coefficient that is continuous in `(x, s)` on `Ω × ℝ`, frozen at a measurable function, is
measurable on `Ω`. -/
private theorem aestronglyMeasurable_comp_of_contDiffOn
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    {v : E → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    AEStronglyMeasurable (fun x => A x (v x)) (volume.restrict Omega) :=
  hv.apply_of_forall_of_continuousAt
    (fun s => ((continuous_apply_and_continuousOn_apply hAC).2 s).aestronglyMeasurable
      Omega.isOpen.measurableSet)
    (ae_restrict_of_forall_mem Omega.isOpen.measurableSet fun x hx =>
      ((continuous_apply_and_continuousOn_apply hAC).1 x hx).continuousAt)

/-- The coefficient field `A(·, u(·))` frozen at a weak solution is bounded, so its energy
integrand is essentially bounded on every open subset of `Ω`. -/
private theorem memLp_energyIntegrand_comp
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set E) (fun x => A x s) lam Lam)
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    {v : E → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) {B : Opens E}
    (hB : B ≤ Omega) :
    MemLp (fun x => energyIntegrand (A x (v x)) 0 0) ⊤ (volume.restrict B) := by
  have hell : UniformlyEllipticOn (B : Set E) (fun x => A x (v x)) lam Lam :=
    (UniformlyEllipticOn.apply_of_forall hA v).mono_set hB
  exact memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    hell.upper_nonneg ((aestronglyMeasurable_comp_of_contDiffOn hAC hv).mono_measure
      (Measure.restrict_mono hB le_rfl)) aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ hy eta xi => hell.upper_bound hy eta xi) (fun _ _ => by simp) (fun _ _ => by simp)

/-- **Continuity.** The precise representative of a weak solution is continuous on `Ω`. -/
private theorem continuousOn_preciseRepresentative_value
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set E) (fun x => A x s) lam Lam)
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    (hf : ContinuousOn f Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) = ∫ x in Omega, f x * φ x) :
    ContinuousOn (preciseRepresentative volume (W1p.value u)) Omega := by
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  exact continuousOn_preciseRepresentative_of_forall_memLp (r := n + 2)
    (by exact_mod_cast (show (2 : ℕ) ≤ n + 2 by omega)) (by rw [hcard]; push_cast; linarith)
    (UniformlyEllipticOn.apply_of_forall hA _)
    (aestronglyMeasurable_comp_of_contDiffOn hAC (Lp.aestronglyMeasurable _))
    (fun K hK hKΩ => (hf.mono hKΩ).memLp_restrict_of_subset_isCompact hK hK.measurableSet
      subset_rfl _) hu

/-- **Truncation.** Let `M ≥ 0` and let the closed ball `K = closedBall x₀ ε` lie in `Ω`. The
coefficient `A(x, max (-M) (min M s))` is `α`-Hölder in `x ∈ K` uniformly in `s` and Lipschitz in
`s` uniformly in `x ∈ K`, since `A` is `C¹`, hence Lipschitz, on the compact convex set
`K × [-M, M]`. -/
private theorem exists_holderOnWith_and_lipschitzWith_truncation (hα1 : α ≤ 1)
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    {x₀ : E} {ε M : ℝ} (hεΩ : closedBall x₀ ε ⊆ Omega) (hM0 : 0 ≤ M) :
    ∃ Kx L : ℝ≥0, (∀ s, HolderOnWith Kx α
        (fun x => matrixBilinearForm (A x (max (-M) (min M s)))) (closedBall x₀ ε)) ∧
      ∀ x ∈ closedBall x₀ ε, LipschitzWith L
        fun s => matrixBilinearForm (A x (max (-M) (min M s))) := by
  have hcK : ∀ s, max (-M) (min M s) ∈ Icc (-M) M := fun s =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left M s)⟩
  have hcLip : LipschitzWith 1 fun s => max (-M) (min M s) :=
    (LipschitzWith.id.const_min M).const_max (-M)
  choose L hL using fun i j => ContDiffOn.exists_lipschitzOnWith
    ((hAC i j).mono (prod_mono hεΩ (subset_univ (Icc (-M) M)))) one_ne_zero
    ((convex_closedBall x₀ ε).prod (convex_Icc _ _))
    ((isCompact_closedBall x₀ ε).prod isCompact_Icc)
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0, ∀ x ∈ closedBall x₀ ε, ∀ y ∈ closedBall x₀ ε, edist x y ≤ D :=
    ⟨(Metric.ediam (closedBall x₀ ε)).toNNReal, fun x hx y hy => by
      rw [ENNReal.coe_toNNReal (Metric.isBounded_iff_ediam_ne_top.1 isBounded_closedBall)]
      exact Metric.edist_le_ediam_of_mem hx hy⟩
  refine ⟨_, _, fun s => holderOnWith_matrixBilinearForm_of_forall fun i j =>
      ((hL i j).comp (LipschitzWith.prodMk_right _).lipschitzOnWith
        fun _ hx => ⟨hx, hcK s⟩).holderOnWith.of_le hD hα1,
    fun x hx => holderWith_one.1 (holderOnWith_univ.1 (holderOnWith_matrixBilinearForm_of_forall
      fun i j => (holderWith_one.2 (lipschitzOnWith_univ.1 ((hL i j).comp
        ((LipschitzWith.prodMk_left x).comp hcLip).lipschitzOnWith
          fun s _ => ⟨hx, hcK s⟩))).holderOnWith univ))⟩

/-- **The gradient is `α`-Hölder near each point.** Near every point of `Ω`, the precise
representative of the gradient of a weak solution is `α`-Hölder. On a ball whose closure lies in
`Ω` the continuous representative `ū` is bounded by some `M`, and the coefficient
`A(x, max (-M) (min M s))` gives the same equation there and is Lipschitz in `(x, s)`, so the
interior `C^{1,β}` theorem for quasilinear equations applies to it. -/
private theorem exists_holderOnWith_preciseRepresentative_gradient_ball (hα : 0 < α)
    (hα1 : α < 1) (hA : ∀ s, UniformlyEllipticOn (Omega : Set E) (fun x => A x s) lam Lam)
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    (hf : ContinuousOn f Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) = ∫ x in Omega, f x * φ x)
    {x₀ : E} (hx₀ : x₀ ∈ Omega) :
    ∃ r > 0, ∃ C : ℝ≥0,
      HolderOnWith C α (preciseRepresentative volume (W1p.gradient u : E → E)) (ball x₀ r) := by
  obtain ⟨ε, hε, hεΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx₀)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ ε).exists_bound_of_continuousOn
    ((continuousOn_preciseRepresentative_value hA hAC hf hu).mono hεΩ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ (mem_closedBall_self hε.le))
  obtain ⟨Kx, L, hHx, hLs⟩ := exists_holderOnWith_and_lipschitzWith_truncation hα1.le hAC hεΩ hM0
  -- On `B = B(x₀, ε)`, `u` solves the equation with the truncated coefficient.
  let B : Opens E := ⟨ball x₀ ε, isOpen_ball⟩
  have hBΩ : B ≤ Omega := ball_subset_closedBall.trans hεΩ
  have hBK : (B : Set E) ⊆ closedBall x₀ ε := ball_subset_closedBall
  have hfB : MemLp f ⊤ (volume.restrict B) := (hf.mono hεΩ).memLp_restrict_of_subset_isCompact
    (isCompact_closedBall x₀ ε) B.isOpen.measurableSet hBK ⊤
  have : IsFiniteMeasure (volume.restrict (B : Set E)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hW := forall_energyFormH1_restrictL_eq_setIntegral hBΩ
    (memLp_energyIntegrand_comp hA hAC (Lp.aestronglyMeasurable _) hBΩ) hu
    (hfB.mono_exponent le_top)
  have hcoef : (fun x => A x (W1p.value u x)) =ᵐ[volume.restrict B]
      fun x => A x (max (-M) (min M (W1p.value (W1p.restrictL hBΩ u) x))) := by
    filter_upwards [W1p.value_restrictL_ae hBΩ u,
      ae_restrict_of_ae_restrict_of_subset hBΩ (W1p.ae_eq_preciseRepresentative u),
      ae_restrict_mem B.isOpen.measurableSet] with x h1 h2 hx
    have hxM := abs_le.1 (by simpa using hM x (hBK hx))
    rw [h1, h2, min_eq_right hxM.2, max_eq_right hxM.1]
  have hu' : ∀ φ : 𝓓(B, ℝ), energyFormH1
      (fun x => A x (max (-M) (min M (W1p.value (W1p.restrictL hBΩ u) x))))
      0 0 (W1p.restrictL hBΩ u) (W1p.ofTestFunctionₗ volume B 2 φ) =
      (∫ x in B, ⟪(0 : E → E) x, ∇ (φ : E → ℝ) x⟫_ℝ) + ∫ x in B, f x * φ x := fun φ => by
    rw [← energyFormH1_congr_ae hcoef .rfl .rfl, hW ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
    simp only [Pi.zero_apply, inner_zero_left, integral_zero, zero_add]
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with x hx
    rw [hx]
  have hth : thickening (ε / 2) (ball x₀ (ε / 2)) ⊆ (B : Set E) := by
    rw [_root_.thickening_ball (by positivity) (by positivity)]
    exact ball_subset_ball (by linarith)
  obtain ⟨C, hC⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_forall_energyFormH1_quasilinear_eq
      (A := fun x s => A x (max (-M) (min M s))) (G := 0) le_top
      (fun s => (hA _).mono_set hBΩ) (fun s => (hHx s).mono hBK) (fun x hx => hLs x (hBK hx))
      ((HolderWith.zero (C := 0)).holderOnWith _) hfB hu' hα hα1 le_rfl (by simpa using hα1.le)
      isBounded_ball (by positivity) hth
  -- Near `x₀`, the precise representatives of `∇u` and of the gradient of its restriction agree.
  refine ⟨ε / 2, by positivity, C, hC.congr fun y hy => ?_⟩
  exact preciseRepresentative_congr_ae_nhds
    (B.isOpen.mem_nhds (ball_subset_ball (by linarith) hy)) (W1p.gradient_restrictL_ae hBΩ u)

/-- **`ū` is `C¹`.** The precise representative `P∇u` of the gradient of a weak solution is
continuous on `Ω`, and the precise representative `ū` of the solution is differentiable at every
point `x` of `Ω`, with derivative `v ↦ ⟪P∇u(x), v⟫`. -/
private theorem continuousOn_and_hasFDerivAt_preciseRepresentative (hα : 0 < α) (hα1 : α < 1)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set E) (fun x => A x s) lam Lam)
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    (hf : ContinuousOn f Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) = ∫ x in Omega, f x * φ x) :
    ContinuousOn (preciseRepresentative volume (W1p.gradient u : E → E)) Omega ∧
      ∀ x ∈ Omega, HasFDerivAt (preciseRepresentative volume (W1p.value u))
        (innerSL ℝ (preciseRepresentative volume (W1p.gradient u : E → E) x)) x := by
  have hP : ContinuousOn (preciseRepresentative volume (W1p.gradient u : E → E)) Omega :=
    fun x hx => by
      obtain ⟨r, hr, C, hC⟩ :=
        exists_holderOnWith_preciseRepresentative_gradient_ball hα hα1 hA hAC hf hu hx
      exact ((hC.continuousOn hα).continuousAt (ball_mem_nhds x hr)).continuousWithinAt
  refine ⟨hP, fun x hx => ?_⟩
  have hW := ((W1p.hasWeakFDerivOn u).congr_ae (W1p.ae_eq_preciseRepresentative u)).congr_ae_deriv
    ((ae_eq_restrict_preciseRepresentative Omega.isOpen
      (W1p.locallyIntegrableOn_gradient u)).fun_comp (innerSL ℝ))
  exact hW.hasFDerivAt_of_continuousOn (continuousOn_preciseRepresentative_value hA hAC hf hu)
    ((innerSL ℝ).continuous.comp_continuousOn hP) hx

/-- **The chain rule** for the frozen coefficient: if `v` has derivative `D` at `y ∈ Ω`, then
`D[A(·, v(·))](y) = DA(y, v(y)) ∘ (id, D)`, entrywise. -/
private theorem fderiv_comp_eq
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    {v : E → ℝ} {D : E →L[ℝ] ℝ} {y : E} (hy : y ∈ Omega) (hv : HasFDerivAt v D y) (i j) :
    fderiv ℝ (fun x => A x (v x) i j) y =
      (fderiv ℝ (fun p : E × ℝ => A p.1 p.2 i j) (y, v y)).comp
        ((ContinuousLinearMap.id ℝ E).prod D) := by
  have hA : HasFDerivAt (fun p : E × ℝ => A p.1 p.2 i j)
      (fderiv ℝ (fun p : E × ℝ => A p.1 p.2 i j) (y, v y)) (y, v y) :=
    (((hAC i j).differentiableOn one_ne_zero).differentiableAt
      ((Omega.isOpen.prod isOpen_univ).mem_nhds ⟨hy, trivial⟩)).hasFDerivAt
  exact (hA.comp y ((hasFDerivAt_id y).prodMk hv)).fderiv

/-- **The frozen coefficient is `C^{1,α}`.** The entries of `x ↦ A(x, ū(x))` are `C¹` on `Ω`, and
their derivatives are `α`-Hölder near each point of `Ω`. -/
private theorem contDiffOn_comp_and_exists_holderOnWith_fderiv (hα : 0 < α) (hα1 : α < 1)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set E) (fun x => A x s) lam Lam)
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    (hdA : ∀ p ∈ (Omega : Set E) ×ˢ (univ : Set ℝ), ∃ r > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun p : E × ℝ => A p.1 p.2 i j)) (ball p r))
    (hf : ContinuousOn f Omega)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) = ∫ x in Omega, f x * φ x) :
    (∀ i j, ContDiffOn ℝ 1
        (fun x => A x (preciseRepresentative volume (W1p.value u) x) i j) Omega) ∧
      ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j, HolderOnWith L α
        (fderiv ℝ fun y => A y (preciseRepresentative volume (W1p.value u) y) i j) (ball x r) := by
  set ub := preciseRepresentative volume (W1p.value u)
  set P := preciseRepresentative volume (W1p.gradient u : E → E)
  obtain ⟨hP, hder⟩ := continuousOn_and_hasFDerivAt_preciseRepresentative hα hα1 hA hAC hf hu
  have hub : ContDiffOn ℝ 1 ub Omega := by
    have hfd : ContinuousOn (fderiv ℝ ub) Omega :=
      ((innerSL ℝ).continuous.comp_continuousOn hP).congr fun x hx => (hder x hx).fderiv
    simpa using (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) Omega.isOpen).2
      ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, by simp,
        contDiffOn_zero.2 hfd⟩
  have hg : ContDiffOn ℝ 1 (fun y => (y, ub y)) Omega := contDiffOn_id.prodMk hub
  refine ⟨fun i j => (hAC i j).comp hg fun _ hx => ⟨hx, trivial⟩, fun x hx => ?_⟩
  -- Choose a closed ball `S = closedBall x r` on which `ū` is Lipschitz, `∇ū` is `α`-Hölder, and
  -- the graph map `y ↦ (y, ū(y))` lands where the derivatives of `A` are `α`-Hölder.
  obtain ⟨ρ, hρ, L₁, hL₁⟩ := hdA (x, ub x) ⟨hx, trivial⟩
  obtain ⟨r₁, hr₁, C₁, hC₁⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_ball hα hα1 hA hAC hf hu hx
  obtain ⟨K, t, ht, hKt⟩ := (hub.contDiffAt (Omega.isOpen.mem_nhds hx)).exists_lipschitzOnWith
  have hgc : ContinuousAt (fun y => (y, ub y)) x :=
    hg.continuousOn.continuousAt (Omega.isOpen.mem_nhds hx)
  obtain ⟨r, hr, hrS⟩ := nhds_basis_closedBall.mem_iff.1
    (Filter.inter_mem (Filter.inter_mem ht (Omega.isOpen.mem_nhds hx))
      (Filter.inter_mem (hgc.preimage_mem_nhds (ball_mem_nhds _ hρ)) (ball_mem_nhds x hr₁)))
  have hSt : closedBall x r ⊆ t := fun y hy => (hrS hy).1.1
  have hSΩ : closedBall x r ⊆ Omega := fun y hy => (hrS hy).1.2
  have hSρ : MapsTo (fun y => (y, ub y)) (closedBall x r) (ball (x, ub x) ρ) :=
    fun y hy => (hrS hy).2.1
  have hSr₁ : closedBall x r ⊆ ball x r₁ := fun y hy => (hrS hy).2.2
  -- `y ↦ DA(y, ū(y))` and `y ↦ (id, Dū(y))` are `α`-Hölder on `S`, hence so is their composite.
  have hDA : ∀ i j, HolderOnWith (L₁ * max 1 K ^ (α : ℝ)) α
      (fun y => fderiv ℝ (fun p : E × ℝ => A p.1 p.2 i j) (y, ub y)) (closedBall x r) :=
    fun i j => by
      have h := (hL₁ i j).comp
        (LipschitzWith.id.lipschitzOnWith.prodMk (hKt.mono hSt)).holderOnWith hSρ
      rw [mul_one] at h
      exact h
  have hDu := ((ContinuousLinearMap.prodₗᵢ ℝ :
      (E →L[ℝ] E) × (E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] E →L[ℝ] E × ℝ).lipschitzWith.comp
    (LipschitzWith.prodMk_left (ContinuousLinearMap.id ℝ E))).comp_holderOnWith
      ((innerSL ℝ).lipschitzWith.comp_holderOnWith (hC₁.mono hSr₁))
  choose C hC using fun i j => ContinuousLinearMap.exists_holderOnWith_comp₂_of_isCompact
    (ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ) (isCompact_closedBall x r) hα (hDA i j) hDu
  refine ⟨r, hr, ∑ i, ∑ j, C i j, fun i j => ?_⟩
  refine (((hC i j).mono ball_subset_closedBall).congr fun y hy =>
      (fderiv_comp_eq hAC (hSΩ (ball_subset_closedBall hy))
        (hder y (hSΩ (ball_subset_closedBall hy))) i j).symm).mono_const
    ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, C i j) (fun _ _ => zero_le)
        (Finset.mem_univ i)))

/-- **Interior `C^{2,α}` regularity for quasilinear divergence-form equations.** Let `0 < α < 1`,
let `Ω ⊆ ℝⁿ⁺¹` be open, and let `A(x, s)` be a field of matrices, uniformly elliptic with constants
`λ, Λ` in `x` for every `s`, whose entries are `C¹` in `(x, s)` on `Ω × ℝ` with derivatives that are
`α`-Hölder near each point of `Ω × ℝ`. Let `f` be `α`-Hölder near each point of `Ω`. Let `u ∈ H¹(Ω)`
be a weak solution of the quasilinear equation

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f` in `Ω`,

that is `∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω f φ` for every test function `φ`, and let `V` be open with
compact closure contained in `Ω`. Then for every direction `e`, the weak derivative `∂ₑu` lies in
`H¹(V)`, and the precise representative of its gradient is `α`-Hölder on every compact subset of
`V`.

So the second weak derivatives of `u` have locally `α`-Hölder representatives. No bound on `A`
uniform in `s`, no integrability of `f` on `Ω`, no boundary condition on `u` and nothing about
`∂Ω` is assumed. The precise representative agrees with `∇∂ₑu` almost everywhere on `V`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). -/
theorem exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_quasilinear_eq
    (hα : 0 < α) (hα1 : α < 1)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set E) (fun x => A x s) lam Lam)
    (hAC : ∀ i j, ContDiffOn ℝ 1 (fun p : E × ℝ => A p.1 p.2 i j) ((Omega : Set E) ×ˢ univ))
    (hdA : ∀ p ∈ (Omega : Set E) ×ˢ (univ : Set ℝ), ∃ r > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun p : E × ℝ => A p.1 p.2 i j)) (ball p r))
    (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α f (ball x r))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) = ∫ x in Omega, f x * φ x)
    {V : Opens E} (hV : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Omega)
    (e : E) :
    ∃ d : W1p volume V 2, HasWeakLineDerivOn volume V (W1p.value u) (W1p.value d) e ∧
      ∀ K ⊆ (V : Set E), IsCompact K → ∃ C : ℝ≥0,
        HolderOnWith C α (preciseRepresentative volume (W1p.gradient d : E → E)) K := by
  have hf : ContinuousOn f Omega := fun x hx => by
    obtain ⟨r, hr, L, hL⟩ := hfH x hx
    exact ((hL.continuousOn hα).continuousAt (ball_mem_nhds x hr)).continuousWithinAt
  obtain ⟨hcoef, hdcoef⟩ :=
    contDiffOn_comp_and_exists_holderOnWith_fderiv hα hα1 hA hAC hdA hf hu
  -- An open neighbourhood `W` of the closure of `V` with compact closure in `Ω`.
  obtain ⟨δ, hδ, hδΩ⟩ := hV.exists_cthickening_subset_open Omega.isOpen hVΩ
  let W : Opens E := ⟨thickening δ (closure (V : Set E)), isOpen_thickening⟩
  have hWδ : (W : Set E) ⊆ cthickening δ (closure (V : Set E)) := thickening_subset_cthickening _ _
  have hWΩ : W ≤ Omega := hWδ.trans hδΩ
  have hVW : closure (V : Set E) ⊆ W := self_subset_thickening hδ _
  -- On `W`, `u` solves the linear equation with the coefficient `A(x, ū(x))`.
  have hfW : MemLp f 2 (volume.restrict W) := (hf.mono hδΩ).memLp_restrict_of_subset_isCompact
    hV.cthickening W.isOpen.measurableSet hWδ 2
  have hW := forall_energyFormH1_restrictL_eq_setIntegral hWΩ
    (memLp_energyIntegrand_comp hA hAC (Lp.aestronglyMeasurable _) hWΩ) hu hfW
  have hW' : ∀ v : W1p0 volume W 2, energyFormH1
      (fun x => A x (preciseRepresentative volume (W1p.value u) x)) 0 0 (W1p.restrictL hWΩ u)
        (v : W1p volume W 2) = ∫ x in W, f x * W1p.value (v : W1p volume W 2) x := fun v => by
    rw [← hW v]
    exact energyFormH1_congr_ae ((ae_restrict_of_ae_restrict_of_subset hWΩ
      (W1p.ae_eq_preciseRepresentative u)).mono fun x hx => by rw [hx]) .rfl .rfl _ _
  obtain ⟨d, hd, hdH⟩ :=
    exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_contDiffOn
      hα hα1 ((UniformlyEllipticOn.apply_of_forall hA _).mono_set hWΩ)
      (fun i j => (hcoef i j).mono hWΩ) (fun x hx => hdcoef x (hWΩ hx)) hfW
      (fun x hx => hfH x (hWΩ hx)) hW' hV hVW e
  exact ⟨d, hd.congr_ae (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVW)
    (W1p.value_restrictL_ae hWΩ u)), hdH⟩

end PDE

end TauCeti
