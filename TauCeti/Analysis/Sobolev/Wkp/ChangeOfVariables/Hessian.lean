/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.Wkp.ClosedGraph
import TauCeti.MeasureTheory.Function.Jacobian
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# The weak Hessian under a change of variables with Lipschitz derivative

Let `Φ` be a change of variables of order one from an open set `U` into an open set `V`
(`TauCeti.Wkp.IsChangeOfVariables 1`): `C¹`, injective on `U`, mapping `U` into `V`, with
`‖DΦ‖ ≤ L` and `|det DΦ| ≥ c > 0` on `U`. Let `1 ≤ p < ∞` and `u ∈ W^{2,p}(V)`. Precomposition
with `Φ` keeps `u ∘ Φ` in `W^{1,p}(U)`, with weak gradient `DΦ† ∇u(Φ ·)`. This file shows that
`u ∘ Φ` keeps its second weak derivatives as soon as `DΦ` is Lipschitz on `U`, with no second
classical derivative of `Φ`:

* if `DΦ` is `M`-Lipschitz on `U`, that is `Φ` is of class `C^{1,1}`, then `u ∘ Φ ∈ W^{2,p}(U)`, and
  precomposition with `Φ` is a bounded operator `W^{2,p}(V) →L[ℝ] W^{2,p}(U)`
  (`TauCeti.Wkp.compOfLipschitzFDerivL`);
* if `DΦ` is locally Lipschitz on `U`, then the weak Hessian of every element of `W^{2,p}(U)` whose
  value is `u ∘ Φ` is given by the chain rule

  `⟪D²(u ∘ Φ)(x) f, g⟫ = ⟪D²u(Φ x) (DΦ(x) f), DΦ(x) g⟫ + ⟪∇u(Φ x), D²Φ(x) f g⟫`

  for almost every `x ∈ U` (`TauCeti.Wkp.inner_iteratedGradient_ae_of_firstOrder_eq_w1pCompL`).
  Here `D²Φ(x) = fderiv ℝ (fderiv ℝ Φ) x` is the classical derivative of `DΦ`, which exists at
  almost every point of `U` by Rademacher's theorem, and is bounded by `M` when `DΦ` is
  `M`-Lipschitz.

A change of variables of order two has a `C¹`, hence locally Lipschitz, derivative, so the chain
rule for the weak Hessian along it (`TauCeti.Wkp.inner_iteratedGradient_compL_ae`) is a special
case. Changes of variables of class `C^{1,1}` are the ones that flatten the boundary of a domain
of class `C^{1,1}`, the boundary regularity of the global `W^{2,p}` theory of the Dirichlet
problem (Gilbarg–Trudinger, Theorem 9.15).

## The argument

In an orthonormal basis `(bᵢ)`, each component of the weak gradient of `u ∘ Φ` is
`⟪DΦ† ∇u(Φ ·), c₀⟫ = ∑ᵢ ⟪bᵢ, DΦ c₀⟫ ⟪∇u(Φ ·), bᵢ⟫`. The functions `⟪∇u(Φ ·), bᵢ⟫` lie in
`W^{1,p}(U)` by the first-order change of variables, and the coefficients `⟪bᵢ, DΦ c₀⟫` are
locally Lipschitz, so the Leibniz rule with a locally Lipschitz factor
(`TauCeti.HasWeakLineDerivOn.locallyLipschitzOn_smul`) differentiates the sum weakly; at the
points where `DΦ` is differentiable, the directional derivative of the coefficient is
`⟪bᵢ, D²Φ f c₀⟫`. When `DΦ` is `M`-Lipschitz, these derivatives are bounded by `M`, so they are in
`Lᵖ(U)`, and the components of the weak gradient lie in `W^{1,p}(U)`; this places `u ∘ Φ` in
`W^{2,p}(U)` (`TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn`). Uniqueness of weak
derivatives identifies the weak Hessian. Boundedness of the operator is the closed graph
theorem (`TauCeti.Wkp.exists_norm_le_of_forall_exists_value_ae_eq`).

## Main declarations

* `TauCeti.Wkp.inner_iteratedGradient_ae_of_firstOrder_eq_w1pCompL`: the chain rule for the weak
  Hessian along a change of variables with locally Lipschitz derivative.
* `TauCeti.Wkp.inner_iteratedGradient_compL_ae`: its case of a change of variables of order two.
* `TauCeti.Wkp.compOfLipschitzFDerivL`: precomposition with a change of variables of class
  `C^{1,1}` as a bounded operator on `W^{2,p}`, with
  `TauCeti.Wkp.firstOrder_compOfLipschitzFDerivL`, `TauCeti.Wkp.value_compOfLipschitzFDerivL_ae`,
  `TauCeti.Wkp.compOfLipschitzFDerivL_eq_iff`, the chain rules
  `TauCeti.Wkp.gradient_firstOrder_compOfLipschitzFDerivL_ae` and
  `TauCeti.Wkp.inner_iteratedGradient_compOfLipschitzFDerivL_ae`, and the inverse
  `TauCeti.Wkp.compOfLipschitzFDerivL_compOfLipschitzFDerivL_of_rightInvOn`.
* `TauCeti.Wkp.compOfLipschitzFDerivL_eq_compL`: for a change of variables of order two it is
  `TauCeti.Wkp.compL`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.15 (the `W^{2,p}` Dirichlet problem on `C^{1,1}` domains).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.3 (Rademacher's theorem).
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {Φ : E → E} {L c : ℝ}

/-- At almost every point, the weak gradient of `d ∈ W^{1,p}(V)` pairs with every direction `f`
as `⟪D²u f, c⟫` once it does so with the vectors of an orthonormal basis. -/
private theorem ae_forall_inner_gradient_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (u : Wkp mu V p 2) (c : E) (d : W1p mu V p)
    (hd : ∀ i, (fun y => ⟪W1p.gradient d y, b i⟫_ℝ) =ᵐ[mu.restrict V]
      fun y => ⟪iteratedGradient 1 u y (b i), c⟫_ℝ) :
    ∀ᵐ y ∂mu.restrict V, ∀ f : E,
      ⟪W1p.gradient d y, f⟫_ℝ = ⟪iteratedGradient 1 u y f, c⟫_ℝ := by
  filter_upwards [ae_all_iff.2 hd] with y hy f
  have hL : (innerSL ℝ (W1p.gradient d y) : E →L[ℝ] ℝ) =
      (innerSL ℝ c).comp (iteratedGradient 1 u y) :=
    ContinuousLinearMap.coe_injective (b.toBasis.ext fun i => by
      simpa [real_inner_comm c] using hy i)
  simpa [real_inner_comm c] using congrArg (fun T => T f) hL

/-- For `u ∈ W^{2,p}(V)` and a direction `c₀`, the function `⟪∇u(Φ ·), c₀⟫` lies in `W^{1,p}(U)`,
with weak gradient components `⟪D²u(Φ x) (DΦ(x) f), c₀⟫`. -/
private theorem exists_w1p_value_eq_inner_gradient_comp (h : IsChangeOfVariables 1 U V Φ L c)
    (hp : p ≠ ⊤) (u : Wkp mu V p 2) (c₀ : E) :
    ∃ w : W1p mu U p, ∀ᵐ x ∂mu.restrict U,
      W1p.value w x = ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), c₀⟫_ℝ ∧ ∀ f : E,
        ⟪W1p.gradient w x, f⟫_ℝ = ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), c₀⟫_ℝ := by
  obtain ⟨d, hdv, hdg⟩ := exists_w1p_value_eq_inner_gradient u c₀
  have hdg' := ae_forall_inner_gradient_eq (stdOrthonormalBasis ℝ E) u c₀ d fun i => hdg _
  refine ⟨h.w1pCompL hp d, ?_⟩
  filter_upwards [h.value_w1pCompL_ae hp d, W1p.gradient_compL_ae Φ hp h.differentiableOn h.injOn
    h.mapsTo h.norm_fderiv_le h.pos h.le_abs_det d, h.ae_comp hdv, h.ae_comp hdg']
    with x h1 h2 h3 h4
  refine ⟨h1.trans h3, fun f => ?_⟩
  rw [h2, ContinuousLinearMap.adjoint_inner_left, h4]

/-- Each component `⟪∇(u ∘ Φ), c₀⟫` of the weak gradient of `u ∘ Φ` is weakly differentiable in
every direction `f`, with derivative `⟪D²u(Φ x) (DΦ(x) f), DΦ(x) c₀⟫ + ⟪∇u(Φ x), D²Φ(x) f c₀⟫`,
when `DΦ` is locally Lipschitz on `U`. -/
private theorem hasWeakLineDerivOn_inner_gradient_w1pCompL (h : IsChangeOfVariables 1 U V Φ L c)
    (hΦ : LocallyLipschitzOn (U : Set E) (fderiv ℝ Φ)) (hp : p ≠ ⊤) (u : Wkp mu V p 2)
    (c₀ f : E) :
    HasWeakLineDerivOn mu U (fun x => ⟪W1p.gradient (h.w1pCompL hp (firstOrder 1 u)) x, c₀⟫_ℝ)
      (fun x => ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x c₀⟫_ℝ +
        ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), fderiv ℝ (fderiv ℝ Φ) x f c₀⟫_ℝ) f := by
  set b := stdOrthonormalBasis ℝ E
  set G := iteratedGradient 0 (lowerOrder 1 u)
  -- The weak gradient of `u ∘ Φ` is `DΦ(x)† ∇u(Φ x)`.
  have hgrad : ∀ᵐ x ∂mu.restrict U,
      W1p.gradient (h.w1pCompL hp (firstOrder 1 u)) x = (fderiv ℝ Φ x).adjoint (G (Φ x)) := by
    filter_upwards [W1p.gradient_compL_ae Φ hp h.differentiableOn h.injOn h.mapsTo
      h.norm_fderiv_le h.pos h.le_abs_det (firstOrder 1 u)] with x hx
    rw [hx, gradient_firstOrder_one]
  -- In the basis `(bᵢ)`, `⟪∇(u ∘ Φ), c₀⟫ = ∑ᵢ ⟪bᵢ, DΦ c₀⟫ wᵢ` with `wᵢ = ⟪∇u(Φ ·), bᵢ⟫` in
  -- `W^{1,p}(U)`, and the coefficients `⟪bᵢ, DΦ c₀⟫` are locally Lipschitz on `U`.
  choose w hw using fun i => exists_w1p_value_eq_inner_gradient_comp h hp u (b i)
  set ℓ : Fin _ → (E →L[ℝ] E) →L[ℝ] ℝ := fun i =>
    (innerSL ℝ (b i)).comp (ContinuousLinearMap.apply ℝ E c₀)
  have hψ (i : Fin _) : LocallyLipschitzOn (U : Set E) (fun x => ⟪b i, fderiv ℝ Φ x c₀⟫_ℝ) :=
    fun x hx => by
      obtain ⟨K, t, ht, hK⟩ := hΦ hx
      exact ⟨‖ℓ i‖₊ * K, t, ht, (ℓ i).lipschitzWith.comp_lipschitzOnWith hK⟩
  -- Where `DΦ` is differentiable, the directional derivatives of the coefficients involve `D²Φ`.
  have hψd : ∀ᵐ x ∂mu.restrict U, ∀ i, lineDeriv ℝ (fun x => ⟪b i, fderiv ℝ Φ x c₀⟫_ℝ) x f =
      ⟪b i, fderiv ℝ (fderiv ℝ Φ) x f c₀⟫_ℝ := by
    filter_upwards [ae_restrict_of_ae (hΦ.ae_differentiableAt_of_mem (μ := mu) U.isOpen),
      ae_restrict_mem U.isOpen.measurableSet] with x hx hxU i
    exact (((ℓ i).hasFDerivAt.comp x (hx hxU).hasFDerivAt).hasLineDerivAt f).lineDeriv
  have hsum := HasWeakLineDerivOn.sum (μ := mu) (Ω := U) Finset.univ fun i _ =>
    ((W1p.hasWeakFDerivOn (w i)).hasWeakLineDerivOn f).locallyLipschitzOn_smul (hψ i)
  refine (hsum.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [hgrad, ae_all_iff.2 hw] with x h1 h2
    rw [h1, ContinuousLinearMap.adjoint_inner_left, ← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(h2 i).1, smul_eq_mul, mul_comm]
  · filter_upwards [hψd, ae_all_iff.2 hw] with x h1 h2
    simp only [innerSL_apply_apply, smul_eq_mul, h1, (h2 _).1, (h2 _).2, Finset.sum_add_distrib]
    rw [← b.sum_inner_mul_inner (iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f)),
      ← b.sum_inner_mul_inner (G (Φ x))]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- **The chain rule for the weak Hessian, for a locally Lipschitz derivative.** Let `Φ` be a change
of variables of order one from `U` into `V` whose derivative `DΦ` is locally Lipschitz on `U`, and
let `1 ≤ p < ∞`. If `u ∈ W^{2,p}(V)` and `w ∈ W^{2,p}(U)` has the first-order part `u ∘ Φ`, then

`⟪D²w(x) f, g⟫ = ⟪D²u(Φ x) (DΦ(x) f), DΦ(x) g⟫ + ⟪∇u(Φ x), D²Φ(x) f g⟫`

for almost every `x ∈ U` and all directions `f` and `g`. Here `D²u` is the weak Hessian
`TauCeti.Wkp.iteratedGradient 1 u`, `∇u` the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`, and `DΦ`, `D²Φ` are classical
derivatives; `D²Φ(x)` exists at almost every `x ∈ U` by Rademacher's theorem. -/
theorem inner_iteratedGradient_ae_of_firstOrder_eq_w1pCompL (h : IsChangeOfVariables 1 U V Φ L c)
    (hΦ : LocallyLipschitzOn (U : Set E) (fderiv ℝ Φ)) (hp : p ≠ ⊤) (u : Wkp mu V p 2)
    {w : Wkp mu U p 2} (hw : firstOrder 1 w = h.w1pCompL hp (firstOrder 1 u)) :
    ∀ᵐ x ∂mu.restrict U, ∀ f g : E,
      ⟪iteratedGradient 1 w x f, g⟫_ℝ =
        ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x g⟫_ℝ +
          ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), fderiv ℝ (fderiv ℝ Φ) x f g⟫_ℝ := by
  set b := stdOrthonormalBasis ℝ E
  set G := iteratedGradient 0 (lowerOrder 1 u)
  -- Uniqueness of weak derivatives identifies the entries `⟪D²w f, c₀⟫`.
  have hentry (c₀ f : E) : (fun x => ⟪iteratedGradient 1 w x f, c₀⟫_ℝ)
      =ᵐ[mu.restrict U] fun x => ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x c₀⟫_ℝ +
        ⟪G (Φ x), fderiv ℝ (fderiv ℝ Φ) x f c₀⟫_ℝ := by
    have h' := ((hasWeakFDerivOn_iteratedGradient 0 w).clm_comp
      (innerSL ℝ c₀)).hasWeakLineDerivOn f
    rw [← gradient_firstOrder_one, hw] at h'
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm _ c₀] at h'
    exact h'.ae_eq (hasWeakLineDerivOn_inner_gradient_w1pCompL h hΦ hp u c₀ f)
  -- Both sides are bilinear in `(f, g)`, so they agree once they agree on a basis: the right side
  -- is `⟪N x f, g⟫` for the operator `N x` below.
  set N : E → E →L[ℝ] E := fun x => (fderiv ℝ Φ x).adjoint ∘L iteratedGradient 1 u (Φ x) ∘L
    fderiv ℝ Φ x + InnerProductSpace.continuousLinearMapOfBilin
      ((ContinuousLinearMap.compL ℝ E E ℝ (innerSL ℝ (G (Φ x)))) ∘L fderiv ℝ (fderiv ℝ Φ) x)
  have hN (x f g : E) : ⟪N x f, g⟫_ℝ =
      ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x g⟫_ℝ +
        ⟪G (Φ x), fderiv ℝ (fderiv ℝ Φ) x f g⟫_ℝ := by
    simp [N, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      InnerProductSpace.continuousLinearMapOfBilin_apply]
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry (b j) (b i)] with x hx f g
  have hxN : iteratedGradient 1 w x = N x :=
    ContinuousLinearMap.coe_injective (b.toBasis.ext fun i =>
      InnerProductSpace.ext_inner_right_basis b.toBasis fun j => by simpa [hN] using hx i j)
  rw [hxN, hN]

/-- **The chain rule for the weak Hessian.** Let `Φ` be a change of variables of order two from `U`
into `V`, and `1 ≤ p < ∞`. For `u ∈ W^{2,p}(V)`, the weak Hessian of `u ∘ Φ ∈ W^{2,p}(U)` is

`⟪D²(u ∘ Φ)(x) f, g⟫ = ⟪D²u(Φ x) (DΦ(x) f), DΦ(x) g⟫ + ⟪∇u(Φ x), D²Φ(x) f g⟫`

for almost every `x ∈ U` and all directions `f` and `g`. Here `D²u` is the weak Hessian
`TauCeti.Wkp.iteratedGradient 1 u` and `∇u` the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`; `DΦ` and `D²Φ` are the classical
derivatives. For a linear `Φ` the last term vanishes
(`TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`). -/
theorem inner_iteratedGradient_compL_ae (h : IsChangeOfVariables 2 U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p 2) :
    ∀ᵐ x ∂mu.restrict U, ∀ f g : E,
      ⟪iteratedGradient 1 (compL h u) x f, g⟫_ℝ =
        ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x g⟫_ℝ +
          ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), fderiv ℝ (fderiv ℝ Φ) x f g⟫_ℝ := by
  -- `DΦ` is `C¹` on the open set `U`, hence locally Lipschitz there.
  exact inner_iteratedGradient_ae_of_firstOrder_eq_w1pCompL (h.mono one_le_two)
    (h.contDiffOn_fderiv.locallyLipschitzOn_of_isOpen U.isOpen) hp u (firstOrder_compL h hp u)

/-! ### Changes of variables of class `C^{1,1}` -/

section LipschitzFDeriv

variable {M : ℝ≥0}

/-- The second weak derivatives of `u ∘ Φ` given by the chain rule lie in `Lᵖ(U)` when `DΦ` is
`M`-Lipschitz: they are dominated by `L² ‖D²u(Φ ·)‖` and `M ‖∇u(Φ ·)‖`. -/
private theorem memLp_inner_iteratedGradient_comp_add_inner (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (u : Wkp mu V p 2) (c₀ f : E) :
    MemLp (fun x => ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x c₀⟫_ℝ +
      ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), fderiv ℝ (fderiv ℝ Φ) x f c₀⟫_ℝ) p
      (mu.restrict U) := by
  set H := iteratedGradient 1 u
  set G := iteratedGradient 0 (lowerOrder 1 u)
  have hU : MeasurableSet (U : Set E) := U.isOpen.measurableSet
  -- Precomposition with `Φ` keeps the derivatives of `u` in `Lᵖ(U)`.
  have hV : mu.restrict (Φ '' U) ≤ mu.restrict V :=
    Measure.restrict_mono h.mapsTo.image_subset le_rfl
  have hH : MemLp (fun x => H (Φ x)) p (mu.restrict U) :=
    ((Lp.memLp H).mono_measure hV).comp_restrict_of_le_abs_det U.isOpen h.differentiableOn h.injOn
      subset_rfl hU h.pos h.le_abs_det
  have hG : MemLp (fun x => G (Φ x)) p (mu.restrict U) :=
    ((Lp.memLp G).mono_measure hV).comp_restrict_of_le_abs_det U.isOpen h.differentiableOn h.injOn
      subset_rfl hU h.pos h.le_abs_det
  have hDΦ : AEStronglyMeasurable (fderiv ℝ Φ) (mu.restrict U) :=
    (measurable_fderiv ℝ Φ).aestronglyMeasurable
  have hD2Φ : AEStronglyMeasurable (fderiv ℝ (fderiv ℝ Φ)) (mu.restrict U) :=
    (measurable_fderiv ℝ (fderiv ℝ Φ)).aestronglyMeasurable
  refine MemLp.add (hH.of_le_mul (c := L ^ 2 * ‖f‖ * ‖c₀‖)
    (((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).aestronglyMeasurable_comp₂
      hH.aestronglyMeasurable (hDΦ.apply_continuousLinearMap f)).inner
        (hDΦ.apply_continuousLinearMap c₀)) ?_)
    (hG.of_le_mul (c := M * ‖f‖ * ‖c₀‖) (hG.aestronglyMeasurable.inner
      ((hD2Φ.apply_continuousLinearMap f).apply_continuousLinearMap c₀)) ?_)
  · filter_upwards [ae_restrict_mem hU] with x hx
    have hL := h.norm_fderiv_le x hx
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖H (Φ x) (fderiv ℝ Φ x f)‖ * ‖fderiv ℝ Φ x c₀‖
        ≤ (‖H (Φ x)‖ * (‖fderiv ℝ Φ x‖ * ‖f‖)) * (‖fderiv ℝ Φ x‖ * ‖c₀‖) := by
          gcongr
          · exact (H (Φ x)).le_opNorm_of_le ((fderiv ℝ Φ x).le_opNorm f)
          · exact (fderiv ℝ Φ x).le_opNorm c₀
      _ = ‖fderiv ℝ Φ x‖ ^ 2 * ‖f‖ * ‖c₀‖ * ‖H (Φ x)‖ := by ring
      _ ≤ L ^ 2 * ‖f‖ * ‖c₀‖ * ‖H (Φ x)‖ := by gcongr
  · filter_upwards [ae_restrict_mem hU] with x hx
    have hD2 : ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ M := norm_fderiv_le_of_lipschitzOn ℝ
      (U.isOpen.mem_nhds hx) hM
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖G (Φ x)‖ * ‖fderiv ℝ (fderiv ℝ Φ) x f c₀‖
        ≤ ‖G (Φ x)‖ * (‖fderiv ℝ (fderiv ℝ Φ) x‖ * ‖f‖ * ‖c₀‖) := by
          gcongr
          exact (fderiv ℝ (fderiv ℝ Φ) x).le_opNorm₂ f c₀
      _ ≤ ‖G (Φ x)‖ * (M * ‖f‖ * ‖c₀‖) := by gcongr
      _ = M * ‖f‖ * ‖c₀‖ * ‖G (Φ x)‖ := by ring

/-- A change of variables of class `C^{1,1}` keeps `u ∘ Φ` in `W^{2,p}`. -/
private theorem exists_firstOrder_eq_w1pCompL (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u : Wkp mu V p 2) :
    ∃ w : Wkp mu U p 2, firstOrder 1 w = h.w1pCompL hp (firstOrder 1 u) := by
  have hmem := memLp_inner_iteratedGradient_comp_add_inner h hM u
  have hΦ : LocallyLipschitzOn (U : Set E) (fderiv ℝ Φ) := hM.locallyLipschitzOn
  obtain ⟨w, hw⟩ := W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn
    (h.w1pCompL hp (firstOrder 1 u)) (stdOrthonormalBasis ℝ E) fun i j =>
      ⟨(hmem _ _).toLp _, (hasWeakLineDerivOn_inner_gradient_w1pCompL h hΦ hp u _ _).congr_ae_deriv
        (hmem _ _).coeFn_toLp.symm⟩
  exact ⟨w, by rw [firstOrder_one, hw]⟩

/-- Precomposition with a change of variables of class `C^{1,1}` is bounded on `W^{2,p}`. -/
private theorem exists_bound_firstOrder_eq_w1pCompL (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) :
    ∃ C : ℝ, ∀ u : Wkp mu V p 2, ∀ w : Wkp mu U p 2,
      firstOrder 1 w = h.w1pCompL hp (firstOrder 1 u) → ‖w‖ ≤ C * ‖u‖ := by
  set T : Wkp mu V p 2 →L[ℝ] Lp ℝ p (mu.restrict (U : Set E)) :=
    W1p.valueL.comp ((h.w1pCompL hp).comp (firstOrderL 1))
  have hT {u : Wkp mu V p 2} {w : Wkp mu U p 2}
      (hw : firstOrder 1 w = h.w1pCompL hp (firstOrder 1 u)) : value 2 w = T u := by
    rw [← value_firstOrder 1 w, hw, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      firstOrderL_apply, W1p.valueL_apply]
  obtain ⟨C, hC⟩ := exists_norm_le_of_forall_exists_value_ae_eq (mu := mu) (k := 2) T fun u => by
    obtain ⟨w, hw⟩ := exists_firstOrder_eq_w1pCompL h hM hp u
    exact ⟨w, Filter.EventuallyEq.of_eq (by rw [hT hw])⟩
  refine ⟨C, fun u w hw => ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC u
  rwa [Wkp.ext 2 (Lp.ext (hv.trans (Filter.EventuallyEq.of_eq (by rw [hT hw]))))] at hvC

/-- The element of `W^{2,p}(U)` whose first-order part is that of `u ∘ Φ`. -/
private def compOfLipschitzFDerivFun (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u : Wkp mu V p 2) : Wkp mu U p 2 :=
  (exists_firstOrder_eq_w1pCompL h hM hp u).choose

private theorem firstOrder_compOfLipschitzFDerivFun (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u : Wkp mu V p 2) :
    firstOrder 1 (compOfLipschitzFDerivFun h hM hp u) = h.w1pCompL hp (firstOrder 1 u) :=
  (exists_firstOrder_eq_w1pCompL h hM hp u).choose_spec

private theorem compOfLipschitzFDerivFun_add (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u v : Wkp mu V p 2) :
    compOfLipschitzFDerivFun h hM hp (u + v) =
      compOfLipschitzFDerivFun h hM hp u + compOfLipschitzFDerivFun h hM hp v := by
  refine ext_lowerOrder 1 ?_
  rw [← firstOrder_one, ← firstOrder_one]
  have hU := map_add (firstOrderL (mu := mu) (Omega := U) (p := p) 1)
    (compOfLipschitzFDerivFun h hM hp u) (compOfLipschitzFDerivFun h hM hp v)
  have hV := map_add (firstOrderL (mu := mu) (Omega := V) (p := p) 1) u v
  rw [firstOrderL_apply, firstOrderL_apply, firstOrderL_apply] at hU hV
  rw [hU, firstOrder_compOfLipschitzFDerivFun, firstOrder_compOfLipschitzFDerivFun,
    firstOrder_compOfLipschitzFDerivFun, hV, map_add]

private theorem compOfLipschitzFDerivFun_smul (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (a : ℝ) (u : Wkp mu V p 2) :
    compOfLipschitzFDerivFun h hM hp (a • u) =
      RingHom.id ℝ a • compOfLipschitzFDerivFun h hM hp u := by
  refine ext_lowerOrder 1 ?_
  rw [← firstOrder_one, ← firstOrder_one]
  have hU := map_smul (firstOrderL (mu := mu) (Omega := U) (p := p) 1) a
    (compOfLipschitzFDerivFun h hM hp u)
  have hV := map_smul (firstOrderL (mu := mu) (Omega := V) (p := p) 1) a u
  rw [firstOrderL_apply, firstOrderL_apply] at hU hV
  rw [RingHom.id_apply, hU, firstOrder_compOfLipschitzFDerivFun,
    firstOrder_compOfLipschitzFDerivFun, hV, map_smul]

/-- **Precomposition with a change of variables of class `C^{1,1}` in `W^{2,p}`.** Let `Φ` be a
change of variables of order one from `U` into `V` whose derivative is `M`-Lipschitz on `U`, and
let `1 ≤ p < ∞`. Precomposition with `Φ` is a bounded linear operator
`W^{2,p}(V) →L[ℝ] W^{2,p}(U)`: its value is `u ∘ Φ`
(`TauCeti.Wkp.value_compOfLipschitzFDerivL_ae`), its first-order part is the first-order change
of variables of that of `u` (`TauCeti.Wkp.firstOrder_compOfLipschitzFDerivL`), and its weak
Hessian obeys the chain rule `TauCeti.Wkp.inner_iteratedGradient_compOfLipschitzFDerivL_ae`. For a
change of variables of order two it is `TauCeti.Wkp.compL`
(`TauCeti.Wkp.compOfLipschitzFDerivL_eq_compL`). -/
def compOfLipschitzFDerivL (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) :
    Wkp mu V p 2 →L[ℝ] Wkp mu U p 2 :=
  LinearMap.mkContinuous
    { toFun := compOfLipschitzFDerivFun h hM hp
      map_add' := compOfLipschitzFDerivFun_add h hM hp
      map_smul' := compOfLipschitzFDerivFun_smul h hM hp }
    (exists_bound_firstOrder_eq_w1pCompL h hM hp).choose
    fun u => (exists_bound_firstOrder_eq_w1pCompL h hM hp).choose_spec u _
      (firstOrder_compOfLipschitzFDerivFun h hM hp u)

/-- The first-order part of `compOfLipschitzFDerivL h hM hp u` is the first-order change of
variables of the first-order part of `u`. -/
theorem firstOrder_compOfLipschitzFDerivL (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u : Wkp mu V p 2) :
    firstOrder 1 (compOfLipschitzFDerivL h hM hp u) = h.w1pCompL hp (firstOrder 1 u) :=
  firstOrder_compOfLipschitzFDerivFun h hM hp u

/-- The value of `compOfLipschitzFDerivL h hM hp u` is `u ∘ Φ`, almost everywhere on `U`. -/
theorem value_compOfLipschitzFDerivL_ae (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u : Wkp mu V p 2) :
    value 2 (compOfLipschitzFDerivL h hM hp u) =ᵐ[mu.restrict U] fun x => value 2 u (Φ x) := by
  rw [← value_firstOrder, firstOrder_compOfLipschitzFDerivL]
  filter_upwards [h.value_w1pCompL_ae hp (firstOrder 1 u)] with x hx
  rw [hx, value_firstOrder]

/-- `compOfLipschitzFDerivL h hM hp u` is the only element of `W^{2,p}(U)` whose value is `u ∘ Φ`
almost everywhere on `U`. -/
theorem compOfLipschitzFDerivL_eq_iff (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u : Wkp mu V p 2) (w : Wkp mu U p 2) :
    compOfLipschitzFDerivL h hM hp u = w ↔
      value 2 w =ᵐ[mu.restrict U] fun x => value 2 u (Φ x) := by
  refine ⟨fun hw => hw ▸ value_compOfLipschitzFDerivL_ae h hM hp u, fun hw => Wkp.ext 2 ?_⟩
  exact Lp.ext ((value_compOfLipschitzFDerivL_ae h hM hp u).trans hw.symm)

/-- For a change of variables of order two whose derivative is Lipschitz on `U`, precomposition
with `Φ` in `W^{2,p}` is `TauCeti.Wkp.compL`. -/
theorem compOfLipschitzFDerivL_eq_compL (h : IsChangeOfVariables 2 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) :
    compOfLipschitzFDerivL (h.mono one_le_two) hM hp = compL (mu := mu) (p := p) h := by
  ext1 u
  exact (compOfLipschitzFDerivL_eq_iff _ hM hp u _).2 (value_compL_ae h u)

/-- **The chain rule for the weak Hessian along a change of variables of class `C^{1,1}`.** Let `Φ`
be a change of variables of order one from `U` into `V` whose derivative is `M`-Lipschitz on `U`,
and let `1 ≤ p < ∞`. For `u ∈ W^{2,p}(V)`,

`⟪D²(u ∘ Φ)(x) f, g⟫ = ⟪D²u(Φ x) (DΦ(x) f), DΦ(x) g⟫ + ⟪∇u(Φ x), D²Φ(x) f g⟫`

for almost every `x ∈ U` and all directions `f` and `g`, where `D²Φ(x)`, the derivative of `DΦ`,
exists at almost every `x ∈ U` and is bounded by `M`. -/
theorem inner_iteratedGradient_compOfLipschitzFDerivL_ae (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u : Wkp mu V p 2) :
    ∀ᵐ x ∂mu.restrict U, ∀ f g : E,
      ⟪iteratedGradient 1 (compOfLipschitzFDerivL h hM hp u) x f, g⟫_ℝ =
        ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x g⟫_ℝ +
          ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), fderiv ℝ (fderiv ℝ Φ) x f g⟫_ℝ :=
  inner_iteratedGradient_ae_of_firstOrder_eq_w1pCompL h hM.locallyLipschitzOn hp u
    (firstOrder_compOfLipschitzFDerivL h hM hp u)

/-- **The first-order chain rule along a change of variables of class `C^{1,1}`.** The weak
gradient of the first-order part of `compOfLipschitzFDerivL h hM hp u` is `DΦ(x)† ∇u(Φ x)`, almost
everywhere on `U`. -/
theorem gradient_firstOrder_compOfLipschitzFDerivL_ae (h : IsChangeOfVariables 1 U V Φ L c)
    (hM : LipschitzOnWith M (fderiv ℝ Φ) U) (hp : p ≠ ⊤) (u : Wkp mu V p 2) :
    W1p.gradient (firstOrder 1 (compOfLipschitzFDerivL h hM hp u)) =ᵐ[mu.restrict U]
      fun x => (fderiv ℝ Φ x).adjoint (W1p.gradient (firstOrder 1 u) (Φ x)) := by
  rw [firstOrder_compOfLipschitzFDerivL]
  exact W1p.gradient_compL_ae Φ hp h.differentiableOn h.injOn h.mapsTo h.norm_fderiv_le h.pos
    h.le_abs_det _

/-- If `Ψ` maps `V` back into `U` inverse to `Φ`, and both are changes of variables of class
`C^{1,1}`, then precomposing with `Φ` and then with `Ψ` is the identity of `W^{2,p}(V)`. -/
theorem compOfLipschitzFDerivL_compOfLipschitzFDerivL_of_rightInvOn
    (h : IsChangeOfVariables 1 U V Φ L c) (hM : LipschitzOnWith M (fderiv ℝ Φ) U) {Ψ : E → E}
    {L' c' : ℝ} {M' : ℝ≥0} (h' : IsChangeOfVariables 1 V U Ψ L' c')
    (hM' : LipschitzOnWith M' (fderiv ℝ Ψ) V) (hΦΨ : RightInvOn Ψ Φ V) (hp : p ≠ ⊤)
    (u : Wkp mu V p 2) :
    compOfLipschitzFDerivL h' hM' hp (compOfLipschitzFDerivL h hM hp u) = u := by
  refine (compOfLipschitzFDerivL_eq_iff h' hM' hp _ u).2 ?_
  filter_upwards [h'.ae_comp (value_compOfLipschitzFDerivL_ae h hM hp u),
    ae_restrict_mem V.isOpen.measurableSet] with y hy hyV
  rw [hy, hΦΨ hyV]

end LipschitzFDeriv

end TauCeti.Wkp
