/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import TauCeti.Analysis.PDE.EnergyForm.Integrated.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# The pure Neumann problem

Let `Ω` be an open set of finite measure, `a` an essentially bounded coefficient field with
`λ‖ξ‖² ≤ ξ · a(x) ξ` almost everywhere on `Ω` for some `λ > 0`, and `B(u, v) = ∫_Ω ∇v · a ∇u` the
energy form of `-div(a ∇u)` on `H¹(Ω)`, with no drift and no mass term. The **weak Neumann
problem** for a continuous linear functional `ℓ` on `H¹(Ω)` asks for `u ∈ H¹(Ω)` with

`B(u, v) = ℓ(v)` for every `v ∈ H¹(Ω)`.

The test space is all of `H¹(Ω)` and no boundary values are imposed: the boundary condition is the
natural one, `a ∇u · ν = 0` for `ℓ(v) = ∫_Ω f v`, and more generally a boundary integral
`∫_{∂Ω} h v` in `ℓ` prescribes the conormal derivative `h`. Testing against the constant `1`, which
lies in `H¹(Ω)` and has gradient zero, shows that `ℓ(1) = 0` is necessary. This file proves that it
is also sufficient when `Ω` is connected and the value map `H¹(Ω) → L²(Ω)` is compact, as on a
bounded Lipschitz domain, and that the solution is then unique up to an additive constant.

The proof follows the classical route. On the closed subspace of `H¹(Ω)` of functions with
integral zero over `Ω`, the gradient controls the full `H¹` norm by the Poincaré–Wirtinger
inequality `TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator`. So `B` is
coercive on that subspace and Lax–Milgram gives a unique solution there. Every `v ∈ H¹(Ω)` is a
function of integral zero plus a constant, and both `B(u, ·)` and `ℓ` vanish on constants, so the
solution tests correctly against all of `H¹(Ω)`. Two solutions differ by a function `w` with
`B(w, w) = 0`, hence `∇w = 0`, and `w` is constant on the connected domain.

Neither hypothesis can be dropped. On `Ω = (0, 1) ∪ (2, 3)` the indicator of `(0, 1)` minus that of
`(2, 3)` has gradient zero, so `ℓ(v) = ∫_Ω v (1_{(0,1)} - 1_{(2,3)})` satisfies `ℓ(1) = 0` but has
no solution, and solutions differ by locally constant functions. Without compactness the
Poincaré–Wirtinger inequality fails (for instance on a chain of rooms joined by ever thinner
passages) and the range of the Neumann operator is not closed.

## Main declarations

* `TauCeti.PDE.existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq`: for `ℓ(1) = 0`, the
  Neumann problem has exactly one solution of integral zero.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_iff`: the Neumann problem is solvable exactly when
  `ℓ(1) = 0`.
* `TauCeti.PDE.forall_energyFormH1_eq_iff_exists_eq_add_const`: on a connected domain, two
  functions have the same Neumann data exactly when they differ by a constant.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_iff`: for `f ∈ L²(Ω)`, the problem
  `-div(a ∇u) = f`, `a ∇u · ν = 0` is weakly solvable exactly when `∫_Ω f = 0`.
* `Set.IsLipschitzDomain.exists_forall_energyFormH1_eq_setIntegral_iff`: the same on every bounded
  connected Lipschitz domain, through Rellich–Kondrachov compactness
  `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomain`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Proposition 9.24 and Problem 47.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.1, Theorem 1 (Poincaré–Wirtinger),
  and §6.2.2 (the energy method).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Matrix

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam : ℝ}

-- The shortcut instances of the energy-form file, so that the operator norm of the bundled
-- energy form `TauCeti.PDE.energyFormH1L` is found by instance search.
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

/-- The integral over `Ω` of a Sobolev function, as a continuous linear functional on `H¹(Ω)`. -/
private def integralL [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))] :
    W1p mu Omega 2 →L[ℝ] ℝ :=
  (setIntegralLp (𝕜 := ℝ) univ (measure_lt_top _ _)).comp W1p.valueL

private theorem integralL_apply [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]
    (u : W1p mu Omega 2) : integralL u = ∫ x in Omega, W1p.value u x ∂mu := by
  rw [integralL, ContinuousLinearMap.comp_apply, setIntegralLp_apply, Measure.restrict_univ,
    W1p.valueL_apply]

/-- The integral over `Ω` of the constant `1` is the measure of `Ω`. -/
private theorem integralL_const_one
    [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))] :
    integralL (W1p.const 1 : W1p mu Omega 2) = mu.real Omega := by
  rw [integralL_apply, W1p.value_const,
    integral_congr_ae (Lp.coeFn_const 2 (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) 1)]
  simp

/-- With no drift and no mass term, a constant has zero energy against every function. -/
private theorem energyFormH1_const_right
    [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]
    (u : W1p mu Omega 2) (δ : ℝ) : energyFormH1 a 0 0 u (W1p.const δ) = 0 := by
  rw [energyFormH1_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [Lp.coeFn_zero (EuclideanSpace ℝ ι) 2
    (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))] with x hx
  rw [jetField_apply (W1p.const δ), W1p.gradient_const, hx]
  simp

/-- An almost-everywhere ellipticity floor `λ` integrates to `λ‖∇u‖² ≤ B(u, u)` on `H¹(Ω)`. -/
private theorem mul_norm_gradient_sq_le_energyFormH1_self
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (u : W1p mu Omega 2) : lam * ‖W1p.gradient u‖ ^ 2 ≤ energyFormH1 a 0 0 u u := by
  have key := integral_mul_norm_snd_sq_le_energyFormIntegral_zero_drift_self
    (μ := mu.restrict Omega) (a := a) (c := 0) (U := jetField u) ha
    (ae_of_all _ fun _ => le_rfl) ((integrable_norm_jetField_snd_sq u).const_mul lam)
    (integrable_energyIntegrand_jetField (b := 0) (c := 0) hcoeff u u)
  rw [← integral_norm_jetField_snd_sq_eq_norm_gradient_sq u, ← integral_const_mul]
  exact key.trans_eq ((energyFormIntegral_def _ _ _ _ _ _).trans (energyFormH1_def _ _ _ _ _).symm)

/-- On a connected domain, a Sobolev function with zero gradient is a constant. -/
private theorem exists_eq_const_of_gradient_eq_zero
    [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι))) {u : W1p mu Omega 2}
    (hu : W1p.gradient u = 0) : ∃ c : ℝ, u = W1p.const c := by
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero hconn hu
  refine ⟨c, W1p.ext_value (Lp.ext ?_)⟩
  rw [W1p.value_const]
  filter_upwards [hc, Lp.coeFn_const 2 (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) c]
    with x h₁ h₂
  rw [h₁, h₂, Function.const_apply]

section FiniteMeasure

variable [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]

/-- **Poincaré–Wirtinger for functions of integral zero.** On a connected domain with compact
value map, the gradient controls the `H¹` norm on the kernel of the integral over `Ω`. -/
private theorem exists_pos_mul_norm_le_norm_gradient
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ u ∈ LinearMap.ker (integralL (mu := mu) (Omega := Omega) : W1p mu Omega 2 →ₗ[ℝ] ℝ),
        c * ‖u‖ ≤ ‖W1p.gradient u‖ := by
  rcases eq_or_ne (mu Omega) 0 with h0 | h0
  · -- On a null set every Sobolev function vanishes.
    refine ⟨1, one_pos, fun u _ => ?_⟩
    have hu : u = 0 := by
      refine W1p.ext_value (Lp.ext ?_)
      rw [Filter.EventuallyEq, ae_eq_bot.2 (Measure.restrict_eq_zero.2 h0)]
      exact Filter.eventually_bot
    simp [hu]
  have hfin := measure_lt_top (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) univ
  rw [Measure.restrict_apply_univ] at hfin
  obtain ⟨C, hC, hPW⟩ :=
    W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator hK hconn hfin.ne subset_rfl h0
  refine ⟨(C + 1)⁻¹, by positivity, fun u hu => ?_⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, integralL_apply] at hu
  -- A function of integral zero has mean zero, so its `L²` norm is at most `C ‖∇u‖`.
  have hval : ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖ := by
    have h := hPW u
    rw [setAverage_eq, hu, smul_zero] at h
    simp only [sub_zero] at h
    rw [Lp.norm_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (h.trans_eq (by rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]))
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith [W1p.norm_le_norm_value_add_norm_gradient u]

/-- **The Neumann problem has a unique solution of integral zero.** Let `Ω` be connected with
compact value map `H¹(Ω) → L²(Ω)`, let `a` be essentially bounded with `λ‖ξ‖² ≤ ξ · a(x) ξ` almost
everywhere on `Ω` for some `λ > 0`, and let `ℓ` be a continuous linear functional on `H¹(Ω)` with
`ℓ(1) = 0`. Then exactly one `u ∈ H¹(Ω)` with `∫_Ω u = 0` satisfies

`∫_Ω ∇v · a ∇u = ℓ(v)` for every `v ∈ H¹(Ω)`. -/
theorem existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    {ℓ : StrongDual ℝ (W1p mu Omega 2)} (hℓ : ℓ (W1p.const 1) = 0) :
    ∃! u : W1p mu Omega 2, ∫ x in Omega, W1p.value u x ∂mu = 0 ∧
      ∀ v : W1p mu Omega 2, energyFormH1 a 0 0 u v = ℓ v := by
  -- The energy form is coercive on the functions of integral zero.
  obtain ⟨c, hc, hcM⟩ := exists_pos_mul_norm_le_norm_gradient hK hconn
  set M := LinearMap.ker (integralL (mu := mu) (Omega := Omega) : W1p mu Omega 2 →ₗ[ℝ] ℝ)
  -- Shortcut instances: the nested Sobolev subtypes make their synthesis slow.
  let : NormedAddCommGroup M := inferInstance
  let : InnerProductSpace ℝ M := inferInstance
  have : CompleteSpace M := integralL.isClosed_ker.completeSpace_coe
  let BM : M →L[ℝ] M →L[ℝ] ℝ :=
    (energyFormH1L (b := 0) (c := 0) hcoeff).bilinearComp M.subtypeL M.subtypeL
  have hBM (w v : M) : BM w v = energyFormH1 a 0 0 (w : W1p mu Omega 2) v := by
    simp [BM, Pi.zero_def]
  have hcoer : IsCoercive BM := by
    refine ⟨lam * c ^ 2, by positivity, fun w => ?_⟩
    rw [hBM]
    calc lam * c ^ 2 * ‖w‖ * ‖w‖ = lam * (c * ‖(w : W1p mu Omega 2)‖) ^ 2 := by
          rw [Submodule.norm_coe]; ring
      _ ≤ lam * ‖W1p.gradient (w : W1p mu Omega 2)‖ ^ 2 := by
          gcongr
          exact hcM w w.property
      _ ≤ _ := mul_norm_gradient_sq_le_energyFormH1_self hcoeff ha w
  obtain ⟨w, hw, huniq⟩ := hcoer.existsUnique_forall_eq (ℓ.comp M.subtypeL)
  -- Every `v` is a function of integral zero plus a multiple of `1`, on which both sides vanish.
  have hfin := measure_lt_top (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) univ
  rw [Measure.restrict_apply_univ] at hfin
  have hsplit (v : W1p mu Omega 2) :
      v - (integralL v / mu.real Omega) • W1p.const 1 ∈ M := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, map_smul, integralL_const_one,
      smul_eq_mul]
    rcases eq_or_ne (mu Omega) 0 with h0 | h0
    · rw [measureReal_def, h0, ENNReal.toReal_zero, mul_zero, sub_zero, integralL_apply,
        setIntegral_measure_zero _ h0]
    · rw [div_mul_cancel₀ _ (by rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨h0, hfin.ne⟩),
        sub_self]
  have hsol (u : M) (hu : ∀ v : M, BM u v = (ℓ.comp M.subtypeL) v) (v : W1p mu Omega 2) :
      energyFormH1 a 0 0 (u : W1p mu Omega 2) v = ℓ v := by
    have h := hu ⟨_, hsplit v⟩
    rw [hBM, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.coe_mk,
      energyFormH1_sub_right (b := 0) (c := 0) hcoeff, energyFormH1_smul_right,
      energyFormH1_const_right, mul_zero, sub_zero, map_sub, map_smul, hℓ, smul_zero,
      sub_zero] at h
    exact h
  refine ⟨w, ⟨(integralL_apply _).symm.trans w.property, hsol w hw⟩, ?_⟩
  rintro u ⟨hu0, hu⟩
  have huM : u ∈ M := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, integralL_apply]
    exact hu0
  exact congrArg Subtype.val (huniq ⟨u, huM⟩ fun v => by
    rw [hBM, hu, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply])

/-- **Solvability of the Neumann problem.** Under the hypotheses of
`TauCeti.PDE.existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq`, for a continuous linear
functional `ℓ` on `H¹(Ω)` there is `u ∈ H¹(Ω)` with `∫_Ω ∇v · a ∇u = ℓ(v)` for every
`v ∈ H¹(Ω)` exactly when `ℓ(1) = 0`. For `ℓ(v) = ∫_Ω f v + ∫_{∂Ω} h v`, the boundary integral
taken against the trace of `v`, this is the compatibility condition `∫_Ω f + ∫_{∂Ω} h = 0` between
the source and the prescribed conormal derivative. -/
theorem exists_forall_energyFormH1_eq_iff
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (ℓ : StrongDual ℝ (W1p mu Omega 2)) :
    (∃ u : W1p mu Omega 2, ∀ v, energyFormH1 a 0 0 u v = ℓ v) ↔ ℓ (W1p.const 1) = 0 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun hℓ => ?_⟩
  · rw [← hu, energyFormH1_const_right]
  · obtain ⟨u, ⟨-, hu⟩, -⟩ :=
      existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq hcoeff hlam ha hK hconn hℓ
    exact ⟨u, hu⟩

/-- **Uniqueness up to constants for the Neumann problem.** On a connected domain, if `a` is
essentially bounded with `λ‖ξ‖² ≤ ξ · a(x) ξ` almost everywhere on `Ω` for some `λ > 0`, two
functions `u, u' ∈ H¹(Ω)` satisfy `∫_Ω ∇v · a ∇u = ∫_Ω ∇v · a ∇u'` for every `v ∈ H¹(Ω)`
exactly when `u - u'` is constant. No compactness is needed. -/
theorem forall_energyFormH1_eq_iff_exists_eq_add_const
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι))) {u u' : W1p mu Omega 2} :
    (∀ v, energyFormH1 a 0 0 u v = energyFormH1 a 0 0 u' v) ↔
      ∃ c : ℝ, u = u' + W1p.const c := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ v => by rw [hc, energyFormH1_add_const_left]⟩
  -- The difference has zero energy, hence zero gradient, hence is constant.
  have hw : energyFormH1 a 0 0 (u - u') (u - u') = 0 := by
    rw [energyFormH1_sub_left (b := 0) (c := 0) hcoeff, h, sub_self]
  have hgrad : W1p.gradient (u - u') = 0 := by
    have hle := mul_norm_gradient_sq_le_energyFormH1_self hcoeff ha (u - u')
    rw [hw] at hle
    have : ‖W1p.gradient (u - u')‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm this (sq_nonneg _)))
  obtain ⟨c, hc⟩ := exists_eq_const_of_gradient_eq_zero hconn hgrad
  exact ⟨c, by rw [← hc, add_sub_cancel]⟩

/-- **The Neumann problem with an `L²` source.** Under the hypotheses of
`TauCeti.PDE.existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq`, for `f ∈ L²(Ω)` the
problem `-div(a ∇u) = f` in `Ω`, `a ∇u · ν = 0` on `∂Ω`, has a weak solution, a `u ∈ H¹(Ω)` with
`∫_Ω ∇v · a ∇u = ∫_Ω f v` for every `v ∈ H¹(Ω)`, exactly when `∫_Ω f = 0`. -/
theorem exists_forall_energyFormH1_eq_setIntegral_iff
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    (∃ u : W1p mu Omega 2, ∀ v : W1p mu Omega 2,
        energyFormH1 a 0 0 u v = ∫ x in Omega, f x * W1p.value v x ∂mu) ↔
      ∫ x in Omega, f x ∂mu = 0 := by
  have hℓ (v : W1p mu Omega 2) :
      ((innerSL ℝ f).comp W1p.valueL) v = ∫ x in Omega, f x * W1p.value v x ∂mu := by
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.valueL_apply, L2.inner_def]
    simp [mul_comm]
  have hone : ((innerSL ℝ f).comp W1p.valueL) (W1p.const 1 : W1p mu Omega 2) =
      ∫ x in Omega, f x ∂mu := by
    rw [hℓ, W1p.value_const]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_const 2 (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) (1 : ℝ)]
      with x hx
    rw [hx, Function.const_apply, mul_one]
  simp_rw [← hℓ, ← hone]
  exact exists_forall_energyFormH1_eq_iff hcoeff hlam ha hK hconn _

end FiniteMeasure

end TauCeti.PDE

namespace Set.IsLipschitzDomain

open TauCeti TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam : ℝ}

/-- **The Neumann problem on a bounded Lipschitz domain.** Let `Ω ⊆ ℝⁿ` be a bounded connected
Lipschitz domain and `a` an essentially bounded coefficient field with `λ‖ξ‖² ≤ ξ · a(x) ξ` almost
everywhere on `Ω` for some `λ > 0`, as for inverse-coercive coefficients
(`TauCeti.PDE.IsUniformlyEllipticAE`). For `f ∈ L²(Ω)` there is `u ∈ H¹(Ω)` with

`∫_Ω ∇v · a ∇u = ∫_Ω f v` for every `v ∈ H¹(Ω)`,

a weak solution of `-div(a ∇u) = f` in `Ω`, `a ∇u · ν = 0` on `∂Ω`, exactly when `∫_Ω f = 0`. By
`TauCeti.PDE.forall_energyFormH1_eq_iff_exists_eq_add_const` it is then unique up to an additive
constant. -/
theorem exists_forall_energyFormH1_eq_setIntegral_iff
    (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    (∃ u : W1p mu Omega 2, ∀ v : W1p mu Omega 2,
        energyFormH1 a 0 0 u v = ∫ x in Omega, f x * W1p.value v x ∂mu) ↔
      ∫ x in Omega, f x ∂mu = 0 := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  exact TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_iff hcoeff hlam ha
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb) hconn f

end Set.IsLipschitzDomain
