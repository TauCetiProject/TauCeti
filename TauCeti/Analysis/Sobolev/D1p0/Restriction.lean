/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.D1p0.Basic
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Gluing

/-!
# Restricting `D^{1,p}_0(Ω)` to bounded convex subsets

An element of the homogeneous Sobolev space `D^{1,p}_0(Ω)` (`TauCeti.D1p0`) is recorded by its
gradient field in `Lᵖ(Ω, E)`, a limit of gradients of test functions. It need not be the gradient
of a function in `Lᵖ(Ω)`: on the whole space the potential of an element of `D^{1,2}_0(ℝⁿ)` is in
general not square integrable. This file shows that it is nevertheless locally the gradient of a
Sobolev function: on every bounded convex open set `U ⊆ Ω`, the restriction of `u ∈ D^{1,p}_0(Ω)`
to `U` is the weak gradient of an element of `W^{1,p}(U)`
(`TauCeti.D1p0.exists_w1p_gradient_ae_eq`). This lets local estimates stated for `W^{1,p}`
functions, such as mean oscillation estimates on balls, apply to elements of `D^{1,p}_0(Ω)`. On the
whole space these local potentials glue: every element of `D^{1,p}_0(E)` is the weak gradient of a
locally integrable function (`TauCeti.D1p0.exists_hasWeakFDerivOn`).

## The argument

On the bounded convex set `U` the weak gradients of the elements of `W^{1,p}(U)` form a closed
subset of `Lᵖ(U, E)` (`TauCeti.W1p.isClosed_range_gradientL_of_convex`, from the Poincaré–Wirtinger
inequality). It contains the restriction to `U` of the gradient of every test function on `Ω`, and
restriction from `Lᵖ(Ω, E)` to `Lᵖ(U, E)` is continuous, so it contains the restriction of every
element of their closure `D^{1,p}_0(Ω)`.

On the whole space, the potentials on the balls `ball 0 (k + 1)`, normalized to have mean zero on
the unit ball, agree on overlaps, since two Sobolev functions with the same gradient on a connected
set differ by a constant, and glue to a potential on `E`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace
open scoped Distributions ENNReal NNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **Elements of `D^{1,p}_0(Ω)` are locally gradients of Sobolev functions.** On a bounded convex
open set `U ⊆ Ω`, every `u ∈ D^{1,p}_0(Ω)` agrees almost everywhere on `U` with the weak gradient
of some `v ∈ W^{1,p}(U)`. -/
theorem D1p0.exists_w1p_gradient_ae_eq {U : Opens E} (hU : U ≤ Omega)
    (hconv : Convex ℝ (U : Set E)) (hb : Bornology.IsBounded (U : Set E)) (u : D1p0 mu Omega p) :
    ∃ v : W1p mu U p, W1p.gradient v =ᵐ[mu.restrict U] (u : Lp E p (mu.restrict Omega)) := by
  -- Restriction of `Lᵖ` classes from `Ω` to `U`.
  have hle : mu.restrict (U : Set E) ≤ (1 : ℝ≥0∞) • mu.restrict Omega := by
    simpa only [one_smul] using Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
  set ρ : Lp E p (mu.restrict Omega) →L[ℝ] Lp E p (mu.restrict U) :=
    Lp.LpToLpOfMeasureLeSMul (by simp) hle
  -- The gradients of `W^{1,p}(U)` form a closed set, which contains the restricted gradient of
  -- every test function.
  have hclosed := W1p.isClosed_range_gradientL_of_convex (mu := mu) (p := p) hconv hb
  have htest : ∀ φ : 𝓓(Omega, ℝ), ρ (gradientTestFunctionLp p φ) ∈ range
      (W1p.gradientL : W1p mu U p →L[ℝ] Lp E p (mu.restrict U)) := by
    intro φ
    refine ⟨W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p φ), Lp.ext ?_⟩
    have hφU : ∀ᵐ x ∂mu.restrict U, gradientTestFunctionLp (mu := mu) p φ x =
        _root_.gradient (φ : E → ℝ) x :=
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hU)
        (gradientTestFunctionLp_apply_ae p φ)
    filter_upwards [W1p.gradient_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) hU φ,
      Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hle (gradientTestFunctionLp (mu := mu) p φ), hφU]
      with x hw hρ hφ
    rw [W1p.gradientL_apply, hw, hρ, hφ]
  -- So does the restriction of every element of `D^{1,p}_0(Ω)`, their limits.
  have hu : (u : Lp E p (mu.restrict Omega)) ∈
      ρ ⁻¹' range (W1p.gradientL : W1p mu U p →L[ℝ] Lp E p (mu.restrict U)) := by
    have hsub : closure (range (gradientTestFunctionLp (mu := mu) (Omega := Omega) p)) ⊆
        ρ ⁻¹' range (W1p.gradientL : W1p mu U p →L[ℝ] Lp E p (mu.restrict U)) :=
      closure_minimal (range_subset_iff.2 htest) (hclosed.preimage ρ.continuous)
    exact hsub (coe_d1p0Submodule (mu := mu) (Omega := Omega) (p := p) ▸ u.property)
  obtain ⟨v, hv⟩ := hu
  refine ⟨v, ?_⟩
  rw [← W1p.gradientL_apply, hv]
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hle _

/-- **Elements of `D^{1,p}_0(E)` are weak gradients.** Every `u ∈ D^{1,p}_0(E)` on the whole space
is the weak gradient of a function `q : E → ℝ`. The potentials of `u` on the balls
`ball 0 (k + 1)`, normalized to have mean zero on the unit ball, agree on overlaps and glue. -/
theorem D1p0.exists_hasWeakFDerivOn (u : D1p0 mu ⊤ p) :
    ∃ q : E → ℝ, HasWeakFDerivOn mu ⊤ q
      fun x ↦ innerSL ℝ ((u : Lp E p (mu.restrict ((⊤ : Opens E) : Set E))) x) := by
  set w : Lp E p (mu.restrict ((⊤ : Opens E) : Set E)) :=
    (u : Lp E p (mu.restrict ((⊤ : Opens E) : Set E)))
  let B : ℕ → Opens E := fun k ↦ ⟨ball 0 (k + 1), isOpen_ball⟩
  have hBmono {k m : ℕ} (hkm : k ≤ m) : B k ≤ B m :=
    ball_subset_ball (by simp only [add_le_add_iff_right, Nat.cast_le, hkm])
  have hfin (k) : IsFiniteMeasure (mu.restrict (B k : Set E)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hB0 (k) : ball (0 : E) 1 ⊆ B k := fun x hx ↦ hBmono (Nat.zero_le k) (by simpa [B] using hx)
  choose v hv using fun k ↦ D1p0.exists_w1p_gradient_ae_eq (U := B k) le_top (convex_ball _ _)
    isBounded_ball u
  let c : ℕ → ℝ := fun k ↦ ⨍ x in ball (0 : E) 1, W1p.value (v k) x ∂mu
  let a : ℕ → E → ℝ := fun k x ↦ W1p.value (v k) x - c k
  -- Each normalized potential has weak gradient `u` on its ball.
  have ha (k) : HasWeakFDerivOn mu (B k) (a k) fun x ↦ innerSL ℝ (w x) := by
    have hconst : HasWeakFDerivOn mu (B k) (fun _ ↦ c k) fun _ ↦ 0 :=
      hasWeakFDerivOn_iff.2 fun e ↦ by
        simpa only [zero_apply] using hasWeakLineDerivOn_const (μ := mu) (Ω := B k) (v := e) (c k)
    refine ((W1p.hasWeakFDerivOn (v k)).sub hconst).congr_ae_deriv ?_
    filter_upwards [hv k] with x hx
    simp only [Pi.sub_apply, sub_zero, hx, w]
  -- Two potentials differ by a constant on the smaller ball, so their normalizations agree.
  have hle {k m : ℕ} (hkm : k ≤ m) : a m =ᵐ[mu.restrict (B k)] a k := by
    obtain ⟨e, hdiff⟩ := W1p.exists_value_ae_eq_add_const_of_gradient_ae_eq_of_le (hBmono hkm)
      (convex_ball (0 : E) _).isPreconnected (u := v k) (v := v m)
      (.trans (ae_restrict_of_ae_restrict_of_subset (hBmono hkm) (hv m)) (hv k).symm)
    have hint : IntegrableOn (W1p.value (v k)) (ball (0 : E) 1) mu :=
      IntegrableOn.mono_set ((Lp.memLp (W1p.value (v k))).integrable Fact.out) (hB0 k)
    have hc : c m = c k + e := by
      have h₁ := setAverage_congr_fun (μ := mu) measurableSet_ball ((ae_restrict_iff'
        measurableSet_ball).1 (ae_restrict_of_ae_restrict_of_subset (hB0 k) hdiff))
      have h₂ := setAverage_add hint (integrableOn_const (C := e) measure_ball_lt_top.ne)
      rw [setAverage_const (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne] at h₂
      exact h₁.trans h₂
    filter_upwards [hdiff] with x hx
    simp only [a, hx, hc]
    ring
  have hcompat (k m : ℕ) : a k =ᵐ[mu.restrict ((B k : Set E) ∩ B m)] a m := by
    rcases le_total k m with hkm | hmk
    · simpa only [inter_eq_left.2 (hBmono hkm)] using (hle hkm).symm
    · simpa only [inter_eq_right.2 (hBmono hmk)] using hle hmk
  obtain ⟨q, hq⟩ := exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter
    (fun k ↦ (B k).isOpen.measurableSet) hcompat
  have hsup : (⨆ k, B k) = ⊤ := Opens.coe_inj.1 (by simp [B, iUnion_ball_nat_succ])
  have h : HasWeakFDerivOn mu (⨆ k, B k) q fun x ↦ innerSL ℝ (w x) :=
    (hasWeakFDerivOn_iSup_iff B).2 fun k ↦ (ha k).congr_ae (hq k).symm
  exact ⟨q, by rwa [hsup] at h⟩

end TauCeti
