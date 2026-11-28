/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Smooth logarithms of nonvanishing functions on simply connected manifolds

Let `M` be a simply connected, locally path connected `C^n` manifold over `ℝ`, and let
`f : M → ℂ` be a nowhere-vanishing `C^n` function. Since `exp : ℂ → ℂ \ {0}` is a covering map,
`f` has a continuous logarithm, unique once its value at a base point `x₀` is fixed; the branch
`ContMDiffMap.branchLog f x₀` takes the principal value `log (f x₀)` there. Near each point a
continuous logarithm of `f` is a constant plus the principal logarithm of `f` divided by a
constant, so it is again `C^n` (`ContMDiff.of_continuous_of_exp_eq`).

If `f` is `1` near a connected set `s` containing `x₀`, its branch vanishes near `s`, so
`exp ((1 - t) • branchLog f x₀)` stays among the nowhere-vanishing functions equal to `1` near `s`
(`ContMDiffMap.nonvanishingEqOneNear`); this formula is `C^n` in the time and the point jointly.
Its continuity in `f`, and the resulting contractibility of `ContMDiffMap.nonvanishingEqOneNear` in
the weak Whitney topology, are in `TauCeti.Geometry.Manifold.ContMDiffMap.Chart.BranchLog`.

## Main definitions

* `ContMDiffMap.branchLog f x₀`: the `C^n` logarithm of a nowhere-vanishing `C^n` function `f`
  with principal value at `x₀`.
* `ContMDiffMap.nonvanishingEqOneNear I n s`: the nowhere-vanishing `C^n` functions `M → ℂ` equal
  to `1` on a neighbourhood of `s`.

## Main results

* `ContMDiff.of_continuous_of_exp_eq`: a continuous logarithm of a `C^n` function is `C^n`.
* `ContMDiffMap.exp_branchLog_apply`, `ContMDiffMap.branchLog_apply_self`: the defining
  properties, and `ContMDiffMap.coe_branchLog_eq`: they characterize the branch among continuous
  functions.
* `ContMDiffMap.eventually_branchLog_eq_zero`: the branch of a function equal to `1` near a
  preconnected set containing the base point vanishes near that set.
* `ContMDiffMap.contMDiff_exp_smul_branchLog`: the contraction formula
  `(t, x) ↦ exp ((1 - t) • branchLog f x₀ x)` is `C^n` in the time and the point jointly.
-/

public section

noncomputable section

open Set Filter Topology Complex
open scoped Manifold ContDiff Real

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### Continuous logarithms are smooth -/

/-- A continuous logarithm of a `C^n` function on a manifold is `C^n`: near each point it is a
constant plus the principal logarithm of the function divided by a constant
(`TauCeti.eventuallyEq_add_log_div_exp`, the local argument also behind
`TauCeti.exists_contDiffOn_eqOn_exp_comp` on open subsets of `ℂ`). -/
theorem _root_.ContMDiff.of_continuous_of_exp_eq {f w : M → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) n f)
    (hw : Continuous w) (hexp : ∀ x, exp (w x) = f x) : ContMDiff I 𝓘(ℝ, ℂ) n w := by
  intro x
  have hlog : ContDiffAt ℝ n log (f x / exp (w x)) := by
    rw [← hexp x, div_self (Complex.exp_ne_zero _)]
    exact ContDiffAt.restrict_scalars ℝ (contDiffAt_log one_mem_slitPlane)
  have hdiv : ContMDiff I 𝓘(ℝ, ℂ) n fun y ↦ f y / exp (w x) :=
    (contDiff_id.div_const _).comp_contMDiff hf
  exact (contMDiffAt_const.add (ContDiffAt.comp_contMDiffAt (f := fun y ↦ f y / exp (w x))
    hlog hdiv.contMDiffAt)).congr_of_eventuallyEq
    (TauCeti.eventuallyEq_add_log_div_exp hw.continuousAt (Eventually.of_forall hexp))

/-! ### Functions equal to one near a set -/

variable (I n) in
/-- The nowhere-vanishing `C^n` functions `M → ℂ` equal to `1` on a neighbourhood of `s`. When
`M` is a domain in `ℝ²` and `ℂ` is read as `ℝ²`, these are the nowhere-vanishing vector fields
equal to the constant field `(1, 0)` near `s`. -/
def nonvanishingEqOneNear (s : Set M) : Set C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  {f | (∀ x, f x ≠ 0) ∧ ∀ᶠ x in 𝓝ˢ s, f x = 1}

/-- Membership in `nonvanishingEqOneNear`. -/
@[simp]
theorem mem_nonvanishingEqOneNear {s : Set M} :
    f ∈ nonvanishingEqOneNear I n s ↔ (∀ x, f x ≠ 0) ∧ ∀ᶠ x in 𝓝ˢ s, f x = 1 :=
  Iff.rfl

/-- The constant function `1` is nowhere zero and equal to `1` near every set. -/
theorem one_mem_nonvanishingEqOneNear (s : Set M) :
    (1 : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) ∈ nonvanishingEqOneNear I n s :=
  ⟨by simp, by simp⟩

/-! ### The branch of the logarithm -/

variable [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]

/-- A nowhere-vanishing continuous function on a simply connected, locally path connected space
has a unique continuous logarithm with principal value at `x₀`. -/
private theorem existsUnique_lift {f : M → ℂ} (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) (x₀ : M) :
    ∃! w : C(M, ℂ), w x₀ = log (f x₀) ∧ exp ∘ w = f :=
  isCoveringMapOn_exp.existsUnique_continuousMap_lifts ⟨f, hf⟩ (exp_log (h0 x₀)) fun x ↦ h0 x

open scoped Classical in
/-- **The branch of the logarithm** of a nowhere-vanishing `C^n` function `f : M → ℂ` on a simply
connected manifold, normalized at `x₀`: the unique continuous `w : M → ℂ` with `exp ∘ w = f` and
`w x₀ = log (f x₀)`, which is again `C^n`. If `f` has a zero it is `0`, by convention. -/
def branchLog (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x₀ : M) : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ⟨if hf : ∀ x, f x ≠ 0 then ⇑(existsUnique_lift f.contMDiff.continuous hf x₀).exists.choose
    else fun _ ↦ 0, by
    split_ifs with hf
    · exact f.contMDiff.of_continuous_of_exp_eq (map_continuous _) fun x ↦
        congrFun (existsUnique_lift f.contMDiff.continuous hf x₀).exists.choose_spec.2 x
    · exact contMDiff_const⟩

private theorem branchLog_spec (hf : ∀ x, f x ≠ 0) (x₀ : M) :
    branchLog f x₀ x₀ = log (f x₀) ∧ ∀ x, exp (branchLog f x₀ x) = f x := by
  have h := (existsUnique_lift f.contMDiff.continuous hf x₀).exists.choose_spec
  have hc : ⇑(branchLog f x₀) = ⇑(existsUnique_lift f.contMDiff.continuous hf x₀).exists.choose :=
    by rw [branchLog, coeFn_mk, dite_eq_left hf]
  rw [hc]
  exact ⟨h.1, fun x ↦ congrFun h.2 x⟩

/-- The branch of the logarithm of `f` exponentiates to `f`. -/
theorem exp_branchLog_apply (hf : ∀ x, f x ≠ 0) (x₀ x : M) : exp (branchLog f x₀ x) = f x :=
  (branchLog_spec hf x₀).2 x

/-- The branch of the logarithm normalized at `x₀` takes the principal value there. -/
theorem branchLog_apply_self (hf : ∀ x, f x ≠ 0) (x₀ : M) :
    branchLog f x₀ x₀ = log (f x₀) :=
  (branchLog_spec hf x₀).1

/-- The branch of the logarithm normalized at `x₀` is the only continuous logarithm of `f` with
principal value at `x₀`. -/
theorem coe_branchLog_eq (hf : ∀ x, f x ≠ 0) {x₀ : M} {g : M → ℂ} (hg : Continuous g)
    (hexp : ∀ x, exp (g x) = f x) (h₀ : g x₀ = log (f x₀)) : ⇑(branchLog f x₀) = g := by
  have h := (existsUnique_lift f.contMDiff.continuous hf x₀).unique
    (y₁ := ⟨branchLog f x₀, (branchLog f x₀).contMDiff.continuous⟩)
    (y₂ := ⟨g, hg⟩) ⟨branchLog_apply_self hf x₀, funext (exp_branchLog_apply hf x₀)⟩
    ⟨h₀, funext hexp⟩
  exact congrArg (⇑) h

/-- The branch of the logarithm of a function with a zero is `0`, by convention. -/
theorem branchLog_eq_zero_of_exists_eq_zero (h : ∃ x, f x = 0) (x₀ : M) :
    branchLog f x₀ = 0 := by
  refine ContMDiffMap.ext fun x ↦ ?_
  rw [branchLog, coeFn_mk, dite_eq_right (by simpa using h)]
  simp

/-- The branch of the logarithm of the constant function `1` is `0`. -/
@[simp]
theorem branchLog_one (x₀ : M) : branchLog (1 : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀ = 0 :=
  ContMDiffMap.ext fun x ↦ congrFun (coe_branchLog_eq (f := 1) (by simp) continuous_const
    (by simp) (by simp)) x

/-- **The branch of the logarithm vanishes near a set where the function is `1`.** If `f` is `1`
on a neighbourhood of a preconnected set `s` containing the base point, then the branch of its
logarithm normalized there is `0` on a neighbourhood of `s`. -/
theorem eventually_branchLog_eq_zero (hf : ∀ x, f x ≠ 0) {s : Set M} (hs : IsPreconnected s)
    {x₀ : M} (hx₀ : x₀ ∈ s) (h1 : ∀ᶠ x in 𝓝ˢ s, f x = 1) :
    ∀ᶠ x in 𝓝ˢ s, branchLog f x₀ x = 0 := by
  set w := branchLog f x₀
  have hexp1 : ∀ x ∈ s, exp (w x) = 1 := fun x hx ↦
    (exp_branchLog_apply hf x₀ x).trans (h1.self_of_nhdsSet x hx)
  -- On `s` the branch is a continuous logarithm of `1` vanishing at `x₀`, hence `0`.
  have hs0 : ∀ x ∈ s, w x = 0 := fun x hx ↦
    w.contMDiff.continuous.continuousOn.eqOn_of_eqOn_exp_comp continuousOn_const hs
      (fun y hy ↦ by simp [hexp1 y hy]) hx₀
      (by rw [branchLog_apply_self hf, h1.self_of_nhdsSet x₀ hx₀, log_one]) hx
  refine eventually_nhdsSet_iff_forall.2 fun x hx ↦ ?_
  filter_upwards [h1.filter_mono (nhds_le_nhdsSet hx),
    w.contMDiff.continuous.continuousAt.eventually
      (Metric.ball_mem_nhds (w x) (by positivity : (0 : ℝ) < 2 * π))] with y hy1 hyb
  rw [dist_eq_norm, hs0 x hx] at hyb
  exact eq_of_exp_eq_of_norm_sub_lt (by rw [exp_branchLog_apply hf, hy1, Complex.exp_zero]) hyb

/-- **The contraction is smooth in the time and the point jointly**: on `ℝ × M` its formula
`(t, x) ↦ exp ((1 - t) • branchLog f x₀ x)` is `C^n`. -/
theorem contMDiff_exp_smul_branchLog (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x₀ : M) :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, ℂ) n fun p : ℝ × M ↦ exp ((1 - p.1) • branchLog f x₀ p.2) :=
  (Complex.contDiff_exp.comp ((contDiff_const.sub contDiff_fst).smul contDiff_snd)).comp_contMDiff
    (contMDiff_fst.prodMk_space ((branchLog f x₀).contMDiff.comp contMDiff_snd))

end ContMDiffMap
