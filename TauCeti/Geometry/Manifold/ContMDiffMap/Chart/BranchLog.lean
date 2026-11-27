/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Prod
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
public import TauCeti.Geometry.Manifold.Instances.Rectangle
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic

/-!
# Smooth logarithms of nonvanishing functions on simply connected manifolds

Let `M` be a simply connected, locally path connected `C^n` manifold over `ℝ`, and let
`f : M → ℂ` be a nowhere-vanishing `C^n` function. Since `exp : ℂ → ℂ \ {0}` is a covering map,
`f` has a continuous logarithm, unique once its value at a base point `x₀` is fixed; the branch
`ContMDiffMap.branchLog f x₀` takes the principal value `log (f x₀)` there. Near each point a
continuous logarithm of `f` is a constant plus the principal logarithm of `f` divided by its value
at that point, so it is again `C^n` (`ContMDiff.of_continuous_of_exp_eq`).

For compact `M` and `n ≤ ∞` the branch depends continuously on `f` in the weak Whitney topology,
as long as `f x₀` stays off the branch cut of `log` (`ContMDiffMap.continuousOn_branchLog`): near
`f₀`, the branch of `f` is the branch of `f₀` plus the principal logarithm of `f / f₀`, which is
a postcomposition with a fixed smooth map.

The main application is a computation of homotopy type. For a connected nonempty set `s ⊆ M`,
the nowhere-vanishing `C^n` functions `M → ℂ` equal to `1` near `s`
(`ContMDiffMap.nonvanishingEqOneNear`) form a contractible space: their branches normalized at
a point of `s` vanish near `s`, so `exp ((1 - t) • branchLog f x₀)` contracts the space onto the
constant `1`, fixing `1` throughout, and the formula is `C^n` in the time and the point jointly.
For the rectangle `[a, b] × [c, d]` and `s` its boundary, reading `ℂ` as `ℝ²`, these functions are
the nowhere-vanishing vector fields equal to the constant field `(1, 0)` near the boundary
(`ContMDiffMap.contractibleSpace_nonvanishingEqOneNear_boundary_rectangle`). On Smale's route to
the contractibility of the diffeomorphisms of the square equal to the identity near the boundary,
a diffeomorphism `φ` is compared with the vector field `φ_* (1, 0)`, and the contractibility of
this space of fields, a space of maps to the circle with the homotopy type of `Ω² S¹`, is the
homotopy-theoretic input (S. Smale, *Diffeomorphisms of the 2-sphere*, Proc. Amer. Math. Soc. 10
(1959), 621–626).

## Main definitions

* `ContMDiffMap.branchLog f x₀`: the `C^n` logarithm of a nowhere-vanishing `C^n` function `f`
  with principal value at `x₀`.
* `ContMDiffMap.nonvanishingEqOneNear I n s`: the nowhere-vanishing `C^n` functions `M → ℂ` equal
  to `1` on a neighbourhood of `s`.
* `ContMDiffMap.nonvanishingEqOneNearContraction`: the contraction
  `(t, f) ↦ exp ((1 - t) • branchLog f x₀)`, relative to the constant `1`.

## Main results

* `ContMDiff.of_continuous_of_exp_eq`: a continuous logarithm of a `C^n` function is `C^n`.
* `ContMDiffMap.exp_branchLog_apply`, `ContMDiffMap.branchLog_apply_self`: the defining
  properties, and `ContMDiffMap.coe_branchLog_eq`: they characterize the branch among continuous
  functions.
* `ContMDiffMap.eventually_branchLog_eq_zero`: the branch of a function equal to `1` near a
  preconnected set containing the base point vanishes near that set.
* `ContMDiffMap.continuousOn_branchLog`: the branch is continuous in the function.
* `ContMDiffMap.contMDiff_exp_smul_branchLog`: the contraction formula is `C^n` in the time and the
  point jointly.
* `ContMDiffMap.contractibleSpace_nonvanishingEqOneNear`: for connected nonempty `s`, the
  nowhere-vanishing functions equal to `1` near `s` form a contractible space, and
  `ContMDiffMap.contractibleSpace_nonvanishingEqOneNear_boundary_rectangle` is the case of a
  rectangle and its boundary.
-/

public section

noncomputable section

open Set Filter Topology Complex
open scoped Manifold TauCeti.ManifoldWeakWhitney ContDiff Real

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### Continuous logarithms are smooth -/

/-- A continuous logarithm of a `C^n` function on a manifold is `C^n`: near each point it is a
constant plus the principal logarithm of the function divided by its value there. This is the
manifold form of the local argument of `TauCeti.exists_contDiffOn_eqOn_exp_comp`, which treats
open subsets of `ℂ`. -/
theorem _root_.ContMDiff.of_continuous_of_exp_eq {f w : M → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) n f)
    (hw : Continuous w) (hexp : ∀ x, exp (w x) = f x) : ContMDiff I 𝓘(ℝ, ℂ) n w := by
  intro x
  have hev : w =ᶠ[𝓝 x] fun y ↦ w x + log (f y * exp (-w x)) := by
    filter_upwards [hw.continuousAt.eventually (Metric.ball_mem_nhds (w x) one_pos)] with y hy
    rw [dist_eq_norm] at hy
    have him := (abs_le.1 (abs_im_le_norm (w y - w x)))
    rw [← hexp y, ← Complex.exp_add, ← sub_eq_add_neg,
      log_exp (by linarith [Real.two_le_pi]) (by linarith [Real.two_le_pi])]
    ring
  have hlog : ContDiffAt ℝ n log (f x * exp (-w x)) := by
    rw [← hexp x, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    exact ContDiffAt.restrict_scalars ℝ (contDiffAt_log one_mem_slitPlane)
  have hmul : ContMDiff I 𝓘(ℝ, ℂ) n fun y ↦ f y * exp (-w x) :=
    (contDiff_id.mul contDiff_const).comp_contMDiff hf
  exact (contMDiffAt_const.add (ContDiffAt.comp_contMDiffAt (f := fun y ↦ f y * exp (-w x))
    hlog hmul.contMDiffAt)).congr_of_eventuallyEq hev

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

/-- The exponential map of `ℂ`, as a `C^n` map. -/
private def expMap : C^n⟮𝓘(ℝ, ℂ), ℂ; 𝓘(ℝ, ℂ), ℂ⟯ := ⟨exp, Complex.contDiff_exp.contMDiff⟩

@[simp]
private theorem expMap_apply (z : ℂ) : (expMap : C^n⟮𝓘(ℝ, ℂ), ℂ; 𝓘(ℝ, ℂ), ℂ⟯) z = exp z := rfl

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
theorem branchLog_of_exists_eq_zero (h : ∃ x, f x = 0) (x₀ : M) : branchLog f x₀ = 0 := by
  refine ContMDiffMap.ext fun x ↦ ?_
  rw [branchLog, coeFn_mk, dite_eq_right (by simpa using h)]
  rfl

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

private theorem expMap_comp_smul_branchLog_mem {s : Set M} (hs : IsPreconnected s) {x₀ : M}
    (hx₀ : x₀ ∈ s) (t : ℝ) (f : nonvanishingEqOneNear I n s) :
    expMap.comp (t • branchLog (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀) ∈ nonvanishingEqOneNear I n s := by
  refine ⟨fun x ↦ by simp [Complex.exp_ne_zero], ?_⟩
  filter_upwards [eventually_branchLog_eq_zero f.property.1 hs hx₀ f.property.2] with x hx
  simp [hx]

/-! ### Continuity in the function -/

/-- A bump function on `ℂ`, equal to `1` on the closed disc of radius `1 / 4` about `1` and
supported in the disc of radius `1 / 2`. -/
private def bumpOne : ContDiffBump (1 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- A smooth function on `ℂ` which is the principal logarithm near `1`. -/
private def logNearOne (z : ℂ) : ℂ := log (1 + (bumpOne z : ℂ) * (z - 1))

private theorem one_add_bumpOne_mem_slitPlane (z : ℂ) :
    1 + (bumpOne z : ℂ) * (z - 1) ∈ slitPlane := by
  have hlt : ‖(bumpOne z : ℂ) * (z - 1)‖ < 1 := by
    by_cases hz : dist z 1 < 1 / 2
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg bumpOne.nonneg, ← dist_eq_norm]
      calc bumpOne z * dist z 1 ≤ 1 * dist z 1 :=
            mul_le_mul_of_nonneg_right bumpOne.le_one dist_nonneg
        _ < 1 := by linarith
    · rw [bumpOne.zero_of_le_dist (not_lt.1 hz)]
      simp
  refine mem_slitPlane_iff.2 (Or.inl ?_)
  have := neg_abs_le ((bumpOne z : ℂ) * (z - 1)).re
  rw [add_re, one_re]
  linarith [abs_re_le_norm ((bumpOne z : ℂ) * (z - 1))]

private theorem contDiff_logNearOne [ENat.LEInfty n] : ContDiff ℝ n logNearOne := by
  have hb : ContDiff ℝ n fun z : ℂ ↦ (bumpOne z : ℂ) :=
    ofRealCLM.contDiff.comp ((bumpOne.contDiff (n := ⊤)).of_le ENat.LEInfty.out)
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  exact (ContDiffAt.restrict_scalars ℝ (contDiffAt_log (one_add_bumpOne_mem_slitPlane z))).comp z
    (contDiff_const.add (hb.mul (contDiff_id.sub contDiff_const))).contDiffAt

private theorem logNearOne_eq {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 4) : logNearOne z = log z := by
  rw [logNearOne, bumpOne.one_of_mem_closedBall (by rwa [Metric.mem_closedBall, dist_eq_norm])]
  simp

/-- Near a logarithm `w₀` of `z₀`, the function `z ↦ w₀ + logNearOne (z * exp (-w₀))` is a
logarithm of `z`, for `z` within `‖z₀‖ / 4` of `z₀`. -/
private theorem exp_add_logNearOne {z z₀ w₀ : ℂ} (hw₀ : exp w₀ = z₀) (hz : z ≠ 0)
    (h : dist z z₀ < ‖z₀‖ / 4) : exp (w₀ + logNearOne (z * exp (-w₀))) = z := by
  have hz₀ : z₀ ≠ 0 := hw₀ ▸ Complex.exp_ne_zero w₀
  have hinv : exp (-w₀) = z₀⁻¹ := by rw [Complex.exp_neg, hw₀]
  have hn : ‖z * exp (-w₀) - 1‖ ≤ 1 / 4 := by
    rw [dist_eq_norm] at h
    rw [hinv, show z * z₀⁻¹ - 1 = (z - z₀) / z₀ by field_simp, norm_div,
      div_le_iff₀ (norm_pos_iff.2 hz₀)]
    linarith
  rw [Complex.exp_add, logNearOne_eq hn, exp_log (mul_ne_zero hz (Complex.exp_ne_zero _)), hw₀,
    hinv]
  field_simp

variable [IsManifold I n M] [LocallyCompactSpace E] [CompactSpace M] [ENat.LEInfty n]

/-- On compact `M` and for `n ≤ ∞`, **the branch of the logarithm depends continuously on the
function** in the weak Whitney topology, on the nowhere-vanishing functions whose value at the
base point lies off the branch cut of `log`. -/
theorem continuousOn_branchLog (x₀ : M) :
    ContinuousOn (fun f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ↦ branchLog f x₀)
      {f | (∀ x, f x ≠ 0) ∧ f x₀ ∈ slitPlane} := by
  rintro f₀ ⟨hf₀, hx₀⟩
  set w₀ := branchLog f₀ x₀
  have hinv (x : M) : exp (-w₀ x) = (f₀ x)⁻¹ := by
    rw [Complex.exp_neg, exp_branchLog_apply hf₀]
  -- Near `f₀`, the branch of `f` is `w₀ + log (f / f₀)`, a postcomposition with a fixed map.
  let G : C^n⟮𝓘(ℝ, ℂ).prod I, ℂ × M; 𝓘(ℝ, ℂ), ℂ⟯ :=
    ⟨fun p ↦ w₀ p.2 + logNearOne (p.1 * exp (-w₀ p.2)),
      (contDiff_snd.add (contDiff_logNearOne.comp
        (contDiff_fst.mul (Complex.contDiff_exp.comp contDiff_snd.neg)))).comp_contMDiff
        (contMDiff_fst.prodMk_space (w₀.contMDiff.comp contMDiff_snd))⟩
  let Φ (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ := G.comp (f.prodMk ContMDiffMap.id)
  have hΦ : Continuous Φ := (continuous_postcomp_manifoldWeakWhitney G).comp
    (continuous_prodMk_manifoldWeakWhitney.comp (continuous_id.prodMk continuous_const))
  have hΦ_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
      Φ f x = w₀ x + logNearOne (f x * exp (-w₀ x)) := rfl
  have hΦ₀ : Φ f₀ x₀ = log (f₀ x₀) := by
    rw [hΦ_apply, hinv, mul_inv_cancel₀ (hf₀ x₀), logNearOne_eq (by simp), log_one, add_zero,
      branchLog_apply_self hf₀]
  -- Nearby functions are uniformly close to `f₀` relative to `‖f₀‖`, and the value of the
  -- candidate at `x₀` stays close to the principal logarithm.
  have h1 : ∀ᶠ f in 𝓝 f₀, ∀ x ∈ univ, dist (f x) (f₀ x) < ‖f₀ x‖ / 4 :=
    eventually_forall_dist_lt f₀ isCompact_univ (f₀.contMDiff.continuous.norm.div_const 4)
      fun x _ ↦ by have := norm_pos_iff.2 (hf₀ x); positivity
  have h2 : ∀ᶠ f in 𝓝 f₀, ‖Φ f x₀ - log (f x₀)‖ < 2 * π := by
    have ht : Tendsto (fun f ↦ Φ f x₀ - log (f x₀)) (𝓝 f₀) (𝓝 (Φ f₀ x₀ - log (f₀ x₀))) :=
      ((continuous_eval_const_manifoldWeakWhitney x₀).comp hΦ).continuousAt.sub
        (ContinuousAt.comp (f := fun f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ↦ f x₀) (continuousAt_clog hx₀)
          (continuous_eval_const_manifoldWeakWhitney x₀).continuousAt)
    rw [hΦ₀, sub_self] at ht
    exact ht.norm.eventually (gt_mem_nhds (by simpa using Real.two_pi_pos))
  have hEq : ∀ᶠ f in 𝓝 f₀, f ∈ {f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ | (∀ x, f x ≠ 0) ∧ f x₀ ∈ slitPlane} →
      branchLog f x₀ = Φ f := by
    filter_upwards [h1, h2] with f hf1 hf2 hfS
    have hexp (x : M) : exp (Φ f x) = f x := by
      rw [hΦ_apply]
      exact exp_add_logNearOne (exp_branchLog_apply hf₀ x₀ x) (hfS.1 x) (hf1 x (mem_univ x))
    exact ContMDiffMap.ext fun x ↦ congrFun (coe_branchLog_eq hfS.1
      (Φ f).contMDiff.continuous hexp
      (eq_of_exp_eq_of_norm_sub_lt (by rw [hexp, exp_log (hfS.1 x₀)]) hf2)) x
  exact hΦ.continuousAt.continuousWithinAt.congr_of_eventuallyEq
    (eventually_nhdsWithin_iff.2 hEq) (hEq.self_of_nhds ⟨hf₀, hx₀⟩)

/-- **The contraction of the nowhere-vanishing functions equal to `1` near `s`**, for `s`
preconnected and containing `x₀`: `(t, f) ↦ exp ((1 - t) • branchLog f x₀)`, from the identity
to the constant `1`, fixing `1` throughout. -/
def nonvanishingEqOneNearContraction {s : Set M} (hs : IsPreconnected s) {x₀ : M}
    (hx₀ : x₀ ∈ s) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (nonvanishingEqOneNear I n s))
      (ContinuousMap.const _ ⟨1, one_mem_nonvanishingEqOneNear s⟩)
      {⟨1, one_mem_nonvanishingEqOneNear s⟩} where
  toFun p := ⟨expMap.comp (((1 : ℝ) - p.1) • branchLog (p.2 : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀),
    expMap_comp_smul_branchLog_mem hs hx₀ _ p.2⟩
  continuous_toFun := by
    have hb : Continuous fun f : nonvanishingEqOneNear I n s ↦
        branchLog (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀ :=
      (continuousOn_branchLog x₀).comp_continuous continuous_subtypeVal fun f ↦
        ⟨f.property.1, by rw [f.property.2.self_of_nhdsSet x₀ hx₀]; exact one_mem_slitPlane⟩
    exact ((continuous_postcomp_manifoldWeakWhitney expMap).comp
      ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).smul
        (hb.comp continuous_snd))).subtype_mk _
  map_zero_left f := Subtype.ext <| ContMDiffMap.ext fun x ↦ by
    simp [exp_branchLog_apply f.property.1]
  map_one_left f := Subtype.ext <| ContMDiffMap.ext fun x ↦ by simp
  prop' t f hf := by
    rw [mem_singleton_iff.1 hf]
    exact Subtype.ext <| ContMDiffMap.ext fun x ↦ by simp

/-- The contraction at time `t` is `exp ((1 - t) • branchLog f x₀)`. -/
theorem nonvanishingEqOneNearContraction_apply {s : Set M} (hs : IsPreconnected s) {x₀ : M}
    (hx₀ : x₀ ∈ s) (t : unitInterval) (f : nonvanishingEqOneNear I n s) (x : M) :
    (nonvanishingEqOneNearContraction hs hx₀ (t, f) : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x =
      exp ((1 - t : ℝ) • branchLog (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀ x) :=
  (rfl)

/-- **The nowhere-vanishing functions equal to `1` near a connected set form a contractible
space**, on a compact, simply connected, locally path connected manifold, in the weak Whitney
topology. -/
theorem contractibleSpace_nonvanishingEqOneNear {s : Set M} (hs : IsConnected s) :
    ContractibleSpace (nonvanishingEqOneNear I n s) := by
  obtain ⟨x₀, hx₀⟩ := hs.nonempty
  exact (contractible_iff_id_nullhomotopic _).2
    ⟨_, ⟨(nonvanishingEqOneNearContraction hs.isPreconnected hx₀).toHomotopy⟩⟩

/-! ### The rectangle -/

/-- **The nowhere-vanishing functions on a rectangle equal to `1` near its boundary form a
contractible space.** Reading `ℂ` as `ℝ²`, these are the nowhere-vanishing vector fields on
`[a, b] × [c, d]` equal to the constant field `(1, 0)` near the boundary. -/
theorem contractibleSpace_nonvanishingEqOneNear_boundary_rectangle {a b c d : ℝ}
    [Fact (a < b)] [Fact (c < d)] :
    ContractibleSpace (nonvanishingEqOneNear ((𝓡∂ 1).prod (𝓡∂ 1)) n
      (((𝓡∂ 1).prod (𝓡∂ 1)).boundary (Icc a b × Icc c d))) :=
  contractibleSpace_nonvanishingEqOneNear TauCeti.isConnected_boundary_rectangle

end ContMDiffMap
