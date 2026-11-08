/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Analysis.ODE.DysonSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Twisted periodic solutions of linear equations and the return map

Let `M : ℝ → (X →L[ℝ] X)` be a continuous path of bounded operators on a Banach space `X`, periodic
of period `d`, and let `Ψ = TauCeti.dysonSeriesLeft M` be the propagator of `w' = M w`, so that
`P = Ψ(d)` is the return map. For a real twist `ε` consider maps twisted by `ε` along `d`, that is,
with `w (t + d) = ε • w t`: for `ε = 1` these are the `d`-periodic maps, for `ε = -1` the
`d`-antiperiodic ones. On them the first-order operator

`L w = w' - M w`

(`TauCeti.twistedLinearOperator`) maps the `C¹` twisted maps (`TauCeti.twistedContDiff`) to the
continuous twisted maps (`TauCeti.twistedContinuous`). This file computes its kernel and cokernel
in terms of the finite complex `ε - P : X → X`.

By variation of constants (`TauCeti.eq_dysonSeriesLeft_apply_add_integral`), a solution of
`w' = M w + f` satisfies `w d = P (w 0) + E f`, where

`E f = Ψ(d) (∫₀ᵈ Ψ(s)⁻¹ (f s) ds)`

(`TauCeti.twistedEndpoint`) is the value at time `d` of the solution with zero initial value.
Such a solution is twisted exactly when `w d = ε • w 0`
(`TauCeti.forall_add_eq_smul_iff_apply_eq_smul`), that is, when `(ε - P) (w 0) = E f`. Hence:

* evaluation at `0` is a linear equivalence from the kernel of `L` onto the kernel of `ε - P`
  (`TauCeti.kerTwistedLinearOperatorEquiv`), with inverse `x ↦ (t ↦ Ψ t x)`;
* `f` lies in the range of `L` exactly when `E f` lies in the range of `ε - P`
  (`TauCeti.mem_range_twistedLinearOperator_iff`);
* for `d > 0` and `ε = ±1` the endpoint map `E` is surjective
  (`TauCeti.twistedEndpoint_surjective`), so it
  induces a linear equivalence from the cokernel of `L` onto the cokernel of `ε - P`
  (`TauCeti.quotientRangeTwistedLinearOperatorEquiv`).

So the kernel and cokernel of `d/dt - M` on twisted loops are those of the finite complex
`ε - P : X → X`, for an arbitrary continuous periodic coefficient `M`. When `X` is
finite-dimensional the kernel and cokernel of `L` have the same dimension
(`TauCeti.finrank_ker_twistedLinearOperator_eq_finrank_quotient_range`), and `L` is surjective
exactly when it is injective, exactly when `det (ε - P) ≠ 0`
(`TauCeti.range_twistedLinearOperator_eq_top_iff_det_ne_zero`): the Fredholm alternative for
periodic linear equations. For the normal operator `∂s + J₀ ∂t + S(t)` of an orbit torus, the
operators `∂t - J₀ S(t)` on loops twisted by the sign characters of the orbit are of this form, with
`P` the linearized return map; their kernels and cokernels are those of `1 - P` and `-1 - P`.

## Main definitions

* `TauCeti.twistedContinuous X d ε`, `TauCeti.twistedContDiff X d ε`: the continuous and the `C¹`
  maps `ℝ → X` twisted by `ε` along `d`.
* `TauCeti.twistedLinearOperator hM hper ε`: the operator `w ↦ w' - M w` between them.
* `TauCeti.twistedEndpoint hM d ε`: the endpoint map `f ↦ Ψ(d) (∫₀ᵈ Ψ(s)⁻¹ (f s) ds)`.

## Main results

* `TauCeti.exists_twisted_solution_iff`: the twisted problem `w' = M w + f` is solvable exactly when
  `E f` lies in the range of `ε - Ψ(d)`.
* `TauCeti.kerTwistedLinearOperatorEquiv`: `ker L ≃ ker (ε - Ψ(d))`.
* `TauCeti.quotientRangeTwistedLinearOperatorEquiv`: `coker L ≃ coker (ε - Ψ(d))`.
* `TauCeti.finiteDimensional_ker_twistedLinearOperator`,
  `TauCeti.finiteDimensional_quotient_range_twistedLinearOperator`: in finite dimension, the kernel
  and cokernel of `L` are finite-dimensional.
* `TauCeti.range_twistedLinearOperator_eq_top_iff_det_ne_zero`,
  `TauCeti.ker_twistedLinearOperator_eq_bot_iff_det_ne_zero`: the Fredholm alternative.

## References

* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, McGraw–Hill
  (1955), Chapter 3, for linear systems with periodic coefficients and their monodromy.
-/

public section

noncomputable section

open Set intervalIntegral

namespace TauCeti

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section Spaces

variable (X) in
/-- The continuous maps `f : ℝ → X` twisted by `ε` along `d`, that is, with
`f (t + d) = ε • f t`. For `ε = 1` these are the continuous `d`-periodic maps, for `ε = -1` the
continuous `d`-antiperiodic maps. -/
def twistedContinuous (d ε : ℝ) : Submodule ℝ (ℝ → X) where
  carrier := {f | Continuous f ∧ ∀ t, f (t + d) = ε • f t}
  add_mem' {f g} hf hg := ⟨hf.1.add hg.1, fun t => by
    rw [Pi.add_apply, Pi.add_apply, hf.2 t, hg.2 t, smul_add]⟩
  zero_mem' := ⟨continuous_const, fun t => by simp⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun t => by
    rw [Pi.smul_apply, Pi.smul_apply, hf.2 t, smul_comm]⟩

variable (X) in
/-- The `C¹` maps `w : ℝ → X` twisted by `ε` along `d`, that is, with `w (t + d) = ε • w t`. -/
def twistedContDiff (d ε : ℝ) : Submodule ℝ (ℝ → X) where
  carrier := {w | ContDiff ℝ 1 w ∧ ∀ t, w (t + d) = ε • w t}
  add_mem' {w v} hw hv := ⟨hw.1.add hv.1, fun t => by
    rw [Pi.add_apply, Pi.add_apply, hw.2 t, hv.2 t, smul_add]⟩
  zero_mem' := ⟨contDiff_const, fun t => by simp⟩
  smul_mem' c w hw := ⟨hw.1.const_smul c, fun t => by
    rw [Pi.smul_apply, Pi.smul_apply, hw.2 t, smul_comm]⟩

variable {d ε : ℝ}

@[simp]
theorem mem_twistedContinuous {f : ℝ → X} :
    f ∈ twistedContinuous X d ε ↔ Continuous f ∧ ∀ t, f (t + d) = ε • f t :=
  Iff.rfl

@[simp]
theorem mem_twistedContDiff {w : ℝ → X} :
    w ∈ twistedContDiff X d ε ↔ ContDiff ℝ 1 w ∧ ∀ t, w (t + d) = ε • w t :=
  Iff.rfl

/-- The `C¹` twisted maps are continuous twisted maps. -/
theorem twistedContDiff_le_twistedContinuous : twistedContDiff X d ε ≤ twistedContinuous X d ε :=
  fun _ hw => ⟨hw.1.continuous, hw.2⟩

end Spaces

variable {M : ℝ → X →L[ℝ] X} {d ε : ℝ}

section Operator

/-- The operator `L w = w' - M w` from the `C¹` maps twisted by `ε` along `d` to the continuous
maps twisted by `ε` along `d`, for a continuous path `M` of bounded operators of period `d`. -/
def twistedLinearOperator (hM : Continuous M) (hper : Function.Periodic M d) (ε : ℝ) :
    twistedContDiff X d ε →ₗ[ℝ] twistedContinuous X d ε where
  toFun w := ⟨fun t => deriv (w : ℝ → X) t - M t ((w : ℝ → X) t),
    (w.2.1.continuous_deriv le_rfl).sub (hM.clm_apply w.2.1.continuous), fun t => by
      have hd : deriv (w : ℝ → X) (t + d) = ε • deriv (w : ℝ → X) t := by
        simp only [← fderiv_apply_one_eq_deriv, fderiv_add_eq_smul w.2.2 t, smul_apply]
      simp only [hd, hper t, w.2.2 t, map_smul, smul_sub]⟩
  map_add' w v := by
    ext t
    simp [deriv_add (w.2.1.differentiable one_ne_zero t) (v.2.1.differentiable one_ne_zero t)]
    abel
  map_smul' c w := by
    ext t
    simp [deriv_const_smul c (w.2.1.differentiable one_ne_zero t), smul_sub]

@[simp]
theorem twistedLinearOperator_apply (hM : Continuous M) (hper : Function.Periodic M d)
    (w : twistedContDiff X d ε) (t : ℝ) :
    (twistedLinearOperator hM hper ε w : ℝ → X) t = deriv (w : ℝ → X) t - M t ((w : ℝ → X) t) :=
  (rfl)

/-- A `C¹` twisted map `w` solves `w' = M w + f` exactly when `L w = f`. -/
theorem twistedLinearOperator_eq_iff (hM : Continuous M) (hper : Function.Periodic M d)
    (w : twistedContDiff X d ε) (f : twistedContinuous X d ε) :
    twistedLinearOperator hM hper ε w = f ↔
      ∀ t, HasDerivAt (w : ℝ → X) (M t ((w : ℝ → X) t) + (f : ℝ → X) t) t := by
  have hd (t : ℝ) := (w.2.1.differentiable one_ne_zero t).hasDerivAt
  constructor
  · rintro rfl t
    simpa [twistedLinearOperator_apply] using hd t
  · intro h
    ext t
    rw [twistedLinearOperator_apply, (h t).deriv, add_sub_cancel_left]

/-- A `C¹` twisted map lies in the kernel of `L` exactly when it solves `w' = M w`. -/
theorem mem_ker_twistedLinearOperator_iff (hM : Continuous M) (hper : Function.Periodic M d)
    (w : twistedContDiff X d ε) :
    w ∈ LinearMap.ker (twistedLinearOperator hM hper ε) ↔
      ∀ t, HasDerivAt (w : ℝ → X) (M t ((w : ℝ → X) t)) t := by
  rw [LinearMap.mem_ker, twistedLinearOperator_eq_iff]
  simp

end Operator

variable [CompleteSpace X]

section Solutions

/-- A solution of `w' = M w + f`, with `M` periodic of period `d` and `f` twisted by `ε` along `d`,
is twisted by `ε` along `d` exactly when `w d = ε • w 0`. -/
theorem forall_add_eq_smul_iff_apply_eq_smul (hM : Continuous M) (hper : Function.Periodic M d)
    {f : ℝ → X} (hf : ∀ t, f (t + d) = ε • f t) {w : ℝ → X}
    (hw : ∀ t, HasDerivAt w (M t (w t) + f t) t) :
    (∀ t, w (t + d) = ε • w t) ↔ w d = ε • w 0 := by
  refine ⟨fun h => by simpa using h 0, fun h t => ?_⟩
  -- `t ↦ w (t + d) - ε • w t` solves the homogeneous equation and vanishes at `0`.
  have hv (t : ℝ) : HasDerivAt (fun t => w (t + d) - ε • w t) (M t (w (t + d) - ε • w t)) t :=
    (((hw (t + d)).comp_add_const t d).sub ((hw t).const_smul ε)).congr_deriv (by
      rw [hper t, hf t, map_sub, map_smul, smul_add]
      abel)
  have h0 := eq_dysonSeriesLeft_apply hM hv t
  rw [zero_add, h, sub_self, map_zero] at h0
  exact sub_eq_zero.1 h0

/-- A solution of `w' = M w + f` satisfies `w d = Ψ(d) (w 0) + Ψ(d) (∫₀ᵈ Ψ(s)⁻¹ (f s) ds)`, where
`Ψ = dysonSeriesLeft M`. -/
theorem apply_eq_dysonSeriesLeft_apply_add (hM : Continuous M) {f : ℝ → X} (hf : Continuous f)
    {w : ℝ → X} (hw : ∀ t, HasDerivAt w (M t (w t) + f t) t) (d : ℝ) :
    w d = dysonSeriesLeft M d (w 0) +
      dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s (f s)) := by
  rw [eq_dysonSeriesLeft_apply_add_integral hM hf hw d, map_add]

/-- A solution of `w' = M w + f`, with `M` periodic and `f` continuous and twisted by `ε` along
`d`, is twisted by `ε` exactly when `(ε - Ψ(d)) (w 0) = Ψ(d) (∫₀ᵈ Ψ(s)⁻¹ (f s) ds)`. -/
theorem forall_add_eq_smul_iff_smul_one_sub_apply_eq (hM : Continuous M)
    (hper : Function.Periodic M d) {f : ℝ → X} (hfc : Continuous f)
    (hf : ∀ t, f (t + d) = ε • f t) {w : ℝ → X} (hw : ∀ t, HasDerivAt w (M t (w t) + f t) t) :
    (∀ t, w (t + d) = ε • w t) ↔
      (ε • 1 - dysonSeriesLeft M d : X →L[ℝ] X) (w 0) =
        dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s (f s)) := by
  rw [forall_add_eq_smul_iff_apply_eq_smul hM hper hf hw,
    apply_eq_dysonSeriesLeft_apply_add hM hfc hw d, sub_apply, smul_apply, one_apply_eq_self,
    sub_eq_iff_eq_add', eq_comm]

/-- **Solvability of the twisted problem.** For `M` continuous and periodic of period `d`, and `f`
continuous and twisted by `ε` along `d`, the equation `w' = M w + f` has a solution twisted by `ε`
along `d` exactly when `Ψ(d) (∫₀ᵈ Ψ(s)⁻¹ (f s) ds)` lies in the range of `ε - Ψ(d)`. -/
theorem exists_twisted_solution_iff (hM : Continuous M) (hper : Function.Periodic M d)
    {f : ℝ → X} (hfc : Continuous f) (hf : ∀ t, f (t + d) = ε • f t) :
    (∃ w : ℝ → X, (∀ t, HasDerivAt w (M t (w t) + f t) t) ∧ ∀ t, w (t + d) = ε • w t) ↔
      dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s (f s)) ∈
        LinearMap.range (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) := by
  constructor
  · rintro ⟨w, hw, htw⟩
    have h := (forall_add_eq_smul_iff_smul_one_sub_apply_eq hM hper hfc hf hw).1 htw
    exact ⟨w 0, by simpa using h⟩
  · rintro ⟨x, hx⟩
    have hw := hasDerivAt_dysonSeriesLeft_apply_add_integral hM hfc x
    refine ⟨_, hw, (forall_add_eq_smul_iff_smul_one_sub_apply_eq hM hper hfc hf hw).2 ?_⟩
    simpa using hx

end Solutions

section Endpoint

/-- The endpoint map `E f = Ψ(d) (∫₀ᵈ Ψ(s)⁻¹ (f s) ds)` on continuous maps twisted by `ε`, where
`Ψ = dysonSeriesLeft M` and `Ψ(s)⁻¹ = dysonSeries (-M) s`: the value at time `d` of the solution
of `w' = M w + f` with `w 0 = 0` (`TauCeti.apply_eq_dysonSeriesLeft_apply_add`). -/
def twistedEndpoint (hM : Continuous M) (d ε : ℝ) : twistedContinuous X d ε →ₗ[ℝ] X where
  toFun f := dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s ((f : ℝ → X) s))
  map_add' f g := by
    have hi (h : twistedContinuous X d ε) :
        IntervalIntegrable (fun s => dysonSeries (-M) s ((h : ℝ → X) s))
          MeasureTheory.volume 0 d :=
      ((continuous_dysonSeries hM.neg).clm_apply h.2.1).intervalIntegrable 0 d
    simp only [Submodule.coe_add, Pi.add_apply, map_add, integral_add (hi f) (hi g)]
  map_smul' c f := by
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, integral_smul, RingHom.id_apply]

@[simp]
theorem twistedEndpoint_apply (hM : Continuous M) (f : twistedContinuous X d ε) :
    twistedEndpoint hM d ε f =
      dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s ((f : ℝ → X) s)) :=
  (rfl)

/-- The range of `L = d/dt - M` on twisted maps: `f = L w` for a twisted `C¹` map `w` exactly when
the endpoint value `E f` lies in the range of `ε - Ψ(d)`. -/
theorem mem_range_twistedLinearOperator_iff (hM : Continuous M) (hper : Function.Periodic M d)
    (f : twistedContinuous X d ε) :
    f ∈ LinearMap.range (twistedLinearOperator hM hper ε) ↔
      twistedEndpoint hM d ε f ∈
        LinearMap.range (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) := by
  rw [twistedEndpoint_apply, ← exists_twisted_solution_iff hM hper f.2.1 f.2.2]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (twistedLinearOperator_eq_iff hM hper w f).1 hw, w.2.2⟩
  · rintro ⟨w, hw, htw⟩
    have hc : ContDiff ℝ 1 w := contDiff_one_iff_deriv.2 ⟨fun t => (hw t).differentiableAt, by
      rw [funext fun t => (hw t).deriv]
      exact (hM.clm_apply (continuous_iff_continuousAt.2 fun t => (hw t).continuousAt)).add
        f.2.1⟩
    exact ⟨⟨w, hc, htw⟩, (twistedLinearOperator_eq_iff hM hper ⟨w, hc, htw⟩ f).2 hw⟩

/-- The scalar weight `e(s) = (1 + ε) / 2 + (1 - ε) / 2 · sin (π s / d)`, equal to `1` for `ε = 1`
and to `sin (π s / d)` for `ε = -1`: it is twisted by `ε` along `d` and positive on `(0, d)`. -/
private def twistWeight (d ε s : ℝ) : ℝ :=
  (1 + ε) / 2 + (1 - ε) / 2 * Real.sin (Real.pi * s / d)

private theorem continuous_twistWeight (d ε : ℝ) : Continuous (twistWeight d ε) := by
  unfold twistWeight
  fun_prop

private theorem twistWeight_add (hd : d ≠ 0) (hε : ε ^ 2 = 1) (s : ℝ) :
    twistWeight d ε (s + d) = ε * twistWeight d ε s := by
  have h : Real.pi * (s + d) / d = Real.pi * s / d + Real.pi := by field_simp
  simp only [twistWeight, h, Real.sin_add_pi]
  linear_combination (Real.sin (Real.pi * s / d) - 1) / 2 * hε

private theorem twistWeight_pos (hε : ε ^ 2 = 1) {s : ℝ}
    (hsin : 0 < Real.sin (Real.pi * s / d)) : 0 < twistWeight d ε s := by
  obtain rfl | rfl : ε = 1 ∨ ε = -1 := by
    have : (ε - 1) * (ε + 1) = 0 := by linear_combination hε
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · norm_num [twistWeight]
  · norm_num [twistWeight, hsin]

/-- For `d > 0` and `ε = ±1`, every vector `y` is `∫₀ᵈ Ψ(s)⁻¹ (f s) ds` for some continuous map
`f` twisted by `ε` along `d`. -/
theorem exists_mem_twistedContinuous_integral_eq (hM : Continuous M) (hd : 0 < d)
    (hε : ε ^ 2 = 1) (y : X) :
    ∃ f ∈ twistedContinuous X d ε, ∫ s in 0..d, dysonSeries (-M) s (f s) = y := by
  have : Fact (0 < d) := ⟨hd⟩
  set θ : ℝ → ℝ := fun s => Real.sin (Real.pi * s / d)
  -- On `[0, d]`, `g s = θ s • Ψ s y` vanishes at both ends, so it lifts to a continuous `h` of
  -- period `d` which agrees with `g` on `[0, d]`.
  set g : ℝ → X := fun s => θ s • dysonSeriesLeft M s y
  have hg0 : g 0 = 0 := by simp [g, θ]
  have hgd : g d = 0 := by simp [g, θ, mul_div_cancel_right₀ _ hd.ne']
  set h : ℝ → X := fun s => AddCircle.liftIco d 0 g (s : AddCircle d)
  have hh : Continuous h :=
    (AddCircle.liftIco_continuous (p := d) (a := 0) (f := g) (by rw [zero_add, hg0, hgd])
      (Continuous.continuousOn ((by fun_prop : Continuous θ).smul
        ((continuous_dysonSeriesLeft hM).clm_apply continuous_const)))).comp
      (AddCircle.continuous_mk' d)
  have hhg (s : ℝ) (hs : s ∈ Icc 0 d) : h s = g s := by
    rcases hs.2.lt_or_eq with hsd | rfl
    · exact AddCircle.liftIco_coe_apply (by simpa using And.intro hs.1 hsd)
    · rw [hgd, ← hg0]
      simp only [h, AddCircle.coe_period]
      exact AddCircle.liftIco_coe_apply (by simpa using hd)
  -- The twisted map `e • h`, normalized by `c = ∫₀ᵈ e θ > 0`.
  set e := twistWeight d ε
  set c : ℝ := ∫ s in 0..d, e s * θ s
  have hθ (s : ℝ) (hs : s ∈ Ioo 0 d) : 0 < θ s := by
    refine Real.sin_pos_of_pos_of_lt_pi (by have := hs.1; positivity) ?_
    rw [div_lt_iff₀ hd]
    nlinarith [Real.pi_pos, hs.2]
  have hc : 0 < c :=
    intervalIntegral_pos_of_pos_on
      (((continuous_twistWeight d ε).mul (by fun_prop)).intervalIntegrable 0 d)
      (fun s hs => mul_pos (twistWeight_pos hε (hθ s hs)) (hθ s hs)) hd
  refine ⟨c⁻¹ • fun s => e s • h s, Submodule.smul_mem _ _
    ⟨(continuous_twistWeight d ε).smul hh, fun s => ?_⟩, ?_⟩
  · have hper : h (s + d) = h s := by simp only [h, AddCircle.coe_add_period]
    have he : e (s + d) = ε * e s := twistWeight_add hd.ne' hε s
    beta_reduce
    rw [he, hper, mul_smul]
  · have hint : ∫ s in 0..d, dysonSeries (-M) s ((c⁻¹ • fun s => e s • h s) s) =
        ∫ s in 0..d, (c⁻¹ * (e s * θ s)) • y := by
      refine integral_congr fun s hs => ?_
      rw [uIcc_of_le hd.le] at hs
      simp only [Pi.smul_apply, hhg s hs, g, map_smul, ← mul_apply_eq_comp,
        dysonSeries_neg_mul_dysonSeriesLeft hM, one_apply_eq_self, smul_smul]
    rw [hint, intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
      inv_mul_cancel₀ hc.ne', one_smul]

/-- For `d > 0` and `ε = ±1` the endpoint map is surjective. -/
theorem twistedEndpoint_surjective (hM : Continuous M) (hd : 0 < d) (hε : ε ^ 2 = 1) :
    Function.Surjective (twistedEndpoint (X := X) hM d ε) := by
  intro v
  obtain ⟨f, hf, hfy⟩ := exists_mem_twistedContinuous_integral_eq hM hd hε (dysonSeries (-M) d v)
  refine ⟨⟨f, hf⟩, ?_⟩
  rw [twistedEndpoint_apply, hfy, ← mul_apply_eq_comp, dysonSeriesLeft_mul_dysonSeries_neg hM,
    one_apply_eq_self]

end Endpoint

section KernelCokernel

/-- `t ↦ Ψ t x` is twisted by `ε` along `d` when `Ψ(d) x = ε • x`. -/
private theorem dysonSeriesLeft_apply_mem_twistedContDiff (hM : Continuous M)
    (hper : Function.Periodic M d) {x : X}
    (hx : x ∈ LinearMap.ker (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X))) :
    (fun t => dysonSeriesLeft M t x) ∈ twistedContDiff X d ε := by
  have hPx : dysonSeriesLeft M d x = ε • x := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self,
      ContinuousLinearMap.coe_coe, sub_eq_zero] at hx
    exact hx.symm
  have hΨ (t : ℝ) := hasDerivAt_dysonSeriesLeft_apply hM x t
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun t => (hΨ t).differentiableAt, ?_⟩, fun t => ?_⟩
  · rw [funext fun t => (hΨ t).deriv]
    exact hM.clm_apply ((continuous_dysonSeriesLeft hM).clm_apply continuous_const)
  beta_reduce
  rw [dysonSeriesLeft_add_of_periodic hM hper t, mul_apply_eq_comp, hPx, map_smul]

/-- **The kernel of `L` is the kernel of `ε - Ψ(d)`.** Evaluation at `0` is a linear equivalence
from the twisted solutions of `w' = M w` onto the vectors `x` with `Ψ(d) x = ε • x`; the inverse
sends `x` to `t ↦ Ψ t x`. -/
def kerTwistedLinearOperatorEquiv (hM : Continuous M) (hper : Function.Periodic M d) (ε : ℝ) :
    LinearMap.ker (twistedLinearOperator hM hper ε) ≃ₗ[ℝ]
      LinearMap.ker (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) where
  toFun w := ⟨(w.1 : ℝ → X) 0, by
    have hw := (mem_ker_twistedLinearOperator_iff hM hper w.1).1 w.2
    have h := (forall_add_eq_smul_iff_smul_one_sub_apply_eq hM hper continuous_const
      (f := 0) (by simp) (w := w.1) (by simpa using hw)).1 w.1.2.2
    simpa using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨⟨_, dysonSeriesLeft_apply_mem_twistedContDiff hM hper x.2⟩,
    (mem_ker_twistedLinearOperator_iff hM hper _).2 (hasDerivAt_dysonSeriesLeft_apply hM x)⟩
  left_inv w := by
    have hw := (mem_ker_twistedLinearOperator_iff hM hper w.1).1 w.2
    ext t
    exact (eq_dysonSeriesLeft_apply hM hw t).symm
  right_inv x := by
    ext
    simp

@[simp]
theorem kerTwistedLinearOperatorEquiv_apply (hM : Continuous M) (hper : Function.Periodic M d)
    (w : LinearMap.ker (twistedLinearOperator hM hper ε)) :
    (kerTwistedLinearOperatorEquiv hM hper ε w : X) = (w.1 : ℝ → X) 0 :=
  (rfl)

@[simp]
theorem kerTwistedLinearOperatorEquiv_symm_apply (hM : Continuous M)
    (hper : Function.Periodic M d)
    (x : LinearMap.ker (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X))) (t : ℝ) :
    (((kerTwistedLinearOperatorEquiv hM hper ε).symm x).1 : ℝ → X) t = dysonSeriesLeft M t x :=
  (rfl)

/-- The range of `L` is the kernel of the endpoint map followed by the projection onto the
cokernel of `ε - Ψ(d)`. -/
private theorem range_twistedLinearOperator_eq_ker (hM : Continuous M)
    (hper : Function.Periodic M d) :
    LinearMap.range (twistedLinearOperator hM hper ε) =
      LinearMap.ker ((LinearMap.range (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X))).mkQ ∘ₗ
        twistedEndpoint hM d ε) := by
  ext f
  rw [mem_range_twistedLinearOperator_iff, LinearMap.mem_ker, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- **The cokernel of `L` is the cokernel of `ε - Ψ(d)`.** For `d > 0` and `ε = ±1` the endpoint
map induces a linear equivalence from the cokernel of `L = d/dt - M` on maps twisted by `ε` onto
the cokernel of `ε - Ψ(d)`. -/
def quotientRangeTwistedLinearOperatorEquiv (hM : Continuous M) (hper : Function.Periodic M d)
    (hd : 0 < d) (hε : ε ^ 2 = 1) :
    (twistedContinuous X d ε ⧸ LinearMap.range (twistedLinearOperator hM hper ε)) ≃ₗ[ℝ]
      X ⧸ LinearMap.range (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) :=
  (Submodule.quotEquivOfEq _ _ (range_twistedLinearOperator_eq_ker hM hper)).trans
    (LinearMap.quotKerEquivOfSurjective
      ((LinearMap.range (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X))).mkQ ∘ₗ
        twistedEndpoint hM d ε)
      ((Submodule.mkQ_surjective _).comp (twistedEndpoint_surjective hM hd hε)))

@[simp]
theorem quotientRangeTwistedLinearOperatorEquiv_mk (hM : Continuous M)
    (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1) (f : twistedContinuous X d ε) :
    quotientRangeTwistedLinearOperatorEquiv hM hper hd hε (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (twistedEndpoint hM d ε f) :=
  (rfl)

/-- `L` is injective exactly when `ε - Ψ(d)` is. -/
theorem ker_twistedLinearOperator_eq_bot_iff (hM : Continuous M) (hper : Function.Periodic M d) :
    LinearMap.ker (twistedLinearOperator hM hper ε) = ⊥ ↔
      LinearMap.ker (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
    (kerTwistedLinearOperatorEquiv hM hper ε).subsingleton_congr]

/-- For `d > 0` and `ε = ±1`, `L` is surjective exactly when `ε - Ψ(d)` is. -/
theorem range_twistedLinearOperator_eq_top_iff (hM : Continuous M)
    (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1) :
    LinearMap.range (twistedLinearOperator hM hper ε) = ⊤ ↔
      LinearMap.range (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) = ⊤ := by
  rw [← Submodule.Quotient.subsingleton_iff, ← Submodule.Quotient.subsingleton_iff,
    (quotientRangeTwistedLinearOperatorEquiv hM hper hd hε).subsingleton_congr]

end KernelCokernel

section FiniteDimensional

variable [FiniteDimensional ℝ X]

/-- In finite dimension, the kernel of `L = d/dt - M` on maps twisted by `ε` is
finite-dimensional. -/
instance finiteDimensional_ker_twistedLinearOperator (hM : Continuous M)
    (hper : Function.Periodic M d) :
    FiniteDimensional ℝ (LinearMap.ker (twistedLinearOperator hM hper ε)) :=
  (kerTwistedLinearOperatorEquiv hM hper ε).symm.finiteDimensional

/-- In finite dimension, for `d > 0` and `ε = ±1`, the cokernel of `L = d/dt - M` on maps twisted
by `ε` is finite-dimensional. -/
theorem finiteDimensional_quotient_range_twistedLinearOperator (hM : Continuous M)
    (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1) :
    FiniteDimensional ℝ
      (twistedContinuous X d ε ⧸ LinearMap.range (twistedLinearOperator hM hper ε)) :=
  (quotientRangeTwistedLinearOperatorEquiv hM hper hd hε).symm.finiteDimensional

/-- **Index zero.** In finite dimension, for `d > 0` and `ε = ±1`, the kernel and the cokernel of
`L = d/dt - M` on maps twisted by `ε` have the same dimension. -/
theorem finrank_ker_twistedLinearOperator_eq_finrank_quotient_range (hM : Continuous M)
    (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1) :
    Module.finrank ℝ (LinearMap.ker (twistedLinearOperator hM hper ε)) =
      Module.finrank ℝ
        (twistedContinuous X d ε ⧸ LinearMap.range (twistedLinearOperator hM hper ε)) := by
  rw [(kerTwistedLinearOperatorEquiv hM hper ε).finrank_eq,
    (quotientRangeTwistedLinearOperatorEquiv hM hper hd hε).finrank_eq]
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X))
  have h₂ := (LinearMap.range
    (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X))).finrank_quotient_add_finrank
  omega

/-- **Fredholm alternative, injectivity.** In finite dimension, `L` is injective exactly when
`det (ε - Ψ(d)) ≠ 0`. -/
theorem ker_twistedLinearOperator_eq_bot_iff_det_ne_zero (hM : Continuous M)
    (hper : Function.Periodic M d) :
    LinearMap.ker (twistedLinearOperator hM hper ε) = ⊥ ↔
      LinearMap.det (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) ≠ 0 := by
  rw [ker_twistedLinearOperator_eq_bot_iff, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not]

/-- **Fredholm alternative.** In finite dimension, for `d > 0` and `ε = ±1`, the twisted problem
`w' = M w + f` is solvable for every continuous twisted `f` exactly when `det (ε - Ψ(d)) ≠ 0`,
that is, exactly when the twisted problem `w' = M w` has only the zero solution. -/
theorem range_twistedLinearOperator_eq_top_iff_det_ne_zero (hM : Continuous M)
    (hper : Function.Periodic M d) (hd : 0 < d) (hε : ε ^ 2 = 1) :
    LinearMap.range (twistedLinearOperator hM hper ε) = ⊤ ↔
      LinearMap.det (ε • 1 - (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) ≠ 0 := by
  rw [range_twistedLinearOperator_eq_top_iff hM hper hd hε, Ne,
    LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.range_eq_top, LinearMap.ker_eq_bot,
    LinearMap.injective_iff_surjective]

end FiniteDimensional

end TauCeti
