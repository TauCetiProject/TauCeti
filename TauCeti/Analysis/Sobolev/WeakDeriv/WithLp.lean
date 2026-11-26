/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

/-!
# Weak derivatives of graphs

For `u : E → V` on a finite-dimensional domain and an identification `e` of `E × V` with a Banach
space, the graph `x ↦ e (x, u x)` has weak derivative `x ↦ e ∘ (id, D x)` exactly when `D` is a
weak derivative of `u` (`TauCeti.hasWeakFDerivOn_graph_iff`). For the `Lᵖ` product
`WithLp p (E × V)` this reads: the graph `x ↦ (x, u x)` has weak derivative `x ↦ (id, D x)`
(`TauCeti.hasWeakFDerivOn_toLp_prodMk_iff`). This is the first step of Gromov's graph construction
for weak solutions of Cauchy–Riemann equations.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
-/

public noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti

variable {p : ENNReal} [Fact (1 ≤ p)] {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [CompleteSpace V]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → V} {D : E → E →L[ℝ] V}

/-- **The weak derivative of a graph.** On a finite-dimensional domain and for any identification
`e` of `E × V` with a Banach space `W`, the graph `x ↦ e (x, u x)` has weak derivative
`x ↦ e ∘ (id, D x)` on `Ω` exactly when `D` is a weak derivative of `u` on `Ω`. -/
theorem hasWeakFDerivOn_graph_iff {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] (e : (E × V) ≃L[ℝ] W) :
    HasWeakFDerivOn μ Ω (fun x ↦ e (x, u x)) (fun x ↦
        e.toContinuousLinearMap ∘L (ContinuousLinearMap.id ℝ E).prod (D x)) ↔
      HasWeakFDerivOn μ Ω u D := by
  constructor
  · intro h
    set L := ContinuousLinearMap.snd ℝ E V ∘L e.symm.toContinuousLinearMap
    have hfun : (fun x ↦ L (e (x, u x))) = u := funext fun x ↦ by simp [L]
    have hder : (fun x ↦ L ∘L (e.toContinuousLinearMap ∘L
        (ContinuousLinearMap.id ℝ E).prod (D x))) = D :=
      funext fun x ↦ ContinuousLinearMap.ext fun v ↦ by simp [L]
    simpa only [hfun, hder] using h.clm_comp L
  · intro h
    have hfd : fderiv ℝ (id : E → E) = fun _ ↦ ContinuousLinearMap.id ℝ E :=
      funext fun _ ↦ fderiv_id
    have hid := hasWeakFDerivOn_of_differentiableOn (μ := μ) (Ω := Ω) (u := (id : E → E))
      (by rw [hfd]; exact locallyIntegrableOn_const _) fun x _ ↦ differentiableAt_id
    rw [hfd] at hid
    exact (hid.prodMk h).clm_comp e.toContinuousLinearMap

/-- **The weak derivative of a graph in an `Lᵖ` product.** On a finite-dimensional domain, the
graph `x ↦ (x, u x)` in the `Lᵖ` product has weak derivative `x ↦ (id, D x)` on `Ω` exactly when
`D` is a weak derivative of `u` on `Ω`. -/
theorem hasWeakFDerivOn_toLp_prodMk_iff :
    HasWeakFDerivOn μ Ω (fun x ↦ WithLp.toLp p (x, u x)) (fun x ↦
        (WithLp.prodContinuousLinearEquiv p ℝ E V).symm.toContinuousLinearMap ∘L
          (ContinuousLinearMap.id ℝ E).prod (D x)) ↔
      HasWeakFDerivOn μ Ω u D := by
  simpa only [WithLp.prodContinuousLinearEquiv_symm_apply] using
    hasWeakFDerivOn_graph_iff (μ := μ) (Ω := Ω) (u := u) (D := D)
      (WithLp.prodContinuousLinearEquiv p ℝ E V).symm

end TauCeti
