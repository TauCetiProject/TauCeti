/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

/-!
# Weak derivatives of graphs and block sums in an `Lᵖ` product

Two weakly differentiable fields of continuous linear maps pair through
`ContinuousLinearMap.withLpProdMapL` to a weakly differentiable field of `Lᵖ` block sums
(`TauCeti.HasWeakFDerivOn.withLpProdMap`).

For `u : E → V`, the graph map `x ↦ (x, u x)` into the `Lᵖ` product `WithLp p (E × V)` is the sum
of the inclusion of `E` in the first factor and of `u` followed by the inclusion of `V` in the
second factor (`TauCeti.toLp_prodMk_eq_add`). On a finite-dimensional domain this identifies the
weak derivative of the graph: it is `x ↦ (id, D x)` exactly when `D` is a weak derivative of `u`
(`TauCeti.hasWeakFDerivOn_toLp_prodMk_iff`). This is the first step of Gromov's graph
construction for weak solutions of Cauchy–Riemann equations.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
-/

public noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti

section BlockSum

variable {E E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [CompleteSpace E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [CompleteSpace E₄]
  {μ : Measure E} {Ω : Opens E}

/-- **Weak derivatives of `Lᵖ` block sums.** If two fields of continuous linear maps are weakly
differentiable on `Ω`, so is their pointwise `Lᵖ` block sum `(A x).withLpProdMap p (B x)`. -/
theorem HasWeakFDerivOn.withLpProdMap {A : E → E₁ →L[ℝ] E₂} {B : E → E₃ →L[ℝ] E₄}
    {DA : E → E →L[ℝ] E₁ →L[ℝ] E₂} {DB : E → E →L[ℝ] E₃ →L[ℝ] E₄}
    (hA : HasWeakFDerivOn μ Ω A DA) (p : ENNReal) [Fact (1 ≤ p)] (hB : HasWeakFDerivOn μ Ω B DB) :
    HasWeakFDerivOn μ Ω (fun x => (A x).withLpProdMap p (B x))
      (fun x => (ContinuousLinearMap.withLpProdMapL p ℝ E₁ E₃ E₂ E₄).comp
        ((DA x).prod (DB x))) := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.withLpProdMapL p ℝ E₁ E₃ E₂ E₄)

end BlockSum

variable {p : ENNReal} [Fact (1 ≤ p)] {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [CompleteSpace V]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → V} {D : E → E →L[ℝ] V}

/-- **The weak derivative of a graph.** On a finite-dimensional domain, the graph
`x ↦ (x, u x)` in the `Lᵖ` product has weak derivative `x ↦ (id, D x)` on `Ω` exactly when
`D` is a weak derivative of `u` on `Ω`. -/
theorem hasWeakFDerivOn_toLp_prodMk_iff :
    HasWeakFDerivOn μ Ω (fun x ↦ WithLp.toLp p (x, u x)) (fun x ↦
        (WithLp.prodContinuousLinearEquiv p ℝ E V).symm.toContinuousLinearMap ∘L
          (ContinuousLinearMap.id ℝ E).prod (D x)) ↔
      HasWeakFDerivOn μ Ω u D := by
  set e := (WithLp.prodContinuousLinearEquiv p ℝ E V).symm.toContinuousLinearMap
  constructor
  · intro h
    set L := ContinuousLinearMap.snd ℝ E V ∘L
      (WithLp.prodContinuousLinearEquiv p ℝ E V).toContinuousLinearMap
    have hfun : (fun x ↦ L (WithLp.toLp p (x, u x))) = u := funext fun x ↦ by simp [L]
    have hder : (fun x ↦ L ∘L (e ∘L (ContinuousLinearMap.id ℝ E).prod (D x))) = D :=
      funext fun x ↦ ContinuousLinearMap.ext fun v ↦ by simp [L, e]
    simpa only [hfun, hder] using h.clm_comp L
  · intro h
    have hfd : fderiv ℝ (id : E → E) = fun _ ↦ ContinuousLinearMap.id ℝ E :=
      funext fun _ ↦ fderiv_id
    have hid := hasWeakFDerivOn_of_differentiableOn (μ := μ) (Ω := Ω) (u := (id : E → E))
      (by rw [hfd]; exact locallyIntegrableOn_const _) fun x _ ↦ differentiableAt_id
    rw [hfd] at hid
    have hder : (fun x ↦ e ∘L (ContinuousLinearMap.id ℝ E).prod (D x)) =
        fun x ↦ (e ∘L ContinuousLinearMap.inl ℝ E V) ∘L ContinuousLinearMap.id ℝ E +
          (e ∘L ContinuousLinearMap.inr ℝ E V) ∘L D x :=
      funext fun x ↦ ContinuousLinearMap.ext fun v ↦ by simp [e, WithLp.ext_iff]
    rw [toLp_prodMk_eq_add (𝕜 := ℝ), hder]
    exact (hid.clm_comp (e ∘L ContinuousLinearMap.inl ℝ E V)).add
      (h.clm_comp (e ∘L ContinuousLinearMap.inr ℝ E V))

end TauCeti
