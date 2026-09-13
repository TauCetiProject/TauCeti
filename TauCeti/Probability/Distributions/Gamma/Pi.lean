/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.Distributions.Gamma.Sum

/-!
# Finite products of Gamma distributions

This file collects what a finite product of Gamma measures looks like from the outside: the
almost-sure positivity of its coordinates, and the laws of the partial sums of those
coordinates.

The coordinatewise positivity holds for arbitrary shape and rate vectors because
`ae_pos_gammaMeasure` is parameter-independent, and every Gamma measure is sigma-finite.  For a
nonempty index type, coordinatewise positivity makes the coordinate sum positive.

At a common rate the Gamma family is closed under convolution, so the total of the coordinates
of a Gamma product is again Gamma, with the total shape.  Summing instead over the fibres of a
map `f` between finite index types leaves a Gamma product on the target type, whose shapes are
the fibre sums of the original shapes; the fibres are independent, so no correlation survives
the aggregation.  Both facts feed the normalized-Gamma construction of the Dirichlet
distribution, whose denominator is the total and whose aggregation law is the fibre-sum
statement.

## Main results

* `TauCeti.ae_pos_pi_gammaMeasure` gives coordinatewise positivity in a finite Gamma product.
* `TauCeti.ae_pos_sum_pi_gammaMeasure` gives positivity of the coordinate sum for a nonempty
  finite Gamma product.
* `TauCeti.map_sum_pi_gammaMeasure` identifies the law of the total of the coordinates.
* `TauCeti.map_funOnFinite_map_pi_gammaMeasure` identifies the joint law of the fibre sums of
  the coordinates along a surjection of index types.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Every coordinate in a finite product of Gamma measures is almost everywhere strictly
positive. -/
theorem ae_pos_pi_gammaMeasure (a r : ι → ℝ) :
    ∀ᵐ x ∂Measure.pi (fun i ↦ gammaMeasure (a i) (r i)), ∀ i, 0 < x i := by
  exact ae_all_iff.mpr fun i ↦
    Measure.tendsto_eval_ae_ae.eventually (ae_pos_gammaMeasure (a i) (r i))

/-- The coordinate sum in a nonempty finite product of Gamma measures is almost everywhere
strictly positive. -/
theorem ae_pos_sum_pi_gammaMeasure [Nonempty ι] (a r : ι → ℝ) :
    ∀ᵐ x ∂Measure.pi (fun i ↦ gammaMeasure (a i) (r i)), 0 < ∑ i, x i := by
  filter_upwards [ae_pos_pi_gammaMeasure a r] with x hx
  exact Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty

/-! ### The law of the coordinate sum -/

/-- The total of the coordinates of a nonempty finite product of Gamma measures at a common
positive rate is Gamma distributed, with the total of the shapes. -/
theorem map_sum_pi_gammaMeasure [Nonempty ι] {a : ι → ℝ} {r : ℝ} (ha : ∀ i, 0 < a i)
    (hr : 0 < r) :
    (Measure.pi fun i ↦ gammaMeasure (a i) r).map (fun x ↦ ∑ i, x i) =
      gammaMeasure (∑ i, a i) r := by
  let _ (i : ι) : IsProbabilityMeasure (gammaMeasure (a i) r) :=
    isProbabilityMeasure_gammaMeasure (ha i) hr
  exact (iIndepFun.hasLaw_sum_gammaMeasure (s := Finset.univ)
    (iIndepFun_pi (X := fun _ ↦ (id : ℝ → ℝ)) fun _ ↦ aemeasurable_id) hr Finset.univ_nonempty
    (fun i _ ↦ ha i)
    fun i _ ↦ ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩).map_eq

/-! ### The joint law of the fibre sums -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Summing the coordinates of a finite product of Gamma measures over the fibres of a surjection
`f` gives the product of Gamma measures on the target index type whose shapes are the fibre sums
of the original shapes.  Here `FunOnFinite.map f` is the fibre-sum map `(ι → ℝ) → (κ → ℝ)`. -/
theorem map_funOnFinite_map_pi_gammaMeasure {f : ι → κ} (hf : Function.Surjective f)
    {a : ι → ℝ} {r : ℝ} (ha : ∀ i, 0 < a i) (hr : 0 < r) :
    (Measure.pi fun i ↦ gammaMeasure (a i) r).map (FunOnFinite.map f) =
      Measure.pi fun j ↦ gammaMeasure (∑ i with f i = j, a i) r := by
  let _ (i : ι) : IsProbabilityMeasure (gammaMeasure (a i) r) :=
    isProbabilityMeasure_gammaMeasure (ha i) hr
  have hfib (j : κ) : Nonempty {i // f i = j} := (hf j).elim fun i hi ↦ ⟨⟨i, hi⟩⟩
  have hsub (g : ι → ℝ) (j : κ) : ∑ i : {i // f i = j}, g i = ∑ i with f i = j, g i :=
    (Finset.sum_subtype _ (by simp) g).symm
  -- Read the coordinates of the product along the fibre decomposition of `ι`.
  have h₁ : MeasurePreserving
      (fun (x : ι → ℝ) (p : (j : κ) × {i // f i = j}) ↦ x p.2)
      (Measure.pi fun i ↦ gammaMeasure (a i) r)
      (Measure.pi fun p : (j : κ) × {i // f i = j} ↦ gammaMeasure (a p.2) r) := by
    have h := (measurePreserving_piCongrLeft (fun i : ι ↦ gammaMeasure (a i) r)
      (Equiv.sigmaFiberEquiv f)).symm
      (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) (Equiv.sigmaFiberEquiv f))
    have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) (Equiv.sigmaFiberEquiv f)).symm =
        fun (x : ι → ℝ) (p : (j : κ) × {i // f i = j}) ↦ x p.2 := by
      funext x p
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply, Equiv.sigmaFiberEquiv]
    rw [hfun] at h
    exact h
  -- Group those coordinates by fibre.
  have h₂ : MeasurePreserving
      (Sigma.curry (γ := fun (j : κ) (_ : {i // f i = j}) ↦ ℝ))
      (Measure.pi fun p : (j : κ) × {i // f i = j} ↦ gammaMeasure (a p.2) r)
      (Measure.pi fun j ↦ Measure.pi fun i : {i // f i = j} ↦ gammaMeasure (a i) r) := by
    refine ⟨(MeasurableEquiv.piCurry fun (j : κ) (_ : {i // f i = j}) ↦ ℝ).measurable, ?_⟩
    have h := Measure.infinitePi_map_piCurry
      (X := fun (j : κ) (_ : {i // f i = j}) ↦ ℝ)
      (μ := fun (j : κ) (i : {i // f i = j}) ↦ gammaMeasure (a i) r)
    simpa only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_piCurry] using h
  -- Add up the coordinates inside each fibre.
  have hfactor (j : κ) : MeasurePreserving (fun y : {i // f i = j} → ℝ ↦ ∑ i, y i)
      (Measure.pi fun i : {i // f i = j} ↦ gammaMeasure (a i) r)
      (gammaMeasure (∑ i with f i = j, a i) r) := by
    have := hfib j
    refine ⟨by fun_prop, ?_⟩
    rw [map_sum_pi_gammaMeasure (fun i : {i // f i = j} ↦ ha i.1) hr, hsub]
  have hcomp : ((fun (y : (j : κ) → {i // f i = j} → ℝ) (j : κ) ↦ ∑ i, y j i) ∘
      Sigma.curry) ∘ (fun (x : ι → ℝ) (p : (j : κ) × {i // f i = j}) ↦ x p.2) =
      FunOnFinite.map (M := ℝ) f := by
    funext x j
    simp [FunOnFinite.map_apply_apply, Sigma.curry, hsub]
  have hmp := ((measurePreserving_pi _ _ hfactor).comp h₂).comp h₁
  rw [hcomp] at hmp
  exact hmp.map_eq

end TauCeti
