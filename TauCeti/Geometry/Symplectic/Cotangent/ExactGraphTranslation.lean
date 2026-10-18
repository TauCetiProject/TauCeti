/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Exact
public import TauCeti.Geometry.Symplectic.Cotangent.Fiberwise

/-!
# Exact graph translations in a linear cotangent space

For a function `f : V → ℝ`, its differential defines a one-form `df` on `V`
(`TauCeti.differentialOneForm`). Fibre translation by this one-form carries the graph of `df` to
the zero section. More generally, translations by scalar multiples of `df` form a one-parameter
group. Each map has the translation at the opposite parameter as its inverse. At points where the
Hessian exists and is symmetric, the translations preserve the canonical cotangent symplectic
form.

This is the linear cotangent-space model of the exact symplectic isotopy that normalizes an exact
Lagrangian graph to the zero section. It provides the geometric reduction used when comparing the
zero section with an exact graph in cotangent-bundle Floer theory.

## Main declarations

* `TauCeti.cotangentExactGraphTranslation`: fibre translation by a scalar multiple of the
  differential.
* `TauCeti.cotangentExactGraphTranslation_one_differential_graph`: translation at time one carries
  the differential graph to the zero section.
* `TauCeti.strongDualCotangentSymplecticForm_fderiv_cotangentExactGraphTranslation`: where the
  Hessian exists and is symmetric, every translation in the family preserves the canonical
  symplectic form.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

open ContinuousAlternatingMap

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Translation of the cotangent fibres by `t df`. At time zero this is the identity, and at time
one it subtracts `df` from every covector. -/
def cotangentExactGraphTranslation (f : V → ℝ) (t : ℝ) :
    V × StrongDual ℝ V → V × StrongDual ℝ V :=
  cotangentFiberTranslate (t • differentialOneForm f)

/-- Exact graph translation is fibre translation by the one-form `t df`. -/
lemma cotangentExactGraphTranslation_def (f : V → ℝ) (t : ℝ) :
    cotangentExactGraphTranslation f t = cotangentFiberTranslate (t • differentialOneForm f) :=
  (rfl)

/-- Exact graph translation fixes the base point. -/
@[simp]
lemma cotangentExactGraphTranslation_fst (f : V → ℝ) (t : ℝ) (x : V × StrongDual ℝ V) :
    (cotangentExactGraphTranslation f t x).1 = x.1 :=
  cotangentFiberTranslate_fst _ _

/-- Exact graph translation subtracts `t df` from the fibre coordinate. -/
@[simp]
lemma cotangentExactGraphTranslation_snd_apply (f : V → ℝ) (t : ℝ)
    (x : V × StrongDual ℝ V) (v : V) :
    (cotangentExactGraphTranslation f t x).2 v = x.2 v - t * fderiv ℝ f x.1 v := by
  simp [cotangentExactGraphTranslation_def]

/-- Exact graph translation at time zero is the identity. -/
@[simp]
lemma cotangentExactGraphTranslation_zero (f : V → ℝ) :
    cotangentExactGraphTranslation f 0 = id := by
  simp [cotangentExactGraphTranslation_def]

/-- Exact graph translations form a one-parameter group under composition. -/
lemma cotangentExactGraphTranslation_add (f : V → ℝ) (s t : ℝ)
    (x : V × StrongDual ℝ V) :
    cotangentExactGraphTranslation f (s + t) x =
      cotangentExactGraphTranslation f s (cotangentExactGraphTranslation f t x) := by
  simp only [cotangentExactGraphTranslation_def, add_smul, cotangentFiberTranslate_add]

/-- Translation at parameter `-t` is a left inverse to translation at parameter `t`. -/
lemma leftInverse_cotangentExactGraphTranslation_neg (f : V → ℝ) (t : ℝ) :
    Function.LeftInverse (cotangentExactGraphTranslation f (-t))
      (cotangentExactGraphTranslation f t) :=
  fun x ↦ by
    rw [← cotangentExactGraphTranslation_add, neg_add_cancel,
      cotangentExactGraphTranslation_zero, id_eq]

/-- Translation at parameter `-t` is a right inverse to translation at parameter `t`. -/
lemma rightInverse_cotangentExactGraphTranslation_neg (f : V → ℝ) (t : ℝ) :
    Function.RightInverse (cotangentExactGraphTranslation f (-t))
      (cotangentExactGraphTranslation f t) :=
  fun x ↦ by
    rw [← cotangentExactGraphTranslation_add, add_neg_cancel,
      cotangentExactGraphTranslation_zero, id_eq]

/-- Translation at time one carries the graph of `df` to the zero section. -/
@[simp]
lemma cotangentExactGraphTranslation_one_differential_graph (f : V → ℝ) (x : V) :
    cotangentExactGraphTranslation f 1 (x, fderiv ℝ f x) = (x, 0) := by
  ext v
  · simp
  · simp

/-- Translation at time minus one carries the zero section to the graph of `df`. -/
@[simp]
lemma cotangentExactGraphTranslation_neg_one_zeroSection (f : V → ℝ) (x : V) :
    cotangentExactGraphTranslation f (-1) (x, 0) = (x, fderiv ℝ f x) := by
  ext v
  · simp
  · simp

/-- If `f` is `C^n` and `m + 1 ≤ n`, then every exact graph translation is `C^m`. -/
lemma contDiff_cotangentExactGraphTranslation {f : V → ℝ} {m n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (t : ℝ) :
    ContDiff ℝ m (cotangentExactGraphTranslation f t) :=
  contDiff_cotangentFiberTranslate <|
    (contDiff_differentialOneForm hf hmn).const_smul t

/-- The derivative of exact graph translation at time `t`:
`(δq, δp) ↦ (δq, δp - t D²f δq)`. -/
lemma hasFDerivAt_cotangentExactGraphTranslation {f : V → ℝ} {x : V × StrongDual ℝ V}
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x.1) (t : ℝ) :
    HasFDerivAt (cotangentExactGraphTranslation f t)
      ((ContinuousLinearMap.fst ℝ V (StrongDual ℝ V)).prod
        (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V) -
          t • (fderiv ℝ (fderiv ℝ f) x.1).comp (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V))))
      x := by
  have h : cotangentExactGraphTranslation f t = fun y ↦ (y.1, y.2 - t • fderiv ℝ f y.1) := by
    funext y
    ext v <;> simp
  rw [h]
  exact hasFDerivAt_fst.prodMk <| hasFDerivAt_snd.sub <|
    (hdf.hasFDerivAt.comp x hasFDerivAt_fst).const_smul t

/-- The derivative of exact graph translation at time `t` on a tangent vector. -/
lemma fderiv_cotangentExactGraphTranslation {f : V → ℝ} {x : V × StrongDual ℝ V}
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x.1) (t : ℝ) (v : V × StrongDual ℝ V) :
    fderiv ℝ (cotangentExactGraphTranslation f t) x v =
      (v.1, v.2 - t • fderiv ℝ (fderiv ℝ f) x.1 v.1) := by
  simp [(hasFDerivAt_cotangentExactGraphTranslation hdf t).fderiv]

/-- At points where `fderiv ℝ f` is differentiable, translation at time `t` pulls the Liouville
form back to `λ - π^*(t df)`. -/
lemma cotangentLiouvilleForm_cotangentExactGraphTranslation {f : V → ℝ}
    {x : V × StrongDual ℝ V} (hdf : DifferentiableAt ℝ (fderiv ℝ f) x.1) (t : ℝ) :
    (cotangentLiouvilleForm (cotangentExactGraphTranslation f t x)).compContinuousLinearMap
        (fderiv ℝ (cotangentExactGraphTranslation f t) x) =
      cotangentLiouvilleForm x -
        (t • differentialOneForm f x.1).compContinuousLinearMap
          (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V)) := by
  apply cotangentLiouvilleForm_cotangentFiberTranslate
  exact (differentiableAt_differentialOneForm hdf).const_smul t

/-- Wherever the Hessian exists and is symmetric, exact graph translation preserves the
canonical cotangent symplectic form. -/
lemma strongDualCotangentSymplecticForm_fderiv_cotangentExactGraphTranslation
    {f : V → ℝ} {x : V × StrongDual ℝ V}
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x.1) (hf : IsSymmSndFDerivAt ℝ f x.1) (t : ℝ)
    (v w : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm (fderiv ℝ (cotangentExactGraphTranslation f t) x v)
        (fderiv ℝ (cotangentExactGraphTranslation f t) x w) =
      strongDualCotangentSymplecticForm v w := by
  apply strongDualCotangentSymplecticForm_fderiv_cotangentFiberTranslate_of_extDeriv_eq_zero
  · exact (differentiableAt_differentialOneForm hdf).const_smul t
  · rw [extDeriv_smul, extDeriv_differentialOneForm_apply_eq_zero hdf hf]
    exact smul_zero _

end TauCeti

end
