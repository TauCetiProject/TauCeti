/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Signature
import TauCeti.Analysis.Matrix.HermitianSignature.Continuity

/-!
# The Morse index

This file defines the Hessian quadratic form of a real-valued function on a real normed space and,
in finite dimensions, its **Morse index**: the negative index of inertia of the Hessian.  Thus the
index is the maximal dimension of a subspace on which the Hessian is negative-definite.

The Hessian quadratic form used here is

`v ↦ fderiv ℝ (fderiv ℝ f) x v v`.

Some statements of the Morse lemma put a factor `2⁻¹` in front of this form.  That positive factor
does not change its negative index, by
`QuadraticForm.sigNeg_smul_of_pos`.  In particular the convention agrees with the normal
form in `TauCeti.Analysis.Calculus.Morse.NormalForm`.

The definition is made at every point, not only at a critical point, since the index of the
Hessian is meaningful there and this keeps regularity and criticality hypotheses on the results
that use them.  It follows Mathlib's total `sigNeg`, whose value is defined to be zero outside
finite dimensions; all results interpreting the value as a Morse-theoretic index assume finite
dimension.  At a nondegenerate critical point the Hessian quadratic form is nondegenerate, so its
positive and negative indices add to the dimension.  Consequently index zero is equivalent to a
positive-definite Hessian and full index is equivalent to a negative-definite Hessian.

The index depends only on the germ of the function and is invariant under a twice continuously
differentiable change of coordinates with invertible derivative.  Finally, Sylvester's law of
inertia puts the Hessian into a diagonal normal form with weights `±1`; the number of negative
weights is exactly the Morse index.  This supplies the integer grading of critical points needed
by the Morse complex in Lane M of the analytic Heegaard Floer roadmap.

## Main declarations

* `TauCeti.hessianQuadraticForm`: the quadratic form defined by the Hessian at a point.
* `TauCeti.morseIndex`: the negative index of inertia of the Hessian quadratic form.
* `TauCeti.morseIndex_comp`: invariance under a change of coordinates.
* `TauCeti.eventually_morseIndex_le`: in finite dimensions the Morse index of a `C²` function is
  lower semicontinuous, also at degenerate and noncritical points.
* `TauCeti.span_range_hessianQuadraticForm_comp_left`, `TauCeti.span_range_hessianQuadraticForm_pi`,
  `TauCeti.range_hessianQuadraticForm_comp`: the space spanned by the Hessians of the functions
  `ℓ ∘ φ`, for `ℓ` a continuous linear functional, computed from a spanning family of functionals,
  from the components of `φ`, and after composing `φ` at a critical point with a map whose
  differential is injective.
* `TauCeti.IsNondegenerateCriticalPoint.hessianQuadraticForm_nondegenerate`: the Hessian
  quadratic form at a nondegenerate critical point is nondegenerate.
* `TauCeti.isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate`: in finite
  dimensions, the converse.
* `TauCeti.IsNondegenerateCriticalPoint.hessianQuadraticForm_posDef_iff_morseIndex_eq_zero`:
  index zero characterizes a positive-definite Hessian at a nondegenerate critical point.
* `TauCeti.IsNondegenerateCriticalPoint.exists_hessianQuadraticForm_equivalent_weightedSumSquares`:
  the Hessian has a diagonal `±1` normal form.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function Module Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → ℝ} {x : E}

/-- The **Hessian quadratic form** of `f` at `x`, sending `v` to the second derivative of `f` at
`x` evaluated twice on `v`.  The definition uses Mathlib's totalized Fréchet derivative, so no
regularity hypothesis is needed to form it. -/
noncomputable def hessianQuadraticForm (f : E → ℝ) (x : E) : QuadraticForm ℝ E :=
  (fderiv ℝ (fderiv ℝ f) x).toBilinForm.toQuadraticMap

/-- The Hessian quadratic form evaluates the second derivative twice on the same vector. -/
@[simp]
theorem hessianQuadraticForm_apply (f : E → ℝ) (x v : E) :
    hessianQuadraticForm f x v = fderiv ℝ (fderiv ℝ f) x v v := by
  simp only [hessianQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply,
    ContinuousLinearMap.toBilinForm_apply]

/-- The Hessian quadratic form is the quadratic form of the second derivative. -/
theorem hessianQuadraticForm_def (f : E → ℝ) (x : E) :
    hessianQuadraticForm f x = (fderiv ℝ (fderiv ℝ f) x).toBilinForm.toQuadraticMap :=
  (rfl)

/-- For a twice continuously differentiable function, the bilinear form associated to its
Hessian quadratic form is its second derivative. -/
@[simp]
theorem associated_hessianQuadraticForm (hf : ContDiffAt ℝ 2 f x) :
    QuadraticMap.associated (R := ℝ) (hessianQuadraticForm f x) =
      (fderiv ℝ (fderiv ℝ f) x).toBilinForm := by
  let B := (fderiv ℝ (fderiv ℝ f) x).toBilinForm
  have hsymm : B.IsSymm := ⟨hf.isSymmSndFDerivAt (by norm_num)⟩
  simpa only [hessianQuadraticForm, B] using
    QuadraticMap.associated_left_inverse (S := ℝ) hsymm.eq

/-- The Hessian quadratic form depends only on the germ of the function at the point. -/
theorem hessianQuadraticForm_congr_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    hessianQuadraticForm f x = hessianQuadraticForm g x := by
  rw [hessianQuadraticForm, hessianQuadraticForm, hfg.fderiv.fderiv_eq]

/-- The Hessian quadratic form is additive on functions which are `C²` at the point. -/
theorem hessianQuadraticForm_add (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    hessianQuadraticForm (f + g) x = hessianQuadraticForm f x + hessianQuadraticForm g x := by
  ext v
  simpa [iteratedFDeriv_two_apply] using
    congr($(iteratedFDeriv_add_apply (i := 2) hf hg) ![v, v])

/-- Negating a function negates its Hessian quadratic form. -/
@[simp]
theorem hessianQuadraticForm_neg (f : E → ℝ) (x : E) :
    hessianQuadraticForm (-f) x = -hessianQuadraticForm f x := by
  ext v
  have hfd : fderiv ℝ (-f) = -fderiv ℝ f := funext fun _ ↦ fderiv_neg
  simp only [hessianQuadraticForm_apply, neg_apply]
  rw [hfd, fderiv_neg]
  rfl

/-- Scaling a function by a real constant scales its Hessian quadratic form. -/
@[simp]
theorem hessianQuadraticForm_smul (a : ℝ) (f : E → ℝ) (x : E) :
    hessianQuadraticForm (a • f) x = a • hessianQuadraticForm f x := by
  ext v
  simp [fderiv_fderiv_const_smul]

/-- At a critical point the Hessian quadratic form pulls back along the derivative of a `C²`
change of variables. -/
theorem hessianQuadraticForm_comp {φ : F → E} {b : F} (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b) (hcrit : fderiv ℝ f (φ b) = 0) :
    hessianQuadraticForm (f ∘ φ) b =
      (hessianQuadraticForm f (φ b)).comp (fderiv ℝ φ b).toLinearMap := by
  ext v
  simp only [hessianQuadraticForm_apply, QuadraticMap.comp_apply]
  rw [fderiv_fderiv_comp_apply_of_fderiv_eq_zero hf hφ hcrit]
  simp only [ContinuousLinearMap.coe_coe]

/-- The Hessian quadratic form pulls back along a continuous linear map. -/
theorem _root_.ContinuousLinearMap.hessianQuadraticForm_comp (L : F →L[ℝ] E) {b : F}
    (hf : ContDiffAt ℝ 2 f (L b)) :
    hessianQuadraticForm (f ∘ L) b = (hessianQuadraticForm f (L b)).comp L.toLinearMap := by
  ext v
  simp only [hessianQuadraticForm_apply, QuadraticMap.comp_apply]
  have hf1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (L b)) (L b) :=
    ContDiffAt.hasFDerivAt_fderiv hf le_rfl
  have hA : HasFDerivAt (fun y ↦ fderiv ℝ f (L y))
      ((fderiv ℝ (fderiv ℝ f) (L b)).comp L) b := hf1.comp b L.hasFDerivAt
  have hL : HasFDerivAt (fun _ : F ↦ L) 0 b := hasFDerivAt_const (𝕜 := ℝ) L b
  have hev : ∀ᶠ y in 𝓝 b, fderiv ℝ (f ∘ L) y = (fderiv ℝ f (L y)).comp L := by
    have hdiff : ∀ᶠ y in 𝓝 b, DifferentiableAt ℝ f (L y) :=
      L.continuous.continuousAt.eventually
        (((hf.of_le (by norm_num)).eventually (by norm_num)).mono fun _ hy ↦
          hy.differentiableAt one_ne_zero)
    filter_upwards [hdiff] with y hy
    simpa only [L.hasFDerivAt.fderiv] using fderiv_comp (x := y) hy L.differentiableAt
  rw [((hA.clm_comp hL).congr_of_eventuallyEq hev).fderiv]
  simp

/-- The Hessian of `ℓ ∘ φ`, for a continuous linear functional `ℓ`, is `ℓ` applied to the second
derivative of `φ`. -/
theorem _root_.ContinuousLinearMap.hessianQuadraticForm_comp_left_apply (ℓ : F →L[ℝ] ℝ)
    {φ : E → F} (hφ : ContDiffAt ℝ 2 φ x) (v : E) :
    hessianQuadraticForm (ℓ ∘ φ) x v = ℓ (fderiv ℝ (fderiv ℝ φ) x v v) := by
  have hℓ : fderiv ℝ ℓ = fun _ ↦ ℓ := funext fun _ ↦ ℓ.fderiv
  rw [hessianQuadraticForm_apply, fderiv_fderiv_comp_apply ℓ.contDiff.contDiffAt hφ]
  simp [hℓ]

/-- At a critical point `x` of a `C²` map `φ`, the Hessian of `h ∘ φ` only involves the
differential of `h` at `φ x`: it is the Hessian of `Dh(φ x) ∘ φ`. -/
theorem hessianQuadraticForm_comp_eq_fderiv_comp {h : F → ℝ} {φ : E → F}
    (hh : ContDiffAt ℝ 2 h (φ x)) (hφ : ContDiffAt ℝ 2 φ x) (hc : fderiv ℝ φ x = 0) :
    hessianQuadraticForm (h ∘ φ) x = hessianQuadraticForm (fderiv ℝ h (φ x) ∘ φ) x := by
  ext v
  rw [ContinuousLinearMap.hessianQuadraticForm_comp_left_apply _ hφ, hessianQuadraticForm_apply,
    fderiv_fderiv_comp_apply hh hφ, hc]
  simp

/-- At a `C²` point of `φ`, the Hessians of all the functions `ℓ ∘ φ`, for `ℓ` a continuous linear
functional, span the same space as the Hessians of the `L i ∘ φ`, for any family `L` spanning the
functionals. -/
theorem span_range_hessianQuadraticForm_comp_left {ι : Type*} {φ : E → F}
    (hφ : ContDiffAt ℝ 2 φ x) {L : ι → F →L[ℝ] ℝ} (hL : Submodule.span ℝ (range L) = ⊤) :
    Submodule.span ℝ (range fun ℓ : F →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ φ) x) =
      Submodule.span ℝ (range fun i ↦ hessianQuadraticForm (L i ∘ φ) x) := by
  -- `ℓ ↦ Hess (ℓ ∘ φ)` is linear, so it maps the span of `L` onto its range.
  let Λ : (F →L[ℝ] ℝ) →ₗ[ℝ] QuadraticForm ℝ E :=
    { toFun ℓ := hessianQuadraticForm (ℓ ∘ φ) x
      map_add' ℓ₁ ℓ₂ := by
        ext v
        rw [add_apply]
        simp only [ContinuousLinearMap.hessianQuadraticForm_comp_left_apply _ hφ,
          add_apply]
      map_smul' c ℓ := by
        ext v
        rw [smul_apply]
        simp only [ContinuousLinearMap.hessianQuadraticForm_comp_left_apply _ hφ,
          smul_apply, RingHom.id_apply] }
  have hΛ : ⇑Λ = fun ℓ : F →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ φ) x := by
    simp only [Λ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hΛ, ← LinearMap.coe_range, Submodule.span_eq, LinearMap.range_eq_map, ← hL,
    Submodule.map_span, ← range_comp, hΛ, Function.comp_def]

/-- For a `C²` map into `ι → ℝ`, the Hessians of the functions `ℓ ∘ φ` span the same space as the
Hessians of the components of `φ`. -/
theorem span_range_hessianQuadraticForm_pi {ι : Type*} [Fintype ι] {φ : E → ι → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) :
    Submodule.span ℝ (range fun ℓ : (ι → ℝ) →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ φ) x) =
      Submodule.span ℝ (range fun i ↦ hessianQuadraticForm (fun y ↦ φ y i) x) := by
  classical
  refine span_range_hessianQuadraticForm_comp_left hφ
    (L := fun i ↦ ContinuousLinearMap.proj i) (eq_top_iff.2 fun ℓ _ ↦ ?_)
  -- Every functional on `ι → ℝ` is a combination of the coordinate projections.
  have hℓ : ℓ = ∑ i, ℓ (fun j ↦ if i = j then 1 else 0) • ContinuousLinearMap.proj i := by
    ext v
    rw [← ℓ.coe_coe, LinearMap.pi_apply_eq_sum_univ]
    simp [mul_comm]
  rw [hℓ]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- At a critical point of `φ`, the Hessians of the functions `ℓ ∘ g ∘ φ` are the Hessians of the
functions `ℓ ∘ φ`, provided the differential of `g` at `φ x` is injective. -/
theorem range_hessianQuadraticForm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {g : F → G} {φ : E → F} (hg : ContDiffAt ℝ 2 g (φ x))
    (hinj : Function.Injective (fderiv ℝ g (φ x))) (hφ : ContDiffAt ℝ 2 φ x)
    (hc : fderiv ℝ φ x = 0) :
    range (fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ g ∘ φ) x) =
      range fun ℓ : F →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ φ) x := by
  -- The Hessian of `ℓ ∘ g ∘ φ` is that of `(ℓ ∘ Dg) ∘ φ`, and every functional on `F` is of the
  -- form `ℓ ∘ Dg`.
  have hℓ : ∀ ℓ : G →L[ℝ] ℝ, hessianQuadraticForm (ℓ ∘ g ∘ φ) x =
      hessianQuadraticForm ((ℓ.comp (fderiv ℝ g (φ x))) ∘ φ) x := by
    intro ℓ
    rw [← Function.comp_assoc, hessianQuadraticForm_comp_eq_fderiv_comp
      (ℓ.contDiff.contDiffAt.comp _ hg) hφ hc, fderiv_comp _ ℓ.differentiableAt
      (hg.differentiableAt (by norm_num)), ℓ.fderiv]
  simp only [hℓ]
  refine le_antisymm (by rintro _ ⟨ℓ, rfl⟩; exact ⟨_, rfl⟩) ?_
  rintro _ ⟨ℓ, rfl⟩
  obtain ⟨h, hh⟩ := (fderiv ℝ g (φ x) : F →ₗ[ℝ] G).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  have hℓ' : (ℓ.comp (LinearMap.toContinuousLinearMap h)).comp (fderiv ℝ g (φ x)) = ℓ := by
    ext w
    simpa using congr(ℓ ($hh w))
  exact ⟨ℓ.comp (LinearMap.toContinuousLinearMap h), by beta_reduce; rw [hℓ']⟩

/-- The **Morse index** of `f` at `x` is the negative index of inertia of its Hessian quadratic
form.  In finite dimensions it is equivalently the maximal dimension of a subspace on which the
Hessian is negative-definite.  Following Mathlib's `sigNeg`, its value is defined to be zero in
infinite dimensions; the Morse-theoretic results below assume finite dimension. -/
noncomputable def morseIndex (f : E → ℝ) (x : E) : ℕ :=
  sigNeg (hessianQuadraticForm f x)

/-- The Morse index is the negative index of inertia of the Hessian quadratic form. -/
theorem morseIndex_def : morseIndex f x = sigNeg (hessianQuadraticForm f x) := by
  simp [morseIndex]

/-- The Morse index depends only on the germ of the function at the point. -/
theorem morseIndex_congr_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    morseIndex f x = morseIndex g x := by
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_congr_of_eventuallyEq hfg]

/-- The Morse index is invariant under a `C²` change of coordinates with invertible derivative.
Criticality is needed because it removes the first-order term from the second-order chain rule. -/
theorem morseIndex_comp {φ : F → E} {b : F} (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b)
    (hcrit : fderiv ℝ f (φ b) = 0) (hinv : (fderiv ℝ φ b).IsInvertible) :
    morseIndex (f ∘ φ) b = morseIndex f (φ b) := by
  obtain ⟨e, he⟩ := hinv
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_comp hf hφ hcrit, ← he]
  exact (QuadraticMap.Equivalent.sigNeg_eq
    ⟨QuadraticMap.isometryEquivOfCompLinearEquiv
      (hessianQuadraticForm f (φ b)) e.toLinearEquiv⟩).symm

/-- **The Morse index is lower semicontinuous.** In finite dimensions, if `f` is `C²` at `x`, then
at every point near `x` the Morse index of `f` is at least its Morse index at `x`. The point `x`
need not be critical, nor nondegenerate: a degenerate Hessian can acquire new negative directions
under perturbation, but negative directions are never lost. -/
theorem eventually_morseIndex_le [FiniteDimensional ℝ E] (hf : ContDiffAt ℝ 2 f x) :
    ∀ᶠ y in 𝓝 x, morseIndex f x ≤ morseIndex f y := by
  have hc : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  simpa only [morseIndex_def, hessianQuadraticForm_def] using
    ContinuousLinearMap.eventually_sigNeg_toBilinForm_le_of_continuousAt hc

/-- At a nondegenerate critical point, the Hessian quadratic form is nondegenerate. -/
theorem IsNondegenerateCriticalPoint.hessianQuadraticForm_nondegenerate
    (h : IsNondegenerateCriticalPoint f x) : (hessianQuadraticForm f x).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot,
    QuadraticMap.radical_eq_ker_associated, associated_hessianQuadraticForm h.contDiffAt]
  exact LinearMap.separatingLeft_iff_ker_eq_bot.mp h.separatingLeft

/-- In finite dimensions, a nondegenerate critical point is exactly a `C²` critical point whose
Hessian quadratic form is nondegenerate. -/
theorem isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate
    [FiniteDimensional ℝ E] :
    IsNondegenerateCriticalPoint f x ↔
      ContDiffAt ℝ 2 f x ∧ fderiv ℝ f x = 0 ∧ (hessianQuadraticForm f x).Nondegenerate := by
  rw [isNondegenerateCriticalPoint_iff_separatingLeft]
  refine and_congr_right fun hf ↦ and_congr_right fun _ ↦ ?_
  rw [← QuadraticMap.nondegenerate_associated_iff, associated_hessianQuadraticForm hf,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft]
  exact LinearMap.BilinForm.IsSymm.isRefl ⟨hf.isSymmSndFDerivAt (by norm_num)⟩

/-- The Morse index is at most the dimension of the ambient space. -/
theorem morseIndex_le_finrank [FiniteDimensional ℝ E] :
    morseIndex f x ≤ Module.finrank ℝ E := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := hessianQuadraticForm f x)
  rw [morseIndex_def]
  omega

/-- If the Hessian is nondegenerate, the Morse indices of a function and its negation add to the
dimension of the ambient space. -/
theorem morseIndex_neg_add_morseIndex_eq_finrank [FiniteDimensional ℝ E]
    (h : (hessianQuadraticForm f x).Nondegenerate) :
    morseIndex (-f) x + morseIndex f x = Module.finrank ℝ E := by
  simpa only [morseIndex_def, hessianQuadraticForm_neg, sigNeg_neg] using
    QuadraticForm.sigPos_add_sigNeg_of_nondegenerate (hessianQuadraticForm f x) h

/-- At a nondegenerate critical point, the positive index of the Hessian and the Morse index add
to the dimension of the ambient space. -/
theorem IsNondegenerateCriticalPoint.sigPos_hessianQuadraticForm_add_morseIndex_eq_finrank
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    sigPos (hessianQuadraticForm f x) + morseIndex f x = Module.finrank ℝ E := by
  have hsig := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := hessianQuadraticForm f x)
  rw [h.hessianQuadraticForm_nondegenerate.radical_eq_bot, finrank_bot, add_zero] at hsig
  simpa only [morseIndex_def] using hsig

/-- At a nondegenerate critical point, the Morse indices of a function and its negation add to
the dimension of the ambient space. -/
theorem IsNondegenerateCriticalPoint.morseIndex_neg_add_morseIndex_eq_finrank
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    morseIndex (-f) x + morseIndex f x = Module.finrank ℝ E := by
  exact TauCeti.morseIndex_neg_add_morseIndex_eq_finrank h.hessianQuadraticForm_nondegenerate

/-- At a nondegenerate critical point, the Hessian is positive-definite exactly when the Morse
index is zero. -/
theorem IsNondegenerateCriticalPoint.hessianQuadraticForm_posDef_iff_morseIndex_eq_zero
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    (hessianQuadraticForm f x).PosDef ↔ morseIndex f x = 0 := by
  rw [QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot,
    h.hessianQuadraticForm_nondegenerate.radical_eq_bot, morseIndex_def]
  simp only [eq_self, and_true]

/-- At a nondegenerate critical point, the Hessian is negative-definite exactly when the Morse
index is the dimension of the ambient space. -/
theorem IsNondegenerateCriticalPoint.neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    (-hessianQuadraticForm f x).PosDef ↔ morseIndex f x = Module.finrank ℝ E := by
  rw [QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot,
    QuadraticMap.radical_neg, h.hessianQuadraticForm_nondegenerate.radical_eq_bot, sigNeg_neg]
  simp only [eq_self, and_true]
  have hsum := h.sigPos_hessianQuadraticForm_add_morseIndex_eq_finrank
  omega

/-- At a nondegenerate critical point, the Hessian quadratic form has a diagonal normal form with
every weight equal to `-1` or `1`.  The returned equivalence can be passed to
`QuadraticForm.sigNeg_of_equiv_weightedSumSquares` to count the negative weights by the Morse
index, after rewriting with `morseIndex_def`.  This is Sylvester's law of inertia applied to the
Hessian. -/
theorem IsNondegenerateCriticalPoint.exists_hessianQuadraticForm_equivalent_weightedSumSquares
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        QuadraticMap.Equivalent (hessianQuadraticForm f x)
          (QuadraticMap.weightedSumSquares ℝ w) := by
  have hassoc : (QuadraticMap.associated (R := ℝ) (hessianQuadraticForm f x)).SeparatingLeft := by
    rw [associated_hessianQuadraticForm h.contDiffAt]
    exact h.separatingLeft
  exact QuadraticForm.equivalent_one_neg_one_weighted_sum_squared
    (hessianQuadraticForm f x) hassoc

end TauCeti
