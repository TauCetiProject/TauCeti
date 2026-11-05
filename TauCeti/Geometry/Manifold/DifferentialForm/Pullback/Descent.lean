/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic

/-!
# Descent of basic rough forms

Let `f : M → M'` be a map whose derivatives are all surjective. A form `α` on `M` is the
pullback `f^* β` of a form `β` on `M'` only if its value at `x` depends on tangent vectors at `x`
only through their images under `df_x`, and, at two points of one fibre of `f`, gives the same
value on tangent vectors with the same images. Such a form is **basic** for `f`
(`TauCeti.RoughForm.IsBasic`): `α_x(v) = α_y(w)` whenever `f x = f y` and `df_x vᵢ = df_y wᵢ`
for every `i`. Being basic is a pointwise condition, and it is all that descent requires.

* Pullbacks are basic (`TauCeti.RoughForm.isBasic_mpullback`). Conversely, when every derivative of
  `f` has a continuous right inverse, a basic form `α` is the pullback of
  `TauCeti.RoughForm.descendedForm I I' f α` (`TauCeti.RoughForm.IsBasic.mpullback_descendedForm`),
  the form that at `f x` reads `α_x` through a right inverse of `df_x`; on images under `df_x` it
  takes the values of `α_x` (`TauCeti.RoughForm.IsBasic.descendedForm_apply_mfderiv`). So the basic
  forms are exactly the pullbacks (`TauCeti.RoughForm.exists_mpullback_eq_iff_isBasic`).
* When moreover `f` is surjective, pullback along `f` is injective
  (`TauCeti.mpullback_injective_of_surjective`), so the descended form is unique.

No regularity of `f` is assumed here. The descent applies along submersions with boundaryless
source, local diffeomorphisms and orbit projections of properly discontinuous actions, whose
derivatives all have continuous right inverses.

## Main definitions

* `TauCeti.RoughForm.IsBasic I' f α`: the form `α` is basic for `f`.
* `TauCeti.RoughForm.descendedForm I I' f α`: the descent of `α` along `f`, through chosen preimages
  and right inverses of the derivative.

## Main results

* `TauCeti.RoughForm.exists_mpullback_eq_iff_isBasic`: when the derivatives of `f` have continuous
  right inverses, a form is a pullback along `f` exactly when it is basic.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (pullbacks of differential forms).
-/

public section

noncomputable section

open Bundle Set Function Manifold
open scoped Manifold

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  {k : ℕ} {f : M → M'}

namespace TauCeti

namespace RoughForm

section Basic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

variable (I') (f) in
/-- A form `α` on `M` is **basic** for a map `f : M → M'` when its values only depend on the
images of tangent vectors under the derivative of `f`, also across a fibre of `f`: `α_x(v) = α_y(w)`
whenever `f x = f y` and `df_x vᵢ = df_y wᵢ` for every `i`. The tangent spaces at `f x` and `f y`
are both the model space, identified by `tangentSpaceCast`. Pullbacks along `f` are basic, and
when the derivatives of `f` have continuous right inverses the basic forms are exactly the
pullbacks (`TauCeti.RoughForm.exists_mpullback_eq_iff_isBasic`). -/
def IsBasic (α : RoughForm I M V k) : Prop :=
  ∀ ⦃x y : M⦄, f x = f y → ∀ (v : Fin k → TangentSpace I x) (w : Fin k → TangentSpace I y),
    (∀ i, mfderiv I I' f x (v i) = tangentSpaceCast I' (f y) (f x) (mfderiv I I' f y (w i))) →
      α x v = α y w

/-- The defining property of a basic form: `α_x(v) = α_y(w)` whenever `f x = f y` and
`df_x vᵢ = df_y wᵢ` for every `i`. -/
theorem isBasic_iff {α : RoughForm I M V k} :
    IsBasic I' f α ↔ ∀ ⦃x y : M⦄, f x = f y →
      ∀ (v : Fin k → TangentSpace I x) (w : Fin k → TangentSpace I y),
        (∀ i, mfderiv I I' f x (v i) = tangentSpaceCast I' (f y) (f x) (mfderiv I I' f y (w i))) →
          α x v = α y w :=
  Iff.rfl

/-- The pullback of any form along `f` is basic for `f`. -/
@[simp]
theorem isBasic_mpullback (ω : RoughForm I' M' V k) : IsBasic I' f (mpullback I I' f ω) := by
  refine isBasic_iff.mpr fun x y hxy v w hvw ↦ ?_
  simp only [mpullback_apply, hvw]
  exact apply_tangentSpaceCast hxy.symm _

open scoped Classical in
variable (I I') in
/-- The descent of a form `α` on `M` along `f : M → M'`. At a point `y` of the image of `f` it is
`α` at a chosen preimage `x` at which the derivative of `f` has a continuous right inverse `r`,
read through `r`: `v ↦ α_x(r v)`. Elsewhere it is zero. When `α` is basic for `f` and every
derivative of `f` has a continuous right inverse, these choices do not matter, and the descent
pulls back to `α` (`TauCeti.RoughForm.IsBasic.mpullback_descendedForm`). -/
def descendedForm (f : M → M') (α : RoughForm I M V k) : RoughForm I' M' V k := fun y ↦
  if h : ∃ x, f x = y ∧ (mfderiv I I' f x).HasRightInverse then
    (α h.choose).compContinuousLinearMap (h.choose_spec.2.rightInverse ∘L
      (tangentSpaceCast I' y (f h.choose) : TangentSpace I' y →L[ℝ] TangentSpace I' (f h.choose)))
  else 0

/-- **Descent of basic forms.** If every derivative of `f` has a continuous right inverse, a form
that is basic for `f` is the pullback of its descent along `f`. -/
theorem IsBasic.mpullback_descendedForm {α : RoughForm I M V k} (hα : IsBasic I' f α)
    (hf : ∀ x, (mfderiv I I' f x).HasRightInverse) :
    mpullback I I' f (descendedForm I I' f α) = α := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [mpullback_apply, descendedForm]
  split_ifs with h
  swap
  · exact absurd ⟨x, rfl, hf x⟩ h
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  -- The chosen preimage `x'` and `x` lie in one fibre, and the right inverse at `x'` sends
  -- `df_x vᵢ` to a vector with the same image under `df_x'`.
  exact isBasic_iff.mp hα h.choose_spec.1 _ v fun i ↦ h.choose_spec.2.rightInverse_rightInverse _

/-- The descent of a basic form `α` evaluates on images under the derivative of `f` as `α`:
`(descendedForm α)_(f x)(df_x v₁, …, df_x vₖ) = α_x(v₁, …, vₖ)`. -/
theorem IsBasic.descendedForm_apply_mfderiv {α : RoughForm I M V k} (hα : IsBasic I' f α)
    (hf : ∀ x, (mfderiv I I' f x).HasRightInverse) (x : M) (v : Fin k → TangentSpace I x) :
    descendedForm I I' f α (f x) (fun i ↦ mfderiv I I' f x (v i)) = α x v := by
  rw [← mpullback_apply, hα.mpullback_descendedForm hf]

/-- **Basic forms are the pullbacks.** If every derivative of `f` has a continuous right inverse,
for instance for a submersion with boundaryless source, a form on `M` is the pullback of a form on
`M'` exactly when it is basic for `f`. -/
theorem exists_mpullback_eq_iff_isBasic (hf : ∀ x, (mfderiv I I' f x).HasRightInverse)
    {α : RoughForm I M V k} : (∃ ω : RoughForm I' M' V k, mpullback I I' f ω = α) ↔
      IsBasic I' f α :=
  ⟨fun ⟨ω, hω⟩ ↦ hω ▸ isBasic_mpullback ω, fun hα ↦ ⟨_, hα.mpullback_descendedForm hf⟩⟩

end Basic

end RoughForm

end TauCeti

