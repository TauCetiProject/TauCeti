/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
import TauCeti.LinearAlgebra.Multilinear.Quotient

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
* **Basic forms are the invariant horizontal forms.** Let `f` be differentiable and let `σ` be a
  family of differentiable self-maps of `M` over `f` (`f ∘ σ i = f`), transitive on the fibres of
  `f`, such as the action of a group whose orbits are the fibres. A form is basic for `f` exactly
  when it is invariant under every `σ i` and **horizontal**: it vanishes as soon as one argument
  lies in the kernel of the derivative of `f`
  (`TauCeti.RoughForm.isBasic_iff_forall_mpullback_eq_and_apply_eq_zero`). This is the usual
  criterion for a form on the total space of a principal bundle to descend to its base.

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
* `TauCeti.RoughForm.isBasic_iff_forall_mpullback_eq_and_apply_eq_zero`: for a family of maps over
  `f` that is transitive on its fibres, a form is basic exactly when it is invariant and
  horizontal.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (pullbacks of differential forms).
* Victor W. Guillemin and Shlomo Sternberg, *Supersymmetry and Equivariant de Rham Theory*,
  Springer, 1999, Chapter 2 (basic forms as the horizontal invariant forms, and their
  identification with forms on the base of a principal bundle).
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

section Invariant

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A basic form is **horizontal**: it vanishes as soon as one of its arguments lies in the kernel
of the derivative of `f`. -/
theorem IsBasic.apply_eq_zero_of_mfderiv_eq_zero {α : RoughForm I M V k} (hα : IsBasic I' f α)
    {x : M} (v : Fin k → TangentSpace I x) {j : Fin k} (hj : mfderiv I I' f x (v j) = 0) :
    α x v = 0 := by
  classical
  rw [isBasic_iff.mp hα rfl v (update v j 0) fun i ↦ ?_]
  · exact (α x).map_coord_zero j (update_self _ _ _)
  · -- `tangentSpaceCast` is the identity of the model space.
    rcases eq_or_ne i j with rfl | hi
    · simpa using hj
    · rw [update_of_ne hi]
      rfl

/-- A basic form is invariant under every self-map `σ` of `M` over `f` (`f ∘ σ = f`), when `f` and
`σ` are differentiable. -/
theorem IsBasic.mpullback_eq {α : RoughForm I M V k} (hα : IsBasic I' f α)
    (hf : MDifferentiable I I' f) {σ : M → M} (hσ : MDifferentiable I I σ) (hfσ : f ∘ σ = f) :
    mpullback I I σ α = α := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [mpullback_apply]
  refine isBasic_iff.mp hα (congrFun hfσ x) _ v fun i ↦ ?_
  -- By the chain rule, `df_x` factors through the derivative of `σ`.
  have hcomp := mfderiv_comp x (hf (σ x)) (hσ x)
  rw [hfσ] at hcomp
  exact (congrArg (· (v i)) hcomp).symm

/-- At a single point, a horizontal form only depends on the images of its arguments under the
derivative of `f`. -/
private theorem apply_eq_apply_of_horizontal {α : RoughForm I M V k}
    (hhor : ∀ x (v : Fin k → TangentSpace I x) j, mfderiv I I' f x (v j) = 0 → α x v = 0)
    {x : M} {u w : Fin k → TangentSpace I x}
    (huw : ∀ j, mfderiv I I' f x (u j) = mfderiv I I' f x (w j)) : α x u = α x w :=
  (α x).toMultilinearMap.apply_eq_of_mkQ_eq
    (fun _ ↦ LinearMap.ker (mfderiv I I' f x).toLinearMap)
    (fun m i y hy ↦ hhor x _ i (by rwa [update_self])) fun j ↦
      (Submodule.Quotient.eq _).mpr (by simp [huw j])

/-- **Invariant horizontal forms are basic.** Let `f` be differentiable and let `σ` be a family of
differentiable self-maps of `M` over `f` (`f ∘ σ i = f`) that is transitive on the fibres of `f`:
two points with the same image are equal or are related by some `σ i`. A form that is invariant
under every `σ i` and vanishes as soon as one argument lies in the kernel of the derivative of `f`
is basic for `f`. -/
theorem isBasic_of_mpullback_eq {ι : Type*} (hf : MDifferentiable I I' f) {σ : ι → M → M}
    (hσ : ∀ i, MDifferentiable I I (σ i)) (hfσ : ∀ i, f ∘ σ i = f)
    (hσf : ∀ x y, f x = f y → x = y ∨ ∃ i, σ i x = y) {α : RoughForm I M V k}
    (hα : ∀ i, mpullback I I (σ i) α = α)
    (hhor : ∀ x (v : Fin k → TangentSpace I x) j, mfderiv I I' f x (v j) = 0 → α x v = 0) :
    IsBasic I' f α := by
  refine isBasic_iff.mpr fun x y hxy v w hvw ↦ ?_
  -- `tangentSpaceCast` is the identity of the model space.
  rcases hσf x y hxy with rfl | ⟨i, rfl⟩
  · exact apply_eq_apply_of_horizontal hhor hvw
  · rw [← congrFun (hα i) x, mpullback_apply]
    refine apply_eq_apply_of_horizontal hhor fun j ↦ ?_
    -- By the chain rule, `df_x` factors through the derivative of `σ i`.
    have hcomp := mfderiv_comp x (hf (σ i x)) (hσ i x)
    rw [hfσ i] at hcomp
    exact (congrArg (· (v j)) hcomp).symm.trans (hvw j)

/-- **Basic forms are the invariant horizontal forms.** Let `f` be differentiable and let `σ` be a
family of differentiable self-maps of `M` over `f` (`f ∘ σ i = f`) that is transitive on the
fibres of `f`. A form is basic for `f` exactly when it is invariant under every `σ i` and vanishes
as soon as one argument lies in the kernel of the derivative of `f`. -/
theorem isBasic_iff_forall_mpullback_eq_and_apply_eq_zero {ι : Type*}
    (hf : MDifferentiable I I' f) {σ : ι → M → M} (hσ : ∀ i, MDifferentiable I I (σ i))
    (hfσ : ∀ i, f ∘ σ i = f) (hσf : ∀ x y, f x = f y → x = y ∨ ∃ i, σ i x = y)
    {α : RoughForm I M V k} :
    IsBasic I' f α ↔ (∀ i, mpullback I I (σ i) α = α) ∧
      ∀ x (v : Fin k → TangentSpace I x) j, mfderiv I I' f x (v j) = 0 → α x v = 0 :=
  ⟨fun hα ↦ ⟨fun i ↦ hα.mpullback_eq hf (hσ i) (hfσ i),
      fun _ v _ hj ↦ hα.apply_eq_zero_of_mfderiv_eq_zero v hj⟩,
    fun h ↦ isBasic_of_mpullback_eq hf hσ hfσ hσf h.1 h.2⟩

end Invariant

end RoughForm

end TauCeti

