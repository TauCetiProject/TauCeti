/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.Submersion

/-!
# Descent of basic forms along submersions

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

For a submersion with boundaryless source, local sections give the regularity of descended forms.
Near `f x`, a form `ω` is the pullback of `f^* ω` along a local section of `f` through `x`, so
`ω` is `C^m` near `f x` exactly when `f^* ω` is `C^m` near `x`, for a `C^n` submersion with
`m + 1 ≤ n`
(`Manifold.IsSubmersionAt.contMDiffAt_mpullback_form_iff`, an instance of
`TauCeti.contMDiffAt_mpullback_form_iff_of_section`). For a surjective smooth submersion `f`
this gives the smooth descent `TauCeti.SmoothForm.descendedForm`: a smooth basic form `α` on `M` is
the pullback of exactly one smooth form on `M'` (`TauCeti.SmoothForm.mpullback_descendedForm` and
`TauCeti.SmoothForm.eq_descendedForm_iff`). The exterior derivative of a smooth basic form is basic
(`TauCeti.SmoothForm.isBasic_mextDerivₗ`), descent commutes with the exterior derivative, and the
descended form is closed exactly when `α` is.

This is how forms are put on the base of a principal bundle or on the quotient of a free and proper
group action, such as the reduced space of a symplectic reduction: the restriction of the
symplectic form to a level set descends along the orbit projection.

## Main definitions

* `TauCeti.RoughForm.IsBasic I' f α`: the form `α` is basic for `f`.
* `TauCeti.RoughForm.descendedForm I I' f α`: the descent of `α` along `f`, through chosen preimages
  and right inverses of the derivative.
* `TauCeti.SmoothForm.descendedForm hf hsurj α hα`: the descent of a smooth basic form along a
  surjective smooth submersion.

## Main results

* `TauCeti.RoughForm.exists_mpullback_eq_iff_isBasic`: when the derivatives of `f` have continuous
  right inverses, a form is a pullback along `f` exactly when it is basic.
* `Manifold.IsSubmersion.isSmoothForm_mpullback_iff`: along a surjective `C^n` submersion with
  boundaryless source, a form is `C^m`, `m + 1 ≤ n`, exactly when its pullback is.
* `Manifold.IsSubmersion.exists_smoothForm_mpullback_eq_iff`: along a surjective smooth submersion,
  a smooth form is the pullback of a smooth form exactly when it is basic.
* `TauCeti.SmoothForm.eq_descendedForm_iff`: the descended form is the unique smooth form pulling
  back to `α`.
* `TauCeti.SmoothForm.mextDerivₗ_descendedForm`, `TauCeti.SmoothForm.isClosed_descendedForm_iff`:
  descent commutes with the exterior derivative and detects closedness.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Theorem 4.26 (local sections of submersions) and Chapter 14
  (pullbacks of differential forms).
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the reduced form of a symplectic quotient as a descended form).
-/

public section

noncomputable section

open Bundle Set Filter Function Manifold
open scoped Manifold Topology

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {m n : WithTop ℕ∞} {f : M → M'} {x : M}

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

/-- The pullback of any form along `f` is basic for `f`. -/
@[simp]
theorem isBasic_mpullback (ω : RoughForm I' M' V k) : IsBasic I' f (mpullback I I' f ω) := by
  intro x y hxy v w hvw
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
  exact hα h.choose_spec.1 _ v fun i ↦ h.choose_spec.2.rightInverse_rightInverse _

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

open TauCeti

namespace Manifold

variable [IsManifold I 1 M] [IsManifold I' 1 M'] [I.Boundaryless]

/-- For a `C^n` submersion `f` at `x` with boundaryless source and `m + 1 ≤ n`, a form is a `C^m`
section near `f x` exactly when its pullback along `f` is a `C^m` section near `x`. -/
theorem IsSubmersionAt.contMDiffAt_mpullback_form_iff (hf : IsSubmersionAt I I' n f x)
    (hmn : m + 1 ≤ n) {ω : RoughForm I' M' F k} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullback I I' f ω y)) x ↔
      ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) (f x) := by
  -- Near `f x`, the form `ω` is the pullback of `f^* ω` along a local section of `f`.
  obtain ⟨U, hU, hxU, s, hsx, hs, hfs⟩ := hf.exists_contMDiffOn_section
  exact contMDiffAt_mpullback_form_iff_of_section hU hxU hsx hs hfs hf.contMDiffAt hmn

/-- For a surjective `C^n` submersion `f` with boundaryless source and `m + 1 ≤ n`, a form is
`C^m` exactly when its pullback along `f` is. -/
theorem IsSubmersion.isSmoothForm_mpullback_iff (hf : IsSubmersion I I' n f)
    (hsurj : Surjective f) (hmn : m + 1 ≤ n) {ω : RoughForm I' M' F k} :
    IsSmoothForm I m (mpullback I I' f ω) ↔ IsSmoothForm I' m ω := by
  simp only [isSmoothForm_def]
  refine ⟨fun h y ↦ ?_, fun h x ↦
    ((hf.isSubmersionAt x).contMDiffAt_mpullback_form_iff hmn).mpr (h (f x))⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hf.isSubmersionAt x).contMDiffAt_mpullback_form_iff hmn).mp (h x)

open scoped ContDiff

/-- **Descent of smooth forms along a submersion.** Along a surjective smooth submersion with
boundaryless source, a smooth form on `M` is the pullback of a smooth form on `M'` exactly when it
is basic for `f`. -/
theorem IsSubmersion.exists_smoothForm_mpullback_eq_iff (hf : IsSubmersion I I' ∞ f)
    (hsurj : Surjective f) {α : SmoothForm I M F k} :
    (∃ β : SmoothForm I' M' F k, SmoothForm.mpullback f hf.contMDiff β = α) ↔
      RoughForm.IsBasic (V := F) I' f α.1 := by
  simp only [Subtype.ext_iff, SmoothForm.coe_mpullback]
  rw [← RoughForm.exists_mpullback_eq_iff_isBasic (hf.hasRightInverse_mfderiv (by simp))]
  refine ⟨fun ⟨β, hβ⟩ ↦ ⟨β.1, hβ⟩, fun ⟨β, hβ⟩ ↦ ⟨⟨β, ?_⟩, hβ⟩⟩
  -- The descended rough form is smooth because its pullback `α` is.
  exact IsSmoothForm.mem_smoothBundleForms
    ((hf.isSmoothForm_mpullback_iff hsurj (by simp)).mp (hβ ▸ α.isSmoothForm))

omit [I.Boundaryless] in
/-- Along a surjective smooth submersion, a smooth form is closed exactly when its pullback is. -/
theorem IsSubmersion.isClosed_mpullback_iff [IsManifold I 2 M] [IsManifold I' 2 M']
    (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f) {φ : SmoothForm I' M' F k} :
    (SmoothForm.mpullback f hf.contMDiff φ).IsClosed ↔ φ.IsClosed :=
  SmoothForm.isClosed_mpullback_iff_of_surjective hf.contMDiff hsurj
    (hf.surjective_mfderiv (by simp))

end Manifold

namespace TauCeti.SmoothForm

open scoped ContDiff

variable [IsManifold I 1 M] [IsManifold I' 1 M'] [I.Boundaryless]

/-- The descent of a smooth form `α` that is basic for a surjective smooth submersion `f` with
boundaryless source: the unique smooth form on `M'` whose pullback along `f` is `α`
(`TauCeti.SmoothForm.eq_descendedForm_iff`). -/
def descendedForm (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f) (α : SmoothForm I M F k)
    (hα : RoughForm.IsBasic (V := F) I' f α.1) : SmoothForm I' M' F k :=
  ⟨RoughForm.descendedForm (V := F) I I' f α.1, IsSmoothForm.mem_smoothBundleForms <|
    (hf.isSmoothForm_mpullback_iff hsurj (by simp)).mp <| by
      rw [hα.mpullback_descendedForm (hf.hasRightInverse_mfderiv (by simp))]
      exact α.isSmoothForm⟩

variable {hf : IsSubmersion I I' ∞ f} {hsurj : Surjective f} {α : SmoothForm I M F k}
  {hα : RoughForm.IsBasic (V := F) I' f α.1}

/-- The underlying rough form of the smooth descent is the rough descent. -/
@[simp]
theorem coe_descendedForm :
    (descendedForm hf hsurj α hα).1 = RoughForm.descendedForm (V := F) I I' f α.1 := (rfl)

/-- A smooth basic form is the pullback of its descent. -/
@[simp]
theorem mpullback_descendedForm : mpullback f hf.contMDiff (descendedForm hf hsurj α hα) = α :=
  Subtype.ext <| (coe_mpullback _ _ _).trans <|
    hα.mpullback_descendedForm (hf.hasRightInverse_mfderiv (by simp))

/-- The descent of a smooth basic form `α` is the unique smooth form whose pullback is `α`. -/
theorem eq_descendedForm_iff {β : SmoothForm I' M' F k} :
    β = descendedForm hf hsurj α hα ↔ mpullback f hf.contMDiff β = α :=
  ⟨fun h ↦ h ▸ mpullback_descendedForm, fun h ↦
    mpullback_injective_of_surjective hf.contMDiff hsurj (hf.surjective_mfderiv (by simp))
      (h.trans mpullback_descendedForm.symm)⟩

/-- The descent of a smooth basic form evaluates on images under the derivative of `f` as the
form. -/
theorem descendedForm_apply_mfderiv (x : M) (v : Fin k → TangentSpace I x) :
    (descendedForm hf hsurj α hα).1 (f x) (fun i ↦ mfderiv I I' f x (v i)) = α.1 x v :=
  hα.descendedForm_apply_mfderiv (hf.hasRightInverse_mfderiv (by simp)) x v

variable [IsManifold I 2 M] [IsManifold I' 2 M']

/-- The exterior derivative of a smooth form that is basic for a surjective smooth submersion is
basic. -/
theorem isBasic_mextDerivₗ (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f)
    {α : SmoothForm I M F k} (hα : RoughForm.IsBasic (V := F) I' f α.1) :
    RoughForm.IsBasic (V := F) I' f (mextDerivₗ I k α).1 := by
  obtain ⟨β, rfl⟩ := (hf.exists_smoothForm_mpullback_eq_iff hsurj).mpr hα
  rw [mextDerivₗ_mpullback, coe_mpullback]
  exact RoughForm.isBasic_mpullback _

/-- The exterior derivative of the descent of a smooth basic form is the descent of its exterior
derivative. -/
theorem mextDerivₗ_descendedForm :
    mextDerivₗ I' k (descendedForm hf hsurj α hα) =
      descendedForm hf hsurj (mextDerivₗ I k α) (isBasic_mextDerivₗ hf hsurj hα) := by
  rw [eq_descendedForm_iff, ← mextDerivₗ_mpullback, mpullback_descendedForm]

/-- The descent of a smooth basic form is closed exactly when the form is closed. -/
@[simp]
theorem isClosed_descendedForm_iff : (descendedForm hf hsurj α hα).IsClosed ↔ α.IsClosed := by
  rw [← hf.isClosed_mpullback_iff hsurj]
  exact iff_of_eq (congrArg IsClosed mpullback_descendedForm)

end TauCeti.SmoothForm
