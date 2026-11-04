/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.Submersion

/-!
# Descent of basic forms along submersions

A form `α` on `M` is basic for `f : M → M'` (`TauCeti.RoughForm.IsBasic`) when
`α_x(v) = α_y(w)` whenever `f x = f y` and `df_x vᵢ = df_y wᵢ` for every `i`. When every
derivative of `f` has a continuous right inverse, a basic form is the pullback along `f` of its
descent `TauCeti.RoughForm.descendedForm`, so the basic forms are exactly the pullbacks (see
`TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent`). This file specializes that descent
to submersions, whose derivatives have such right inverses when the source is boundaryless, and
adds regularity.

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

* `TauCeti.SmoothForm.descendedForm hf hsurj α hα`: the descent of a smooth basic form along a
  surjective smooth submersion.

## Main results

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

/-- Descending the pullback of a smooth form `β` along `f` gives back `β`. -/
@[simp]
theorem descendedForm_mpullback (β : SmoothForm I' M' F k) :
    descendedForm hf hsurj (mpullback f hf.contMDiff β)
      (by rw [coe_mpullback]; exact RoughForm.isBasic_mpullback _) = β :=
  (eq_descendedForm_iff.mpr rfl).symm

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
