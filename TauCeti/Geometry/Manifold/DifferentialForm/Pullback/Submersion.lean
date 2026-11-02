/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.Submersion.Section

/-!
# Descent of basic forms along submersions

Let `f : M → M'` be a map whose derivative at every point has a continuous linear right inverse,
for instance a `C^n` submersion with `n ≠ 0` (`Manifold.IsSubmersion.hasRightInverse_mfderiv`).
A form `α` on `M` is **basic** for `f` (`TauCeti.RoughForm.IsBasic`) when its value on tangent
vectors only depends on their common image under `f` and the derivative of `f`: whenever
`f x = f y` and `df_x vᵢ = df_y wᵢ` for all `i`, then `α_x v = α_y w`. Pullbacks along `f` are
basic, and conversely every basic form is a pullback
(`TauCeti.RoughForm.exists_mpullback_eq_iff_isBasic`): at `y` its descent reads `α` at a chosen
preimage `x` through a right inverse of `df_x` (`TauCeti.RoughForm.descendAlongSubmersion`).
When `f` is moreover surjective, pullback along `f` is injective
(`TauCeti.mpullback_injective_of_surjective`), so this descended form is unique.

For a surjective smooth submersion of a boundaryless manifold, a form is `C^m` exactly when its
pullback is (`Manifold.IsSubmersion.isSmoothForm_mpullback_iff`): near `f x` a form is the pullback
of its own pullback along a smooth local section of `f`. Hence a smooth basic form descends to a
unique smooth form (`TauCeti.SmoothForm.descendAlongSubmersion`), which is closed exactly when the
original form is. This is how forms are put on quotients by free proper group actions, such as
the reduced spaces of symplectic reduction, where the restriction of the symplectic form to a level
set is basic for the orbit projection. It generalizes descent along local diffeomorphisms
(`IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_iff`), where basicness is invariance under deck
transformations.

## Main definitions

* `TauCeti.RoughForm.IsBasic`: a form on `M` is basic for `f : M → M'`.
* `TauCeti.RoughForm.descendAlongSubmersion`: the descent of a form along `f`, through a choice of
  preimages and of right inverses of the derivative.
* `TauCeti.SmoothForm.descendAlongSubmersion`: the descent of a smooth basic form along a surjective
  smooth submersion, as a smooth form.

## Main results

* `TauCeti.RoughForm.exists_mpullback_eq_iff_isBasic`: a form is a pullback along `f` exactly when
  it is basic.
* `TauCeti.mpullback_injective_of_surjective`: pullback along a surjective map with surjective
  derivatives is injective.
* `Manifold.IsSubmersion.isSmoothForm_mpullback_iff`: a form is `C^m` exactly when its pullback
  along a surjective submersion is.
* `Manifold.IsSubmersion.exists_smoothForm_mpullback_eq_iff`: a smooth form is the pullback of a
  smooth form along a surjective smooth submersion exactly when it is basic.
* `TauCeti.SmoothForm.eq_descendAlongSubmersion_iff`: the descent is the unique smooth form
  pulling back to the given one.
* `Manifold.IsSubmersion.isClosed_mpullback_iff`,
  `TauCeti.SmoothForm.isClosed_descendAlongSubmersion_iff`: closedness is detected after pullback.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (pullbacks of differential forms).
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 23 (descent of the restricted form in symplectic reduction).
-/

public section

noncomputable section

open Bundle Set Filter Function Manifold
open scoped Manifold Topology ContDiff

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {m n : WithTop ℕ∞} {f : M → M'}

namespace TauCeti

/-- Pullback along a surjective map whose derivative is surjective at every point is injective on
rough forms. -/
theorem mpullback_injective_of_surjective {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (hsurj : Surjective f) (hf : ∀ x, Surjective (mfderiv I I' f x)) :
    Injective (mpullback I I' f : RoughForm I' M' V k → RoughForm I M V k) := by
  intro β η h
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  exact (mpullback_apply_eq_mpullback_apply_iff (hf x)).mp (congrFun h x)

namespace RoughForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

variable (I') in
/-- A form `α` on `M` is **basic** for `f : M → M'` when its value on tangent vectors only depends
on their images: if `f x = f y` and `df_x vᵢ = df_y wᵢ` for every `i`, then `α_x v = α_y w`.
Pullbacks along `f` are basic (`TauCeti.RoughForm.isBasic_mpullback`), and when every derivative
of `f` has a continuous right inverse, basic forms are exactly the pullbacks along `f`
(`TauCeti.RoughForm.exists_mpullback_eq_iff_isBasic`). -/
def IsBasic (f : M → M') (α : RoughForm I M V k) : Prop :=
  ∀ ⦃x y : M⦄, f x = f y → ∀ (v : Fin k → TangentSpace I x) (w : Fin k → TangentSpace I y),
    (∀ i, mfderiv I I' f x (v i) = mfderiv I I' f y (w i)) → α x v = α y w

/-- A form is basic for `f` when it takes equal values on tangent vectors over the same point with
equal images under the derivative of `f`. -/
theorem isBasic_iff {α : RoughForm I M V k} :
    α.IsBasic I' f ↔ ∀ ⦃x y : M⦄, f x = f y → ∀ (v : Fin k → TangentSpace I x)
      (w : Fin k → TangentSpace I y),
        (∀ i, mfderiv I I' f x (v i) = mfderiv I I' f y (w i)) → α x v = α y w :=
  Iff.rfl

/-- The pullback of a form along `f` is basic for `f`. -/
theorem isBasic_mpullback (η : RoughForm I' M' V k) : (mpullback I I' f η).IsBasic I' f := by
  intro x y hxy v w hvw
  simp only [mpullback_apply, hvw]
  -- The tangent spaces at `f x` and `f y` are both the model space, so only the base point moves.
  rw [hxy]

variable (I I') in
/-- The descent of a form `α` on `M` along `f : M → M'`, through a choice `s : M' → M` of points and
the continuous right inverses `hf x` of the derivatives of `f`: at `y` it is `α` at `s y`, read
through the right inverse of the derivative of `f` at `s y`. `tangentSpaceCast` only identifies
the tangent spaces at `y` and at `f (s y)`, which are both the model space. When `s` picks
preimages on the image of `f` and `α` is basic for `f`, the descent pulls back to `α`
(`TauCeti.RoughForm.mpullback_descendAlongSubmersion`). -/
def descendAlongSubmersion (f : M → M') (hf : ∀ x, (mfderiv I I' f x).HasRightInverse)
    (s : M' → M) (α : RoughForm I M V k) : RoughForm I' M' V k :=
  fun y ↦ (α (s y)).compContinuousLinearMap ((hf (s y)).rightInverse ∘L
    (tangentSpaceCast I' y (f (s y)) : TangentSpace I' y →L[ℝ] TangentSpace I' (f (s y))))

/-- Evaluation of the descent of a form along `f`: tangent vectors at `y` are sent through the
right inverse of the derivative of `f` at the chosen point `s y`. -/
theorem descendAlongSubmersion_apply (hf : ∀ x, (mfderiv I I' f x).HasRightInverse) (s : M' → M)
    (α : RoughForm I M V k) (y : M') (v : Fin k → TangentSpace I' y) :
    descendAlongSubmersion I I' f hf s α y v =
      α (s y) fun i ↦ (hf (s y)).rightInverse (tangentSpaceCast I' y (f (s y)) (v i)) :=
  (rfl)

/-- A form which is basic for `f` is the pullback of its descent along `f`, through any choice `s`
of preimages of the points of the image of `f`. -/
theorem mpullback_descendAlongSubmersion (hf : ∀ x, (mfderiv I I' f x).HasRightInverse)
    {s : M' → M} (hs : ∀ x, f (s (f x)) = f x) {α : RoughForm I M V k} (hα : α.IsBasic I' f) :
    mpullback I I' f (descendAlongSubmersion I I' f hf s α) = α := by
  refine funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [mpullback_apply, descendAlongSubmersion_apply]
  -- The lifted vectors at `s (f x)` have the same images as `v` under the derivative of `f`.
  exact hα (hs x) _ v fun i ↦ (hf (s (f x))).rightInverse_rightInverse _

/-- **Basic forms are pullbacks.** When the derivative of `f` has a continuous right inverse at
every point, a form on `M` is the pullback of a form on `M'` exactly when it is basic for `f`. -/
theorem exists_mpullback_eq_iff_isBasic (hf : ∀ x, (mfderiv I I' f x).HasRightInverse)
    {α : RoughForm I M V k} :
    (∃ β : RoughForm I' M' V k, mpullback I I' f β = α) ↔ α.IsBasic I' f := by
  refine ⟨fun ⟨β, hβ⟩ ↦ hβ ▸ isBasic_mpullback β, fun hα ↦ ?_⟩
  -- Descend along a choice of preimages; on an empty source every form is a pullback.
  cases isEmpty_or_nonempty M
  · exact ⟨0, funext fun x ↦ isEmptyElim x⟩
  · exact ⟨_, mpullback_descendAlongSubmersion hf (fun x ↦ invFun_eq ⟨x, rfl⟩) hα⟩

end RoughForm

end TauCeti

open TauCeti

namespace Manifold.IsSubmersion

/-- Pullback along a surjective `C^n` submersion, `n ≠ 0`, is injective on rough forms. -/
theorem mpullback_injective {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (hf : IsSubmersion I I' n f) (hn : n ≠ 0) (hsurj : Surjective f) :
    Injective (mpullback I I' f : RoughForm I' M' V k → RoughForm I M V k) :=
  mpullback_injective_of_surjective hsurj fun x ↦ (hf.hasRightInverse_mfderiv hn x).surjective

variable [I.Boundaryless] [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold I n M]
  [IsManifold I' n M']

/-- For a `C^n` submersion `f` of a boundaryless manifold and `m + 1 ≤ n`, a form is a `C^m`
section near `f x` exactly when its pullback along `f` is a `C^m` section near `x`. -/
theorem contMDiffAt_mpullback_form_iff (hf : IsSubmersion I I' n f) (hmn : m + 1 ≤ n) (x : M)
    {η : RoughForm I' M' F k} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullback I I' f η y)) x ↔
      ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (η y)) (f x) := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd hmn (by simp)
  refine ⟨fun h ↦ ?_, fun h ↦ h.mpullback_form (hf.contMDiff x) hmn⟩
  -- Near `f x`, the form `η` is the pullback of `f^* η` along a local section `s` of `f`.
  obtain ⟨U, s, hU, hfxU, hsx, hs, hsf⟩ := (hf.isSubmersionAt x).exists_contMDiffOn_rightInvOn
  have hpull := (hsx ▸ h).mpullback_form (hs.contMDiffAt (hU.mem_nhds hfxU)) hmn
  refine hpull.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hfxU] with y hy
  have hsy : MDifferentiableAt I' I s y :=
    (hs.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt hn
  have hid : f ∘ s =ᶠ[𝓝 y] id := eventuallyEq_of_mem (hU.mem_nhds hy) hsf
  rw [← mpullback_comp_at hsy ((hf.contMDiff (s y)).mdifferentiableAt hn), hid.mpullback_eq,
    mpullback_id]

/-- For a surjective `C^n` submersion `f` of a boundaryless manifold and `m + 1 ≤ n`, a form is
`C^m` exactly when its pullback along `f` is. -/
theorem isSmoothForm_mpullback_iff (hf : IsSubmersion I I' n f) (hsurj : Surjective f)
    (hmn : m + 1 ≤ n) {η : RoughForm I' M' F k} :
    IsSmoothForm I m (mpullback I I' f η) ↔ IsSmoothForm I' m η := by
  simp only [isSmoothForm_def]
  refine ⟨fun h y ↦ ?_, fun h x ↦ (hf.contMDiffAt_mpullback_form_iff hmn x).mpr (h (f x))⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact (hf.contMDiffAt_mpullback_form_iff hmn x).mp (h x)

end Manifold.IsSubmersion

namespace TauCeti.SmoothForm

variable [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I' ∞ M']

/-- The descent of a smooth form `α`, basic for a surjective smooth submersion `f` of a
boundaryless manifold, along `f`: the unique smooth form whose pullback along `f` is `α`
(`TauCeti.SmoothForm.eq_descendAlongSubmersion_iff`). -/
def descendAlongSubmersion (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f)
    (α : SmoothForm I M F k) (hα : RoughForm.IsBasic (V := F) I' f α.1) : SmoothForm I' M' F k :=
  ⟨RoughForm.descendAlongSubmersion (V := F) I I' f (hf.hasRightInverse_mfderiv (by simp))
      (surjInv hsurj) α.1,
    IsSmoothForm.mem_smoothBundleForms <| (hf.isSmoothForm_mpullback_iff (m := ∞) hsurj
      (by simp)).mp <| by
      rw [RoughForm.mpullback_descendAlongSubmersion (hf.hasRightInverse_mfderiv (by simp))
      (fun x ↦ surjInv_eq hsurj (f x)) hα]
      exact α.isSmoothForm⟩

variable {hf : IsSubmersion I I' ∞ f} {hsurj : Surjective f} {α : SmoothForm I M F k}
  {hα : RoughForm.IsBasic (V := F) I' f α.1}

/-- The underlying rough form of the descent of a smooth form is its rough descent. -/
@[simp]
theorem coe_descendAlongSubmersion :
    (descendAlongSubmersion hf hsurj α hα).1 =
      RoughForm.descendAlongSubmersion (V := F) I I' f (hf.hasRightInverse_mfderiv (by simp))
        (surjInv hsurj) α.1 :=
  (rfl)

/-- A smooth basic form is the pullback of its descent along the submersion. -/
@[simp]
theorem mpullback_descendAlongSubmersion :
    mpullback f hf.contMDiff (descendAlongSubmersion hf hsurj α hα) = α :=
  Subtype.ext <| (coe_mpullback _ _ _).trans <|
    RoughForm.mpullback_descendAlongSubmersion (hf.hasRightInverse_mfderiv (by simp))
      (fun x ↦ surjInv_eq hsurj (f x)) hα

/-- The descent of a smooth basic form `α` is the unique smooth form whose pullback along the
submersion is `α`. -/
theorem eq_descendAlongSubmersion_iff {β : SmoothForm I' M' F k} :
    β = descendAlongSubmersion hf hsurj α hα ↔ mpullback f hf.contMDiff β = α :=
  ⟨fun h ↦ h ▸ mpullback_descendAlongSubmersion, fun h ↦ Subtype.ext <|
    hf.mpullback_injective (by simp) hsurj <| by
      simpa only [coe_mpullback] using
        congrArg Subtype.val
          (h.trans (mpullback_descendAlongSubmersion (hf := hf) (hsurj := hsurj) (hα := hα)).symm)⟩

end TauCeti.SmoothForm

namespace Manifold.IsSubmersion

variable [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I' ∞ M']

/-- **Descent of smooth forms along a submersion.** For a surjective smooth submersion `f` of a
boundaryless manifold, a smooth form on `M` is the pullback of a smooth form on `M'` exactly when
it is basic for `f`. The smooth form is then unique
(`TauCeti.SmoothForm.eq_descendAlongSubmersion_iff`). -/
theorem exists_smoothForm_mpullback_eq_iff (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f)
    {α : SmoothForm I M F k} :
    (∃ β : SmoothForm I' M' F k, SmoothForm.mpullback f hf.contMDiff β = α) ↔
      RoughForm.IsBasic (V := F) I' f α.1 := by
  refine ⟨fun ⟨β, hβ⟩ ↦ ?_, fun hα ↦
    ⟨_, SmoothForm.mpullback_descendAlongSubmersion (hf := hf) (hsurj := hsurj) (hα := hα)⟩⟩
  rw [← hβ, SmoothForm.coe_mpullback f hf.contMDiff β]
  exact RoughForm.isBasic_mpullback (I := I) (f := f) _

omit [I.Boundaryless] in
/-- For a surjective smooth submersion `f`, a smooth form is closed exactly when its pullback
along `f` is. -/
theorem isClosed_mpullback_iff (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f)
    {φ : SmoothForm I' M' F k} : (SmoothForm.mpullback f hf.contMDiff φ).IsClosed ↔ φ.IsClosed := by
  rw [SmoothForm.isClosed_def, SmoothForm.isClosed_def, ← mextDerivₗ_apply,
    SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback, mextDerivₗ_apply]
  exact (hf.mpullback_injective (by simp) hsurj).eq_iff' (mpullback_zero f)

end Manifold.IsSubmersion

namespace TauCeti.SmoothForm

variable [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I' ∞ M']
  {hf : IsSubmersion I I' ∞ f} {hsurj : Surjective f} {α : SmoothForm I M F k}
  {hα : RoughForm.IsBasic (V := F) I' f α.1}

/-- The descent of a smooth basic form is closed exactly when the form is closed. -/
@[simp]
theorem isClosed_descendAlongSubmersion_iff :
    (descendAlongSubmersion hf hsurj α hα).IsClosed ↔ α.IsClosed := by
  rw [← hf.isClosed_mpullback_iff hsurj, mpullback_descendAlongSubmersion]

end TauCeti.SmoothForm
