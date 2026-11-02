/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Submersion

/-!
# Basic forms and descent along submersions

Let `f : M → M'` be a map of manifolds. A form `α` on `M` is **basic** for `f`
(`TauCeti.RoughForm.IsBasic`) when its value on tangent vectors only depends on the image point
and on the images of the vectors under the derivative of `f`: whenever `f x = f y` and
`df_x vᵢ = df_y wᵢ` for all `i`, then `α_x(v) = α_y(w)`. All tangent spaces of `M'` are its model
space, so the vectors `df_x vᵢ` and `df_y wᵢ` can be compared. A pullback `f^* η` is always basic
(`TauCeti.RoughForm.isBasic_mpullback`).

For a submersion the converse holds. The descent `TauCeti.RoughForm.descendBasic f α` reads `α`
at a chosen preimage `x` of `y` through a chosen continuous right inverse of `df_x`. For a basic
form neither choice matters (`TauCeti.RoughForm.IsBasic.descendBasic_apply`). The derivative of a
submersion has continuous right inverses, so a basic form is the pullback of its descent
(`TauCeti.RoughForm.IsBasic.mpullback_descendBasic`), and a form is a pullback along a submersion
exactly when it is basic (`Manifold.IsSubmersion.exists_mpullback_eq_iff_isBasic`). Since the
derivative is surjective, pullback along a surjective submersion is injective
(`Manifold.IsSubmersion.mpullback_injective`).

Regularity descends as well. Near `f x`, the submersion has a smooth local section `s` through `x`
when the model of `M` has no boundary, and a form `η` is the pullback of `f^* η` along `s`. Hence
`η` is `C^m` near `f x` exactly when `f^* η` is `C^m` near `x`, for a `C^n` submersion with
`m + 1 ≤ n` (`Manifold.IsSubmersionAt.contMDiffAt_mpullback_form_iff`). For a surjective smooth
submersion the descent of a smooth basic form is therefore smooth
(`TauCeti.SmoothForm.descendBasic`); it is the unique smooth form pulling back to the given one
(`TauCeti.SmoothForm.eq_descendBasic_iff`), it commutes with the exterior derivative, and it is
closed exactly when the given form is.

This extends the descent along local diffeomorphisms of
`TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph`, where a form invariant
under a family of maps over `f` transitive on its fibres is basic, to maps with
positive-dimensional fibres such as the quotient map of a free proper group action. The proofs of
regularity and closedness follow those of `IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff` and
`IsLocalDiffeomorph.isClosed_mpullback_iff` there, with a local section of the submersion in place
of a local inverse.

## Main definitions

* `TauCeti.RoughForm.IsBasic`: a form whose values only depend on the derivative of `f`.
* `TauCeti.RoughForm.descendBasic`: the descent of a form along `f`.
* `TauCeti.SmoothForm.descendBasic`: the descent of a smooth basic form along a surjective smooth
  submersion, as a smooth form.

## Main results

* `TauCeti.RoughForm.isBasic_iff`: the defining property of a basic form.
* `TauCeti.RoughForm.isBasic_mpullback`: pullbacks are basic.
* `TauCeti.RoughForm.IsBasic.mpullback_descendBasic`,
  `Manifold.IsSubmersion.mpullback_descendBasic`: a basic form is the pullback of its descent along
  a map whose derivatives have continuous right inverses, in particular along a submersion.
* `Manifold.IsSubmersion.exists_mpullback_eq_iff_isBasic`: a form is a pullback along a submersion
  exactly when it is basic.
* `Manifold.IsSubmersion.mpullback_injective`, `Manifold.IsSubmersion.descendBasic_mpullback`:
  pullback along a surjective submersion is injective, with the descent as left inverse.
* `Manifold.IsSubmersionAt.contMDiffAt_mpullback_form_iff`,
  `Manifold.IsSubmersion.isSmoothForm_mpullback_iff`: regularity of a form and of its pullback
  along a submersion agree.
* `Manifold.IsSubmersion.isClosed_mpullback_iff`: a smooth form is closed exactly when its
  pullback along a surjective smooth submersion is.
* `TauCeti.SmoothForm.eq_descendBasic_iff`: the descent is the unique smooth form pulling back to
  the given form.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Theorem 4.26 (local sections of submersions) and Chapter 14
  (pullbacks of differential forms).
* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Volume I,
  Interscience, 1963, Section II.5 (basic forms on the total space of a principal bundle).
-/

public section

noncomputable section

open Bundle Set Filter Function Manifold
open scoped Manifold Topology ContDiff

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  {k : ℕ} {m n : WithTop ℕ∞} {f : M → M'} {x : M}

namespace TauCeti

namespace RoughForm

section Basic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

variable (I I') in
/-- A form `α` on `M` is **basic** for `f : M → M'` when its values only depend on the derivative
of `f`: evaluations of `α` at two points with the same image agree on tuples of tangent vectors
with the same images under the derivative of `f`. The tangent spaces of `M'` at the two image
points are both the model space, which is how their vectors are compared. -/
def IsBasic (f : M → M') (α : RoughForm I M V k) : Prop :=
  ∀ ⦃x y : M⦄, f x = f y → ∀ (v : Fin k → TangentSpace I x) (w : Fin k → TangentSpace I y),
    (∀ i, mfderiv I I' f x (v i) = mfderiv I I' f y (w i)) → α x v = α y w

/-- The defining property of a basic form. -/
theorem isBasic_iff {α : RoughForm I M V k} :
    α.IsBasic I I' f ↔ ∀ ⦃x y : M⦄, f x = f y →
      ∀ (v : Fin k → TangentSpace I x) (w : Fin k → TangentSpace I y),
        (∀ i, mfderiv I I' f x (v i) = mfderiv I I' f y (w i)) → α x v = α y w :=
  Iff.rfl

/-- A pullback is basic. -/
theorem isBasic_mpullback (f : M → M') (η : RoughForm I' M' V k) :
    (mpullback I I' f η).IsBasic I I' f := by
  intro x y hxy v w hvw
  simp only [mpullback_apply]
  -- Transport along the equality of the image points.
  have key : ∀ (a b : M') (_ : a = b) (p : Fin k → TangentSpace I' a)
      (q : Fin k → TangentSpace I' b), (∀ i, p i = q i) → η a p = η b q := by
    rintro a _ rfl p q hpq
    exact congrArg (η a) (funext hpq)
  exact key _ _ hxy _ _ hvw

open Classical in
variable (I I') in
/-- The descent of a form `α` on `M` along `f : M → M'`. At `y` it is `α` at a chosen point `x`
with `f x = y`, read through a chosen continuous linear right inverse of the derivative of `f` at
`x`; it is `0` where no such choice exists. For a basic form the choices do not matter
(`TauCeti.RoughForm.IsBasic.descendBasic_apply`), and along a submersion a basic form is the
pullback of its descent (`TauCeti.RoughForm.IsBasic.mpullback_descendBasic`). -/
def descendBasic (f : M → M') (α : RoughForm I M V k) : RoughForm I' M' V k := fun y ↦
  if h : ∃ (x : M) (_ : f x = y) (R : TangentSpace I' y →L[ℝ] TangentSpace I x),
      RightInverse R (mfderiv I I' f x) then
    (α h.choose).compContinuousLinearMap h.choose_spec.choose_spec.choose
  else 0

/-- The descent of a basic form at `y` is the form at any point `x` over `y`, read through any
continuous linear right inverse of the derivative of `f` at `x`. -/
theorem IsBasic.descendBasic_apply {α : RoughForm I M V k} (hα : α.IsBasic I I' f) {y : M'}
    (hx : f x = y) {R : TangentSpace I' y →L[ℝ] TangentSpace I x}
    (hR : RightInverse R (mfderiv I I' f x)) :
    descendBasic I I' f α y = (α x).compContinuousLinearMap R := by
  have h : ∃ (x : M) (_ : f x = y) (R : TangentSpace I' y →L[ℝ] TangentSpace I x),
      RightInverse R (mfderiv I I' f x) := ⟨x, hx, R, hR⟩
  rw [descendBasic, dite_eq_left_of_eq_true (eq_true h)]
  have hx' := h.choose_spec.choose
  have hR' := h.choose_spec.choose_spec.choose_spec
  refine ContinuousAlternatingMap.ext fun v ↦ hα (hx'.trans hx.symm) _ _ fun i ↦ ?_
  -- Both right inverses send `v i` to vectors with image `v i` in the model space of `M'`.
  exact (hR' (v i)).trans (hR (v i)).symm

/-- The descent of a basic form, at a point of an open set on which `s` is a section of `f`, is
the pullback of the form along `s`. -/
theorem IsBasic.descendBasic_eq_mpullback {α : RoughForm I M V k} (hα : α.IsBasic I I' f)
    {s : M' → M} {U : Set M'} (hU : IsOpen U) (hfs : EqOn (f ∘ s) id U) {y : M'} (hy : y ∈ U)
    (hs : MDifferentiableAt I' I s y) (hf : MDifferentiableAt I I' f (s y)) :
    descendBasic I I' f α y = mpullback I' I s α y := by
  -- By the chain rule, `df ∘ ds` is the derivative of `f ∘ s`, which is the identity near `y`.
  have hcomp : mfderiv I I' f (s y) ∘L mfderiv I' I s y = ContinuousLinearMap.id ℝ _ :=
    hasMFDerivAt_unique (hf.hasMFDerivAt.comp y hs.hasMFDerivAt)
      ((hasMFDerivAt_id y).congr_of_eventuallyEq_abuse (eventuallyEq_of_mem (hU.mem_nhds hy) hfs))
  have hsy : f (s y) = y := hfs hy
  rw [hα.descendBasic_apply hsy (R := mfderiv I' I s y)
    fun v ↦ congrArg (· v) hcomp]
  exact ContinuousAlternatingMap.ext fun v ↦ (mpullback_apply s α y v).symm

/-- **A basic form is the pullback of its descent** along a map whose derivative has continuous
linear right inverses, such as a submersion. -/
theorem IsBasic.mpullback_descendBasic {α : RoughForm I M V k} (hα : α.IsBasic I I' f)
    (hR : ∀ x, ∃ R : TangentSpace I' (f x) →L[ℝ] TangentSpace I x,
      RightInverse R (mfderiv I I' f x)) :
    mpullback I I' f (descendBasic I I' f α) = α := by
  refine funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨R, hR⟩ := hR x
  rw [mpullback_apply, hα.descendBasic_apply rfl hR]
  exact hα rfl _ _ fun i ↦ hR _

end Basic

end RoughForm

end TauCeti

namespace Manifold

open TauCeti

section Rough

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- Pullback along a surjective `C^n` submersion, `n ≠ 0`, is injective on rough forms. -/
theorem IsSubmersion.mpullback_injective (hf : IsSubmersion I I' n f) (hn : n ≠ 0)
    (hsurj : Surjective f) :
    Injective (mpullback I I' f : RoughForm I' M' V k → RoughForm I M V k) := by
  intro η η h
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  exact (mpullback_apply_eq_mpullback_apply_iff (hf.surjective_mfderiv hn x)).mp (congrFun h x)

/-- A basic form is the pullback of its descent along a `C^n` submersion, `n ≠ 0`. -/
theorem IsSubmersion.mpullback_descendBasic (hf : IsSubmersion I I' n f) (hn : n ≠ 0)
    {α : RoughForm I M V k} (hα : α.IsBasic I I' f) :
    mpullback I I' f (RoughForm.descendBasic I I' f α) = α :=
  hα.mpullback_descendBasic fun x ↦ (hf.isSubmersionAt x).exists_rightInverse_mfderiv hn

/-- Along a surjective `C^n` submersion, `n ≠ 0`, the descent of a pullback `f^* η` is `η`. -/
theorem IsSubmersion.descendBasic_mpullback (hf : IsSubmersion I I' n f) (hn : n ≠ 0)
    (hsurj : Surjective f) (η : RoughForm I' M' V k) :
    RoughForm.descendBasic I I' f (mpullback I I' f η) = η :=
  hf.mpullback_injective hn hsurj
    (hf.mpullback_descendBasic hn (RoughForm.isBasic_mpullback f η))

/-- **Descent of forms along a submersion.** A form is the pullback of a form along a `C^n`
submersion, `n ≠ 0`, exactly when it is basic. -/
theorem IsSubmersion.exists_mpullback_eq_iff_isBasic (hf : IsSubmersion I I' n f) (hn : n ≠ 0)
    {α : RoughForm I M V k} :
    (∃ η : RoughForm I' M' V k, mpullback I I' f η = α) ↔ α.IsBasic I I' f :=
  ⟨fun ⟨η, hη⟩ ↦ hη ▸ RoughForm.isBasic_mpullback f η,
    fun hα ↦ ⟨_, hf.mpullback_descendBasic hn hα⟩⟩

end Rough

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a `C^n` submersion `f` at `x` out of a manifold whose model has no boundary and
`m + 1 ≤ n`, a form is a `C^m` section near `f x` exactly when its pullback along `f` is a `C^m`
section near `x`. -/
theorem IsSubmersionAt.contMDiffAt_mpullback_form_iff [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I' 1 M'] (hf : IsSubmersionAt I I' n f x) (hmn : m + 1 ≤ n)
    {η : RoughForm I' M' F k} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullback I I' f η y)) x ↔
      ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (η y)) (f x) := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd hmn (by simp)
  refine ⟨fun h ↦ ?_, fun h ↦ h.mpullback_form hf.contMDiffAt hmn⟩
  -- Near `f x`, the form `η` is the pullback of `f^* η` along a local section `s` of `f`.
  obtain ⟨s, U, hU, hxU, hsx, hs, hfs⟩ := hf.exists_localSection
  have hsU : ContMDiffAt I' I n s (f x) := hs.contMDiffAt (hU.mem_nhds hxU)
  have hpull := (hsx ▸ h).mpullback_form hsU hmn
  refine hpull.congr_of_eventuallyEq ?_
  -- Near `f x`, the section lands in the domain chart of `f`, where `f` is `C^n`.
  have hsdom : ∀ᶠ y in 𝓝 (f x), s y ∈ hf.domChart.source :=
    hsU.continuousAt.preimage_mem_nhds (by
      rw [hsx]
      exact hf.domChart.open_source.mem_nhds hf.mem_domChart_source)
  filter_upwards [hsdom, hU.mem_nhds hxU] with y hy hyU
  have hsy : MDifferentiableAt I' I s y :=
    (hs.contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt hn
  have hfy : MDifferentiableAt I I' f (s y) :=
    ((hf.contMDiffOn _ hy).contMDiffAt (hf.domChart.open_source.mem_nhds hy)).mdifferentiableAt hn
  have hid : f ∘ s =ᶠ[𝓝 y] id := eventuallyEq_of_mem (hU.mem_nhds hyU) hfs
  rw [← mpullback_comp_at hsy hfy, hid.mpullback_eq, mpullback_id]

/-- For a surjective `C^n` submersion `f` out of a manifold whose model has no boundary and
`m + 1 ≤ n`, a form is `C^m` exactly when its pullback along `f` is. -/
theorem IsSubmersion.isSmoothForm_mpullback_iff [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I' 1 M'] (hf : IsSubmersion I I' n f) (hsurj : Surjective f) (hmn : m + 1 ≤ n)
    {η : RoughForm I' M' F k} :
    IsSmoothForm I m (mpullback I I' f η) ↔ IsSmoothForm I' m η := by
  simp only [isSmoothForm_def]
  refine ⟨fun h y ↦ ?_, fun h x ↦ ((hf.isSubmersionAt x).contMDiffAt_mpullback_form_iff hmn).mpr
    (h (f x))⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hf.isSubmersionAt x).contMDiffAt_mpullback_form_iff hmn).mp (h x)

/-- For a surjective smooth submersion `f`, a smooth form is closed exactly when its pullback
along `f` is. -/
theorem IsSubmersion.isClosed_mpullback_iff [IsManifold I 2 M] [IsManifold I' 2 M']
    (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f) {φ : SmoothForm I' M' F k} :
    (SmoothForm.mpullback f hf.contMDiff φ).IsClosed ↔ φ.IsClosed := by
  rw [SmoothForm.isClosed_def, SmoothForm.isClosed_def, ← mextDerivₗ_apply,
    SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback, mextDerivₗ_apply]
  exact (hf.mpullback_injective (by simp) hsurj).eq_iff' (mpullback_zero f)

/-- **Descent of smooth forms along a surjective submersion.** For a surjective smooth submersion
`f` out of a manifold whose model has no boundary, a smooth form is the pullback of a smooth form
exactly when it is basic. -/
theorem IsSubmersion.exists_smoothForm_mpullback_eq_iff_isBasic [I.Boundaryless]
    [IsManifold I ∞ M] [IsManifold I' ∞ M'] (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f)
    {α : SmoothForm I M F k} :
    (∃ β : SmoothForm I' M' F k, SmoothForm.mpullback f hf.contMDiff β = α) ↔
      RoughForm.IsBasic (V := F) (k := k) I I' f α.1 := by
  simp only [Subtype.ext_iff, SmoothForm.coe_mpullback]
  rw [← hf.exists_mpullback_eq_iff_isBasic (by simp)]
  refine ⟨fun ⟨β, hβ⟩ ↦ ⟨β.1, hβ⟩, fun ⟨β, hβ⟩ ↦ ⟨⟨β, ?_⟩, hβ⟩⟩
  -- The rough form `β` is smooth because its pullback `α` is.
  exact IsSmoothForm.mem_smoothBundleForms
    ((hf.isSmoothForm_mpullback_iff hsurj (by simp)).mp (hβ ▸ α.isSmoothForm))

end Manifold

namespace TauCeti

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I' ∞ M']

/-- The descent of a smooth form `α`, basic for a surjective smooth submersion `f` out of a
manifold whose model has no boundary: the unique smooth form whose pullback along `f` is `α`
(`TauCeti.SmoothForm.eq_descendBasic_iff`). -/
def descendBasic (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f) (α : SmoothForm I M F k)
    (hα : RoughForm.IsBasic (V := F) (k := k) I I' f α.1) : SmoothForm I' M' F k :=
  ⟨RoughForm.descendBasic (V := F) I I' f α.1, IsSmoothForm.mem_smoothBundleForms <|
    (hf.isSmoothForm_mpullback_iff hsurj (by simp)).mp <| by
      rw [hf.mpullback_descendBasic (by simp) hα]
      exact α.isSmoothForm⟩

variable {hf : IsSubmersion I I' ∞ f} {hsurj : Surjective f} {α : SmoothForm I M F k}
  {hα : RoughForm.IsBasic (V := F) (k := k) I I' f α.1}

/-- The underlying rough form of the descent of a smooth basic form is its rough descent. -/
@[simp]
theorem coe_descendBasic :
    (descendBasic hf hsurj α hα).1 = RoughForm.descendBasic (V := F) I I' f α.1 :=
  (rfl)

/-- A smooth basic form is the pullback of its descent. -/
@[simp]
theorem mpullback_descendBasic : mpullback f hf.contMDiff (descendBasic hf hsurj α hα) = α :=
  Subtype.ext <| (coe_mpullback _ _ _).trans <| hf.mpullback_descendBasic (by simp) hα

/-- The descent of a smooth basic form `α` is the unique smooth form whose pullback along the
submersion is `α`. -/
theorem eq_descendBasic_iff {β : SmoothForm I' M' F k} :
    β = descendBasic hf hsurj α hα ↔ mpullback f hf.contMDiff β = α :=
  ⟨fun h ↦ h ▸ mpullback_descendBasic, fun h ↦ Subtype.ext <|
    hf.mpullback_injective (by simp) hsurj <| by
      simpa only [coe_mpullback] using congrArg Subtype.val
        (h.trans (mpullback_descendBasic (hf := hf) (hsurj := hsurj) (hα := hα)).symm)⟩

/-- The exterior derivative of a smooth basic form for a surjective smooth submersion is basic. -/
theorem isBasic_mextDerivₗ (hf : IsSubmersion I I' ∞ f) (hsurj : Surjective f)
    (hα : RoughForm.IsBasic (V := F) (k := k) I I' f α.1) :
    RoughForm.IsBasic (V := F) (k := k + 1) I I' f (mextDerivₗ I k α).1 := by
  rw [← mpullback_descendBasic (hf := hf) (hsurj := hsurj) (hα := hα), mextDerivₗ_mpullback,
    coe_mpullback]
  exact RoughForm.isBasic_mpullback f _

/-- The exterior derivative of the descent of a smooth basic form is the descent of its exterior
derivative. -/
theorem mextDerivₗ_descendBasic :
    mextDerivₗ I' k (descendBasic hf hsurj α hα) =
      descendBasic hf hsurj (mextDerivₗ I k α) (isBasic_mextDerivₗ hf hsurj hα) := by
  rw [eq_descendBasic_iff, ← mextDerivₗ_mpullback, mpullback_descendBasic]

/-- The descent of a smooth basic form is closed exactly when the form is closed. -/
@[simp]
theorem isClosed_descendBasic_iff : (descendBasic hf hsurj α hα).IsClosed ↔ α.IsClosed := by
  rw [← hf.isClosed_mpullback_iff hsurj]
  exact iff_of_eq (congrArg IsClosed mpullback_descendBasic)

end SmoothForm

end TauCeti
