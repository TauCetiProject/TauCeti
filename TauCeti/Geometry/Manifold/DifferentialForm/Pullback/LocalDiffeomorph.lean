/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Pullback of forms along local diffeomorphisms

Pullback along a map `f` only sees the value of a form at `f x` through the derivative of `f`
at `x`. When that derivative is surjective, the pullback at `x` therefore determines the form at
`f x` (`TauCeti.mpullback_apply_eq_mpullback_apply_iff`), so pullback along a surjective local
diffeomorphism is injective (`IsLocalDiffeomorph.mpullback_injective`).

Regularity transfers in both directions as well. Near `f x`, a form `ω` is the pullback of
`f^* ω` along a local inverse of `f`, so `ω` is `C^m` near `f x` exactly when `f^* ω` is `C^m`
near `x`, for a `C^n` local diffeomorphism with `m + 1 ≤ n`
(`IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`). For a surjective local diffeomorphism
this gives `IsLocalDiffeomorph.isSmoothForm_mpullback_iff`, and, since pullback commutes with the
exterior derivative, a smooth form is closed exactly when its pullback is
(`IsLocalDiffeomorph.isClosed_mpullback_iff`).

These facts are what let forms on a covering space that are invariant under the deck group
descend to the base. The descent `TauCeti.RoughForm.descendAlong` reads a form at a chosen
preimage through the inverse of the derivative of `f` there. Given a family of self-maps of the
source lying over `f` and transitive on its fibres, invariance under the family makes the choice
of preimage irrelevant, so the descent pulls back to the form
(`IsLocalDiffeomorph.mpullback_descendAlong`). Hence a form is a pullback along `f` exactly
when it is invariant under the family (`IsLocalDiffeomorph.exists_mpullback_eq_iff`). For a
surjective smooth local diffeomorphism the descended form of a smooth form is smooth
(`IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_iff`).

## Main definitions

* `TauCeti.RoughForm.descendAlong`: the descent of a form along a map, through a choice of points
  of the source.

## Main results

* `IsLocalDiffeomorph.mpullback_injective`: pullback along a surjective local diffeomorphism is
  injective.
* `IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`,
  `IsLocalDiffeomorph.isSmoothForm_mpullback_iff`: a form is `C^m` exactly when its pullback
  along a (surjective) `C^n` local diffeomorphism is, for `m + 1 ≤ n`.
* `IsLocalDiffeomorph.isClosed_mpullback_iff`: a smooth form is closed exactly when its pullback
  along a surjective smooth local diffeomorphism is.
* `IsLocalDiffeomorph.mpullback_descendAlong`: a form invariant under a family of maps over a
  local diffeomorphism that is transitive on its fibres is the pullback of its descent.
* `IsLocalDiffeomorph.exists_mpullback_eq_iff`,
  `IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_iff`: a (smooth) form is the pullback of a
  (smooth) form along a local diffeomorphism exactly when it is invariant under a family of maps
  over it that is transitive on its fibres.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (pullbacks of differential forms).
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {m n : WithTop ℕ∞} {f g : M → M'} {x : M}

open TauCeti

/-- Pullback along a surjective `C^n` local diffeomorphism, `n ≠ 0`, is injective on rough
forms. -/
theorem IsLocalDiffeomorph.mpullback_injective (hf : IsLocalDiffeomorph I I' n f) (hn : n ≠ 0)
    (hsurj : Function.Surjective f) :
    Function.Injective (mpullback I I' f : RoughForm I' M' F k → RoughForm I M F k) := by
  intro ω η h
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  exact (mpullback_apply_eq_mpullback_apply_iff
    ((hf.isInvertible_mfderiv hn x).surjective)).mp (congrFun h x)

section descendAlong

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

variable (I I') in
/-- The descent of a form `α` on `M` along a map `f : M → M'`, through a choice `s : M' → M` of
points: at `y` it is `α` at `s y`, read through the inverse of the derivative of `f` at `s y`.
`tangentSpaceCast` only identifies the tangent spaces at `y` and at `f (s y)`, which are both the
model space. When `f` is a local diffeomorphism, `s` picks preimages on the image of `f`, and `α`
is invariant under a family of maps over `f` that is transitive on its fibres, the descent pulls
back to `α` (`IsLocalDiffeomorph.mpullback_descendAlong`). -/
def TauCeti.RoughForm.descendAlong (f : M → M') (s : M' → M) (α : RoughForm I M V k) :
    RoughForm I' M' V k :=
  fun y ↦ (α (s y)).compContinuousLinearMap ((mfderiv I I' f (s y)).inverse ∘L
    (tangentSpaceCast I' y (f (s y)) : TangentSpace I' y →L[ℝ] TangentSpace I' (f (s y))))

/-- Evaluation of the descent of a form along `f`: tangent vectors at `y` are sent through the
inverse of the derivative of `f` at the chosen point `s y`. -/
theorem TauCeti.RoughForm.descendAlong_apply (s : M' → M) (α : RoughForm I M V k) (y : M')
    (v : Fin k → TangentSpace I' y) :
    descendAlong I I' f s α y v =
      α (s y) fun i ↦ (mfderiv I I' f (s y)).inverse (tangentSpaceCast I' y (f (s y)) (v i)) :=
  (rfl)

/-- Let `f` be a `C^n` local diffeomorphism, `n ≠ 0`, let `σ` be a family of differentiable
self-maps of `M` over `f` that is transitive on the fibres of `f`, and let `s` choose a preimage
of every point of the image of `f`. Then a form `α` invariant under every `σ i` is the pullback of
its descent along `f` through `s`. -/
theorem IsLocalDiffeomorph.mpullback_descendAlong {ι : Type*} (hf : IsLocalDiffeomorph I I' n f)
    (hn : n ≠ 0) {σ : ι → M → M} (hσ : ∀ i, MDifferentiable I I (σ i))
    (hfσ : ∀ i, f ∘ σ i = f) (hσf : ∀ x y, f x = f y → x = y ∨ ∃ i, σ i x = y)
    {s : M' → M} (hs : ∀ x, f (s (f x)) = f x) {α : RoughForm I M V k}
    (hα : ∀ i, mpullback I I (σ i) α = α) :
    mpullback I I' f (RoughForm.descendAlong I I' f s α) = α := by
  refine funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  -- The chosen preimage `s (f x)` is `g x` for `g` the identity or some `σ i`; `g` lies over `f`
  -- and fixes `α`.
  obtain ⟨g, hgx, hgd, hfg, hgα⟩ : ∃ g : M → M, g x = s (f x) ∧ MDifferentiableAt I I g x ∧
      f ∘ g = f ∧ mpullback I I g α x = α x := by
    rcases hσf x (s (f x)) (hs x).symm with h | ⟨i, h⟩
    · exact ⟨id, h, mdifferentiableAt_id, rfl, by rw [mpullback_id]⟩
    · exact ⟨σ i, h, hσ i x, hfσ i, by rw [hα i]⟩
  -- By the chain rule, the derivative of `f` at `x` factors through the derivative of `g`.
  have hderiv (w : TangentSpace I x) :
      (mfderiv I I' f (g x)).inverse (mfderiv I I' f x w) = mfderiv I I g x w := by
    have hcomp := mfderiv_comp x (hf.mdifferentiable hn (g x)) hgd
    rw [hfg] at hcomp
    rw [hcomp]
    exact (hf.isInvertible_mfderiv hn (g x)).inverse_apply_self _
  -- `tangentSpaceCast` is the identity of the model space.
  have hcast (w : TangentSpace I x) :
      (mfderiv I I' f (g x)).inverse (tangentSpaceCast I' (f x) (f (g x)) (mfderiv I I' f x w)) =
        mfderiv I I g x w :=
    hderiv w
  rw [mpullback_apply, RoughForm.descendAlong_apply, ← hgx]
  simp only [hcast]
  rw [← mpullback_apply, hgα]

/-- **Descent of forms along a local diffeomorphism.** Let `f` be a `C^n` local diffeomorphism,
`n ≠ 0`, and let `σ` be a family of differentiable self-maps of `M` over `f` (`f ∘ σ i = f`) that
is transitive on the fibres of `f`: two points with the same image are equal or are related by
some `σ i`. Then a form on `M` is the pullback of a form on `M'` exactly when it is invariant
under every `σ i`. For a covering map, the `σ i` are deck transformations. -/
theorem IsLocalDiffeomorph.exists_mpullback_eq_iff {ι : Type*} (hf : IsLocalDiffeomorph I I' n f)
    (hn : n ≠ 0) {σ : ι → M → M} (hσ : ∀ i, MDifferentiable I I (σ i))
    (hfσ : ∀ i, f ∘ σ i = f) (hσf : ∀ x y, f x = f y → x = y ∨ ∃ i, σ i x = y)
    {α : RoughForm I M V k} :
    (∃ ω : RoughForm I' M' V k, mpullback I I' f ω = α) ↔ ∀ i, mpullback I I (σ i) α = α := by
  refine ⟨?_, fun hα ↦ ?_⟩
  · rintro ⟨ω, rfl⟩ i
    rw [← mpullback_comp (hσ i) (hf.mdifferentiable hn), hfσ i]
  -- Descend along a choice of preimages; on an empty source every form is a pullback.
  cases isEmpty_or_nonempty M
  · exact ⟨0, funext fun x ↦ isEmptyElim x⟩
  · exact ⟨_, hf.mpullback_descendAlong hn hσ hfσ hσf (fun x ↦ Function.invFun_eq ⟨x, rfl⟩) hα⟩

end descendAlong

/-- For a `C^n` local diffeomorphism `f` at `x` and `m + 1 ≤ n`, a form is a `C^m` section near
`f x` exactly when its pullback along `f` is a `C^m` section near `x`. -/
theorem IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff [IsManifold I 1 M]
    [IsManifold I' 1 M'] (hf : IsLocalDiffeomorphAt I I' n f x) (hmn : m + 1 ≤ n)
    {ω : RoughForm I' M' F k} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullback I I' f ω y)) x ↔
      ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) (f x) := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd hmn (by simp)
  refine ⟨fun h ↦ ?_, fun h ↦ h.mpullback_form hf.contMDiffAt hmn⟩
  -- Near `f x`, the form `ω` is the pullback of `f^* ω` along a local inverse `s` of `f`.
  set s := hf.localInverse
  have hsx : s (f x) = x := hf.localInverse_left_inv hf.localInverse_mem_target
  have hs : ContMDiffAt I' I n s (f x) := hf.contMDiffAt_localInverse
  have hpull := (hsx ▸ h).mpullback_form hs hmn
  refine hpull.congr_of_eventuallyEq ?_
  have hfs : ∀ᶠ y in 𝓝 (f x), IsLocalDiffeomorphAt I I' n f (s y) :=
    hf.continuousAt_localInverse.tendsto.eventually (by rw [hsx]; exact hf.eventually)
  filter_upwards [hfs, hf.localInverse_open_source.mem_nhds hf.localInverse_mem_source]
    with y hy hys
  have hsy : MDifferentiableAt I' I s y :=
    (hf.contMDiffOn_localInverse.contMDiffAt
      (hf.localInverse_open_source.mem_nhds hys)).mdifferentiableAt hn
  have hid : f ∘ s =ᶠ[𝓝 y] id :=
    eventuallyEq_of_mem (hf.localInverse_open_source.mem_nhds hys) hf.localInverse_eqOn_right
  rw [← mpullback_comp_at hsy (hy.mdifferentiableAt hn), hid.mpullback_eq, mpullback_id]

/-- For a surjective `C^n` local diffeomorphism `f` and `m + 1 ≤ n`, a form is `C^m` exactly when
its pullback along `f` is. -/
theorem IsLocalDiffeomorph.isSmoothForm_mpullback_iff [IsManifold I 1 M] [IsManifold I' 1 M']
    (hf : IsLocalDiffeomorph I I' n f) (hsurj : Function.Surjective f) (hmn : m + 1 ≤ n)
    {ω : RoughForm I' M' F k} :
    IsSmoothForm I m (mpullback I I' f ω) ↔ IsSmoothForm I' m ω := by
  simp only [isSmoothForm_def]
  refine ⟨fun h y ↦ ?_, fun h x ↦ ((hf x).contMDiffAt_mpullback_form_iff hmn).mpr (h (f x))⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hf x).contMDiffAt_mpullback_form_iff hmn).mp (h x)

open scoped ContDiff in
/-- **Descent of smooth forms along a surjective local diffeomorphism.** For a surjective smooth
local diffeomorphism `f` and a family of smooth self-maps `σ i` of `M` over `f` that is transitive
on the fibres of `f`, a smooth form on `M` is the pullback of a smooth form on `M'` exactly when it
is invariant under every `σ i`. -/
theorem IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_iff [IsManifold I ∞ M]
    [IsManifold I' ∞ M'] {ι : Type*} (hf : IsLocalDiffeomorph I I' ∞ f)
    (hsurj : Function.Surjective f) {σ : ι → M → M} (hσ : ∀ i, ContMDiff I I ∞ (σ i))
    (hfσ : ∀ i, f ∘ σ i = f) (hσf : ∀ x y, f x = f y → x = y ∨ ∃ i, σ i x = y)
    {α : SmoothForm I M F k} :
    (∃ β : SmoothForm I' M' F k, SmoothForm.mpullback f hf.contMDiff β = α) ↔
      ∀ i, SmoothForm.mpullback (σ i) (hσ i) α = α := by
  simp only [Subtype.ext_iff, SmoothForm.coe_mpullback]
  rw [← hf.exists_mpullback_eq_iff (by simp) (fun i ↦ (hσ i).mdifferentiable (by simp)) hfσ hσf]
  refine ⟨fun ⟨β, hβ⟩ ↦ ⟨β.1, hβ⟩, fun ⟨β, hβ⟩ ↦ ⟨⟨β, ?_⟩, hβ⟩⟩
  -- The descended rough form is smooth because its pullback `α` is.
  exact IsSmoothForm.mem_smoothBundleForms
    ((hf.isSmoothForm_mpullback_iff hsurj (by simp)).mp (hβ ▸ α.isSmoothForm))

open scoped ContDiff in
/-- For a surjective smooth local diffeomorphism `f`, a smooth form is closed exactly when its
pullback along `f` is. -/
theorem IsLocalDiffeomorph.isClosed_mpullback_iff [IsManifold I 2 M] [IsManifold I' 2 M']
    (hf : IsLocalDiffeomorph I I' ∞ f) (hsurj : Function.Surjective f)
    {φ : SmoothForm I' M' F k} : (SmoothForm.mpullback f hf.contMDiff φ).IsClosed ↔ φ.IsClosed := by
  rw [SmoothForm.isClosed_def, SmoothForm.isClosed_def, ← mextDerivₗ_apply,
    SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback, mextDerivₗ_apply]
  exact (hf.mpullback_injective (by simp) hsurj).eq_iff' (mpullback_zero f)
