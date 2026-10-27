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
descend to the base.

## Main results

* `IsLocalDiffeomorph.mpullback_injective`: pullback along a surjective local diffeomorphism is
  injective.
* `IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`,
  `IsLocalDiffeomorph.isSmoothForm_mpullback_iff`: a form is `C^m` exactly when its pullback
  along a (surjective) `C^n` local diffeomorphism is, for `m + 1 ≤ n`.
* `IsLocalDiffeomorph.isClosed_mpullback_iff`: a smooth form is closed exactly when its pullback
  along a surjective smooth local diffeomorphism is.

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
/-- For a surjective smooth local diffeomorphism `f`, a smooth form is closed exactly when its
pullback along `f` is. -/
theorem IsLocalDiffeomorph.isClosed_mpullback_iff [IsManifold I 2 M] [IsManifold I' 2 M']
    (hf : IsLocalDiffeomorph I I' ∞ f) (hsurj : Function.Surjective f)
    {φ : SmoothForm I' M' F k} : (SmoothForm.mpullback f hf.contMDiff φ).IsClosed ↔ φ.IsClosed := by
  rw [SmoothForm.isClosed_def, SmoothForm.isClosed_def, ← mextDerivₗ_apply,
    SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback, mextDerivₗ_apply]
  exact (hf.mpullback_injective (by simp) hsurj).eq_iff' (mpullback_zero f)
