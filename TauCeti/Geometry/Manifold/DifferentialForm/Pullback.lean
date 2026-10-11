/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Pullback of rough bundle-valued differential forms

Pullback precomposes each alternating map with the manifold derivative. Its value fiber
at `x` is the original fiber at `f x`, so it works without a trivialization of the value
bundle. Both within-set and unrestricted pullbacks are total; their chain rules carry
the differentiability and unique-derivative hypotheses of Mathlib's `mfderivWithin`.

This construction follows Lee, *Introduction to Smooth Manifolds*, second edition,
Chapter 14. The proofs reuse Mathlib's manifold chain rule and alternating-map composition.
-/

public section

noncomputable section

namespace TauCeti

open Set
open scoped Manifold

variable {E H M E' H' M' E'' H'' M'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  [TopologicalSpace M''] [ChartedSpace H'' M''] {I'' : ModelWithCorners ℝ E'' H''}
  {k : ℕ}

section Definitions

variable {V : M' → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module ℝ (V y)]
  [∀ y, TopologicalSpace (V y)]

/-- Pullback using the derivative within `s`; the value bundle is pulled back along `f`. -/
def bundleMpullbackWithin (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (f : M → M') (s : Set M) (ω : RoughBundleForm I' M' V k) :
    RoughBundleForm I M (fun x ↦ V (f x)) k :=
  fun x ↦ (ω (f x)).compContinuousLinearMap (mfderivWithin I I' f s x)

/-- Evaluation of within-set pullback on tangent vectors. -/
@[simp]
theorem bundleMpullbackWithin_apply (f : M → M') (s : Set M)
    (ω : RoughBundleForm I' M' V k) (x : M) (v : Fin k → TangentSpace I x) :
    bundleMpullbackWithin I I' f s ω x v =
      ω (f x) (fun i ↦ mfderivWithin I I' f s x (v i)) := (rfl)

/-- Pullback of a rough form, with values in the pulled-back value bundle. -/
def bundleMpullback (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (f : M → M') (ω : RoughBundleForm I' M' V k) :
    RoughBundleForm I M (fun x ↦ V (f x)) k :=
  fun x ↦ (ω (f x)).compContinuousLinearMap (mfderiv I I' f x)

/-- Evaluation of pullback on tangent vectors. -/
@[simp]
theorem bundleMpullback_apply (f : M → M') (ω : RoughBundleForm I' M' V k)
    (x : M) (v : Fin k → TangentSpace I x) :
    bundleMpullback I I' f ω x v = ω (f x) (fun i ↦ mfderiv I I' f x (v i)) := (rfl)

/-- The within-set construction on the whole manifold is ordinary pullback. -/
@[simp]
theorem bundleMpullbackWithin_univ (f : M → M') (ω : RoughBundleForm I' M' V k) :
    bundleMpullbackWithin I I' f univ ω = bundleMpullback I I' f ω := by
  ext x v
  simp

/-- Within-set and ordinary pullback agree where the derivatives agree. -/
@[simp]
theorem bundleMpullbackWithin_eq_bundleMpullback {f : M → M'} {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x) (hf : MDifferentiableAt I I' f x)
    (ω : RoughBundleForm I' M' V k) :
    bundleMpullbackWithin I I' f s ω x = bundleMpullback I I' f ω x := by
  ext v
  simp [mfderivWithin_eq_mfderiv hs hf]

/-- Within-set pullback preserves the zero form. -/
@[simp]
theorem bundleMpullbackWithin_zero (f : M → M') (s : Set M) :
    bundleMpullbackWithin I I' f s (0 : RoughBundleForm I' M' V k) = 0 := by
  ext x v
  simp

/-- Pullback preserves the zero form. -/
@[simp]
theorem bundleMpullback_zero (f : M → M') :
    bundleMpullback I I' f (0 : RoughBundleForm I' M' V k) = 0 := by
  simpa only [bundleMpullbackWithin_univ] using
    (bundleMpullbackWithin_zero (I := I) (I' := I') (V := V) (k := k) f univ)

/-- Within-set pullback distributes over addition. -/
@[simp]
theorem bundleMpullbackWithin_add [∀ y, ContinuousAdd (V y)] (f : M → M') (s : Set M)
    (ω η : RoughBundleForm I' M' V k) :
    bundleMpullbackWithin I I' f s (ω + η) =
      bundleMpullbackWithin I I' f s ω + bundleMpullbackWithin I I' f s η := by
  ext x v
  simp

/-- Pullback distributes over addition. -/
@[simp]
theorem bundleMpullback_add [∀ y, ContinuousAdd (V y)] (f : M → M')
    (ω η : RoughBundleForm I' M' V k) :
    bundleMpullback I I' f (ω + η) = bundleMpullback I I' f ω + bundleMpullback I I' f η := by
  simpa only [bundleMpullbackWithin_univ] using
    (bundleMpullbackWithin_add (I := I) (I' := I') f univ ω η)

/-- Within-set pullback commutes with scalar multiplication. -/
@[simp]
theorem bundleMpullbackWithin_smul [∀ y, ContinuousConstSMul ℝ (V y)]
    (f : M → M') (s : Set M) (c : ℝ) (ω : RoughBundleForm I' M' V k) :
    bundleMpullbackWithin I I' f s (c • ω) = c • bundleMpullbackWithin I I' f s ω := by
  ext x v
  simp

/-- Pullback commutes with scalar multiplication. -/
@[simp]
theorem bundleMpullback_smul [∀ y, ContinuousConstSMul ℝ (V y)]
    (f : M → M') (c : ℝ) (ω : RoughBundleForm I' M' V k) :
    bundleMpullback I I' f (c • ω) = c • bundleMpullback I I' f ω := by
  simpa only [bundleMpullbackWithin_univ] using
    (bundleMpullbackWithin_smul (I := I) (I' := I') f univ c ω)

end Definitions

section Identity

variable {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]

/-- Within-set pullback by the identity fixes a form wherever the derivative is unique. -/
@[simp]
theorem bundleMpullbackWithin_id {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (ω : RoughBundleForm I M V k) : bundleMpullbackWithin I I id s ω x = ω x := by
  ext v
  simp [mfderivWithin_id hs]

/-- Pullback by the identity fixes a rough form. -/
@[simp]
theorem bundleMpullback_id (ω : RoughBundleForm I M V k) : bundleMpullback I I id ω = ω := by
  ext x v
  simp [mfderiv_id]

end Identity

section Composition

variable {V : M'' → Type*} [∀ z, AddCommGroup (V z)] [∀ z, Module ℝ (V z)]
  [∀ z, TopologicalSpace (V z)]

/-- The chain rule for bundle-valued pullbacks within sets. -/
theorem bundleMpullbackWithin_comp_at {f : M → M'} {g : M' → M''}
    {s : Set M} {t : Set M'} {x : M} (hf : MDifferentiableWithinAt I I' f s x)
    (hg : MDifferentiableWithinAt I' I'' g t (f x)) (hst : MapsTo f s t)
    (hs : UniqueMDiffWithinAt I s x) (ω : RoughBundleForm I'' M'' V k) :
    bundleMpullbackWithin I I'' (g ∘ f) s ω x =
      bundleMpullbackWithin I I' f s (bundleMpullbackWithin I' I'' g t ω) x := by
  ext v
  simp [mfderivWithin_comp x hg hf hst hs]

/-- The chain rule for bundle-valued pullback at one point. -/
theorem bundleMpullback_comp_at {f : M → M'} {g : M' → M''} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' I'' g (f x))
    (ω : RoughBundleForm I'' M'' V k) :
    bundleMpullback I I'' (g ∘ f) ω x =
      bundleMpullback I I' f (bundleMpullback I' I'' g ω) x := by
  ext v
  simp [mfderiv_comp x hg hf]

/-- The chain rule on a set, requiring differentiability only at its points and their images. -/
theorem bundleMpullback_comp_on {f : M → M'} {g : M' → M''} {s : Set M}
    (hf : ∀ x ∈ s, MDifferentiableAt I I' f x)
    (hg : ∀ x ∈ s, MDifferentiableAt I' I'' g (f x)) (ω : RoughBundleForm I'' M'' V k) :
    ∀ x ∈ s, bundleMpullback I I'' (g ∘ f) ω x =
      bundleMpullback I I' f (bundleMpullback I' I'' g ω) x :=
  fun x hx ↦ bundleMpullback_comp_at (hf x hx) (hg x hx) ω

/-- Pullback reverses composition of differentiable maps. -/
theorem bundleMpullback_comp {f : M → M'} {g : M' → M''}
    (hf : MDifferentiable I I' f) (hg : MDifferentiable I' I'' g)
    (ω : RoughBundleForm I'' M'' V k) :
    bundleMpullback I I'' (g ∘ f) ω =
      bundleMpullback I I' f (bundleMpullback I' I'' g ω) :=
  funext fun x ↦ bundleMpullback_comp_at (hf x) (hg (f x)) ω

end Composition
end TauCeti
