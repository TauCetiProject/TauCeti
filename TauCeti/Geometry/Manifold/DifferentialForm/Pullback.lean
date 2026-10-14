/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Pullback of rough bundle-valued differential forms

Pullback precomposes each alternating map with the manifold derivative. Its value fiber
at `x` is the original fiber at `f x`, so it works without a trivialization of the value
bundle. Both within-set and unrestricted pullbacks are total; their chain rules carry
the differentiability and unique-derivative hypotheses of Mathlib's `mfderivWithin`.
For a trivial value bundle, `mpullbackWithin` and `mpullback` retain the fixed coefficient
space. On model spaces they agree with precomposition by the Fréchet derivative.

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

section FixedCoefficients

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- Pullback of a fixed-coefficient form using the derivative within `s`. -/
def mpullbackWithin (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (f : M → M') (s : Set M) (ω : RoughForm I' M' F k) : RoughForm I M F k :=
  bundleMpullbackWithin I I' f s ω

/-- Fixed-coefficient within-set pullback is the trivial-bundle specialization. -/
theorem mpullbackWithin_eq_bundleMpullbackWithin (f : M → M') (s : Set M)
    (ω : RoughForm I' M' F k) :
    mpullbackWithin I I' f s ω = bundleMpullbackWithin I I' f s ω := (rfl)

/-- Evaluation of fixed-coefficient within-set pullback on tangent vectors. -/
@[simp]
theorem mpullbackWithin_apply (f : M → M') (s : Set M) (ω : RoughForm I' M' F k)
    (x : M) (v : Fin k → TangentSpace I x) :
    mpullbackWithin I I' f s ω x v =
      ω (f x) (fun i ↦ mfderivWithin I I' f s x (v i)) :=
  bundleMpullbackWithin_apply f s ω x v

/-- Pullback of a fixed-coefficient rough form along the manifold derivative. -/
def mpullback (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (f : M → M') (ω : RoughForm I' M' F k) : RoughForm I M F k :=
  bundleMpullback I I' f ω

/-- Fixed-coefficient pullback is the trivial-bundle specialization. -/
theorem mpullback_eq_bundleMpullback (f : M → M') (ω : RoughForm I' M' F k) :
    mpullback I I' f ω = bundleMpullback I I' f ω := (rfl)

/-- Evaluation of fixed-coefficient pullback on tangent vectors. -/
@[simp]
theorem mpullback_apply (f : M → M') (ω : RoughForm I' M' F k)
    (x : M) (v : Fin k → TangentSpace I x) :
    mpullback I I' f ω x v = ω (f x) (fun i ↦ mfderiv I I' f x (v i)) :=
  bundleMpullback_apply f ω x v

/-- Pullback within the whole manifold is ordinary pullback. -/
@[simp]
theorem mpullbackWithin_univ (f : M → M') (ω : RoughForm I' M' F k) :
    mpullbackWithin I I' f univ ω = mpullback I I' f ω :=
  bundleMpullbackWithin_univ f ω

/-- Within-set and ordinary pullback agree where their derivatives agree. -/
@[simp]
theorem mpullbackWithin_eq_mpullback {f : M → M'} {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x) (hf : MDifferentiableAt I I' f x)
    (ω : RoughForm I' M' F k) : mpullbackWithin I I' f s ω x = mpullback I I' f ω x :=
  bundleMpullbackWithin_eq_bundleMpullback hs hf ω

/-- Within-set pullback preserves zero. -/
@[simp]
theorem mpullbackWithin_zero (f : M → M') (s : Set M) :
    mpullbackWithin I I' f s (0 : RoughForm I' M' F k) = 0 :=
  bundleMpullbackWithin_zero f s

/-- Pullback preserves zero. -/
@[simp]
theorem mpullback_zero (f : M → M') : mpullback I I' f (0 : RoughForm I' M' F k) = 0 :=
  bundleMpullback_zero f

/-- Within-set pullback preserves addition. -/
@[simp]
theorem mpullbackWithin_add [ContinuousAdd F] (f : M → M') (s : Set M)
    (ω η : RoughForm I' M' F k) :
    mpullbackWithin I I' f s (ω + η) =
      mpullbackWithin I I' f s ω + mpullbackWithin I I' f s η :=
  bundleMpullbackWithin_add f s ω η

/-- Pullback preserves addition. -/
@[simp]
theorem mpullback_add [ContinuousAdd F] (f : M → M') (ω η : RoughForm I' M' F k) :
    mpullback I I' f (ω + η) = mpullback I I' f ω + mpullback I I' f η :=
  bundleMpullback_add f ω η

/-- Within-set pullback respects scalar multiplication. -/
@[simp]
theorem mpullbackWithin_smul [ContinuousConstSMul ℝ F] (f : M → M') (s : Set M)
    (c : ℝ) (ω : RoughForm I' M' F k) :
    mpullbackWithin I I' f s (c • ω) = c • mpullbackWithin I I' f s ω :=
  bundleMpullbackWithin_smul f s c ω

/-- Pullback respects scalar multiplication. -/
@[simp]
theorem mpullback_smul [ContinuousConstSMul ℝ F] (f : M → M') (c : ℝ)
    (ω : RoughForm I' M' F k) : mpullback I I' f (c • ω) = c • mpullback I I' f ω :=
  bundleMpullback_smul f c ω

/-- Within-set pullback by the identity fixes forms wherever the derivative is unique. -/
@[simp]
theorem mpullbackWithin_id {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (ω : RoughForm I M F k) : mpullbackWithin I I id s ω x = ω x :=
  bundleMpullbackWithin_id hs ω

/-- Pullback by the identity fixes forms. -/
@[simp]
theorem mpullback_id (ω : RoughForm I M F k) : mpullback I I id ω = ω :=
  bundleMpullback_id ω

/-- The within-set chain rule for fixed-coefficient forms. -/
theorem mpullbackWithin_comp_at {f : M → M'} {g : M' → M''}
    {s : Set M} {t : Set M'} {x : M} (hf : MDifferentiableWithinAt I I' f s x)
    (hg : MDifferentiableWithinAt I' I'' g t (f x)) (hst : MapsTo f s t)
    (hs : UniqueMDiffWithinAt I s x) (ω : RoughForm I'' M'' F k) :
    mpullbackWithin I I'' (g ∘ f) s ω x =
      mpullbackWithin I I' f s (mpullbackWithin I' I'' g t ω) x :=
  bundleMpullbackWithin_comp_at hf hg hst hs ω

/-- The chain rule for fixed-coefficient forms at a point. -/
theorem mpullback_comp_at {f : M → M'} {g : M' → M''} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' I'' g (f x))
    (ω : RoughForm I'' M'' F k) :
    mpullback I I'' (g ∘ f) ω x = mpullback I I' f (mpullback I' I'' g ω) x :=
  bundleMpullback_comp_at hf hg ω

/-- The fixed-coefficient chain rule on a set. -/
theorem mpullback_comp_on {f : M → M'} {g : M' → M''} {s : Set M}
    (hf : ∀ x ∈ s, MDifferentiableAt I I' f x)
    (hg : ∀ x ∈ s, MDifferentiableAt I' I'' g (f x)) (ω : RoughForm I'' M'' F k) :
    ∀ x ∈ s, mpullback I I'' (g ∘ f) ω x =
      mpullback I I' f (mpullback I' I'' g ω) x :=
  bundleMpullback_comp_on hf hg ω

/-- Pullback reverses composition of differentiable maps. -/
theorem mpullback_comp {f : M → M'} {g : M' → M''}
    (hf : MDifferentiable I I' f) (hg : MDifferentiable I' I'' g)
    (ω : RoughForm I'' M'' F k) :
    mpullback I I'' (g ∘ f) ω = mpullback I I' f (mpullback I' I'' g ω) :=
  bundleMpullback_comp hf hg ω

/-- Pullback of a degree-zero form is composition of its underlying function. -/
@[simp]
theorem mpullback_ofFunction (f : M → M') (a : M' → F) :
    mpullback I I' f (RoughForm.ofFunction I' a) = RoughForm.ofFunction I (a ∘ f) := by
  ext x v
  simp

/-- Within-set pullback of a degree-zero form is function composition. -/
@[simp]
theorem mpullbackWithin_ofFunction (f : M → M') (s : Set M) (a : M' → F) :
    mpullbackWithin I I' f s (RoughForm.ofFunction I' a) = RoughForm.ofFunction I (a ∘ f) := by
  ext x v
  simp

/-- On model spaces, within-set pullback is the flat pullback by the Fréchet derivative. -/
theorem mpullbackWithin_eq_flat (f : E → E') (s : Set E)
    (ω : RoughForm 𝓘(ℝ, E') E' F k) :
    mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E') f s ω =
      fun x ↦ (ω (f x)).compContinuousLinearMap (fderivWithin ℝ f s x) := by
  ext x v
  simp only [mpullbackWithin_apply, mfderivWithin_eq_fderivWithin]
  -- Mathlib identifies model-space tangent spaces definitionally with the model spaces.
  rfl

/-- On model spaces, pullback is the flat pullback by the Fréchet derivative. -/
theorem mpullback_eq_flat (f : E → E') (ω : RoughForm 𝓘(ℝ, E') E' F k) :
    mpullback 𝓘(ℝ, E) 𝓘(ℝ, E') f ω =
      fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x) := by
  ext x v
  simp only [mpullback_apply, mfderiv_eq_fderiv]
  -- Mathlib identifies model-space tangent spaces definitionally with the model spaces.
  rfl

end FixedCoefficients
end TauCeti
