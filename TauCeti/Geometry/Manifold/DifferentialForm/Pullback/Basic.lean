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
Pullback at `x` only depends on the germ of `f` at `x`, within-set pullback at `x` only on the
value at `x` and the germ within the set, and when the derivative of `f` at `x`
is surjective it determines the form at `f x`.

This construction follows Lee, *Introduction to Smooth Manifolds*, second edition,
Chapter 14. The proofs reuse Mathlib's manifold chain rule and alternating-map composition.
-/

public section

noncomputable section

namespace TauCeti

open Set Filter
open scoped Manifold Topology

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

/-- Within-set pullback commutes with scalar multiplication of the values, by any scalars
acting continuously on the fibres and commuting with the real action. -/
@[simp]
theorem bundleMpullbackWithin_smul {S : Type*} [Monoid S] [∀ y, DistribMulAction S (V y)]
    [∀ y, ContinuousConstSMul S (V y)] [∀ y, SMulCommClass ℝ S (V y)]
    (f : M → M') (s : Set M) (c : S) (ω : RoughBundleForm I' M' V k) :
    bundleMpullbackWithin I I' f s (c • ω) = c • bundleMpullbackWithin I I' f s ω := by
  ext x v
  simp

/-- Pullback commutes with scalar multiplication of the values, by any scalars acting
continuously on the fibres and commuting with the real action. -/
@[simp]
theorem bundleMpullback_smul {S : Type*} [Monoid S] [∀ y, DistribMulAction S (V y)]
    [∀ y, ContinuousConstSMul S (V y)] [∀ y, SMulCommClass ℝ S (V y)]
    (f : M → M') (c : S) (ω : RoughBundleForm I' M' V k) :
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

/-- The chain rule for bundle-valued pullbacks when the intermediate set condition holds only
locally at the base point. -/
theorem bundleMpullbackWithin_comp_of_preimage_mem_nhdsWithin
    {f : M → M'} {g : M' → M''} {s : Set M} {t : Set M'} {x : M}
    (hf : MDifferentiableWithinAt I I' f s x)
    (hg : MDifferentiableWithinAt I' I'' g t (f x))
    (hst : f ⁻¹' t ∈ 𝓝[s] x) (hs : UniqueMDiffWithinAt I s x)
    (ω : RoughBundleForm I'' M'' V k) :
    bundleMpullbackWithin I I'' (g ∘ f) s ω x =
      bundleMpullbackWithin I I' f s (bundleMpullbackWithin I' I'' g t ω) x := by
  ext v
  simp only [bundleMpullbackWithin_apply]
  rw [mfderivWithin_comp_of_preimage_mem_nhdsWithin x hg hf hst hs]
  rfl

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

/-- Evaluation of fixed-coefficient pullback on tangent vectors. -/
@[simp]
theorem mpullback_apply (f : M → M') (ω : RoughForm I' M' F k)
    (x : M) (v : Fin k → TangentSpace I x) :
    mpullback I I' f ω x v = ω (f x) (fun i ↦ mfderiv I I' f x (v i)) :=
  bundleMpullback_apply f ω x v

/-- Evaluation of the pullback of a two-form on a pair of tangent vectors. -/
theorem mpullback_apply_pair (f : M → M') (ω : RoughForm I' M' F 2) (x : M)
    (a b : TangentSpace I x) :
    mpullback I I' f ω x ![a, b] = ω (f x) ![mfderiv I I' f x a, mfderiv I I' f x b] := by
  rw [mpullback_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

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

/-- A form evaluated at `a` on tangent vectors at `b = a` moved by `tangentSpaceCast` is the form
evaluated at `b` on the original vectors. -/
theorem RoughForm.apply_tangentSpaceCast {ω : RoughForm I' M' F k} {a b : M'} (h : b = a)
    (u : Fin k → TangentSpace I' b) : ω a (fun i ↦ tangentSpaceCast I' b a (u i)) = ω b u := by
  subst h
  -- `tangentSpaceCast` from a tangent space to itself is the identity.
  rfl

/-- Maps that agree near `x` within `s`, and at `x`, pull a form back within `s` to the same value
at `x`. -/
theorem _root_.Filter.EventuallyEq.mpullbackWithin_eq {f g : M → M'} {s : Set M} {x : M}
    (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x) (ω : RoughForm I' M' F k) :
    mpullbackWithin I I' f s ω x = mpullbackWithin I I' g s ω x := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [mpullbackWithin_apply, mpullbackWithin_apply, h.mfderivWithin_eq hx]
  -- `tangentSpaceCast` is the identity of the model space, so only the base point differs.
  change ω (f x) (fun i ↦ mfderivWithin I I' g s x (v i)) =
    ω (g x) (fun i ↦ mfderivWithin I I' g s x (v i))
  rw [hx]

/-- Maps that agree on `s` pull a form back within `s` to the same value at each point of `s`. -/
theorem mpullbackWithin_congr {f g : M → M'} {s : Set M} {x : M} (h : EqOn f g s) (hx : x ∈ s)
    (ω : RoughForm I' M' F k) : mpullbackWithin I I' f s ω x = mpullbackWithin I I' g s ω x :=
  (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h).mpullbackWithin_eq (h hx) ω

/-- Maps that agree near `x` pull a form back to the same value at `x`. -/
theorem _root_.Filter.EventuallyEq.mpullback_eq {f g : M → M'} {x : M} (h : f =ᶠ[𝓝 x] g)
    (ω : RoughForm I' M' F k) : mpullback I I' f ω x = mpullback I I' g ω x := by
  rw [← mpullbackWithin_univ, ← mpullbackWithin_univ]
  exact (h.filter_mono nhdsWithin_le_nhds).mpullbackWithin_eq h.eq_of_nhds ω

/-- If the derivative of `f` at `x` is surjective, two forms have the same pullback along `f` at
`x` exactly when they agree at `f x`. -/
theorem mpullback_apply_eq_mpullback_apply_iff {f : M → M'} {x : M}
    (hf : Function.Surjective (mfderiv I I' f x)) {ω η : RoughForm I' M' F k} :
    mpullback I I' f ω x = mpullback I I' f η x ↔ ω (f x) = η (f x) := by
  refine ⟨fun h ↦ ContinuousAlternatingMap.ext fun v ↦ ?_, fun h ↦ ?_⟩
  · choose w hw using fun i ↦ hf (v i)
    have h₁ := DFunLike.congr_fun h w
    simp only [mpullback_apply, hw] at h₁
    exact h₁
  · refine ContinuousAlternatingMap.ext fun v ↦ ?_
    rw [mpullback_apply, mpullback_apply, h]

/-- A pullback vanishes at every point where the form vanishes at the image point. -/
theorem mpullback_apply_eq_zero {f : M → M'} {ω : RoughForm I' M' F k} {x : M}
    (h : ω (f x) = 0) : mpullback I I' f ω x = 0 := by
  ext v
  simp [mpullback_apply, h]

/-- Pullback along a surjective map whose derivatives are all surjective is injective. -/
theorem mpullback_injective_of_surjective {f : M → M'} (hsurj : Function.Surjective f)
    (hf : ∀ x, Function.Surjective (mfderiv I I' f x)) :
    Function.Injective (mpullback I I' f : RoughForm I' M' F k → RoughForm I M F k) := by
  intro ω η h
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  exact (mpullback_apply_eq_mpullback_apply_iff (hf x)).mp (congrFun h x)

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

/-- Within-set pullback respects scalar multiplication of the coefficients, by any scalars
acting continuously on the coefficient space and commuting with the real action. -/
@[simp]
theorem mpullbackWithin_smul {S : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] (f : M → M') (s : Set M)
    (c : S) (ω : RoughForm I' M' F k) :
    mpullbackWithin I I' f s (c • ω) = c • mpullbackWithin I I' f s ω :=
  bundleMpullbackWithin_smul f s c ω

/-- Pullback respects scalar multiplication of the coefficients, by any scalars acting
continuously on the coefficient space and commuting with the real action. -/
@[simp]
theorem mpullback_smul {S : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] (f : M → M') (c : S)
    (ω : RoughForm I' M' F k) : mpullback I I' f (c • ω) = c • mpullback I I' f ω :=
  bundleMpullback_smul f c ω

/-- Pullback of a form multiplied pointwise by a scalar function multiplies the pullback by the
composite function, for any scalars acting continuously on the coefficient space and commuting
with the real action. -/
@[simp]
theorem mpullback_fun_smul {S : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] (f : M → M') (c : M' → S)
    (ω : RoughForm I' M' F k) :
    mpullback I I' f (fun y ↦ c y • ω y) = fun x ↦ c (f x) • mpullback I I' f ω x := by
  funext x
  ext v
  simp only [mpullback_apply, ContinuousAlternatingMap.smul_apply]

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

/-- The within-set chain rule for fixed-coefficient forms with a local intermediate-set
condition. -/
theorem mpullbackWithin_comp_of_preimage_mem_nhdsWithin
    {f : M → M'} {g : M' → M''} {s : Set M} {t : Set M'} {x : M}
    (hf : MDifferentiableWithinAt I I' f s x)
    (hg : MDifferentiableWithinAt I' I'' g t (f x))
    (hst : f ⁻¹' t ∈ 𝓝[s] x) (hs : UniqueMDiffWithinAt I s x)
    (ω : RoughForm I'' M'' F k) :
    mpullbackWithin I I'' (g ∘ f) s ω x =
      mpullbackWithin I I' f s (mpullbackWithin I' I'' g t ω) x :=
  bundleMpullbackWithin_comp_of_preimage_mem_nhdsWithin hf hg hst hs ω

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

/-- The chain rule for precomposition by a map of normed spaces: the pullback along `u ∘ L`, for a
map `L` with derivative `A` at `y`, is the pullback along `u` at `L y` precomposed with `A`. -/
theorem mpullback_comp_apply_of_hasFDerivAt {u : E' → M} {L : E'' → E'} {A : E'' →L[ℝ] E'}
    {y : E''} (hL : HasFDerivAt L A y) (hu : MDifferentiableAt 𝓘(ℝ, E') I u (L y))
    (ω : RoughForm I M F k) :
    mpullback 𝓘(ℝ, E'') I (u ∘ L) ω y =
      (mpullback 𝓘(ℝ, E') I u ω (L y)).compContinuousLinearMap A := by
  rw [mpullback_comp_at hL.differentiableAt.mdifferentiableAt hu, mpullback_eq_flat]
  exact congrArg _ hL.fderiv

/-- The pullback of a form along `γ ∘ P`, for a continuous linear map `P` of normed spaces,
vanishes on every family of vectors one of which lies in the kernel of `P`. Where `γ ∘ P` is
differentiable, it is constant along the line through `z` in that direction; where it is not, the
derivative is zero by convention. -/
theorem mpullback_comp_clm_apply_eq_zero (ω : RoughForm I M F k) (γ : E' → M)
    (P : E'' →L[ℝ] E') {z : E''} {v : Fin k → E''} {i : Fin k} (hv : P (v i) = 0) :
    mpullback 𝓘(ℝ, E'') I (γ ∘ P) ω z v = 0 := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, E'') I (γ ∘ P) z
  · refine (mpullback_apply (γ ∘ P) ω z v).trans ((ω _).map_coord_zero i ?_)
    let c : ℝ → E'' := fun t ↦ z + t • v i
    have hc : HasFDerivAt c ((1 : ℝ →L[ℝ] ℝ).smulRight (v i)) 0 :=
      ((hasFDerivAt_id (0 : ℝ)).smul_const (v i)).const_add z
    have hconst : (γ ∘ P) ∘ c = fun _ ↦ γ (P z) := funext fun t ↦ by simp [c, hv]
    have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E'')) (I'' := I) (0 : ℝ)
      (by simpa [c] using hd) hc.differentiableAt.mdifferentiableAt
    have hmc : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E'') c 0 = (1 : ℝ →L[ℝ] ℝ).smulRight (v i) := by
      rw [mfderiv_eq_fderiv, hc.fderiv]
      rfl
    rw [hconst, mfderiv_const, hmc] at hcomp
    have hcz : c 0 = z := by simp [c]
    have key : mfderiv 𝓘(ℝ, E'') I (γ ∘ P) (c 0) ((1 : ℝ →L[ℝ] ℝ).smulRight (v i) 1) = 0 :=
      (DFunLike.congr_fun hcomp (1 : ℝ)).symm
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul, hcz] at key
    exact key
  · have h0 : mpullback 𝓘(ℝ, E'') I (γ ∘ P) ω z = 0 := by
      ext w
      rw [mpullback_apply, mfderiv_zero_of_not_mdifferentiableAt hd,
        ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
      exact (ω _).map_coord_zero i (zero_apply _)
    -- The zero alternating map evaluates to zero.
    rw [h0]
    rfl

end FixedCoefficients
end TauCeti
