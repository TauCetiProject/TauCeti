/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Smooth pullback of differential forms

A `C^(n+1)` map pulls a `C^n` fixed-coefficient differential form back to a `C^n` form.
The relative theorem uses derivatives within the source set, so it applies at boundary and
corner points. No invertibility, finite dimensionality, or completeness is required.

For smooth maps, `SmoothForm.mpullback` bundles this operation as a linear map on smooth forms.
Its underlying rough form is the existing `TauCeti.mpullback`. Pullback along a smooth map with a
smooth right inverse, such as a vector bundle projection, is injective.

In tangent coordinates, pullback precomposes the form's coordinates with those of Mathlib's
`mfderivWithin`, via `ContinuousAlternatingMap.compContinuousLinearMap`. This expresses
pullback regularity in terms of maps between fixed model fibres. For bundle-valued forms,
the file provides the coordinate identity `inCoordinates_bundleMpullbackWithin`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [IsManifold I 1 M] [IsManifold I' 1 M']
  {k : ℕ} {m n : WithTop ℕ∞} {f : M → M'} {s : Set M} {t : Set M'} {x : M}
  {ω : RoughForm I' M' F k}

/-- Read with the coefficient trivialization of `V'` at `f x` and the tangent trivializations at
`x` and `f x`, a bundle-valued pullback is the form's coordinates precomposed with the
coordinates of `mfderivWithin`. The target tangent trivialization must be valid at `f y`. -/
theorem inCoordinates_bundleMpullbackWithin
    {V' : M' → Type*} [∀ y, AddCommGroup (V' y)] [∀ y, Module ℝ (V' y)]
    [∀ y, TopologicalSpace (V' y)] [TopologicalSpace (TotalSpace F V')]
    [FiberBundle F V'] [VectorBundle ℝ F V']
    (ω : RoughBundleForm I' M' V' k) (f : M → M') (s : Set M) (x y : M)
    (hyT : f y ∈ (trivializationAt E' (TangentSpace I') (f x)).baseSet) :
    ContinuousAlternatingMap.inCoordinates E F x y (f x) (f y)
      (bundleMpullbackWithin I I' f s ω y) =
      (ContinuousAlternatingMap.inCoordinates E' F (f x) (f y) (f x) (f y)
        (ω (f y))).compContinuousLinearMap
        (inTangentCoordinates I I' id f (mfderivWithin I I' f s) x y) := by
  have h := ContinuousAlternatingMap.inCoordinates_compContinuousLinearMap
    (F₁ := E) (F₂ := E') (F₃ := F) (x₀ := x) (z₀ := f x)
    (ω (f y)) (mfderivWithin I I' f s y) hyT
  have hb : bundleMpullbackWithin I I' f s ω y =
      (ω (f y)).compContinuousLinearMap (mfderivWithin I I' f s y) := by
    ext v
    simp only [bundleMpullbackWithin_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      Function.comp_def]
  rw [hb, inTangentCoordinates]
  exact h

namespace RoughForm

/-- In fibre coordinates, pullback precomposes the form's coordinates with the derivative's
coordinates. The target tangent trivialization must be valid at `f y`. -/
theorem inCoordinates_mpullbackWithin (ω : RoughForm I' M' F k) (f : M → M')
    (s : Set M) (x y : M)
    (hy : f y ∈ (trivializationAt E' (TangentSpace I') (f x)).baseSet) :
    ContinuousAlternatingMap.inCoordinates E F x y x y (mpullbackWithin I I' f s ω y) =
      (ContinuousAlternatingMap.inCoordinates E' F (f x) (f y) (f x) (f y)
        (ω (f y))).compContinuousLinearMap
          (inTangentCoordinates I I' id f (mfderivWithin I I' f s) x y) := by
  have h := inCoordinates_bundleMpullbackWithin (I := I) (I' := I') (F := F)
    (V' := Trivial M' F) ω f s x y hy
  ext v
  simpa only [ContinuousAlternatingMap.inCoordinates,
    Bundle.Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x),
    Bundle.Trivial.eq_trivialization M' F (trivializationAt F (Trivial M' F) (f x)),
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_def,
    ContinuousLinearMap.id_apply, inTangentCoordinates, id_eq, mpullbackWithin_apply,
    bundleMpullbackWithin_apply] using congrArg (fun a ↦ a v) h

end RoughForm

/-- A form of regularity `C^m` pulls back to a `C^m` section along a `C^n` map when `m + 1 ≤ n`.
The derivative defining pullback is taken within the unique-differentiability set `s`. -/
theorem _root_.ContMDiffWithinAt.mpullbackWithin_form
    (hω : ContMDiffWithinAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) t (f x))
    (hf : ContMDiffWithinAt I I' n f s x) (hmn : m + 1 ≤ n)
    (hst : MapsTo f s t) (hx : x ∈ s) (hs : UniqueMDiffOn I s) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullbackWithin I I' f s ω y)) s x := by
  have hfm : ContMDiffWithinAt I I' m f s x :=
    hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)
  have hcoeff := (contMDiffWithinAt_continuousAlternatingMap_bundle _).mp hω |>.2
  have hc := hcoeff.comp x hfm hst
  have hd := hf.mfderivWithin_const hmn hx hs
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E') (G := F) (ι := Fin k) m
  have hp := (hpre.comp_contMDiffWithinAt hd).clm_apply hc
  apply (contMDiffWithinAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨contMDiffWithinAt_id, hp.congr_of_eventuallyEq_of_mem ?_ hx⟩
  have hmem : f ⁻¹' (trivializationAt E' (TangentSpace I') (f x)).baseSet ∈ 𝓝[s] x :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt E' (TangentSpace I') (f x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (f x)))
  filter_upwards [hmem] with y hy
  simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    using ω.inCoordinates_mpullbackWithin (I := I) f s x y hy

/-- Pullback within a unique-differentiability set preserves `C^m` sections when the map is
`C^n` and `m + 1 ≤ n`. -/
theorem _root_.ContMDiffOn.mpullbackWithin_form
    (hω : ContMDiffOn I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) t)
    (hf : ContMDiffOn I I' n f s) (hmn : m + 1 ≤ n)
    (hst : MapsTo f s t) (hs : UniqueMDiffOn I s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullbackWithin I I' f s ω y)) s :=
  fun x hx ↦ (hω _ (hst hx)).mpullbackWithin_form (hf x hx) hmn hst hx hs

/-- Pointwise regularity of the pullback of a form. -/
theorem _root_.ContMDiffAt.mpullback_form
    (hω : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) (f x))
    (hf : ContMDiffAt I I' n f x) (hmn : m + 1 ≤ n) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullback I I' f ω y)) x := by
  simpa only [mpullbackWithin_univ, contMDiffWithinAt_univ] using
    ContMDiffWithinAt.mpullbackWithin_form (s := univ) (t := univ)
      hω.contMDiffWithinAt hf.contMDiffWithinAt hmn (mapsTo_univ _ _) (mem_univ x)
      uniqueMDiffOn_univ

/-- Pullback of a fixed-coefficient `C^m` form along a `C^n` map is `C^m` for `m + 1 ≤ n`.
In particular, smooth maps pull smooth forms back to smooth forms. -/
theorem IsSmoothBundleForm.mpullback
    (hω : IsSmoothBundleForm I' F (Trivial M' F) m ω)
    (hf : ContMDiff I I' n f) (hmn : m + 1 ≤ n) :
    IsSmoothBundleForm I F (Trivial M F) m (mpullback I I' f ω) := by
  rw [isSmoothBundleForm_def] at hω ⊢
  exact fun x ↦ (hω (f x)).mpullback_form (hf x) hmn

/-- Pullback of a fixed-coefficient `C^m` form along a `C^(m+1)` map is `C^m`.
This is the form-level interface to the general bundle-section pullback theorem. -/
theorem IsSmoothForm.mpullback (hω : IsSmoothForm I' m ω)
    (hf : ContMDiff I I' (m + 1) f) : IsSmoothForm I m (mpullback I I' f ω) := by
  rw [isSmoothForm_def]
  exact (isSmoothBundleForm_def _ _).mp
    (IsSmoothBundleForm.mpullback ((isSmoothBundleForm_def _ _).mpr hω.contMDiff) hf le_rfl)

namespace SmoothForm

open scoped ContDiff

/-- Pullback along a smooth map, as a linear map on smooth fixed-coefficient forms. -/
def mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) :
    SmoothForm I' M' F k →ₗ[ℝ] SmoothForm I M F k where
  toFun φ := ⟨TauCeti.mpullback I I' f φ.1,
    mem_smoothForms.mpr ((mem_smoothForms.mp φ.2).mpullback hf (by simp))⟩
  map_add' φ ψ := Subtype.ext (TauCeti.mpullback_add f φ.1 ψ.1)
  map_smul' c φ := Subtype.ext (TauCeti.mpullback_smul f c φ.1)

/-- The underlying rough form of smooth pullback is rough pullback. -/
@[simp]
theorem coe_mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (φ : SmoothForm I' M' F k) :
    (mpullback f hf φ).1 = TauCeti.mpullback I I' f φ.1 := (rfl)

/-- Evaluation of smooth pullback on tangent vectors. Simplification also obtains this from
`coe_mpullback` and the rough pullback's application law. -/
theorem mpullback_apply (f : M → M') (hf : ContMDiff I I' ∞ f)
    (φ : SmoothForm I' M' F k) (x : M) (v : Fin k → TangentSpace I x) :
    (mpullback f hf φ).1 x v = φ.1 (f x) (fun i ↦ mfderiv I I' f x (v i)) := by
  rw [coe_mpullback, TauCeti.mpullback_apply]

/-- Evaluation of the smooth pullback of a two-form on a pair of tangent vectors. -/
theorem eval₂_mpullback (f : M → M') (hf : ContMDiff I I' ∞ f)
    (φ : SmoothForm I' M' F 2) (x : M) (v w : TangentSpace I x) :
    (mpullback f hf φ).eval₂ x v w = φ.eval₂ (f x) (mfderiv I I' f x v) (mfderiv I I' f x w) := by
  rw [eval₂_apply, eval₂_apply, mpullback_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Pullback by the identity is the identity linear map. -/
@[simp]
theorem mpullback_id :
    mpullback (I := I) (I' := I) (M := M) (F := F) (k := k) id contMDiff_id = LinearMap.id := by
  ext φ : 1
  apply Subtype.ext
  simp only [coe_mpullback, LinearMap.id_apply, TauCeti.mpullback_id]

variable {E'' H'' M'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] [TopologicalSpace M''] [ChartedSpace H'' M'']
  {I'' : ModelWithCorners ℝ E'' H''} [IsManifold I'' 1 M'']

/-- Pullback reverses composition of smooth maps. -/
theorem mpullback_comp (f : M → M') (g : M' → M'')
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I' I'' ∞ g) :
    mpullback (F := F) (k := k) (g ∘ f) (hg.comp hf) =
      (mpullback f hf).comp (mpullback g hg) := by
  ext φ : 1
  apply Subtype.ext
  simp only [coe_mpullback, LinearMap.comp_apply]
  exact TauCeti.mpullback_comp (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp)) φ.1

/-- Pullback along a smooth map with a smooth right inverse is injective. -/
theorem mpullback_injective_of_rightInverse {f : M → M'} {g : M' → M}
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I' I ∞ g) (hfg : Function.RightInverse g f) :
    Function.Injective (mpullback (F := F) (k := k) f hf) := by
  refine Function.LeftInverse.injective (g := mpullback g hg) fun φ ↦ ?_
  rw [← LinearMap.comp_apply, ← mpullback_comp]
  simp only [hfg.comp_eq_id, mpullback_id, LinearMap.id_apply]

/-- Pullback along the projection of a smooth vector bundle is injective: the zero section is a
smooth right inverse of the projection. -/
theorem mpullback_proj_injective {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {V : M → Type*} [TopologicalSpace (TotalSpace F' V)] [∀ x, AddCommMonoid (V x)]
    [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F' V]
    [VectorBundle ℝ F' V] [IsManifold (I.prod 𝓘(ℝ, F')) 1 (TotalSpace F' V)] :
    Function.Injective
      (mpullback (I := I.prod 𝓘(ℝ, F')) (I' := I) (F := F) (k := k) (π F' V) (contMDiff_proj V)) :=
  mpullback_injective_of_rightInverse _ (contMDiff_zeroSection ℝ V) fun _ ↦ rfl

variable {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {k l : ℕ}

/-- Smooth pullback is a homomorphism for every fixed continuous coefficient pairing. -/
theorem mpullback_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (f : M → M')
    (hf : ContMDiff I I' ∞ f) (φ : SmoothForm I' M' F₁ k) (ψ : SmoothForm I' M' F₂ l) :
    mpullback (F := F₃) (k := k + l) f hf (SmoothForm.wedgeWith μ φ ψ) =
      SmoothForm.wedgeWith μ
        (mpullback (F := F₁) (k := k) f hf φ)
        (mpullback (F := F₂) (k := l) f hf ψ) := by
  apply Subtype.ext
  simp only [coe_mpullback, SmoothForm.coe_wedgeWith]
  exact TauCeti.mpullback_wedgeWith μ f φ.1 ψ.1

/-- Smooth real-valued pullback is a homomorphism for the usual wedge. -/
theorem mpullback_wedge (f : M → M') (hf : ContMDiff I I' ∞ f)
    (φ : SmoothForm I' M' ℝ k) (ψ : SmoothForm I' M' ℝ l) :
    mpullback (k := k + l) f hf (SmoothForm.wedge φ ψ) =
      SmoothForm.wedge (mpullback (k := k) f hf φ) (mpullback (k := l) f hf ψ) := by
  simpa only [SmoothForm.wedge_def] using
    mpullback_wedgeWith (ContinuousLinearMap.mul ℝ ℝ) f hf φ ψ

end SmoothForm

end TauCeti
