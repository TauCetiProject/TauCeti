/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Orientation behavior of manifold maps

This file records the pointwise interface for a map to preserve or reverse manifold orientations.
The differential is required to be represented by a continuous linear equivalence, and its induced
orientation must agree with the target orientation (or its opposite). These predicates are the local
input for pullback orientations and orientation-sensitive integration.

For orientation lifts with a common model orientation, the chart signs of the lifts compensate the
sign of the coordinate Jacobian of an orientation-preserving map.

For one-dimensional manifolds modelled on `ℝ` whose orientations are the standard orientation of
`ℝ` at the relevant points, `isOrientationPreservingAt_of_orientationAt_eq` and
`isOrientationReversingAt_of_orientationAt_eq` reduce preservation and reversal to the sign of the
real number by which the derivative multiplies.
-/

public section

noncomputable section

open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [FiniteDimensional ℝ E']
  {E'' H'' M'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace M''] [ChartedSpace H'' M''] [FiniteDimensional ℝ E'']
  {ι : Type*} [Fintype ι]

/-- A map preserves orientations at `x` when its manifold derivative is an equivalence that maps
`o`'s tangent orientation at `x` to `o'`'s tangent orientation at `f x`. -/
def IsOrientationPreservingAt [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) : Prop :=
  ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
    (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = o'.orientationAt (f x)

/-- Unfold `IsOrientationPreservingAt` into its derivative witness and orientation equation. -/
theorem isOrientationPreservingAt_iff [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationPreservingAt o o' f x ↔
      ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
        (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
          _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = o'.orientationAt (f x) :=
  Iff.rfl

/-- A map reverses orientations at `x` when its manifold derivative is an equivalence that maps
`o`'s tangent orientation at `x` to the opposite of `o'`'s tangent orientation at `f x`. -/
def IsOrientationReversingAt [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) : Prop :=
  ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
    (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = -(o'.orientationAt (f x))

/-- Unfold `IsOrientationReversingAt` into its derivative witness and orientation equation. -/
theorem isOrientationReversingAt_iff [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationReversingAt o o' f x ↔
      ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
        (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
          _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) =
            -(o'.orientationAt (f x)) :=
  Iff.rfl

/-- Given a continuous linear equivalence representing the derivative, preservation is exactly its
orientation equation. -/
theorem isOrientationPreservingAt_iff_of_coe_eq [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) (e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x))
    (he : (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x) :
    IsOrientationPreservingAt o o' f x ↔
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = o'.orientationAt (f x) := by
  constructor
  · rintro ⟨e', he', h⟩
    have heq : e' = e := ContinuousLinearEquiv.coe_injective (he'.trans he.symm)
    simpa [heq] using h
  · intro h
    exact ⟨e, he, h⟩

/-- Given a continuous linear equivalence representing the derivative, reversal is exactly its
orientation equation with the opposite target orientation. -/
theorem isOrientationReversingAt_iff_of_coe_eq [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) (e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x))
    (he : (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x) :
    IsOrientationReversingAt o o' f x ↔
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) =
        -(o'.orientationAt (f x)) := by
  constructor
  · rintro ⟨e', he', h⟩
    have heq : e' = e := ContinuousLinearEquiv.coe_injective (he'.trans he.symm)
    simpa [heq] using h
  · intro h
    exact ⟨e, he, h⟩

/-- Given a continuous linear equivalence representing the derivative, every map is either
orientation-preserving or orientation-reversing at the point. -/
theorem isOrientationPreservingAt_or_isOrientationReversingAt [IsManifold I 1 M]
    [IsManifold I' 1 M'] (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) (e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x))
    (he : (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x) :
    IsOrientationPreservingAt o o' f x ∨ IsOrientationReversingAt o o' f x := by
  have hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I' (f x)) := by
    simpa only [TauCeti.finrank_tangentSpace] using o'.card_eq
  rcases _root_.Orientation.eq_or_eq_neg
    (_root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x))
    (o'.orientationAt (f x)) hcard with h | h
  · exact .inl ((isOrientationPreservingAt_iff_of_coe_eq o o' f x e he).2 h)
  · exact .inr ((isOrientationReversingAt_iff_of_coe_eq o o' f x e he).2 h)

/-- An orientation-preserving map has an invertible manifold derivative. -/
theorem IsOrientationPreservingAt.isInvertible_mfderiv [IsManifold I 1 M]
    [IsManifold I' 1 M'] {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation I' M' ι}
    {f : M → M'} {x : M} (h : IsOrientationPreservingAt o o' f x) :
    (mfderiv I I' f x).IsInvertible := by
  obtain ⟨e, he, _⟩ := h
  exact ⟨e, he⟩

/-- An orientation-reversing map has an invertible manifold derivative. -/
theorem IsOrientationReversingAt.isInvertible_mfderiv [IsManifold I 1 M]
    [IsManifold I' 1 M'] {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation I' M' ι}
    {f : M → M'} {x : M} (h : IsOrientationReversingAt o o' f x) :
    (mfderiv I I' f x).IsInvertible := by
  obtain ⟨e, he, _⟩ := h
  exact ⟨e, he⟩

/-- Negating the source orientation exchanges preservation and reversal. -/
@[simp] theorem isOrientationPreservingAt_neg_left
    [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationPreservingAt (-o) o' f x ↔ IsOrientationReversingAt o o' f x := by
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [orientationAt_neg, _root_.Orientation.map_neg] at h
    have hh := congrArg Neg.neg h
    exact (neg_neg _).symm.trans hh
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [orientationAt_neg, _root_.Orientation.map_neg]
    have hh := congrArg Neg.neg h
    exact hh.trans (_root_.neg_neg (o'.orientationAt (f x)))

/-- Negating the target orientation exchanges preservation and reversal. -/
@[simp] theorem isOrientationPreservingAt_neg_right [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationPreservingAt o (-o') f x ↔ IsOrientationReversingAt o o' f x := by
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [orientationAt_neg] at h
    exact h
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [orientationAt_neg]
    exact h

/-- Negating the source orientation exchanges reversal and preservation. -/
@[simp] theorem isOrientationReversingAt_neg_left [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationReversingAt (-o) o' f x ↔ IsOrientationPreservingAt o o' f x := by
  rw [← isOrientationPreservingAt_neg_left, neg_neg]

/-- Negating the target orientation exchanges reversal and preservation. -/
@[simp] theorem isOrientationReversingAt_neg_right [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    IsOrientationReversingAt o (-o') f x ↔ IsOrientationPreservingAt o o' f x := by
  rw [← isOrientationPreservingAt_neg_right, neg_neg]

/-- A map cannot preserve and reverse the same pair of orientations at one point. -/
theorem not_isOrientationPreservingAt_and_isOrientationReversingAt
    [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    ¬(IsOrientationPreservingAt o o' f x ∧ IsOrientationReversingAt o o' f x) := by
  rintro ⟨⟨e, he, h⟩, hrev⟩
  exact Module.Ray.ne_neg_self _
    (h.symm.trans ((isOrientationReversingAt_iff_of_coe_eq o o' f x e he).mp hrev))

/-- The identity map preserves every manifold orientation. -/
@[simp] theorem isOrientationPreservingAt_id [IsManifold I 1 M]
    (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationPreservingAt (I := I) (I' := I) (M' := M) o o id x := by
  refine ⟨ContinuousLinearEquiv.refl ℝ _, ?_, ?_⟩
  · rw [ContinuousLinearEquiv.coe_refl, mfderiv_id]
  · /- The continuous and plain linear equivalence wrappers share this definitional equality,
      which lets the orientation map use its identity lemma. -/
    have h_refl :
        (ContinuousLinearEquiv.refl ℝ (TangentSpace I x)).toLinearEquiv =
          LinearEquiv.refl ℝ (TangentSpace I x) := rfl
    rw [h_refl, _root_.Orientation.map_refl]
    simp only [Equiv.refl_apply, id_eq]

/-- The identity map reverses an orientation when its target is given the opposite orientation. -/
theorem isOrientationReversingAt_id_neg [IsManifold I 1 M]
    (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationReversingAt (I := I) (I' := I) (M' := M) o (-o) id x := by
  simp

/-- The composition of two orientation-preserving maps preserves orientations at a point. -/
theorem IsOrientationPreservingAt.comp [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationPreservingAt o' o'' g (f x))
    (hgf : IsOrientationPreservingAt o o' f x) :
    IsOrientationPreservingAt o o'' (g ∘ f) x := by
  obtain ⟨e, he, h⟩ := hgf
  obtain ⟨e', he', h'⟩ := hgg
  have hf := mdifferentiableAt_of_isInvertible_mfderiv ⟨e, he⟩
  have hg := mdifferentiableAt_of_isInvertible_mfderiv ⟨e', he'⟩
  refine ⟨e.trans e', ?_, ?_⟩
  · rw [mfderiv_comp (x := x) hg hf, ← he', ← he]
    exact ContinuousLinearEquiv.comp_coe e e'
  · rw [ContinuousLinearEquiv.trans_toLinearEquiv, _root_.Orientation.map_trans, h, h']
    simp only [Function.comp_apply]

/-- Two orientations of `M'` from which a map preserves orientation at `x`, from the same
orientation of `M`, agree at `f x`. -/
theorem IsOrientationPreservingAt.orientationAt_eq [IsManifold I 1 M] [IsManifold I' 1 M']
    {o : Manifold.Orientation I M ι} {o' o'' : Manifold.Orientation I' M' ι} {f : M → M'}
    {x : M} (h' : IsOrientationPreservingAt o o' f x) (h'' : IsOrientationPreservingAt o o'' f x) :
    o'.orientationAt (f x) = o''.orientationAt (f x) := by
  obtain ⟨D, hD, hDo⟩ := h'
  rwa [← hDo, ← isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ D hD]

/-- A differentiable map `f` preserves orientations at `x` when `g ∘ f` does and `g` preserves
orientations at `f x`. -/
theorem IsOrientationPreservingAt.of_comp [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationPreservingAt o' o'' g (f x))
    (hgf : IsOrientationPreservingAt o o'' (g ∘ f) x) (hf : MDifferentiableAt I I' f x) :
    IsOrientationPreservingAt o o' f x := by
  obtain ⟨e, he, h⟩ := hgf
  obtain ⟨e', he', h'⟩ := hgg
  refine ⟨e.trans e'.symm, ?_, ?_⟩
  · -- `e' ∘ mfderiv f x = mfderiv (g ∘ f) x = e`, so `mfderiv f x = e'⁻¹ ∘ e`.
    have hcomp : (e' : TangentSpace I' (f x) →L[ℝ] TangentSpace I'' (g (f x))).comp
        (mfderiv I I' f x) = (e : TangentSpace I x →L[ℝ] TangentSpace I'' ((g ∘ f) x)) := by
      rw [he', he, mfderiv_comp x (mdifferentiableAt_of_isInvertible_mfderiv ⟨e', he'⟩) hf]
    ext v
    have hv := congrArg (fun L ↦ L v) hcomp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hv
    simp [← hv]
  · rw [ContinuousLinearEquiv.trans_toLinearEquiv, _root_.Orientation.map_trans, h,
      Function.comp_apply, ← h',
      ContinuousLinearEquiv.toLinearEquiv_symm, ← _root_.Orientation.map_symm,
      Equiv.symm_apply_apply]

/-- The composition of two orientation-reversing maps preserves orientations at a point. -/
theorem IsOrientationReversingAt.comp [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationReversingAt o' o'' g (f x))
    (hgf : IsOrientationReversingAt o o' f x) :
    IsOrientationPreservingAt o o'' (g ∘ f) x := by
  have hgg' : IsOrientationPreservingAt (-o') o'' g (f x) :=
    (isOrientationPreservingAt_neg_left o' o'' g (f x)).2 hgg
  have hgf' : IsOrientationPreservingAt o (-o') f x :=
    (isOrientationPreservingAt_neg_right o o' f x).2 hgf
  exact IsOrientationPreservingAt.comp hgg' hgf'

/-- Composing an orientation-preserving map after an orientation-reversing map reverses
orientations at a point. -/
theorem IsOrientationPreservingAt.comp_reversing [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationPreservingAt o' o'' g (f x))
    (hgf : IsOrientationReversingAt o o' f x) :
    IsOrientationReversingAt o o'' (g ∘ f) x := by
  have hgg' : IsOrientationPreservingAt (-o') (-o'') g (f x) := by
    simpa only [isOrientationPreservingAt_neg_left, isOrientationReversingAt_neg_right] using hgg
  have hgf' : IsOrientationPreservingAt o (-o') f x :=
    (isOrientationPreservingAt_neg_right o o' f x).2 hgf
  have h := IsOrientationPreservingAt.comp hgg' hgf'
  exact (isOrientationPreservingAt_neg_right o o'' (g ∘ f) x).1 h

/-- Composing an orientation-reversing map after an orientation-preserving map reverses
orientations at a point. -/
theorem IsOrientationReversingAt.comp_preserving [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation I' M' ι} {o'' : Manifold.Orientation I'' M'' ι}
    {f : M → M'} {g : M' → M''} {x : M}
    (hgg : IsOrientationReversingAt o' o'' g (f x))
    (hgf : IsOrientationPreservingAt o o' f x) :
    IsOrientationReversingAt o o'' (g ∘ f) x := by
  have hgg' : IsOrientationPreservingAt (-o') o'' g (f x) :=
    (isOrientationPreservingAt_neg_left o' o'' g (f x)).2 hgg
  have hgf' : IsOrientationPreservingAt (-o) (-o') f x := by
    simpa only [isOrientationPreservingAt_neg_left, isOrientationReversingAt_neg_right] using hgf
  have h := IsOrientationPreservingAt.comp hgg' hgf'
  exact (isOrientationPreservingAt_neg_left o o'' (g ∘ f) x).1 h

section RealLine

variable {N N' : Type*} [TopologicalSpace N] [ChartedSpace ℝ N] [IsManifold 𝓘(ℝ) 1 N]
  [TopologicalSpace N'] [ChartedSpace ℝ N'] [IsManifold 𝓘(ℝ) 1 N']

/-- For orientations of one-dimensional manifolds modelled on `ℝ` which are the standard
orientation of `ℝ` at `x` and at `f x`, a map whose derivative at `x` is multiplication by a
positive real number preserves orientation at `x`. -/
theorem isOrientationPreservingAt_of_orientationAt_eq
    {o : Manifold.Orientation 𝓘(ℝ) N (Fin 1)} {o' : Manifold.Orientation 𝓘(ℝ) N' (Fin 1)}
    {f : N → N'} {x : N} (ho : o.orientationAt x = (Module.Basis.singleton (Fin 1) ℝ).orientation)
    (ho' : o'.orientationAt (f x) = (Module.Basis.singleton (Fin 1) ℝ).orientation) {c : ℝ}
    (hc : 0 < c) (hf : mfderiv 𝓘(ℝ) 𝓘(ℝ) f x = c • ContinuousLinearMap.id ℝ ℝ) :
    IsOrientationPreservingAt o o' f x := by
  -- Tangent spaces of manifolds modelled on `ℝ` are `ℝ`, and the derivative is `c • id`.
  refine (isOrientationPreservingAt_iff_of_coe_eq o o' f x
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc.ne').toContinuousLinearEquiv
    (hf.symm ▸ ContinuousLinearMap.ext fun _ ↦ rfl)).mpr ?_
  rw [ho, ho']
  refine (_root_.Orientation.map_eq_iff_det_pos _ _ (by simp)).mpr ?_
  -- On `ℝ`, the determinant of multiplication by `c` is `c`.
  exact hc.trans_eq ((LinearMap.det_ring (R := ℝ) _).trans (mul_one c)).symm

/-- For orientations of one-dimensional manifolds modelled on `ℝ` which are the standard
orientation of `ℝ` at `x` and at `f x`, a map whose derivative at `x` is multiplication by a
negative real number reverses orientation at `x`. -/
theorem isOrientationReversingAt_of_orientationAt_eq
    {o : Manifold.Orientation 𝓘(ℝ) N (Fin 1)} {o' : Manifold.Orientation 𝓘(ℝ) N' (Fin 1)}
    {f : N → N'} {x : N} (ho : o.orientationAt x = (Module.Basis.singleton (Fin 1) ℝ).orientation)
    (ho' : o'.orientationAt (f x) = (Module.Basis.singleton (Fin 1) ℝ).orientation) {c : ℝ}
    (hc : c < 0) (hf : mfderiv 𝓘(ℝ) 𝓘(ℝ) f x = c • ContinuousLinearMap.id ℝ ℝ) :
    IsOrientationReversingAt o o' f x := by
  -- Tangent spaces of manifolds modelled on `ℝ` are `ℝ`, and the derivative is `c • id`.
  refine (isOrientationReversingAt_iff_of_coe_eq o o' f x
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc.ne).toContinuousLinearEquiv
    (hf.symm ▸ ContinuousLinearMap.ext fun _ ↦ rfl)).mpr ?_
  rw [ho, ho']
  refine (_root_.Orientation.map_eq_neg_iff_det_neg _ _ (by simp)).mpr ?_
  -- On `ℝ`, the determinant of multiplication by `c` is `c`.
  exact ((LinearMap.det_ring (R := ℝ) _).trans (mul_one c)).trans_lt hc

end RealLine

end TauCeti.Manifold.Orientation

namespace TauCeti.Manifold.OrientationLift

variable {E H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] {k : ℕ}

open Set

/-- If `f` preserves the orientations of two lifts with the same model orientation, then the
chart signs of the lifts compensate the sign of the coordinate Jacobian of `f` between any two
preferred charts. -/
theorem signAt_mul_signAt_mul_det_pos
    (l : OrientationLift I M (Fin k)) (l' : OrientationLift J N (Fin k))
    (hl : l'.modelOrientation = l.modelOrientation) {f : M → N} {x : M}
    (hf : MDifferentiableAt I J f x)
    (ho : Manifold.Orientation.IsOrientationPreservingAt (Manifold.Orientation.mk l)
      (Manifold.Orientation.mk l') f x)
    {β : M} {α : N} (hx : x ∈ (chartAt H β).source) (hfx : f x ∈ (chartAt H' α).source) :
    0 < (l.signAt β x : ℝ) * (l'.signAt α (f x) : ℝ) *
      (fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm) (range I)
        (extChartAt I β x)).det := by
  obtain ⟨e, he, hp⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).mp ho
  rw [Manifold.Orientation.orientationAt_mk, Manifold.Orientation.orientationAt_mk] at hp
  -- The tangent spaces are the model space `E`; restate `hp` there, where the tangent
  -- orientations can be rewritten to the signed model orientations they equal.
  obtain ⟨A, hA⟩ : ∃ A : E ≃ₗ[ℝ] E, A = e.toLinearEquiv := ⟨_, rfl⟩
  replace hp : _root_.Orientation.map (Fin k) A
      (l.orientationAt x : _root_.Orientation ℝ E (Fin k)) =
        (l'.orientationAt (f x) : _root_.Orientation ℝ E (Fin k)) := by
    subst hA
    exact hp
  rw [orientationAt_eq, orientationAt_eq] at hp
  rw [chartOrientation_eq_ite, chartOrientation_eq_ite, hl,
    ← _root_.Orientation.intCast_units_smul_eq_ite,
    ← _root_.Orientation.intCast_units_smul_eq_ite] at hp
  have h₁ := (_root_.Orientation.map_units_smul_eq_iff_det_mul_pos l.modelOrientation
    A _ _ l.card_eq).mp hp
  have h₂ := l.compatible β x x hx (mem_chart_source H x)
  have h₃ := l'.compatible (f x) α (f x) (mem_chart_source H' (f x)) hfx
  rw [← tangentCoordChange_def] at h₂ h₃
  -- The tangent spaces at `x` and `f x` are the model space `E`, so the manifold derivative of
  -- `f` is an endomorphism `D` of `E`, which composes with the tangent coordinate changes.
  obtain ⟨D, hD₀⟩ : ∃ D : E →L[ℝ] E, D = mfderiv I J f x := ⟨_, rfl⟩
  have hD : fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm) (range I)
      (extChartAt I β x) = tangentCoordChange J (f x) α (f x) ∘L D ∘L
        tangentCoordChange I β x x := by
    subst hD₀
    exact hf.fderivWithin_extChartAt_comp_extChartAt_symm
      (by simpa only [extChartAt_source] using hx) (by simpa only [extChartAt_source] using hfx)
  have hdet : LinearMap.det (D : E →ₗ[ℝ] E) = LinearMap.det (A : E →ₗ[ℝ] E) := by
    subst hD₀ hA
    rw [← he]
    rfl
  rw [hD, signAt_of_mem _ hx, signAt_of_mem _ hfx, ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, LinearMap.det_comp, hdet]
  simp only [Units.coe_map] at h₁
  -- Multiply the three positive quantities; the signs at `x` and at `f x` appear squared.
  have ha := Int.isUnit_mul_self (l.sign x ⟨x, mem_chart_source H x⟩).isUnit
  have hc := Int.isUnit_mul_self (l'.sign (f x) ⟨f x, mem_chart_source H' (f x)⟩).isUnit
  generalize (l.sign x ⟨x, mem_chart_source H x⟩ : ℤ) = a at h₁ h₂ ha
  generalize (l'.sign (f x) ⟨f x, mem_chart_source H' (f x)⟩ : ℤ) = c at h₁ h₃ hc
  have ha' : (a : ℝ) * a = 1 := by exact_mod_cast ha
  have hc' : (c : ℝ) * c = 1 := by exact_mod_cast hc
  have hprod := mul_pos (mul_pos h₁ h₂) h₃
  convert hprod using 1
  linear_combination
    (-((l.sign β ⟨x, hx⟩ : ℤ) : ℝ) * (l'.sign α ⟨f x, hfx⟩ : ℤ) *
      (tangentCoordChange J (f x) α (f x)).det * LinearMap.det (A : E →ₗ[ℝ] E) *
      (tangentCoordChange I β x x).det) * ((c : ℝ) * c * ha' + hc')

end TauCeti.Manifold.OrientationLift
