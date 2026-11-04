/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelWithCorners.LinearEquiv
public import TauCeti.Geometry.Manifold.Orientation.Atlas
public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.Geometry.Manifold.Orientation.Sign

/-!
# Recharting manifold orientations along continuous linear equivalences

Let `I : ModelWithCorners ℝ E H` be a real model with corners and `e : E ≃L[ℝ] F` a continuous
linear equivalence. Replacing `I` by `I.transContinuousLinearEquiv e` changes the model vector
space coordinates without changing the chart carrier `H`. Because within-range transition
derivatives conjugate by `e` (`ModelWithCorners.fderivWithin_transContinuousLinearEquiv`), their
determinants are unchanged (`LinearMap.det_conj`), even when `e` has negative determinant and at
boundary or corner points. Consequently the orientation-preserving groupoid and the notion of an
oriented atlas are invariant under `e`.

An orientation lift or manifold orientation on `(M, I)` transports along `e` by mapping its model
orientation along `e.toLinearEquiv` while keeping the same source-indexed chart signs. The
comparison diffeomorphism `ContinuousLinearEquiv.toTransContinuousLinearEquiv` (whose underlying
map is `id`) always preserves this transported orientation, with orientation sign `1`.

By contrast, when an oriented atlas of `M` is oriented before and after recharting using a
*separately fixed* model orientation (for instance the same orientation of `E` under an
automorphism `e : E ≃L[ℝ] E`, or fixed basis orientations of `E` and `F`), the comparison
diffeomorphism preserves or reverses orientation according to the sign of the real determinant of
`e`, and its `orientationSign` equals `SignType.sign` of that determinant.

## Main definitions

* `TauCeti.Manifold.OrientationLift.congrModel`, `TauCeti.Manifold.Orientation.congrModel`:
  cast an orientation lift or manifold orientation along an equality of models `I = J`.
* `TauCeti.Manifold.OrientationLift.transContinuousLinearEquiv`,
  `TauCeti.Manifold.Orientation.transContinuousLinearEquiv`: transport an orientation lift or
  manifold orientation along `e : E ≃L[ℝ] F`.

## Main results

* `TauCeti.orientationPreservingGroupoid_transContinuousLinearEquiv`,
  `TauCeti.isOrientedAtlas_transContinuousLinearEquiv_iff`: invariance of orientation-preserving
  coordinate changes and oriented atlases under `e : E ≃L[ℝ] F`.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv`,
  `TauCeti.Manifold.Orientation.orientationSign_id_transContinuousLinearEquiv`: real recharting
  preserves the transported orientation.
* `TauCeti.IsOrientedAtlas.orientation_transContinuousLinearEquiv`: transporting the orientation
  determined by an oriented atlas and `model` gives the orientation determined by `map e model`.
* `TauCeti.IsOrientedAtlas.orientationSign_toTransContinuousLinearEquiv`,
  `TauCeti.IsOrientedAtlas.orientationSign_toTransContinuousLinearEquiv_basis`: comparison with a
  separately fixed model orientation has the sign of the real determinant of `e`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Volume I, Chapter I.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition, Chapters 15 and 17.
-/

public section

noncomputable section

open Set Module
open scoped Manifold Topology ContDiff

namespace TauCeti

/-! ### Invariance of the orientation-preserving groupoid and oriented atlases -/

section Groupoid

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- Recharting the model along a continuous linear equivalence `e : E ≃L[ℝ] F` leaves
`OrientationPreservingOn` unchanged, regardless of the sign of the determinant of `e`: transition
derivatives conjugate by `e`. -/
@[simp]
theorem orientationPreservingOn_transContinuousLinearEquiv_iff (e : E ≃L[ℝ] F) {f : H → H}
    {s : Set H} :
    OrientationPreservingOn (I.transContinuousLinearEquiv e) f s ↔
      OrientationPreservingOn I f s := by
  simp only [orientationPreservingOn_iff]
  refine forall₂_congr fun x _ ↦ ?_
  rw [I.differentiableWithinAt_transContinuousLinearEquiv_iff e f x,
    I.fderivWithin_transContinuousLinearEquiv e f x]
  have hdet :
      LinearMap.det (((e : E →L[ℝ] F) ∘L fderivWithin ℝ (I ∘ f ∘ I.symm) (range I) (I x) ∘L
        (e.symm : F →L[ℝ] E)) : F →ₗ[ℝ] F) =
        LinearMap.det (fderivWithin ℝ (I ∘ f ∘ I.symm) (range I) (I x) : E →ₗ[ℝ] E) :=
    LinearMap.det_conj _ e.toLinearEquiv
  rw [hdet]

/-- The groupoid of orientation-preserving open partial homeomorphisms is unchanged by a continuous
linear change of model coordinates. -/
@[simp]
theorem orientationPreservingGroupoid_transContinuousLinearEquiv (e : E ≃L[ℝ] F) :
    orientationPreservingGroupoid (I.transContinuousLinearEquiv e) =
      orientationPreservingGroupoid I := by
  apply le_antisymm <;> rw [StructureGroupoid.le_iff] <;> intro φ hφ <;>
    simpa [mem_orientationPreservingGroupoid_iff] using hφ

/-- A charted space with orientation-preserving coordinate changes retains that property after any
continuous linear change of model coordinates. -/
instance hasGroupoid_orientationPreservingGroupoid_transContinuousLinearEquiv
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    [h : HasGroupoid M (orientationPreservingGroupoid I)] (e : E ≃L[ℝ] F) :
    HasGroupoid M (orientationPreservingGroupoid (I.transContinuousLinearEquiv e)) := by
  rwa [orientationPreservingGroupoid_transContinuousLinearEquiv]

/-- Being an oriented atlas is invariant under a continuous linear change of model coordinates. -/
@[simp]
theorem isOrientedAtlas_transContinuousLinearEquiv_iff (n : ℕ∞ω) [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (e : E ≃L[ℝ] F)
    {A : Set (OpenPartialHomeomorph M H)} :
    IsOrientedAtlas (I.transContinuousLinearEquiv e) n A ↔ IsOrientedAtlas I n A := by
  constructor <;> intro ⟨hsub, hcov, htr⟩ <;> refine ⟨?_, hcov, ?_⟩
  · rwa [I.maximalAtlas_transContinuousLinearEquiv e n] at hsub
  · intro φ ψ hφ hψ
    simpa using htr hφ hψ
  · rwa [I.maximalAtlas_transContinuousLinearEquiv e n]
  · intro φ ψ hφ hψ
    simpa using htr hφ hψ

end Groupoid

/-! ### Casting orientations along an equality of models -/

namespace Manifold.OrientationLift

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [Fintype ι]

/-- Cast an orientation lift along an equality of models on the same model vector space and chart
carrier. -/
def congrModel {I J : ModelWithCorners ℝ E H} (h : I = J) (o : OrientationLift I M ι) :
    OrientationLift J M ι where
  modelOrientation := o.modelOrientation
  card_eq := o.card_eq
  sign := o.sign
  locallyConstant_sign := o.locallyConstant_sign
  compatible := h ▸ o.compatible

@[simp]
theorem congrModel_modelOrientation {I J : ModelWithCorners ℝ E H} (h : I = J)
    (o : OrientationLift I M ι) :
    (o.congrModel h).modelOrientation = o.modelOrientation := (rfl)

@[simp]
theorem congrModel_sign {I J : ModelWithCorners ℝ E H} (h : I = J)
    (o : OrientationLift I M ι) (α : M) (x : (chartAt H α).source) :
    (o.congrModel h).sign α x = o.sign α x := (rfl)

@[simp]
theorem congrModel_signAt {I J : ModelWithCorners ℝ E H} (h : I = J)
    (o : OrientationLift I M ι) (α x : M) :
    (o.congrModel h).signAt α x = o.signAt α x := by
  by_cases hx : x ∈ (chartAt H α).source <;> simp [hx]

@[simp]
theorem congrModel_refl {I : ModelWithCorners ℝ E H} (o : OrientationLift I M ι) :
    o.congrModel rfl = o := (rfl)

@[simp]
theorem congrModel_congrModel {I J K : ModelWithCorners ℝ E H} (h₁ : I = J) (h₂ : J = K)
    (o : OrientationLift I M ι) :
    (o.congrModel h₁).congrModel h₂ = o.congrModel (h₁.trans h₂) := (rfl)

@[simp]
theorem flip_congrModel {I J : ModelWithCorners ℝ E H} (h : I = J)
    (o : OrientationLift I M ι) :
    (o.congrModel h).flip = o.flip.congrModel h := by
  ext α x <;> simp

@[simp]
theorem neg_congrModel {I J : ModelWithCorners ℝ E H} (h : I = J)
    (o : OrientationLift I M ι) :
    (-o).congrModel h = -(o.congrModel h) := by
  ext α x <;> simp

@[simp]
theorem orientationAt_congrModel {I J : ModelWithCorners ℝ E H} (h : I = J)
    [IsManifold I 1 M] [IsManifold J 1 M] (o : OrientationLift I M ι) (x : M) :
    (o.congrModel h).orientationAt x = o.orientationAt x := by
  subst h
  rfl

end Manifold.OrientationLift

namespace Manifold.Orientation

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [Fintype ι]

/-- Cast a manifold orientation along an equality of models on the same model vector space and
chart carrier. -/
def congrModel {I J : ModelWithCorners ℝ E H} (h : I = J) (o : Orientation I M ι) :
    Orientation J M ι :=
  o.lift (fun l ↦ mk (l.congrModel h)) fun l ↦
    (mk_eq_mk_iff _ _).mpr (.inr (l.flip_congrModel h).symm)

@[simp]
theorem congrModel_mk {I J : ModelWithCorners ℝ E H} (h : I = J) (l : OrientationLift I M ι) :
    (mk l).congrModel h = mk (l.congrModel h) := by
  unfold congrModel
  rw [lift_mk]

@[simp]
theorem congrModel_refl {I : ModelWithCorners ℝ E H} (o : Orientation I M ι) :
    o.congrModel rfl = o :=
  o.inductionOn fun l ↦ by simp

@[simp]
theorem congrModel_congrModel {I J K : ModelWithCorners ℝ E H} (h₁ : I = J) (h₂ : J = K)
    (o : Orientation I M ι) :
    (o.congrModel h₁).congrModel h₂ = o.congrModel (h₁.trans h₂) :=
  o.inductionOn fun l ↦ by simp

@[simp]
theorem neg_congrModel {I J : ModelWithCorners ℝ E H} (h : I = J) (o : Orientation I M ι) :
    (-o).congrModel h = -(o.congrModel h) :=
  o.inductionOn fun l ↦ by simp

theorem congrModel_injective {I J : ModelWithCorners ℝ E H} (h : I = J) :
    Function.Injective (congrModel (M := M) (ι := ι) h) := fun o₁ o₂ heq ↦ by
  simpa using congrArg (congrModel h.symm) heq

@[simp]
theorem congrModel_inj {I J : ModelWithCorners ℝ E H} (h : I = J) {o₁ o₂ : Orientation I M ι} :
    o₁.congrModel h = o₂.congrModel h ↔ o₁ = o₂ :=
  (congrModel_injective h).eq_iff

@[simp]
theorem orientationAt_congrModel {I J : ModelWithCorners ℝ E H} (h : I = J)
    [IsManifold I 1 M] [IsManifold J 1 M] (o : Orientation I M ι) (x : M) :
    (o.congrModel h).orientationAt x = o.orientationAt x := by
  subst h
  rw [congrModel_refl]

section CongrModelMap

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']

@[simp]
theorem isOrientationPreservingAt_congrModel_left {I J : ModelWithCorners ℝ E H} (h : I = J)
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I 1 M] [IsManifold J 1 M] [IsManifold I' 1 M']
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationPreservingAt (o.congrModel h) o' f x ↔ IsOrientationPreservingAt o o' f x := by
  subst h
  rw [congrModel_refl]

@[simp]
theorem isOrientationPreservingAt_congrModel_right {I : ModelWithCorners ℝ E H}
    {I' J' : ModelWithCorners ℝ E' H'} (h : I' = J') [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold J' 1 M'] (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationPreservingAt o (o'.congrModel h) f x ↔ IsOrientationPreservingAt o o' f x := by
  subst h
  rw [congrModel_refl]

@[simp]
theorem isOrientationReversingAt_congrModel_left {I J : ModelWithCorners ℝ E H} (h : I = J)
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I 1 M] [IsManifold J 1 M] [IsManifold I' 1 M']
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationReversingAt (o.congrModel h) o' f x ↔ IsOrientationReversingAt o o' f x := by
  subst h
  rw [congrModel_refl]

@[simp]
theorem isOrientationReversingAt_congrModel_right {I : ModelWithCorners ℝ E H}
    {I' J' : ModelWithCorners ℝ E' H'} (h : I' = J') [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold J' 1 M'] (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    IsOrientationReversingAt o (o'.congrModel h) f x ↔ IsOrientationReversingAt o o' f x := by
  subst h
  rw [congrModel_refl]

@[simp]
theorem orientationSign_congrModel_left {I J : ModelWithCorners ℝ E H} (h : I = J)
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I 1 M] [IsManifold J 1 M] [IsManifold I' 1 M']
    (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    orientationSign (o.congrModel h) o' f x = orientationSign o o' f x := by
  subst h
  rw [congrModel_refl]

@[simp]
theorem orientationSign_congrModel_right {I : ModelWithCorners ℝ E H}
    {I' J' : ModelWithCorners ℝ E' H'} (h : I' = J') [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold J' 1 M'] (o : Orientation I M ι) (o' : Orientation I' M' ι) (f : M → M') (x : M) :
    orientationSign o (o'.congrModel h) f x = orientationSign o o' f x := by
  subst h
  rw [congrModel_refl]

end CongrModelMap

theorem isOrientationPreservingAt_id_congrModel {I J : ModelWithCorners ℝ E H} (h : I = J)
    [IsManifold I 1 M] [IsManifold J 1 M] (o : Orientation I M ι) (x : M) :
    IsOrientationPreservingAt o (o.congrModel h) id x := by
  simp

end Manifold.Orientation

/-! ### Transporting lifts and orientations along continuous linear equivalences -/

namespace Manifold.OrientationLift

variable {E F G H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [Fintype ι]

/-- Transport an orientation lift along a continuous linear equivalence `e : E ≃L[ℝ] F` of model
spaces: its model orientation is mapped along `e.toLinearEquiv` and its chart signs are kept
unchanged. -/
def transContinuousLinearEquiv (o : OrientationLift I M ι) (e : E ≃L[ℝ] F) :
    OrientationLift (I.transContinuousLinearEquiv e) M ι where
  modelOrientation := _root_.Orientation.map ι e.toLinearEquiv o.modelOrientation
  card_eq := o.card_eq.trans e.toLinearEquiv.finrank_eq
  sign := o.sign
  locallyConstant_sign := o.locallyConstant_sign
  compatible α β x hα hβ := by
    rw [I.fderivWithin_extChartAt_transContinuousLinearEquiv e α β x]
    have hdet :
        ((e : E →L[ℝ] F) ∘L
          fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I) (extChartAt I α x) ∘L
          (e.symm : F →L[ℝ] E)).det =
          (fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
            (extChartAt I α x)).det :=
      LinearMap.det_conj _ e.toLinearEquiv
    rw [hdet]
    exact o.compatible α β x hα hβ

@[simp]
theorem transContinuousLinearEquiv_modelOrientation (o : OrientationLift I M ι) (e : E ≃L[ℝ] F) :
    (o.transContinuousLinearEquiv e).modelOrientation =
      _root_.Orientation.map ι e.toLinearEquiv o.modelOrientation := (rfl)

@[simp]
theorem transContinuousLinearEquiv_sign (o : OrientationLift I M ι) (e : E ≃L[ℝ] F)
    (α : M) (x : (chartAt H α).source) :
    (o.transContinuousLinearEquiv e).sign α x = o.sign α x := (rfl)

@[simp]
theorem transContinuousLinearEquiv_signAt (o : OrientationLift I M ι) (e : E ≃L[ℝ] F) (α x : M) :
    (o.transContinuousLinearEquiv e).signAt α x = o.signAt α x := by
  by_cases hx : x ∈ (chartAt H α).source <;> simp [hx]

@[simp]
theorem flip_transContinuousLinearEquiv (o : OrientationLift I M ι) (e : E ≃L[ℝ] F) :
    o.flip.transContinuousLinearEquiv e = (o.transContinuousLinearEquiv e).flip := by
  ext α x <;> simp

@[simp]
theorem neg_transContinuousLinearEquiv (o : OrientationLift I M ι) (e : E ≃L[ℝ] F) :
    (-o).transContinuousLinearEquiv e = -(o.transContinuousLinearEquiv e) := by
  ext α x <;> simp

@[simp]
theorem chartOrientation_transContinuousLinearEquiv
    (o : OrientationLift I M ι) (e : E ≃L[ℝ] F) (α : M) (x : (chartAt H α).source) :
    (o.transContinuousLinearEquiv e).chartOrientation α x =
      _root_.Orientation.map ι e.toLinearEquiv (o.chartOrientation α x) := by
  rw [chartOrientation_eq_ite, chartOrientation_eq_ite, transContinuousLinearEquiv_sign,
    transContinuousLinearEquiv_modelOrientation]
  split_ifs <;> simp

@[simp]
theorem ofHasGroupoid_transContinuousLinearEquiv [IsManifold I 1 M]
    [HasGroupoid M (orientationPreservingGroupoid I)]
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = finrank ℝ E) (e : E ≃L[ℝ] F) :
    (ofHasGroupoid (I := I) (M := M) model hι).transContinuousLinearEquiv e =
      ofHasGroupoid (I := I.transContinuousLinearEquiv e) (M := M)
        (_root_.Orientation.map ι e.toLinearEquiv model)
        (hι.trans e.toLinearEquiv.finrank_eq) := by
  ext α x <;> simp

@[simp]
theorem transContinuousLinearEquiv_refl (o : OrientationLift I M ι) :
    (o.transContinuousLinearEquiv (ContinuousLinearEquiv.refl ℝ E)).congrModel
      I.transContinuousLinearEquiv_refl = o := by
  ext α x
  · exact Equiv.ext_iff.mp (_root_.Orientation.map_refl (R := ℝ) (M := E) ι) o.modelOrientation
  · rfl

@[simp]
theorem transContinuousLinearEquiv_trans (o : OrientationLift I M ι) (e : E ≃L[ℝ] F)
    (f : F ≃L[ℝ] G) :
    ((o.transContinuousLinearEquiv e).transContinuousLinearEquiv f).congrModel
      (I.transContinuousLinearEquiv_trans e f) =
      o.transContinuousLinearEquiv (e.trans f) := by
  ext α x
  · exact (_root_.Orientation.map_trans e.toLinearEquiv f.toLinearEquiv o.modelOrientation).symm
  · rfl

end Manifold.OrientationLift

namespace Manifold.Orientation

variable {E F G H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [Fintype ι]

/-- Transport a manifold orientation along a continuous linear equivalence `e : E ≃L[ℝ] F` of
model spaces. -/
def transContinuousLinearEquiv (o : Orientation I M ι) (e : E ≃L[ℝ] F) :
    Orientation (I.transContinuousLinearEquiv e) M ι :=
  o.lift (fun l ↦ mk (l.transContinuousLinearEquiv e)) fun l ↦ by
    rw [OrientationLift.flip_transContinuousLinearEquiv]
    exact (mk_eq_mk_iff _ _).mpr (.inr rfl)

@[simp]
theorem transContinuousLinearEquiv_mk (l : OrientationLift I M ι) (e : E ≃L[ℝ] F) :
    (mk l).transContinuousLinearEquiv e = mk (l.transContinuousLinearEquiv e) := by
  unfold transContinuousLinearEquiv
  rw [lift_mk]

@[simp]
theorem neg_transContinuousLinearEquiv (o : Orientation I M ι) (e : E ≃L[ℝ] F) :
    (-o).transContinuousLinearEquiv e = -(o.transContinuousLinearEquiv e) :=
  o.inductionOn fun l ↦ by
    rw [neg_mk, transContinuousLinearEquiv_mk, transContinuousLinearEquiv_mk, neg_mk,
      OrientationLift.neg_transContinuousLinearEquiv]

@[simp]
theorem model_transContinuousLinearEquiv
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = finrank ℝ E) (e : E ≃L[ℝ] F) :
    (Orientation.model (I := I) model hι).transContinuousLinearEquiv e =
      Orientation.model (I := I.transContinuousLinearEquiv e)
        (_root_.Orientation.map ι e.toLinearEquiv model)
        (hι.trans e.toLinearEquiv.finrank_eq) := by
  rw [model_eq_mk, model_eq_mk, transContinuousLinearEquiv_mk,
    OrientationLift.ofHasGroupoid_transContinuousLinearEquiv]

theorem transContinuousLinearEquiv_congr (o : Orientation I M ι) {e₁ e₂ : E ≃L[ℝ] F}
    (h : e₁ = e₂) :
    (o.transContinuousLinearEquiv e₁).congrModel (congrArg I.transContinuousLinearEquiv h) =
      o.transContinuousLinearEquiv e₂ := by
  subst h
  exact congrModel_refl _

@[simp]
theorem transContinuousLinearEquiv_refl (o : Orientation I M ι) :
    (o.transContinuousLinearEquiv (ContinuousLinearEquiv.refl ℝ E)).congrModel
      I.transContinuousLinearEquiv_refl = o :=
  o.inductionOn fun l ↦ by
    rw [transContinuousLinearEquiv_mk, congrModel_mk,
      OrientationLift.transContinuousLinearEquiv_refl]

@[simp]
theorem transContinuousLinearEquiv_trans (o : Orientation I M ι) (e : E ≃L[ℝ] F) (f : F ≃L[ℝ] G) :
    ((o.transContinuousLinearEquiv e).transContinuousLinearEquiv f).congrModel
      (I.transContinuousLinearEquiv_trans e f) =
      o.transContinuousLinearEquiv (e.trans f) :=
  o.inductionOn fun l ↦ by
    rw [transContinuousLinearEquiv_mk, transContinuousLinearEquiv_mk, congrModel_mk,
      transContinuousLinearEquiv_mk, OrientationLift.transContinuousLinearEquiv_trans]

@[simp]
theorem transContinuousLinearEquiv_symm_self (o : Orientation I M ι) (e : E ≃L[ℝ] F) :
    ((o.transContinuousLinearEquiv e).transContinuousLinearEquiv e.symm).congrModel
      ((I.transContinuousLinearEquiv_trans e e.symm).trans
        ((congrArg I.transContinuousLinearEquiv e.self_trans_symm).trans
          I.transContinuousLinearEquiv_refl)) = o := by
  have h₁ := I.transContinuousLinearEquiv_trans e e.symm
  have h₂ := congrArg I.transContinuousLinearEquiv e.self_trans_symm
  have h₃ := I.transContinuousLinearEquiv_refl
  rw [← congrModel_congrModel h₁ (h₂.trans h₃), transContinuousLinearEquiv_trans,
    ← congrModel_congrModel h₂ h₃, transContinuousLinearEquiv_congr o e.self_trans_symm,
    transContinuousLinearEquiv_refl]

theorem transContinuousLinearEquiv_injective (e : E ≃L[ℝ] F) :
    Function.Injective (fun o : Orientation I M ι ↦ o.transContinuousLinearEquiv e) := by
  intro o₁ o₂ h
  have h' := congrArg (fun o' ↦ (o'.transContinuousLinearEquiv e.symm).congrModel
    ((I.transContinuousLinearEquiv_trans e e.symm).trans
      ((congrArg I.transContinuousLinearEquiv e.self_trans_symm).trans
        I.transContinuousLinearEquiv_refl))) h
  simpa using h'

@[simp]
theorem transContinuousLinearEquiv_inj (e : E ≃L[ℝ] F) {o₁ o₂ : Orientation I M ι} :
    o₁.transContinuousLinearEquiv e = o₂.transContinuousLinearEquiv e ↔ o₁ = o₂ :=
  (transContinuousLinearEquiv_injective e).eq_iff

end Manifold.Orientation

section Orientable

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Orientability is preserved by a continuous linear change of model coordinates. -/
theorem Orientable.transContinuousLinearEquiv (h : Orientable I M) (e : E ≃L[ℝ] F) :
    Orientable (I.transContinuousLinearEquiv e) M := by
  obtain ⟨⟨o⟩⟩ := h
  obtain ⟨l, _⟩ := o.exists_lift
  let l' := l.transContinuousLinearEquiv e
  refine ⟨⟨Manifold.Orientation.mk
    { modelOrientation := _root_.Orientation.reindex ℝ F
        (finCongr e.toLinearEquiv.finrank_eq) l'.modelOrientation
      card_eq := Fintype.card_fin _
      sign := l'.sign
      locallyConstant_sign := l'.locallyConstant_sign
      compatible := l'.compatible }⟩⟩

/-- Orientability is invariant under a continuous linear change of model coordinates. -/
@[simp]
theorem orientable_transContinuousLinearEquiv_iff (I : ModelWithCorners ℝ E H) (e : E ≃L[ℝ] F) :
    Orientable (I.transContinuousLinearEquiv e) M ↔ Orientable I M :=
  ⟨fun h ↦ by
    obtain ⟨⟨o⟩⟩ := h.transContinuousLinearEquiv e.symm
    have hmod : (I.transContinuousLinearEquiv e).transContinuousLinearEquiv e.symm = I := by
      rw [I.transContinuousLinearEquiv_trans, e.self_trans_symm,
        I.transContinuousLinearEquiv_refl]
    exact ⟨⟨o.congrModel hmod⟩⟩,
    fun h ↦ h.transContinuousLinearEquiv e⟩

end Orientable

/-! ### Real recharting preserves the transported orientation -/

namespace Manifold.Orientation

variable {E F H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [Fintype ι]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The manifold derivative of `id : M → M` from `I` to `I.transContinuousLinearEquiv e` at `x`:
`e` itself, read through the tangent-to-model identifications at `x`. -/
private def tangentEquivTrans (I : ModelWithCorners ℝ E H) (e : E ≃L[ℝ] F) (x : M) :
    TangentSpace I x ≃L[ℝ] TangentSpace (I.transContinuousLinearEquiv e) x :=
  ((tangentSpaceCastModel I x).trans e).trans
    (tangentSpaceCastModel (I.transContinuousLinearEquiv e) x).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem hasMFDerivAt_id_transContinuousLinearEquiv (I : ModelWithCorners ℝ E H)
    (e : E ≃L[ℝ] F) (x : M) :
    HasMFDerivAt I (I.transContinuousLinearEquiv e) (id : M → M) x
      (tangentEquivTrans I e x :
        TangentSpace I x →L[ℝ] TangentSpace (I.transContinuousLinearEquiv e) x) := by
  refine ⟨continuousAt_id, ?_⟩
  have hcast :
      (tangentSpaceCastModel (I.transContinuousLinearEquiv e) x : _ →L[ℝ] F) ∘L
        (tangentEquivTrans I e x :
          TangentSpace I x →L[ℝ] TangentSpace (I.transContinuousLinearEquiv e) x) ∘L
        ((tangentSpaceCastModel I x).symm : E →L[ℝ] _) = (e : E →L[ℝ] F) := by
    ext v
    simp [tangentEquivTrans]
  have heq : writtenInExtChartAt I (I.transContinuousLinearEquiv e) x (id : M → M) =ᶠ[
      𝓝[range I] (extChartAt I x x)] e := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
    rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, id_eq, id_eq,
      I.coe_extChartAt_transContinuousLinearEquiv, Function.comp_apply,
      (extChartAt I x).right_inv hy]
  have hx : writtenInExtChartAt I (I.transContinuousLinearEquiv e) x (id : M → M)
      (extChartAt I x x) = e (extChartAt I x x) := by
    rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, id_eq, id_eq,
      I.coe_extChartAt_transContinuousLinearEquiv, Function.comp_apply,
      (extChartAt I x).right_inv (mem_extChartAt_target x)]
  rw [id_eq, hcast]
  exact e.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq hx

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem coe_tangentEquivTrans (I : ModelWithCorners ℝ E H) (e : E ≃L[ℝ] F) (x : M) :
    (tangentEquivTrans I e x :
      TangentSpace I x →L[ℝ] TangentSpace (I.transContinuousLinearEquiv e) x) =
      mfderiv I (I.transContinuousLinearEquiv e) (id : M → M) x :=
  (hasMFDerivAt_id_transContinuousLinearEquiv I e x).mfderiv.symm

variable [IsManifold I 1 M]

private theorem map_tangentEquivTrans_orientationAt (o : Orientation I M ι) (e : E ≃L[ℝ] F)
    (x : M) :
    _root_.Orientation.map ι (tangentEquivTrans I e x).toLinearEquiv (o.orientationAt x) =
      (o.transContinuousLinearEquiv e).orientationAt x := by
  induction o using Orientation.inductionOn with | _ l =>
    rw [transContinuousLinearEquiv_mk, orientationAt_mk, orientationAt_mk,
      l.orientationAt_eq x, (l.transContinuousLinearEquiv e).orientationAt_eq x,
      OrientationLift.chartOrientation_transContinuousLinearEquiv]
    congr 1

/-- The derivative of `id : M → M` from `(M, I)` to `(M, I.transContinuousLinearEquiv e)` carries
each tangent orientation of `o` to that of `o.transContinuousLinearEquiv e`. -/
theorem map_orientationAt_id_transContinuousLinearEquiv (o : Orientation I M ι) (e : E ≃L[ℝ] F)
    (x : M) (D : TangentSpace I x ≃L[ℝ] TangentSpace (I.transContinuousLinearEquiv e) x)
    (hD : (D : TangentSpace I x →L[ℝ] TangentSpace (I.transContinuousLinearEquiv e) x) =
      mfderiv I (I.transContinuousLinearEquiv e) (id : M → M) x) :
    _root_.Orientation.map ι D.toLinearEquiv (o.orientationAt x) =
      (o.transContinuousLinearEquiv e).orientationAt x := by
  have hDeq : D = tangentEquivTrans I e x :=
    ContinuousLinearEquiv.coe_injective (hD.trans (coe_tangentEquivTrans I e x).symm)
  rw [hDeq]
  exact map_tangentEquivTrans_orientationAt o e x

/-- The identity map from `(M, I)` to `(M, I.transContinuousLinearEquiv e)` preserves the
transported orientation at every point, including boundary and corner points. -/
@[simp]
theorem isOrientationPreservingAt_id_transContinuousLinearEquiv (o : Orientation I M ι)
    (e : E ≃L[ℝ] F) (x : M) :
    IsOrientationPreservingAt o (o.transContinuousLinearEquiv e) (id : M → M) x :=
  (isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ (tangentEquivTrans I e x)
    (coe_tangentEquivTrans I e x)).2 (map_tangentEquivTrans_orientationAt o e x)

/-- The identity map from `(M, I.transContinuousLinearEquiv e)` back to `(M, I)` preserves
orientation from `o.transContinuousLinearEquiv e` to `o`. -/
@[simp]
theorem isOrientationPreservingAt_id_transContinuousLinearEquiv_symm
    (o : Orientation I M ι) (e : E ≃L[ℝ] F) (x : M) :
    IsOrientationPreservingAt (o.transContinuousLinearEquiv e) o (id : M → M) x := by
  have hcomp :
      IsOrientationPreservingAt (o.transContinuousLinearEquiv e) (o.transContinuousLinearEquiv e)
        ((id : M → M) ∘ (id : M → M)) x := by
    simp
  have hid_symm : MDifferentiableAt (I.transContinuousLinearEquiv e) I (id : M → M) x := by
    have h := (hasMFDerivAt_id_transContinuousLinearEquiv
      (I.transContinuousLinearEquiv e) e.symm x).mdifferentiableAt
    rwa [I.transContinuousLinearEquiv_trans, e.self_trans_symm,
      I.transContinuousLinearEquiv_refl] at h
  exact (isOrientationPreservingAt_id_transContinuousLinearEquiv o e x).of_comp hcomp hid_symm

/-- The orientation sign of `id : M → M` from `o` to `o.transContinuousLinearEquiv e` is `1`. -/
@[simp]
theorem orientationSign_id_transContinuousLinearEquiv (o : Orientation I M ι) (e : E ≃L[ℝ] F)
    (x : M) :
    orientationSign o (o.transContinuousLinearEquiv e) (id : M → M) x = 1 :=
  orientationSign_of_isOrientationPreservingAt
    (isOrientationPreservingAt_id_transContinuousLinearEquiv o e x)

/-- `o.transContinuousLinearEquiv e` is the unique orientation of
`(M, I.transContinuousLinearEquiv e)` from which `id : M → M` preserves orientation everywhere. -/
theorem eq_transContinuousLinearEquiv_iff_id (o : Orientation I M ι) (e : E ≃L[ℝ] F)
    {o' : Orientation (I.transContinuousLinearEquiv e) M ι} :
    o' = o.transContinuousLinearEquiv e ↔
      ∀ x, IsOrientationPreservingAt o o' (id : M → M) x := by
  refine ⟨fun h ↦ h ▸ isOrientationPreservingAt_id_transContinuousLinearEquiv o e, fun h ↦ ?_⟩
  ext x
  exact (h x).orientationAt_eq (isOrientationPreservingAt_id_transContinuousLinearEquiv o e x)

end Manifold.Orientation

/-! ### Compatibility with oriented atlases and sign of the real determinant -/

section AtlasAndSign

variable {E F H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω} [NeZero n] [Fintype ι]

/-- Transporting the manifold orientation determined by an oriented atlas `A` and a model
orientation `model` along `e : E ≃L[ℝ] F` gives the manifold orientation determined by `A` (as an
oriented atlas for `I.transContinuousLinearEquiv e`) and `Orientation.map ι e.toLinearEquiv model`.
-/
theorem IsOrientedAtlas.orientation_transContinuousLinearEquiv
    {A : Set (OpenPartialHomeomorph M H)} (hA : IsOrientedAtlas I n A)
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = finrank ℝ E) (e : E ≃L[ℝ] F) :
    (hA.orientation model hι).transContinuousLinearEquiv e =
      ((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation
        (_root_.Orientation.map ι e.toLinearEquiv model)
        (hι.trans e.toLinearEquiv.finrank_eq) := by
  let hAe := (isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA
  let hι' := hι.trans e.toLinearEquiv.finrank_eq
  symm
  rw [Manifold.Orientation.eq_transContinuousLinearEquiv_iff_id]
  intro x
  obtain ⟨φ, hφ, hx⟩ := hA.exists_mem_source x
  obtain ⟨L, hL, hmap⟩ := hA.orientation_spec model hι hφ hx
  obtain ⟨L', hL', hmap'⟩ :=
    hAe.orientation_spec (_root_.Orientation.map ι e.toLinearEquiv model) hι' hφ hx
  have hφd : MDifferentiableAt I I φ x := mdifferentiableAt_of_isInvertible_mfderiv ⟨L, hL⟩
  have hφd' : MDifferentiableAt (I.transContinuousLinearEquiv e)
      (I.transContinuousLinearEquiv e) φ x :=
    mdifferentiableAt_of_isInvertible_mfderiv ⟨L', hL'⟩
  have hidM := Manifold.Orientation.hasMFDerivAt_id_transContinuousLinearEquiv I e x
  have hidH := Manifold.Orientation.hasMFDerivAt_id_transContinuousLinearEquiv I e (φ x)
  have hcomm :
      mfderiv I (I.transContinuousLinearEquiv e) ((id : H → H) ∘ φ) x =
        mfderiv I (I.transContinuousLinearEquiv e) (φ ∘ (id : M → M)) x := rfl
  rw [mfderiv_comp x hidH.mdifferentiableAt hφd, hidH.mfderiv,
    mfderiv_comp x hφd' hidM.mdifferentiableAt, hidM.mfderiv, id_eq] at hcomm
  have hLeq :
      ((Manifold.Orientation.tangentEquivTrans I e x).trans L').toLinearEquiv =
        L.toLinearEquiv.trans e.toLinearEquiv := by
    ext v
    have hv := congrArg (fun T ↦ T v) hcomm
    set w := Manifold.Orientation.tangentEquivTrans I e x v
    have hLv : (tangentSpaceCastModel I (φ x)) (mfderiv I I φ x v) = L v :=
      congrArg (fun f : TangentSpace I x →L[ℝ] E ↦ f v) hL.symm
    have hL'v :
        (tangentSpaceCastModel (I.transContinuousLinearEquiv e) (φ x))
          (mfderiv (I.transContinuousLinearEquiv e) (I.transContinuousLinearEquiv e) φ x w) =
          L' w :=
      congrArg (fun f : TangentSpace (I.transContinuousLinearEquiv e) x →L[ℝ] F ↦ f w) hL'.symm
    have hv' := congrArg (tangentSpaceCastModel (I.transContinuousLinearEquiv e) (φ x)) hv
    dsimp only [id_eq] at hv'
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe] at hv'
    have hw : Manifold.Orientation.tangentEquivTrans I e x v = w := rfl
    rw [hw] at hv'
    simp only [Manifold.Orientation.tangentEquivTrans, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply] at hv'
    rw [hLv, hL'v] at hv'
    exact hv'.symm
  refine (Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq _ _ _ _
    (Manifold.Orientation.tangentEquivTrans I e x)
    (Manifold.Orientation.coe_tangentEquivTrans I e x)).2 ?_
  rw [id_eq]
  apply (_root_.Orientation.map ι L'.toLinearEquiv).injective
  rw [← _root_.Orientation.map_trans, ← ContinuousLinearEquiv.trans_toLinearEquiv, hLeq,
    _root_.Orientation.map_trans, hmap, hmap']

section SelfEquiv

/-- When `e : E ≃L[ℝ] E` has positive determinant, transporting the orientation of an oriented
atlas with model orientation `model` gives the orientation of that atlas for the same fixed model
orientation `model`. -/
theorem IsOrientedAtlas.orientation_transContinuousLinearEquiv_eq_of_det_pos
    {A : Set (OpenPartialHomeomorph M H)} (hA : IsOrientedAtlas I n A)
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = finrank ℝ E) {e : E ≃L[ℝ] E}
    (he : 0 < LinearMap.det (e : E →ₗ[ℝ] E)) :
    (hA.orientation model hι).transContinuousLinearEquiv e =
      ((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation model hι := by
  rw [hA.orientation_transContinuousLinearEquiv model hι e]
  congr 1
  exact (_root_.Orientation.map_eq_iff_det_pos model e.toLinearEquiv hι).2 he

/-- When `e : E ≃L[ℝ] E` has negative determinant, transporting the orientation of an oriented
atlas with model orientation `model` gives the opposite of the orientation of that atlas for the
fixed model orientation `model`. -/
theorem IsOrientedAtlas.orientation_transContinuousLinearEquiv_eq_neg_of_det_neg
    {A : Set (OpenPartialHomeomorph M H)} (hA : IsOrientedAtlas I n A)
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = finrank ℝ E) {e : E ≃L[ℝ] E}
    (he : LinearMap.det (e : E →ₗ[ℝ] E) < 0) :
    (hA.orientation model hι).transContinuousLinearEquiv e =
      -((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation model hι := by
  rw [hA.orientation_transContinuousLinearEquiv model hι e,
    (_root_.Orientation.map_eq_neg_iff_det_neg model e.toLinearEquiv hι).2 he,
    IsOrientedAtlas.orientation_neg]

/-- Against a separately fixed model orientation `model` on `E`, `toTransContinuousLinearEquiv`
preserves orientation when `0 < LinearMap.det e`. -/
theorem IsOrientedAtlas.isOrientationPreservingAt_toTransContinuousLinearEquiv_of_det_pos
    {m : ℕ∞ω} {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = finrank ℝ E) {e : E ≃L[ℝ] E}
    (he : 0 < LinearMap.det (e : E →ₗ[ℝ] E)) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (hA.orientation model hι)
      (((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation model hι)
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m) I M e) x := by
  rw [← hA.orientation_transContinuousLinearEquiv_eq_of_det_pos model hι he]
  exact Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv _ e x

/-- Against a separately fixed model orientation `model` on `E`, `toTransContinuousLinearEquiv`
reverses orientation when `LinearMap.det e < 0`. -/
theorem IsOrientedAtlas.isOrientationReversingAt_toTransContinuousLinearEquiv_of_det_neg
    {m : ℕ∞ω} {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = finrank ℝ E) {e : E ≃L[ℝ] E}
    (he : LinearMap.det (e : E →ₗ[ℝ] E) < 0) (x : M) :
    Manifold.Orientation.IsOrientationReversingAt (hA.orientation model hι)
      (((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation model hι)
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m) I M e) x := by
  rw [← Manifold.Orientation.isOrientationPreservingAt_neg_right,
    ← hA.orientation_transContinuousLinearEquiv_eq_neg_of_det_neg model hι he]
  exact Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv _ e x

/-- Against a separately fixed model orientation `model` on `E`, the orientation sign of
`toTransContinuousLinearEquiv` at every point is the sign of the real determinant of `e`. -/
theorem IsOrientedAtlas.orientationSign_toTransContinuousLinearEquiv
    {m : ℕ∞ω} {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (model : _root_.Orientation ℝ E ι)
    (hι : Fintype.card ι = finrank ℝ E) (e : E ≃L[ℝ] E) (x : M) :
    Manifold.Orientation.orientationSign (hA.orientation model hι)
        (((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation model hι)
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m) I M e) x =
      (SignType.sign (LinearMap.det (e : E →ₗ[ℝ] E)) : ℤ) := by
  rcases lt_or_gt_of_ne e.toLinearEquiv.isUnit_det'.ne_zero with hneg | hpos
  · rw [Manifold.Orientation.orientationSign_of_isOrientationReversingAt
      (hA.isOrientationReversingAt_toTransContinuousLinearEquiv_of_det_neg model hι hneg x),
      sign_neg hneg, SignType.coe_neg, SignType.coe_one]
  · rw [Manifold.Orientation.orientationSign_of_isOrientationPreservingAt
      (hA.isOrientationPreservingAt_toTransContinuousLinearEquiv_of_det_pos model hι hpos x),
      sign_pos hpos, SignType.coe_one]

/-- When the given atlas is oriented, comparing the orientations represented by `ofHasGroupoid`
with the same fixed model orientation `model` before and after recharting along `e : E ≃L[ℝ] E` has
orientation sign equal to the sign of `LinearMap.det e`. -/
theorem Manifold.OrientationLift.orientationSign_toTransContinuousLinearEquiv_ofHasGroupoid
    {m : ℕ∞ω} [HasGroupoid M (orientationPreservingGroupoid I)]
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = finrank ℝ E)
    (e : E ≃L[ℝ] E) (x : M) :
    Manifold.Orientation.orientationSign
        (Manifold.Orientation.mk (ofHasGroupoid (I := I) (M := M) model hι))
        (Manifold.Orientation.mk
          (ofHasGroupoid (I := I.transContinuousLinearEquiv e) (M := M) model hι))
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m) I M e) x =
      (SignType.sign (LinearMap.det (e : E →ₗ[ℝ] E)) : ℤ) := by
  rw [mk_ofHasGroupoid, mk_ofHasGroupoid]
  exact (isOrientedAtlas_atlas I 1 M).orientationSign_toTransContinuousLinearEquiv model hι e x

end SelfEquiv

section BasisSign

variable [DecidableEq ι]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem det_map_basis_eq_det_toMatrix (bE : Module.Basis ι ℝ E) (bF : Module.Basis ι ℝ F)
    (e : E ≃L[ℝ] F) :
    bF.det (bE.map e.toLinearEquiv) = (LinearMap.toMatrix bE bF (e : E →ₗ[ℝ] F)).det := by
  rw [Module.Basis.det_apply]
  congr 1
  ext i j
  simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]

/-- Given bases `bE` of `E` and `bF` of `F`, `toTransContinuousLinearEquiv` along `e : E ≃L[ℝ] F`
preserves the orientations determined by `bE.orientation` and `bF.orientation` when the matrix of
`e` in those bases has positive determinant. -/
theorem IsOrientedAtlas.isOrientationPreservingAt_toTransContinuousLinearEquiv_basis_of_det_pos
    {m : ℕ∞ω} {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (bE : Module.Basis ι ℝ E) (bF : Module.Basis ι ℝ F)
    {e : E ≃L[ℝ] F} (he : 0 < (LinearMap.toMatrix bE bF (e : E →ₗ[ℝ] F)).det) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt
      (hA.orientation bE.orientation (finrank_eq_card_basis bE).symm)
      (((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation
        bF.orientation (finrank_eq_card_basis bF).symm)
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m) I M e) x := by
  have hmap : _root_.Orientation.map ι e.toLinearEquiv bE.orientation = bF.orientation := by
    rw [← Module.Basis.orientation_map, eq_comm, bF.orientation_eq_iff_det_pos,
      det_map_basis_eq_det_toMatrix]
    exact he
  have ho :
      ((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation
          bF.orientation (finrank_eq_card_basis bF).symm =
        (hA.orientation bE.orientation (finrank_eq_card_basis bE).symm).transContinuousLinearEquiv
          e := by
    rw [hA.orientation_transContinuousLinearEquiv]
    congr 1
    exact hmap.symm
  rw [ho]
  exact Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv _ e x

/-- Given bases `bE` of `E` and `bF` of `F`, `toTransContinuousLinearEquiv` along `e : E ≃L[ℝ] F`
reverses the orientations determined by `bE.orientation` and `bF.orientation` when the matrix of
`e` in those bases has negative determinant. -/
theorem IsOrientedAtlas.isOrientationReversingAt_toTransContinuousLinearEquiv_basis_of_det_neg
    {m : ℕ∞ω} {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (bE : Module.Basis ι ℝ E) (bF : Module.Basis ι ℝ F)
    {e : E ≃L[ℝ] F} (he : (LinearMap.toMatrix bE bF (e : E →ₗ[ℝ] F)).det < 0) (x : M) :
    Manifold.Orientation.IsOrientationReversingAt
      (hA.orientation bE.orientation (finrank_eq_card_basis bE).symm)
      (((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation
        bF.orientation (finrank_eq_card_basis bF).symm)
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m) I M e) x := by
  have hmap : _root_.Orientation.map ι e.toLinearEquiv bE.orientation = -bF.orientation := by
    rw [← Module.Basis.orientation_map, ← bF.orientation_ne_iff_eq_neg, ne_comm, ne_eq,
      bF.orientation_eq_iff_det_pos, det_map_basis_eq_det_toMatrix]
    exact not_lt.2 he.le
  have ho :
      -((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation
          bF.orientation (finrank_eq_card_basis bF).symm =
        (hA.orientation bE.orientation (finrank_eq_card_basis bE).symm).transContinuousLinearEquiv
          e := by
    rw [hA.orientation_transContinuousLinearEquiv, ← IsOrientedAtlas.orientation_neg]
    congr 1
    exact hmap.symm
  rw [← Manifold.Orientation.isOrientationPreservingAt_neg_right, ho]
  exact Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv _ e x

/-- Given bases `bE` of `E` and `bF` of `F`, the orientation sign of `toTransContinuousLinearEquiv`
between the orientations determined by `bE.orientation` and `bF.orientation` equals the sign of
`(LinearMap.toMatrix bE bF e).det`. -/
theorem IsOrientedAtlas.orientationSign_toTransContinuousLinearEquiv_basis
    {m : ℕ∞ω} {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (bE : Module.Basis ι ℝ E) (bF : Module.Basis ι ℝ F)
    (e : E ≃L[ℝ] F) (x : M) :
    Manifold.Orientation.orientationSign
        (hA.orientation bE.orientation (finrank_eq_card_basis bE).symm)
        (((isOrientedAtlas_transContinuousLinearEquiv_iff I n e).2 hA).orientation
          bF.orientation (finrank_eq_card_basis bF).symm)
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m) I M e) x =
      (SignType.sign (LinearMap.toMatrix bE bF (e : E →ₗ[ℝ] F)).det : ℤ) := by
  have hunit : IsUnit (LinearMap.toMatrix bE bF (e : E →ₗ[ℝ] F)).det :=
    e.toLinearEquiv.isUnit_det bE bF
  rcases lt_or_gt_of_ne hunit.ne_zero with hneg | hpos
  · rw [Manifold.Orientation.orientationSign_of_isOrientationReversingAt
      (hA.isOrientationReversingAt_toTransContinuousLinearEquiv_basis_of_det_neg bE bF hneg x),
      sign_neg hneg, SignType.coe_neg, SignType.coe_one]
  · rw [Manifold.Orientation.orientationSign_of_isOrientationPreservingAt
      (hA.isOrientationPreservingAt_toTransContinuousLinearEquiv_basis_of_det_pos bE bF hpos x),
      sign_pos hpos, SignType.coe_one]

end BasisSign

end AtlasAndSign

end TauCeti
