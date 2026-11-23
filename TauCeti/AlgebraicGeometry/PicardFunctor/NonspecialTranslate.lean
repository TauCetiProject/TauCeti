/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NonspecialTwist
public import TauCeti.AlgebraicGeometry.PicardFunctor.Relative

/-!
# Ground-field translates of nonspecial field-valued Picard classes

For a smooth proper geometrically connected curve over a separably closed field, every
field-valued point of the relative Picard presheaf has a ground-field translate represented by
a line bundle with one global section and vanishing first cohomology. This is a statement
about field-valued classes; it does not assert representability or openness of a chart.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Module (finrank)

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyConnected (X ↘ Spec (.of k))]

/-- Every field-valued class of the relative Picard presheaf has a translate by a line bundle
from the ground-field curve with exactly one global section and vanishing first cohomology. -/
theorem exists_nonspecial_groundField_translate (K : Type u) [Field K] [Algebra k K]
    (a : (relativePicardPresheaf (X ↘ Spec (.of k))).obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    let _ : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (X ↘ Spec (.of k))).Over (Spec (.of K)) := ⟨pullback.fst _ _⟩
    ∃ (M : InvertibleSheaf X)
      (N : InvertibleSheaf
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (X ↘ Spec (.of k)))),
      finrank K (Scheme.Modules.Cohomology N.obj 0) = 1 ∧
      Subsingleton (Scheme.Modules.Cohomology N.obj 1) ∧
      (QuotientGroup.mk (LineBundleClass.mk N) : (relativePicardPresheaf
        (X ↘ Spec (.of k))).obj (op (Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) =
        Mul.mul (α := (relativePicardPresheaf (X ↘ Spec (.of k))).obj (op (Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) a (QuotientGroup.mk
          (LineBundleClass.pullback
            (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              (X ↘ Spec (.of k))) (LineBundleClass.mk M))) := by
  let _ : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (X ↘ Spec (.of k))).Over (Spec (.of K)) := ⟨pullback.fst _ _⟩
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective b
  obtain ⟨M, hdim, hvan⟩ := InvertibleSheaf.exists_groundField_nonspecial_twist K L
  refine ⟨M, InvertibleSheaf.tensorProduct L
    ((InvertibleSheaf.pullback (pullback.snd _ _)).obj M), hdim, hvan, ?_⟩
  rw [LineBundleClass.mk_tensorProduct, QuotientGroup.mk_mul, LineBundleClass.pullback_mk]
  rfl

end

end TauCeti.AlgebraicGeometry
