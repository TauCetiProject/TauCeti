/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.AlgebraicGeometry.BaseChangeSection
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
import TauCeti.AlgebraicGeometry.RationalPoint.AffineSpace
import TauCeti.FieldTheory.IsSepClosed

/-!
# Rational points on smooth schemes over separably closed fields

Rational points are dense on a smooth scheme over a separably closed field. The proof uses
étale charts over affine space and lifting of geometric points along étale morphisms.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Rational sections of a smooth scheme over a separably closed field have dense image. -/
theorem denseRange_rationalSections {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] :
    DenseRange fun s : {s : Spec (.of k) ⟶ X // s ≫ f = 𝟙 _} ↦ s.val default := by
  refine dense_iff_inter_open.mpr fun U hU ⟨x, hx⟩ ↦ ?_
  obtain ⟨V, _, hxV, n, g, hg, hgf⟩ := Smooth.exists_etale_affineSpace f x
  let W : Set V.toScheme := V.ι ⁻¹' U
  obtain ⟨t, ht, y, hy, hyt⟩ :=
    AffineSpace.exists_rationalPoint_mem_open (ULift.{u} (Fin n)) (g '' W)
    (g.isOpenMap _ (hU.preimage V.ι.continuous)) ⟨_, ⟨⟨x, hxV⟩, hx, rfl⟩⟩
  obtain ⟨s, hs, hsy⟩ := Scheme.exists_fac_of_etale_of_isSepClosed g t y
    (hyt.trans (congrArg t (Subsingleton.elim _ _)))
  refine ⟨V.ι y, hy, ⟨s ≫ V.ι, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hgf, ← Category.assoc, hs, ht]
  · exact (Scheme.Hom.comp_apply s V.ι default).trans (congrArg V.ι hsy)

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

/-- Ground-field rational sections remain dense after an arbitrary extension of a separably
closed field. The points are the actual base changes of sections of the original scheme. -/
theorem denseRange_baseChangeSections {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] :
    DenseRange fun s : {s : Spec (.of k) ⟶ X // s ≫ f = 𝟙 _} ↦
      baseChangeSection f s.val s.property
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (default : Spec (.of K)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine dense_iff_inter_open.mpr fun U hU hne ↦ ?_
  obtain ⟨s, y, hy, hys⟩ := (Scheme.Hom.denseRange_rationalSections f).exists_mem_open
    ((pullback.snd g f).isOpenMap _ hU) (hne.image _)
  refine ⟨_, ?_, s, rfl⟩
  -- The density witness is a subtype evaluation; identify it with the section in the fiber law.
  change baseChangeSection f s.val s.property
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (default : Spec (.of K)) ∈ U
  rw [baseChangeSection_eq_of_snd_eq f s.val s.property g default hys]
  exact hy

end TauCeti.AlgebraicGeometry
