/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation
import TauCeti.AlgebraicGeometry.Modules.Dual
import TauCeti.AlgebraicGeometry.Modules.Sections
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RationalPoint

/-!
# Nonvanishing sections at points descended from the ground field

A line bundle on a base-changed smooth scheme over a separably closed field, with a nonzero
global section, has a dual functional nonvanishing at a point descended from the ground field.
The scheme need not be connected or proper, and its space of global sections may be infinite.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

noncomputable section

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [Smooth (X ↘ Spec (.of k))]

/-- A line bundle with a nonzero global section after a field extension has a
nonzero dual functional whose nonvanishing locus meets a point descended from the separably
closed ground field. Connectedness, properness and finite-dimensionality are not required. -/
theorem exists_groundField_section_avoiding_image
    (K : Type u) [Field K] [Algebra k K]
    (N : InvertibleSheaf
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (X ↘ Spec (.of k)))) :
    let _ : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (X ↘ Spec (.of k))).Over (Spec (.of K)) := ⟨Limits.pullback.fst _ _⟩
    Nontrivial (Cohomology N.obj 0) →
    ∃ (φ : (dual N).obj ⟶ 𝟙_ (Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) (X ↘ Spec (.of k))).Modules)
      (p : {p : Spec (.of k) ⟶ X // p ≫ X ↘ Spec (.of k) = 𝟙 _}),
      baseChangeSection (X ↘ Spec (.of k)) p.val p.property
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (default : Spec (.of K)) ∉ φ.imageIdealSheaf.support := by
  let f := X ↘ Spec (.of k)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := Limits.pullback g f
  let _ : Y.Over (Spec (.of K)) := ⟨Limits.pullback.fst g f⟩
  have : Smooth (Y ↘ Spec (.of K)) :=
    inferInstanceAs (Smooth (Limits.pullback.fst g f))
  have : IsReduced Y := (Y ↘ Spec (.of K)).isReduced_of_smooth
  dsimp only
  intro hnontrivial
  have : Nontrivial (Cohomology N.obj 0) := hnontrivial
  let E : _root_.SheafOfModules Y.ringCatSheaf := N.obj
  have : N.obj.IsLocallyFree := inferInstanceAs E.IsLocallyFree
  have : N.obj.IsFiniteType := inferInstanceAs E.IsFiniteType
  have : Nontrivial Γ(N.obj, ⊤) := (cohomologyZeroBaseLinearEquiv K Y N.obj).symm.toEquiv.nontrivial
  let eD : (dual N).obj ≅ (ihom N.obj).obj (𝟙_ Y.Modules) := eqToIso (dual_obj N)
  let e : ((dual N).obj ⟶ 𝟙_ Y.Modules) ≃ Γ(N.obj, ⊤) :=
    (eD.homCongr (Iso.refl _)).trans
      ((dualHomUnitEquiv N.obj).trans N.obj.unitHomEquivTop)
  have : Nontrivial ((dual N).obj ⟶ 𝟙_ Y.Modules) := e.nontrivial
  obtain ⟨φ, hφ⟩ := exists_ne (0 : (dual N).obj ⟶ 𝟙_ Y.Modules)
  obtain ⟨p, hpφ⟩ := (denseRange_baseChangeSections (K := K) f).exists_mem_open
    φ.imageIdealSheaf.support.isClosed.isOpen_compl
    (φ.nonempty_compl_support_imageIdealSheaf hφ)
  exact ⟨φ, p, hpφ⟩

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf
