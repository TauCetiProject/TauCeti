/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.FinitePresentation
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.PullbackHom
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of bundle maps through inverse limits

Morphisms between pullbacks of finite locally free modules descend along cofiltered limits of
quasi-compact quasi-separated schemes with affine transitions. The geometric argument applies
Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` to the total space
representing bundle maps (`totalSpaceIhomHomEquiv`). See the Stacks Project, Lemma 32.10.2
(Tag 01ZR), part (2).
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalClosed Opposite

namespace CategoryTheory.Limits.IsLimit

open TauCeti.AlgebraicGeometry Scheme.Modules

universe u

local notation "PB" => Scheme.Modules.pullback

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  {c : Cone D} (hc : IsLimit c)

include hc in
/-- A morphism between pullbacks of finite locally free sheaves along a projection of a
cofiltered limit of qcqs schemes with affine transitions descends to a refinement of that
stage. The last equality uses the canonical composite-pullback comparison. -/
theorem exists_pullback_map_eq_of_finiteLocallyFree [∀ i, QuasiSeparatedSpace (D.obj i)]
    {i : I} (E F : FiniteLocallyFreeSheaf (D.obj i))
    (a : (PB (c.π.app i)).obj E.obj ⟶ (PB (c.π.app i)).obj F.obj) :
    ∃ (j : I) (f : j ⟶ i)
      (b : (PB (D.map f)).obj E.obj ⟶ (PB (D.map f)).obj F.obj),
      let e := pullbackComp (c.π.app j) (D.map f) ≪≫ pullbackCongr (c.w f)
      e.inv.app E.obj ≫ (PB (c.π.app j)).map b ≫ e.hom.app F.obj = a := by
  let V := (totalSpaceScheme (D.obj i)).obj ((ihom E).obj F)
  let V' := (MorphismProperty.Over.forget @IsAffineHom ⊤ (D.obj i)).obj V
  let B := FiniteLocallyFreeSheaf.dual ((ihom E).obj F)
  let Q := (FiniteLocallyFreeSheaf.toQuasicoherent _).obj B
  have hQ : Q.obj.IsFinitePresentation :=
    (FiniteLocallyFreeSheaf.toQuasicoherent_obj_obj _ B).symm ▸
      B.property.2
  have hV : LocallyOfFinitePresentation V.hom :=
    @locallyOfFinitePresentation_relativeSpecSymmetricAlgebra _ Q hQ
  have {j k : Over i} (f : j ⟶ k) : IsAffineHom ((Over.forget i ⋙ D).map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left))
  have (j : Over i) : CompactSpace ((Over.forget i ⋙ D).obj j) :=
    inferInstanceAs (CompactSpace (D.obj j.left))
  have (j : Over i) : QuasiSeparatedSpace ((Over.forget i ⋙ D).obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  let q : Over.forget i ⋙ D ⟶ (Functor.const _).obj (D.obj i) :=
    { app j := D.map j.hom
      naturality j k f := by simp [← D.map_comp] }
  let s := (totalSpaceIhomHomEquiv E F (Over.mk (c.π.app i))).symm a
  have hs : (c.whisker (Over.forget i)).π ≫ q = (Functor.const _).map (s.left ≫ V.hom) := by
    ext j
    exact (c.w j.hom).trans (Over.w s).symm
  obtain ⟨j, b, hb, hb'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (Over.forget i ⋙ D) q V.hom _
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc) s.left hs
  let b' : Over.mk (D.map j.hom) ⟶ V' := Over.homMk b hb'
  refine ⟨j.left, j.hom, totalSpaceIhomHomEquiv E F (Over.mk (D.map j.hom)) b', ?_⟩
  have hbs : Over.homMk (V := Over.mk (D.map j.hom)) (c.π.app j.left) (c.w j.hom) ≫ b' = s :=
    Over.OverMorphism.ext hb
  exact (totalSpaceIhomHomEquiv_comp E F _ _ (c.w j.hom) b').symm.trans
    ((congrArg (totalSpaceIhomHomEquiv E F _) hbs).trans (Equiv.apply_symm_apply _ _))

end CategoryTheory.Limits.IsLimit
