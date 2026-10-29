/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.DirectSum
public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra

/-!
# Pullback of the symmetric algebra

For a morphism of schemes `f : X ⟶ Y` and a quasicoherent sheaf `F` on `Y`, the pullback of the
symmetric algebra of `F` is the symmetric algebra of the pullback of `F`:

`f^* (Sym F) ≅ Sym (f^* F)`

as quasicoherent commutative `𝒪_X`-algebras, naturally in `F`.

Both sides are free constructions with the same universal property. Algebra maps
`f^* (Sym F) ⟶ B` into a commutative `𝒪_X`-algebra `B` are algebra maps `Sym F ⟶ f_* B`
(`QuasicoherentAlgebra.pullbackHomEquiv`), hence module maps `F ⟶ f_* B`
(`symmetricAlgebraHomEquiv`). Algebra maps `Sym (f^* F) ⟶ B` are module maps `f^* F ⟶ B`, hence
module maps `F ⟶ f_* B` by the pullback–pushforward adjunction. The two bijections are natural in
`B`, and the isomorphism is the one they induce. On generators it is the pullback of the
inclusion `F ⟶ Sym F` (`symmetricAlgebraι_comp_pullbackSymmetricAlgebraIso_inv`).

## Main declarations

* `TauCeti.AlgebraicGeometry.pullbackSymmetricAlgebraIso`: the isomorphism
  `f^* (Sym F) ≅ Sym (f^* F)` of quasicoherent algebras;
* `TauCeti.AlgebraicGeometry.symmetricAlgebraι_comp_pullbackSymmetricAlgebraIso_inv` and
  `TauCeti.AlgebraicGeometry.pullback_map_symmetricAlgebraι_comp_pullbackSymmetricAlgebraIso_hom`:
  on generators it identifies the pullback of the inclusion `F ⟶ Sym F` with the inclusion
  `f^* F ⟶ Sym (f^* F)`;
* `TauCeti.AlgebraicGeometry.pullbackSymmetricAlgebraNatIso`: the isomorphism is natural in `F`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : QuasicoherentSheaf Y)

/-- Algebra maps `f^* (Sym F) ⟶ B` are module maps `F ⟶ f_* B`. -/
private def pullbackSymmetricAlgebraHomEquiv (B : CommMon X.Modules) :
    (((QuasicoherentAlgebra.pullback f).obj ((symmetricAlgebra Y).obj F)).obj ⟶ B) ≃
      (F.obj ⟶ (Scheme.Modules.pushforward f).obj B.X) :=
  (QuasicoherentAlgebra.pullbackHomEquiv f _ B).trans (symmetricAlgebraHomEquiv F _)

/-- Algebra maps `Sym (f^* F) ⟶ B` are module maps `F ⟶ f_* B`. -/
private def symmetricAlgebraPullbackHomEquiv (B : CommMon X.Modules) :
    (((symmetricAlgebra X).obj ((QuasicoherentSheaf.pullback f).obj F)).obj ⟶ B) ≃
      (F.obj ⟶ (Scheme.Modules.pushforward f).obj B.X) :=
  ((symmetricAlgebraHomEquiv _ B).trans
    (eqToIso (QuasicoherentSheaf.pullback_obj_obj f F)).homFromEquiv).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)

-- The composites in the next two proofs are typed partly in `SheafOfModules _.ringCatSheaf` and
-- partly in `_.Modules`, which `rw` and `simp` do not identify; they are chains of equations.
private lemma pullbackSymmetricAlgebraHomEquiv_comp {B B' : CommMon X.Modules}
    (g : ((QuasicoherentAlgebra.pullback f).obj ((symmetricAlgebra Y).obj F)).obj ⟶ B)
    (b : B ⟶ B') :
    pullbackSymmetricAlgebraHomEquiv f F B' (g ≫ b) =
      pullbackSymmetricAlgebraHomEquiv f F B g ≫ (Scheme.Modules.pushforward f).map b.hom.hom :=
  (symmetricAlgebraHomEquiv_apply _).trans <|
    ((congrArg (fun φ ↦ symmetricAlgebraι F ≫ φ.hom.hom)
      (QuasicoherentAlgebra.pullbackHomEquiv_naturality_right f _ g b)).trans
        (Category.assoc _ _ _).symm).trans
      (congrArg (· ≫ (Scheme.Modules.pushforward f).map b.hom.hom)
        (symmetricAlgebraHomEquiv_apply _).symm)

private lemma symmetricAlgebraPullbackHomEquiv_comp {B B' : CommMon X.Modules}
    (g : ((symmetricAlgebra X).obj ((QuasicoherentSheaf.pullback f).obj F)).obj ⟶ B)
    (b : B ⟶ B') :
    symmetricAlgebraPullbackHomEquiv f F B' (g ≫ b) =
      symmetricAlgebraPullbackHomEquiv f F B g ≫ (Scheme.Modules.pushforward f).map b.hom.hom := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := eqToHom (QuasicoherentSheaf.pullback_obj_obj f F).symm
  have h : e ≫ symmetricAlgebraHomEquiv _ B' (g ≫ b) =
      (e ≫ symmetricAlgebraHomEquiv _ B g) ≫ b.hom.hom :=
    ((congrArg (e ≫ ·) (symmetricAlgebraHomEquiv_apply _)).trans
      ((congrArg (e ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)).trans
      (congrArg (fun x ↦ (e ≫ x) ≫ b.hom.hom) (symmetricAlgebraHomEquiv_apply _).symm)
  exact (congrArg (A.homEquiv _ _) h).trans (A.homEquiv_naturality_right _ _)

private lemma pullbackSymmetricAlgebraHomEquiv_naturality {F' : QuasicoherentSheaf Y}
    (g : F' ⟶ F) {B : CommMon X.Modules}
    (h : ((QuasicoherentAlgebra.pullback f).obj ((symmetricAlgebra Y).obj F)).obj ⟶ B) :
    pullbackSymmetricAlgebraHomEquiv f F' B
        (((QuasicoherentAlgebra.pullback f).map ((symmetricAlgebra Y).map g)).hom ≫ h) =
      g.hom ≫ pullbackSymmetricAlgebraHomEquiv f F B h :=
  (symmetricAlgebraHomEquiv_apply _).trans <|
    (congrArg (fun φ ↦ symmetricAlgebraι F' ≫ φ.hom.hom)
      (QuasicoherentAlgebra.pullbackHomEquiv_naturality_left f _ B h)).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) (symmetricAlgebraι_naturality g).symm).trans <|
          (Category.assoc _ _ _).trans
            (congrArg (g.hom ≫ ·) (symmetricAlgebraHomEquiv_apply _).symm)

private lemma symmetricAlgebraPullbackHomEquiv_naturality {F' : QuasicoherentSheaf Y}
    (g : F' ⟶ F) {B : CommMon X.Modules}
    (h : ((symmetricAlgebra X).obj ((QuasicoherentSheaf.pullback f).obj F)).obj ⟶ B) :
    symmetricAlgebraPullbackHomEquiv f F' B
        (((symmetricAlgebra X).map ((QuasicoherentSheaf.pullback f).map g)).hom ≫ h) =
      g.hom ≫ symmetricAlgebraPullbackHomEquiv f F B h := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  have h₀ : eqToHom (QuasicoherentSheaf.pullback_obj_obj f F').symm ≫
      symmetricAlgebraHomEquiv _ B
        (((symmetricAlgebra X).map ((QuasicoherentSheaf.pullback f).map g)).hom ≫ h) =
      (Scheme.Modules.pullback f).map g.hom ≫
        eqToHom (QuasicoherentSheaf.pullback_obj_obj f F).symm ≫
          symmetricAlgebraHomEquiv _ B h := by
    have hι := symmetricAlgebraι_naturality ((QuasicoherentSheaf.pullback f).map g)
    rw [QuasicoherentSheaf.pullback_map_hom] at hι
    rw [symmetricAlgebraHomEquiv_apply, symmetricAlgebraHomEquiv_apply]
    refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (fun x ↦ _ ≫ x ≫ h.hom.hom) hι.symm).trans ?_
    -- Cancel the transport `((f^* F').obj = f^* F'.obj)` against its inverse.
    exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (Category.assoc _ _ _))).trans <|
      (eqToHom_trans_assoc _ _ _).trans <| (congrArg (· ≫ _) (eqToHom_refl _ _)).trans <|
        (Category.id_comp _).trans (Category.assoc _ _ _)
  exact (congrArg (A.homEquiv _ _) h₀).trans (A.homEquiv_naturality_left _ _)

/-- **Pullback of the symmetric algebra.** For a morphism of schemes `f : X ⟶ Y` and a
quasicoherent sheaf `F` on `Y`, the pullback `f^* (Sym F)` of the symmetric algebra of `F` is
isomorphic, as a quasicoherent commutative `𝒪_X`-algebra, to the symmetric algebra
`Sym (f^* F)` of the pullback of `F`. -/
def pullbackSymmetricAlgebraIso :
    (QuasicoherentAlgebra.pullback f).obj ((symmetricAlgebra Y).obj F) ≅
      (symmetricAlgebra X).obj ((QuasicoherentSheaf.pullback f).obj F) where
  hom := ObjectProperty.homMk ((pullbackSymmetricAlgebraHomEquiv f F _).symm
    (symmetricAlgebraPullbackHomEquiv f F _ (𝟙 _)))
  inv := ObjectProperty.homMk ((symmetricAlgebraPullbackHomEquiv f F _).symm
    (pullbackSymmetricAlgebraHomEquiv f F _ (𝟙 _)))
  hom_inv_id := by
    refine ObjectProperty.hom_ext _ ((pullbackSymmetricAlgebraHomEquiv f F _).injective ?_)
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.homMk_hom, pullbackSymmetricAlgebraHomEquiv_comp, Equiv.apply_symm_apply,
      ← symmetricAlgebraPullbackHomEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
    -- The identity of an algebra in the full subcategory is the identity of the algebra.
    rfl
  inv_hom_id := by
    refine ObjectProperty.hom_ext _ ((symmetricAlgebraPullbackHomEquiv f F _).injective ?_)
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.homMk_hom, symmetricAlgebraPullbackHomEquiv_comp, Equiv.apply_symm_apply,
      ← pullbackSymmetricAlgebraHomEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
    -- The identity of an algebra in the full subcategory is the identity of the algebra.
    rfl

/-- On generators, the inverse of `pullbackSymmetricAlgebraIso` is the pullback of the inclusion
`F ⟶ Sym F`: it restricts on `f^* F` to `f^* F ⟶ f^* (Sym F)`. -/
theorem symmetricAlgebraι_comp_pullbackSymmetricAlgebraIso_inv :
    symmetricAlgebraι ((QuasicoherentSheaf.pullback f).obj F) ≫
        (pullbackSymmetricAlgebraIso f F).inv.hom.hom.hom =
      eqToHom (QuasicoherentSheaf.pullback_obj_obj f F) ≫
        (Scheme.Modules.pullback f).map (symmetricAlgebraι F) ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let P := (QuasicoherentAlgebra.pullback f).obj ((symmetricAlgebra Y).obj F)
  -- The transpose of the identity of `f^* (Sym F)` restricts on `F` to the unit of the
  -- pullback–pushforward adjunction followed by the inclusion `F ⟶ Sym F`; its inverse transpose
  -- is the pullback of the inclusion.
  have hy : pullbackSymmetricAlgebraHomEquiv f F P.obj (𝟙 _) =
      symmetricAlgebraι F ≫ A.homEquiv _ _
        (eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm ≫ 𝟙 _) :=
    (symmetricAlgebraHomEquiv_apply _).trans
      (congrArg (symmetricAlgebraι F ≫ ·) (QuasicoherentAlgebra.pullbackHomEquiv_apply_hom_hom ..))
  have hD : (A.homEquiv _ _).symm (symmetricAlgebraι F ≫ A.homEquiv _ _
      (eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm ≫ 𝟙 P.obj.X)) =
      (Scheme.Modules.pullback f).map (symmetricAlgebraι F) ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm :=
    (A.homEquiv_naturality_left_symm _ _).trans
      ((congrArg (_ ≫ ·) (Equiv.symm_apply_apply _ _)).trans
        (congrArg (_ ≫ ·) (Category.comp_id _)))
  have h1 : (pullbackSymmetricAlgebraIso f F).inv.hom =
      symmetricAlgebraLift (eqToHom (QuasicoherentSheaf.pullback_obj_obj f F) ≫
        (A.homEquiv _ _).symm (pullbackSymmetricAlgebraHomEquiv f F P.obj (𝟙 _))) :=
    symmetricAlgebraHomEquiv_symm_apply _
  refine (congrArg (fun φ ↦ symmetricAlgebraι _ ≫ φ.hom.hom) h1).trans ?_
  refine (symmetricAlgebraι_comp_lift _).trans ?_
  exact congrArg (_ ≫ ·) ((congrArg (A.homEquiv _ _).symm hy).trans hD)

/-- On generators, `pullbackSymmetricAlgebraIso` sends the pullback of the inclusion
`F ⟶ Sym F` to the inclusion `f^* F ⟶ Sym (f^* F)`. -/
theorem pullback_map_symmetricAlgebraι_comp_pullbackSymmetricAlgebraIso_hom :
    eqToHom (QuasicoherentSheaf.pullback_obj_obj f F) ≫
        (Scheme.Modules.pullback f).map (symmetricAlgebraι F) ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm ≫
            (pullbackSymmetricAlgebraIso f F).hom.hom.hom.hom =
      symmetricAlgebraι ((QuasicoherentSheaf.pullback f).obj F) := by
  have h := congrArg (· ≫ (pullbackSymmetricAlgebraIso f F).hom.hom.hom.hom)
    (symmetricAlgebraι_comp_pullbackSymmetricAlgebraIso_inv f F)
  have e : (pullbackSymmetricAlgebraIso f F).inv.hom.hom.hom ≫
      (pullbackSymmetricAlgebraIso f F).hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun φ ↦ φ.hom.hom.hom) (pullbackSymmetricAlgebraIso f F).inv_hom_id
  exact ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).trans <|
    h.symm.trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) e).trans (Category.comp_id _)

/-- The isomorphism `pullbackSymmetricAlgebraIso` is natural in the quasicoherent sheaf. -/
@[reassoc]
theorem pullbackSymmetricAlgebraIso_hom_naturality {F' : QuasicoherentSheaf Y} (g : F' ⟶ F) :
    (QuasicoherentAlgebra.pullback f).map ((symmetricAlgebra Y).map g) ≫
        (pullbackSymmetricAlgebraIso f F).hom =
      (pullbackSymmetricAlgebraIso f F').hom ≫
        (symmetricAlgebra X).map ((QuasicoherentSheaf.pullback f).map g) := by
  refine ObjectProperty.hom_ext _ ((pullbackSymmetricAlgebraHomEquiv f F' _).injective ?_)
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    pullbackSymmetricAlgebraHomEquiv_naturality, pullbackSymmetricAlgebraHomEquiv_comp]
  simp only [pullbackSymmetricAlgebraIso, ObjectProperty.homMk_hom, Equiv.apply_symm_apply]
  rw [← symmetricAlgebraPullbackHomEquiv_comp, Category.id_comp,
    ← Category.comp_id ((symmetricAlgebra X).map ((QuasicoherentSheaf.pullback f).map g)).hom,
    symmetricAlgebraPullbackHomEquiv_naturality]

/-- **Pullback of the symmetric algebra, naturally.** For a morphism of schemes `f : X ⟶ Y`,
pulling back the symmetric algebra of a quasicoherent sheaf on `Y` is naturally isomorphic to
taking the symmetric algebra of its pullback. -/
def pullbackSymmetricAlgebraNatIso :
    symmetricAlgebra Y ⋙ QuasicoherentAlgebra.pullback f ≅
      QuasicoherentSheaf.pullback f ⋙ symmetricAlgebra X :=
  NatIso.ofComponents (pullbackSymmetricAlgebraIso f)
    fun g ↦ pullbackSymmetricAlgebraIso_hom_naturality f _ g

/-- The components of `pullbackSymmetricAlgebraNatIso` are `pullbackSymmetricAlgebraIso`. -/
@[simp]
theorem pullbackSymmetricAlgebraNatIso_hom_app :
    (pullbackSymmetricAlgebraNatIso f).hom.app F = (pullbackSymmetricAlgebraIso f F).hom :=
  (rfl)

/-- The inverse components of `pullbackSymmetricAlgebraNatIso` are the inverses of
`pullbackSymmetricAlgebraIso`. -/
@[simp]
theorem pullbackSymmetricAlgebraNatIso_inv_app :
    (pullbackSymmetricAlgebraNatIso f).inv.app F = (pullbackSymmetricAlgebraIso f F).inv :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
