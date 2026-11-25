/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Coordinate
public import TauCeti.AlgebraicGeometry.GroupScheme.Surjective
public import Mathlib.AlgebraicGeometry.Noetherian
import TauCeti.CategoryTheory.Monoidal.Cartesian.Over
import TauCeti.RingTheory.Noetherian.ULift

/-!
# Diagonalizable group schemes over a base

For a finitely generated abelian group `M` and a scheme `S`, the diagonalizable group scheme
`D_S(M)` is the spectrum of the group algebra `O_S[M]` over `S`, with `M` written multiplicatively
in the group algebra. It is defined here as the base change along `S ⟶ Spec ℤ` of the diagonalizable
group scheme `Spec ℤ[M]` of `TauCeti.DiagonalizableGroup.groupScheme`; for instance `D_S(ℤ)` is
the spectrum of `O_S[t, t⁻¹]` and `D_S(ℤ/n)` that of `O_S[t]/(tⁿ - 1)`. A homomorphism
`φ : N →+ M` induces `D(φ) : D_S(M) ⟶ D_S(N)`, contravariantly.

The structure morphism of `D_S(M)` is affine, flat and locally of finite presentation, and `D_S(M)`
is commutative: each property is stable under base change and holds over `Spec ℤ`, where `ℤ[M]` is
a free `ℤ`-module and a finitely generated algebra over a Noetherian ring. Like every group scheme,
`D_S(M)` is also surjective over `S`, by `TauCeti.GroupScheme.surjective_hom_of_monObj`. The
formation of `D_S(M)` commutes with base change, over an affine base `Spec R` it is `Spec R[M]`, and
so its fibre at a point `s` is `Spec κ(s)[M]`; these identifications are natural in `M`.

## Main declarations

* `TauCeti.GroupScheme.diagonalizable`: the group scheme `D_S(M)` over `S`.
* `TauCeti.GroupScheme.diagonalizableMap`: the homomorphism `D_S(M) ⟶ D_S(N)` induced by
  `N →+ M`, with `diagonalizableMap_id` and `diagonalizableMap_comp`.
* `TauCeti.GroupScheme.isCommMonObj_diagonalizable`, `isAffineHom_diagonalizable`,
  `flat_diagonalizable` and `locallyOfFinitePresentation_diagonalizable`: `D_S(M)` is
  commutative, affine, flat and of finite presentation over `S`. With
  `TauCeti.GroupScheme.surjective_hom_of_monObj`, it is faithfully flat over `S`.
* `TauCeti.GroupScheme.diagonalizableBaseChangeIso`: the base change of `D_S(M)` along
  `S' ⟶ S` is `D_{S'}(M)`.
* `TauCeti.GroupScheme.diagonalizableSpecIso`: `D_{Spec R}(M)` is
  `TauCeti.DiagonalizableGroup.groupScheme R M`, the spectrum of `R[M]`.
* `TauCeti.GroupScheme.diagonalizableFiberIso`: the fibre of `D_S(M)` at `s` is the spectrum of
  `κ(s)[M]`.

## References

* M. Demazure, A. Grothendieck et al., *Schémas en groupes* (SGA 3), Exp. VIII, 1.1 and 2.1:
  the definition of `D_S(M)`, its base change and its affineness, flatness and finite
  presentation.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped MonObj

namespace TauCeti.GroupScheme

universe u

variable (S : Scheme.{u}) (M N P : Type u) [AddCommGroup M] [AddGroup.FG M]
  [AddCommGroup N] [AddGroup.FG N] [AddCommGroup P] [AddGroup.FG P]

/-- The diagonalizable group scheme `D_S(M)` of a finitely generated abelian group `M`: the base
change along `S ⟶ Spec ℤ` of `Spec ℤ[M]`, where `M` is written multiplicatively in the group
algebra. It is a reducible abbreviation so that the base-change API of `Over.pullback` applies to
it directly. -/
noncomputable abbrev diagonalizable : Grp (Over S) :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapGrp.obj
    (DiagonalizableGroup.groupScheme (ULift.{u} ℤ) (FGCommGrpCat.of (Multiplicative M)))

variable {M N P} in
/-- The homomorphism `D(φ) : D_S(M) ⟶ D_S(N)` induced by `φ : N →+ M`: the base change of the
homomorphism of `Spec ℤ[M] ⟶ Spec ℤ[N]` induced by `φ` on group algebras. -/
noncomputable def diagonalizableMap (φ : N →+ M) : diagonalizable S M ⟶ diagonalizable S N :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapGrp.map
    (DiagonalizableGroup.groupSchemeMap (ULift.{u} ℤ)
      (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative φ)))

variable {M N P} in
/-- `diagonalizableMap` is the base change of the corresponding morphism over `Spec ℤ`. -/
theorem diagonalizableMap_def (φ : N →+ M) :
    diagonalizableMap S φ =
      (Over.pullback (specULiftZIsTerminal.from S)).mapGrp.map
        (DiagonalizableGroup.groupSchemeMap (ULift.{u} ℤ)
          (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative φ))) :=
  (rfl)

/-- The identity of `M` induces the identity of `D_S(M)`. -/
@[simp]
theorem diagonalizableMap_id : diagonalizableMap S (AddMonoidHom.id M) = 𝟙 _ := by
  have : FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative (AddMonoidHom.id M)) = 𝟙 _ :=
    FGCommGrpCat.hom_ext AddMonoidHom.toMultiplicative_id
  rw [diagonalizableMap_def, this, DiagonalizableGroup.groupSchemeMap_id,
    CategoryTheory.Functor.map_id]

variable {M N P} in
/-- `D(φ ∘ ψ) = D(φ) ≫ D(ψ)`: the assignment `φ ↦ D(φ)` is contravariant. -/
@[simp]
theorem diagonalizableMap_comp (φ : N →+ M) (ψ : P →+ N) :
    diagonalizableMap S (φ.comp ψ) = diagonalizableMap S φ ≫ diagonalizableMap S ψ := by
  have : FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative (φ.comp ψ)) =
      FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative ψ) ≫
        FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative φ) :=
    FGCommGrpCat.hom_ext (MonoidHom.ext fun _ ↦ rfl)
  rw [diagonalizableMap_def, diagonalizableMap_def, diagonalizableMap_def, this,
    DiagonalizableGroup.groupSchemeMap_comp, CategoryTheory.Functor.map_comp]

/-- `D_S(M)` is a commutative group scheme. -/
instance isCommMonObj_diagonalizable : IsCommMonObj (diagonalizable S M).X :=
  -- `mapGrp` equips `F.obj X` with the group structure `Functor.obj.instGrpObj`, whose monoid
  -- structure is the one `Functor.isCommMonObj_obj` shows commutative for a braided `F`.
  Functor.isCommMonObj_obj (F := Over.pullback (specULiftZIsTerminal.from S))
    (M := (DiagonalizableGroup.groupScheme (ULift.{u} ℤ) (FGCommGrpCat.of (Multiplicative M))).X)

/-- A property of morphisms stable under base change holds for `D_S(M) ⟶ S` as soon as it holds
for `D(M) ⟶ Spec ℤ`. -/
private theorem diagonalizable_X_hom_of_isStableUnderBaseChange {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange]
    (h : P (DiagonalizableGroup.groupScheme (ULift.{u} ℤ)
      (FGCommGrpCat.of (Multiplicative M))).X.hom) :
    P (diagonalizable S M).X.hom :=
  P.pullback_snd _ _ h

/-- `D_S(M)` is affine over `S`. -/
instance isAffineHom_diagonalizable : IsAffineHom (diagonalizable S M).X.hom :=
  diagonalizable_X_hom_of_isStableUnderBaseChange (P := @IsAffineHom) S M <| by
    rw [DiagonalizableGroup.groupScheme_def,
      morphismProperty_hopfSpec_obj_X_hom_iff (P := @IsAffineHom) (ULift.{u} ℤ)]
    infer_instance

/-- `D_S(M)` is flat over `S`, since `ℤ[M]` is a free `ℤ`-module. -/
instance flat_diagonalizable : Flat (diagonalizable S M).X.hom :=
  diagonalizable_X_hom_of_isStableUnderBaseChange (P := @Flat) S M <| by
    rw [DiagonalizableGroup.groupScheme_def, ← moduleFlat_iff_flat_hopfSpec]
    infer_instance

/-- `D_S(M)` is locally of finite presentation over `S`, since `ℤ[M]` is a finitely generated
algebra over the Noetherian ring `ℤ`. -/
instance locallyOfFinitePresentation_diagonalizable :
    LocallyOfFinitePresentation (diagonalizable S M).X.hom :=
  diagonalizable_X_hom_of_isStableUnderBaseChange (P := @LocallyOfFinitePresentation) S M <| by
    infer_instance

section BaseChange

variable {S} {S' : Scheme.{u}} (f : S' ⟶ S)

/-- The formation of `D_S(M)` commutes with base change: pulling `D_S(M)` back along
`f : S' ⟶ S` gives `D_{S'}(M)`. -/
noncomputable def diagonalizableBaseChangeIso :
    (Over.pullback f).mapGrp.obj (diagonalizable S M) ≅ diagonalizable S' M :=
  (Over.mapGrpPullbackCompOfEq f (specULiftZIsTerminal.hom_ext _ _)).app _

/-- The morphism in `Over S'` underlying `diagonalizableBaseChangeIso` is the comparison
`Over.pullbackComp` of the pullbacks along `f ≫ (S ⟶ Spec ℤ)` and `S' ⟶ Spec ℤ`. -/
@[simp]
theorem diagonalizableBaseChangeIso_hom_hom_hom :
    (diagonalizableBaseChangeIso M f).hom.hom.hom =
      (Over.pullbackComp f (specULiftZIsTerminal.from S)).inv.app _ ≫
        eqToHom (congrArg (fun g ↦ (Over.pullback g).obj
          (DiagonalizableGroup.groupScheme (ULift.{u} ℤ) (FGCommGrpCat.of (Multiplicative M))).X)
          (specULiftZIsTerminal.hom_ext _ _)) :=
  Over.mapGrpPullbackCompOfEq_hom_app_hom_hom f _ _

/-- The morphism in `Over S'` underlying the inverse of `diagonalizableBaseChangeIso` is the
comparison `Over.pullbackComp` of the pullbacks along `S' ⟶ Spec ℤ` and `f ≫ (S ⟶ Spec ℤ)`. -/
@[simp]
theorem diagonalizableBaseChangeIso_inv_hom_hom :
    (diagonalizableBaseChangeIso M f).inv.hom.hom =
      eqToHom (congrArg (fun g ↦ (Over.pullback g).obj
          (DiagonalizableGroup.groupScheme (ULift.{u} ℤ) (FGCommGrpCat.of (Multiplicative M))).X)
          (specULiftZIsTerminal.hom_ext _ _)) ≫
        (Over.pullbackComp f (specULiftZIsTerminal.from S)).hom.app _ :=
  Over.mapGrpPullbackCompOfEq_inv_app_hom_hom f _ _

variable {M N} in
/-- The base-change isomorphism `diagonalizableBaseChangeIso` is natural in the character
group. -/
@[reassoc]
theorem diagonalizableBaseChangeIso_hom_naturality (φ : N →+ M) :
    (Over.pullback f).mapGrp.map (diagonalizableMap S φ) ≫
        (diagonalizableBaseChangeIso N f).hom =
      (diagonalizableBaseChangeIso M f).hom ≫ diagonalizableMap S' φ :=
  (Over.mapGrpPullbackCompOfEq f (specULiftZIsTerminal.hom_ext _ _)).hom.naturality _

end BaseChange

section Spec

variable (R : Type u) [CommRing R]

/-- The comparison of `D_{Spec R}(M)` with `Spec R[M]`, for a chosen ring map `ℤ → R`. -/
private noncomputable def diagonalizableSpecIsoOfAlgebra [Algebra (ULift.{u} ℤ) R] :
    diagonalizable (Spec (CommRingCat.of R)) M ≅
      DiagonalizableGroup.groupScheme R (FGCommGrpCat.of (Multiplicative M)) :=
  -- Over `Spec R`, base change from `Spec ℤ` is base change along `Spec` of the ring map `ℤ → R`,
  -- by terminality of `Spec ℤ`.
  (Functor.mapGrpNatIso (eqToIso (congrArg (fun g ↦ Over.pullback g)
      (specULiftZIsTerminal.hom_ext _ (Spec.map (CommRingCat.ofHom (algebraMap _ R))))))).app _ ≪≫
    eqToIso (by rw [DiagonalizableGroup.groupScheme_def]) ≪≫
    AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso
      (DiagonalizableGroup.coordinateRing (ULift.{u} ℤ) (FGCommGrpCat.of (Multiplicative M))).obj ≪≫
    (hopfSpec (CommRingCat.of R)).mapIso
      (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso (ULift.{u} ℤ) R
        (FGCommGrpCat.of (Multiplicative M))).op.symm ≪≫
    eqToIso (DiagonalizableGroup.groupScheme_def R _).symm

variable {M N} in
private theorem diagonalizableSpecIsoOfAlgebra_hom_naturality [alg : Algebra (ULift.{u} ℤ) R]
    (φ : N →+ M) :
    diagonalizableMap (Spec (CommRingCat.of R)) φ ≫ (diagonalizableSpecIsoOfAlgebra N R).hom =
      (diagonalizableSpecIsoOfAlgebra M R).hom ≫ DiagonalizableGroup.groupSchemeMap R
        (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative φ)) := by
  rw [diagonalizableSpecIsoOfAlgebra, diagonalizableSpecIsoOfAlgebra, diagonalizableMap]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
  -- Each of the five factors of the comparison is natural; pass `D(φ)` through them in turn.
  -- First the change of the structure morphism `S ⟶ Spec ℤ`.
  rw [NatTrans.naturality_assoc]
  congr 1
  simp only [Functor.mapIso_hom, Iso.symm_hom, eqToIso.hom,
    DiagonalizableGroup.groupSchemeMap_def, Functor.map_comp, Category.assoc, eqToHom_map,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  -- Then the comparison of the pulled-back Hopf spectrum with the Hopf spectrum of `R ⊗ ℤ[M]`.
  rw [← Category.assoc, AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso_hom_naturality,
    Category.assoc]
  congr 1
  -- Finally the coordinate isomorphism `R ⊗ ℤ[M] ≅ R[M]`, under the spectrum functor.
  simp only [Iso.op_inv, ← Functor.map_comp_assoc, ← op_comp]
  congr 3
  rw [Iso.inv_comp_eq,
    ← DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_naturality_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Over an affine base `Spec R`, `D_{Spec R}(M)` is the diagonalizable group scheme
`Spec R[M]` of `TauCeti.DiagonalizableGroup.groupScheme`. -/
noncomputable def diagonalizableSpecIso :
    diagonalizable (Spec (CommRingCat.of R)) M ≅
      DiagonalizableGroup.groupScheme R (FGCommGrpCat.of (Multiplicative M)) :=
  letI : Algebra (ULift.{u} ℤ) R :=
    ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom).toAlgebra
  diagonalizableSpecIsoOfAlgebra M R

variable {M N} in
/-- The comparison `diagonalizableSpecIso` with `Spec R[M]` is natural in the character group. -/
@[reassoc]
theorem diagonalizableSpecIso_hom_naturality (φ : N →+ M) :
    diagonalizableMap (Spec (CommRingCat.of R)) φ ≫ (diagonalizableSpecIso N R).hom =
      (diagonalizableSpecIso M R).hom ≫ DiagonalizableGroup.groupSchemeMap R
        (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative φ)) := by
  rw [diagonalizableSpecIso, diagonalizableSpecIso]
  exact diagonalizableSpecIsoOfAlgebra_hom_naturality (alg := _) R φ

end Spec

variable {S}

/-- The fibre of `D_S(M)` at a point `s : S` is the diagonalizable group scheme `Spec κ(s)[M]`
over the residue field. -/
noncomputable def diagonalizableFiberIso (s : S) :
    (Over.pullback (S.fromSpecResidueField s)).mapGrp.obj (diagonalizable S M) ≅
      DiagonalizableGroup.groupScheme (S.residueField s) (FGCommGrpCat.of (Multiplicative M)) :=
  diagonalizableBaseChangeIso M (S.fromSpecResidueField s) ≪≫
    diagonalizableSpecIso M (S.residueField s)

variable {M N} in
/-- The fibre comparison `diagonalizableFiberIso` is natural in the character group. -/
@[reassoc]
theorem diagonalizableFiberIso_hom_naturality (s : S) (φ : N →+ M) :
    (Over.pullback (S.fromSpecResidueField s)).mapGrp.map (diagonalizableMap S φ) ≫
        (diagonalizableFiberIso N s).hom =
      (diagonalizableFiberIso M s).hom ≫ DiagonalizableGroup.groupSchemeMap (S.residueField s)
        (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative φ)) := by
  rw [diagonalizableFiberIso, diagonalizableFiberIso, Iso.trans_hom, Iso.trans_hom,
    diagonalizableBaseChangeIso_hom_naturality_assoc, diagonalizableSpecIso_hom_naturality,
    Category.assoc]

end TauCeti.GroupScheme

