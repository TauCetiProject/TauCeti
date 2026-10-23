/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice
import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# Cocharacter lattices of groups of multiplicative type

For a group `T` of multiplicative type over a field `k`, a geometric cocharacter is a group-scheme
morphism `G_m → T` after extension to the chosen algebraic closure. Contravariantly, it is a
morphism of coordinate Hopf algebras

```text
O(T_bar) → O(G_m).
```

The canonical group-like evaluation equivalence reconstructs the geometric fibre from
its characters. Full faithfulness of the diagonalizable-group coordinate-ring functor then
identifies these geometric morphisms with the integral dual of the geometric character group.
This comparison, rather than the definition of cocharacters, supplies the evaluation pairing. The
dual description is specific to groups of multiplicative type: a semisimple group can have trivial
character group and nontrivial cocharacters. For tori, the character lattice is finite free and the
pairing is perfect; those consequences are proved in the torus module.

The absolute Galois action on `X_*(T)` is the contragredient of its action on `X*(T)`. The
evaluation pairing is invariant under the diagonal action.

## Main declarations

* `TauCeti.MultiplicativeTypeCommHopfAlgCat.cocharacterLattice`: geometric group-scheme morphisms
  `G_m → T_bar`.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual`: the comparison
  between geometric cocharacters and the integral character dual.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.geometricCharacterGroupSchemeMap`: the group-scheme
  morphism attached to a geometric character.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.cocharacterGaloisRepresentation`: its contragredient
  absolute Galois representation.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.characterCocharacterPairing`: the evaluation pairing
  between characters and cocharacters, intrinsically characterized by composition of their
  group-scheme morphisms.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace MultiplicativeTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The geometric character group, bundled as a finitely generated commutative
group for use with the diagonalizable coordinate-ring functor. -/
private noncomputable def geometricCharacterFG (T : MultiplicativeTypeCommHopfAlgCat k) :
    FGCommGrpCat.{u} := by
  let _ : Group.FG (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) :=
    CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType T.obj T.property
  exact FGCommGrpCat.of (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)

/-- The bundled geometric character group has the intrinsic geometric characters as its
underlying group. -/
private noncomputable def geometricCharacterFGEquiv (T : MultiplicativeTypeCommHopfAlgCat k) :
    CommHopfAlgCat.geometricCharacterGroup T.obj.obj ≃* geometricCharacterFG T :=
  MulEquiv.refl _

private theorem baseChange_groupLike_span_eq_top (T : MultiplicativeTypeCommHopfAlgCat k) :
    Submodule.span (AlgebraicClosure k)
        (Set.range (_root_.GroupLike.val (R := AlgebraicClosure k)
          (A := FiniteTypeCommHopfAlgCat.baseChange
            (K := AlgebraicClosure k) T.obj))) = ⊤ := by
  rw [← Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  exact (DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).1 <|
    (multiplicativeTypeCommHopfAlgProperty_iff k T.obj).1 T.property

/-- The canonical reconstruction of the geometric coordinate algebra from its
geometric characters. -/
private noncomputable def geometricCoordinateIso (T : MultiplicativeTypeCommHopfAlgCat k) :
    DiagonalizableGroup.coordinateRing (AlgebraicClosure k) (geometricCharacterFG T) ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj :=
  ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    TauCeti.GroupLike.evaluationBialgEquiv (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)
      (baseChange_groupLike_span_eq_top T)

@[simp]
private theorem geometricCoordinateIso_hom_single (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.geometricCharacterGroup T.obj.obj) :
    (geometricCoordinateIso T).hom.hom
        (_root_.MonoidAlgebra.single (geometricCharacterFGEquiv T x) 1) = x.val := by
  -- `ObjectProperty.isoMk` and `CommHopfAlgCat.isoMk` hide the underlying bialgebra equivalence;
  -- expose that wrapper boundary so the evaluation lemma can rewrite its application.
  change TauCeti.GroupLike.evaluationBialgEquiv (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)
        (baseChange_groupLike_span_eq_top T)
          (_root_.MonoidAlgebra.single x 1) = x.val
  rw [TauCeti.GroupLike.evaluationBialgEquiv_apply,
    MonoidAlgebra.liftGroupLikeBialgHom_single, one_smul]

@[simp]
private theorem geometricCoordinateIso_hom_single' (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : geometricCharacterFG T) :
    (geometricCoordinateIso T).hom.hom (_root_.MonoidAlgebra.single x 1) =
      ((geometricCharacterFGEquiv T).symm x).val := by
  simpa using geometricCoordinateIso_hom_single T ((geometricCharacterFGEquiv T).symm x)

/-- The coordinate Hopf-algebra morphism of a geometric character. It sends the standard
generator of the multiplicative group's coordinate algebra to the character's underlying
group-like element. -/
private noncomputable def geometricCharacterCoordinateMap (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
        DiagonalizableGroup.multiplicativeCharacterGroup ⟶
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj :=
  FiniteTypeCommHopfAlgCat.ofHom <|
    (MonoidAlgebra.liftGroupLikeBialgHom (R := AlgebraicClosure k)
      (A := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)).comp <|
        _root_.MonoidAlgebra.mapDomainBialgHom (AlgebraicClosure k)
          (DiagonalizableGroup.uliftZPowersMulEquiv
            (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) x.toMul)

private theorem coordinateMap_comp_geometricCoordinateIso
    (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    DiagonalizableGroup.coordinateMap (AlgebraicClosure k)
        (FGCommGrpCat.ofHom
          (DiagonalizableGroup.uliftZPowersMulEquiv (geometricCharacterFG T)
            (geometricCharacterFGEquiv T x.toMul))) ≫
      (geometricCoordinateIso T).hom = geometricCharacterCoordinateMap T x := by
  apply FiniteTypeCommHopfAlgCat.hom_ext
  ext z
  rw [FiniteTypeCommHopfAlgCat.toBialgHom_comp]
  -- The bundled Hopf-algebra maps must be exposed as bialgebra maps before the `single` lemmas
  -- can rewrite both sides.
  change (geometricCoordinateIso T).hom.hom
      ((DiagonalizableGroup.coordinateMap (AlgebraicClosure k)
        (FGCommGrpCat.ofHom
          (DiagonalizableGroup.uliftZPowersMulEquiv (geometricCharacterFG T)
            (geometricCharacterFGEquiv T x.toMul)))).hom.hom
              (_root_.MonoidAlgebra.single z 1)) =
    ((MonoidAlgebra.liftGroupLikeBialgHom (R := AlgebraicClosure k)
      (A := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T.obj)).comp
        (_root_.MonoidAlgebra.mapDomainBialgHom (AlgebraicClosure k)
          (DiagonalizableGroup.uliftZPowersMulEquiv
            (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) x.toMul)))
              (_root_.MonoidAlgebra.single z 1)
  rw [DiagonalizableGroup.coordinateMap_single, geometricCoordinateIso_hom_single',
    BialgHom.comp_apply, _root_.MonoidAlgebra.mapDomainBialgHom_single,
    MonoidAlgebra.liftGroupLikeBialgHom_single, one_smul]
  rw [geometricCharacterFGEquiv]
  rfl

/-- The geometric fibre as an affine group scheme over the chosen algebraic closure. -/
noncomputable abbrev geometricFiberGroupScheme (T : MultiplicativeTypeCommHopfAlgCat k) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).obj <|
    Opposite.op (FiniteTypeCommHopfAlgCat.baseChange
      (K := AlgebraicClosure k) T.obj).obj

/-- The canonical coordinate reconstruction, viewed as an isomorphism from the geometric fibre to
the diagonalizable group scheme on its intrinsic character group. -/
private noncomputable def geometricFiberGroupSchemeIso (T : MultiplicativeTypeCommHopfAlgCat k) :
    geometricFiberGroupScheme T ≅
      (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).obj
        (Opposite.op
          (DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
            (geometricCharacterFG T)).obj) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).mapIso
    (((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (_root_.CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso
        (geometricCoordinateIso T)).op)

/-- The geometric cocharacter lattice: group-scheme morphisms `G_m → T_bar` over
the chosen algebraic closure. -/
abbrev cocharacterLattice (T : MultiplicativeTypeCommHopfAlgCat k) :=
  DiagonalizableGroup.multiplicativeGroupScheme (AlgebraicClosure k) ⟶
    geometricFiberGroupScheme T

/-- A geometric character, as the corresponding group-scheme morphism from the geometric fibre
of `T` to the multiplicative group. -/
noncomputable def geometricCharacterGroupSchemeMap (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    geometricFiberGroupScheme T ⟶
      DiagonalizableGroup.multiplicativeGroupScheme (AlgebraicClosure k) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).map
      (geometricCharacterCoordinateMap T x).hom.op ≫
    eqToHom (DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
      DiagonalizableGroup.multiplicativeCharacterGroup).symm

/-- The intrinsic character map agrees with the diagonalizable-group character map after the
canonical coordinate reconstruction. -/
private theorem geometricCharacterGroupSchemeMap_eq (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    geometricCharacterGroupSchemeMap T x =
      (geometricFiberGroupSchemeIso T).hom ≫
        eqToHom (DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
          (geometricCharacterFG T)).symm ≫
          DiagonalizableGroup.characterGroupSchemeMap (geometricCharacterFG T)
            (geometricCharacterFGEquiv T x.toMul) := by
  -- Expand the reconstruction isomorphism and the diagonalizable character map into `hopfSpec` of
  -- coordinate maps. Naming the character groups keeps the transports from `groupSchemeMap_def`
  -- syntactically equal to the statement's, so they cancel cheaply.
  rw [geometricFiberGroupSchemeIso, Functor.mapIso_hom, Iso.op_hom, Functor.mapIso_hom,
    FiniteTypeCommHopfAlgCat.forget₂_commHopfAlgCat_map,
    DiagonalizableGroup.characterGroupSchemeMap_def,
    DiagonalizableGroup.groupSchemeMap_def (AlgebraicClosure k)
      (G := DiagonalizableGroup.multiplicativeCharacterGroup) (H := geometricCharacterFG T),
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Functor.map_comp_assoc]
  -- Unfolded, the left side ends with the same transport; cancel it and compare coordinate maps.
  conv_lhs => rw [geometricCharacterGroupSchemeMap]
  rw [cancel_mono]
  apply congrArg (AlgebraicGeometry.hopfSpec (CommRingCat.of (AlgebraicClosure k))).map
  -- The coordinate maps agree by the reconstruction identity.
  rw [← op_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    coordinateMap_comp_geometricCoordinateIso]

/-- Character-group morphisms to the lifted integer group are integral linear functionals on
the additive character group. -/
private noncomputable def characterHomDualEquiv (T : MultiplicativeTypeCommHopfAlgCat k) :
    (geometricCharacterFG T ⟶ DiagonalizableGroup.multiplicativeCharacterGroup) ≃
      Module.Dual ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
  ((ConcreteCategory.homEquiv (X := geometricCharacterFG T)
      (Y := DiagonalizableGroup.multiplicativeCharacterGroup)).trans
    (MulEquiv.monoidHomCongrRightEquiv
      (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ))).trans
    (MonoidHom.toAdditiveLeft.trans (addMonoidHomLequivInt ℤ).toEquiv)

/-- Full faithfulness identifies homomorphisms of character groups with the corresponding
contravariant morphisms of diagonalizable group schemes. -/
private noncomputable def diagonalizableGroupSchemeHomEquiv
    (G H : FGCommGrpCat.{u}) :
    (G ⟶ H) ≃
      (DiagonalizableGroup.groupScheme (AlgebraicClosure k) H ⟶
        DiagonalizableGroup.groupScheme (AlgebraicClosure k) G) :=
  (Quiver.Hom.opEquiv.trans
    (DiagonalizableGroup.fullyFaithfulSchemeFunctor
      (AlgebraicClosure k)).homEquiv).trans <|
        (eqToIso (DiagonalizableGroup.schemeFunctor_obj
          (AlgebraicClosure k) (Opposite.op H))).homCongr
            (eqToIso (DiagonalizableGroup.schemeFunctor_obj
              (AlgebraicClosure k) (Opposite.op G)))

private theorem diagonalizableGroupSchemeHomEquiv_apply
    (G H : FGCommGrpCat.{u}) (f : G ⟶ H) :
    diagonalizableGroupSchemeHomEquiv (k := k) G H f =
      DiagonalizableGroup.groupSchemeMap (AlgebraicClosure k) f := by
  simp [diagonalizableGroupSchemeHomEquiv,
    DiagonalizableGroup.schemeFunctor_map]

/-- The geometric fibre reconstructed from its intrinsic characters, now with the public
diagonalizable-group-scheme presentation as target. -/
private noncomputable def geometricFiberDiagonalizableIso (T : MultiplicativeTypeCommHopfAlgCat k) :
    geometricFiberGroupScheme T ≅
      DiagonalizableGroup.groupScheme (AlgebraicClosure k) (geometricCharacterFG T) :=
  (geometricFiberGroupSchemeIso T).trans <|
    eqToIso (DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
      (geometricCharacterFG T)).symm

/-- Group-like reconstruction identifies a geometric cocharacter with the corresponding
homomorphism from the intrinsic character group to the character group of `G_m`. -/
private noncomputable def cocharacterLatticeEquivFG (T : MultiplicativeTypeCommHopfAlgCat k) :
    cocharacterLattice T ≃
      (geometricCharacterFG T ⟶ DiagonalizableGroup.multiplicativeCharacterGroup) :=
  ((Iso.refl _).homCongr (geometricFiberDiagonalizableIso T)).trans
    (diagonalizableGroupSchemeHomEquiv (k := k) (geometricCharacterFG T)
      DiagonalizableGroup.multiplicativeCharacterGroup).symm

/-- The character-group homomorphism canonically recovered from a geometric cocharacter. -/
private noncomputable def cocharacterFGMap (T : MultiplicativeTypeCommHopfAlgCat k)
    (f : cocharacterLattice T) :
    geometricCharacterFG T ⟶ DiagonalizableGroup.multiplicativeCharacterGroup :=
  cocharacterLatticeEquivFG T f

private theorem cocharacter_comp_geometricFiberGroupSchemeIso
    (T : MultiplicativeTypeCommHopfAlgCat k) (f : cocharacterLattice T) :
    (f ≫ (geometricFiberGroupSchemeIso T).hom) ≫
        eqToHom (DiagonalizableGroup.groupScheme_def (AlgebraicClosure k)
          (geometricCharacterFG T)).symm =
      DiagonalizableGroup.groupSchemeMap (AlgebraicClosure k) (cocharacterFGMap T f) := by
  -- Full faithfulness identifies the reconstructed character-group map: by definition,
  -- `cocharacterFGMap T f` is the preimage of `f ≫ (geometricFiberDiagonalizableIso T).hom`.
  rw [← diagonalizableGroupSchemeHomEquiv_apply, cocharacterFGMap, cocharacterLatticeEquivFG,
    Equiv.trans_apply, Equiv.apply_symm_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  -- Unfold the composite target isomorphism: the coordinate reconstruction, then `eqToHom`.
  rw [geometricFiberDiagonalizableIso, Iso.trans_hom, eqToIso.hom, Category.assoc]

/-- The ordinary-integer-valued homomorphism underlying the lifted character-group map of a
geometric cocharacter. -/
private noncomputable def cocharacterMonoidHom (T : MultiplicativeTypeCommHopfAlgCat k)
    (f : cocharacterLattice T) : geometricCharacterFG T →* Multiplicative ℤ :=
  (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ).toMonoidHom.comp
    (FGCommGrpCat.toMonoidHom (cocharacterFGMap T f))

private theorem cocharacterGroupSchemeMap_eq (T : MultiplicativeTypeCommHopfAlgCat k)
    (f : cocharacterLattice T) :
    DiagonalizableGroup.cocharacterGroupSchemeMap (R := AlgebraicClosure k)
        (geometricCharacterFG T) (cocharacterMonoidHom T f) =
      DiagonalizableGroup.groupSchemeMap (AlgebraicClosure k) (cocharacterFGMap T f) := by
  rw [DiagonalizableGroup.cocharacterGroupSchemeMap_def]
  unfold cocharacterMonoidHom
  congr 1

/-- Group-like reconstruction identifies geometric cocharacters with the integral dual of
geometric characters. This equivalence transports the additive and module structures; the
linear equivalence below is the canonical comparison for consumers. -/
noncomputable def cocharacterLatticeEquivDual (T : MultiplicativeTypeCommHopfAlgCat k) :
    cocharacterLattice T ≃
      Module.Dual ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
  (cocharacterLatticeEquivFG T).trans (characterHomDualEquiv T)

noncomputable instance instCocharacterLatticeAddCommGroup
    (T : MultiplicativeTypeCommHopfAlgCat k) :
    AddCommGroup (cocharacterLattice T) :=
  (cocharacterLatticeEquivDual T).addCommGroup

noncomputable instance instCocharacterLatticeModule (T : MultiplicativeTypeCommHopfAlgCat k) :
    Module ℤ (cocharacterLattice T) :=
  (cocharacterLatticeEquivDual T).addEquiv.module ℤ

/-- The canonical equivalence from geometric cocharacters to the character dual, as a linear
equivalence. -/
noncomputable def cocharacterLatticeLinearEquivDual (T : MultiplicativeTypeCommHopfAlgCat k) :
    cocharacterLattice T ≃ₗ[ℤ]
      Module.Dual ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
  (cocharacterLatticeEquivDual T).addEquiv.linearEquiv ℤ

/-- Two geometric cocharacters are equal when their functionals agree on every character. -/
theorem cocharacterLattice_ext {T : MultiplicativeTypeCommHopfAlgCat k}
    {f g : cocharacterLattice T}
    (h : ∀ x, cocharacterLatticeLinearEquivDual T f x = cocharacterLatticeLinearEquivDual T g x) :
    f = g :=
  (cocharacterLatticeLinearEquivDual T).injective (LinearMap.ext h)

private theorem pairing_cocharacterMonoidHom (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    DiagonalizableGroup.pairing (geometricCharacterFGEquiv T x.toMul)
        (cocharacterMonoidHom T f) =
      cocharacterLatticeLinearEquivDual T f x := by
  -- Both sides evaluate the same character-group homomorphism, with the left side passing
  -- through multiplicative notation and the right side through the transported integral dual.
  rw [DiagonalizableGroup.pairing_def]
  rfl

/-- The contragredient absolute-Galois representation on the cocharacter lattice. Thus a
Galois element `σ` sends a cocharacter functional `f` to `x ↦ f (σ⁻¹ • x)`. -/
noncomputable def cocharacterGaloisRepresentation (T : MultiplicativeTypeCommHopfAlgCat k) :
    Representation ℤ (Field.absoluteGaloisGroup k) (cocharacterLattice T) :=
  (cocharacterLatticeLinearEquivDual T).symm.conjRingEquiv.toMonoidHom.comp <|
    (Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
      (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)).dual

/-- The contragredient Galois representation evaluates by applying the inverse Galois element
to the character. -/
@[simp]
theorem cocharacterGaloisRepresentation_apply_apply (T : MultiplicativeTypeCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k)
    (f : cocharacterLattice T) (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    cocharacterLatticeLinearEquivDual T (cocharacterGaloisRepresentation T σ f) x =
      cocharacterLatticeLinearEquivDual T f (σ⁻¹ • x) := by
  -- The representation is packaged as a composite monoid hom, whereas
  -- `LinearEquiv.conj_apply_apply` rewrites a bare conjugation. This definitional step exposes
  -- that single representation-wrapper boundary before applying the public conjugation lemma.
  rw [show cocharacterGaloisRepresentation T σ f =
      (cocharacterLatticeLinearEquivDual T).symm.conj
        ((Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
          (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)).dual σ) f by
    rfl]
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The character--cocharacter pairing transported through the canonical dual comparison. It is
evaluation of a functional in `X_*(T) = Hom_ℤ(X*(T), ℤ)` on a character. -/
noncomputable def characterCocharacterPairing
    (T : MultiplicativeTypeCommHopfAlgCat k) :
    CommHopfAlgCat.additiveCharacterGroup T.obj.obj →ₗ[ℤ] cocharacterLattice T →ₗ[ℤ] ℤ :=
  (cocharacterLatticeLinearEquivDual T).toLinearMap.flip

/-- The character--cocharacter pairing is evaluation. -/
@[simp]
theorem characterCocharacterPairing_apply (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    characterCocharacterPairing T x f = cocharacterLatticeLinearEquivDual T f x := by
  unfold characterCocharacterPairing
  rfl

/-- Composing an intrinsic geometric cocharacter with an intrinsic geometric character is the
multiplicative-group power map whose exponent is their character--cocharacter pairing. -/
@[simp]
theorem cocharacter_comp_geometricCharacterGroupSchemeMap
    (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    f ≫ geometricCharacterGroupSchemeMap T x =
      DiagonalizableGroup.powEndGroupSchemeMap (R := AlgebraicClosure k)
        (characterCocharacterPairing T x f) := by
  rw [geometricCharacterGroupSchemeMap_eq]
  simp only [← Category.assoc]
  rw [
    cocharacter_comp_geometricFiberGroupSchemeIso,
    ← cocharacterGroupSchemeMap_eq,
    DiagonalizableGroup.cocharacterGroupSchemeMap_comp_characterGroupSchemeMap,
    characterCocharacterPairing_apply, pairing_cocharacterMonoidHom]

private theorem powEndGroupSchemeMap_injective :
    Function.Injective (DiagonalizableGroup.powEndGroupSchemeMap (R := AlgebraicClosure k)) := by
  intro m n h
  -- Full faithfulness (`diagonalizableGroupSchemeHomEquiv`) recovers the lifted power maps of the
  -- character group that induce the power maps. Expose the underlying lifted-power homomorphisms;
  -- each is determined by its value at the generator.
  simp only [DiagonalizableGroup.powEndGroupSchemeMap_def,
    DiagonalizableGroup.characterGroupSchemeMap_def, ← diagonalizableGroupSchemeHomEquiv_apply,
    EmbeddingLike.apply_eq_iff_eq, FGCommGrpCat.hom_ext_iff, FGCommGrpCat.toMonoidHom_ofHom] at h
  -- `simp` does not unfold the carrier of `multiplicativeCharacterGroup` to `ULift`, so the lifted
  -- exponents are compared by rewriting.
  rwa [ULift.up_inj, EmbeddingLike.apply_eq_iff_eq] at h

/-- The pairing is the unique exponent whose power map is the composite of the corresponding
geometric cocharacter and character. -/
theorem characterCocharacterPairing_eq_iff_comp_eq_powEndGroupSchemeMap
    (T : MultiplicativeTypeCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) (n : ℤ) :
    characterCocharacterPairing T x f = n ↔
      f ≫ geometricCharacterGroupSchemeMap T x =
        DiagonalizableGroup.powEndGroupSchemeMap (R := AlgebraicClosure k) n := by
  constructor
  · intro h
    rw [cocharacter_comp_geometricCharacterGroupSchemeMap, h]
  · intro h
    apply powEndGroupSchemeMap_injective (k := k)
    rw [← cocharacter_comp_geometricCharacterGroupSchemeMap]
    exact h

/-- The character--cocharacter pairing is invariant under the diagonal absolute-Galois action. -/
theorem characterCocharacterPairing_galois_invariant (T : MultiplicativeTypeCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    characterCocharacterPairing T (σ • x) (cocharacterGaloisRepresentation T σ f) =
      characterCocharacterPairing T x f := by
  rw [characterCocharacterPairing_apply, cocharacterGaloisRepresentation_apply_apply,
    inv_smul_smul, characterCocharacterPairing_apply]

end MultiplicativeTypeCommHopfAlgCat

end TauCeti
