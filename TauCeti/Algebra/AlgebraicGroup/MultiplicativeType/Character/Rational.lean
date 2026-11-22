/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Character.SeparableDescent
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.GaloisModule
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Characterization
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
public import TauCeti.Algebra.AlgebraicGroup.Torus.Cocharacter.Basic
public import TauCeti.Algebra.Bialgebra.GroupLike.BaseChange

/-!
# Rational characters and split groups of multiplicative type

A character of an affine group `G` over a field `k` that is defined over `k` is a group-like
element of the coordinate algebra `O(G)`. Extending scalars sends it to a geometric character,
a group-like element of `AlgebraicClosure k ⊗[k] O(G)`, fixed by the absolute Galois group. For
a group of multiplicative type the converse holds over every field: a Galois-fixed geometric
character is defined over `k`, so the characters over `k` are exactly the Galois-fixed geometric
characters.

Consequently a group of multiplicative type is diagonalizable over `k` exactly when the absolute
Galois group acts trivially on its geometric characters, and a torus is split exactly when the
Galois action on its character lattice, or equivalently on its cocharacter lattice, is trivial.

No perfectness of `k` is assumed. A fixed geometric character `χ` determines the equivariant map
from the characters of the diagonalizable group `D(⟨χ⟩)` sending the tautological character to
`χ`; descent of character maps between groups of multiplicative type over an arbitrary field
(`existsUnique_geometricCharacterMap_eq_of_multiplicativeType`) produces a Hopf morphism
`k[⟨χ⟩] → O(G)`, and the image of the tautological monomial is a character over `k` extending
to `χ`.

## Main declarations

* `TauCeti.CommHopfAlgCat.smul_groupLikeBaseChange`: characters defined over `k` are Galois-fixed.
* `TauCeti.multiplicativeTypeCommHopfAlgProperty.exists_groupLikeBaseChange_eq_iff`: a geometric
  character of a group of multiplicative type is defined over `k` exactly when it is Galois-fixed.
* `TauCeti.multiplicativeTypeCommHopfAlgProperty.groupLikeEquivFixedPoints`: the characters over
  `k` are isomorphic to the Galois-fixed geometric characters.
* `TauCeti.multiplicativeTypeCommHopfAlgProperty.groupLikeSpannedProperty_iff_forall_smul_eq`: a
  group of multiplicative type is diagonalizable exactly when the Galois action on its geometric
  characters is trivial.
* `TauCeti.torusCommHopfAlgProperty.splitTorusCommHopfAlgProperty_iff_forall_smul_eq`: a torus is
  split exactly when the Galois action on its character lattice is trivial.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.smul_cocharacter_eq_of_forall_smul_eq`: a Galois
  element fixing every character fixes every cocharacter.
* `TauCeti.TorusCommHopfAlgCat.splitTorusCommHopfAlgProperty_iff_forall_smul_cocharacter_eq`: a
  torus is split exactly when the Galois action on its cocharacter lattice is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.g, Theorem 12.23 and Corollary 12.24.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

/-- A character defined over the ground field is fixed by the absolute Galois group. -/
@[simp]
theorem smul_groupLikeBaseChange {A : Type*} [Semiring A] [Bialgebra k A]
    (σ : Field.absoluteGaloisGroup k) (g : _root_.GroupLike k A) :
    σ • (groupLikeBaseChange g :
      _root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) =
      groupLikeBaseChange g := by
  apply _root_.GroupLike.val_injective
  rw [val_smul, val_groupLikeBaseChange, ScalarAut.smul_tmul, map_one]

/-- The map on geometric characters induced by a Hopf-algebra morphism extends the map on
characters defined over the ground field. -/
@[simp]
theorem geometricCharacterMap_groupLikeBaseChange {H K : _root_.CommHopfAlgCat.{u} k}
    (f : H ⟶ K) (g : _root_.GroupLike k H) :
    geometricCharacterMap f (groupLikeBaseChange g) =
      groupLikeBaseChange (f.hom.mapGroupLike g) := by
  apply _root_.GroupLike.val_injective
  rw [val_geometricCharacterMap, val_groupLikeBaseChange, baseChangeMap_apply_tmul,
    val_groupLikeBaseChange, BialgHom.val_mapGroupLike]

end CommHopfAlgCat

namespace multiplicativeTypeCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **A Galois-fixed geometric character of a group of multiplicative type is defined over the
ground field.** No perfectness of `k` is needed. -/
theorem exists_groupLikeBaseChange_eq_of_forall_smul_eq
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    {χ : CommHopfAlgCat.geometricCharacterGroup H.obj}
    (hχ : ∀ σ : Field.absoluteGaloisGroup k, σ • χ = χ) :
    ∃ g : _root_.GroupLike k H.obj, groupLikeBaseChange g = χ := by
  -- The diagonalizable group whose characters are the powers of `χ`.
  let G : FGCommGrpCat.{u} := FGCommGrpCat.of (Subgroup.zpowers χ)
  let e := DiagonalizableGroup.geometricCharacterGroupEquiv k G
  let f : CommHopfAlgCat.geometricCharacterGroup (DiagonalizableGroup.coordinateRing k G).obj →*
      CommHopfAlgCat.geometricCharacterGroup H.obj :=
    (Subgroup.zpowers χ).subtype.comp e.toMonoidHom
  have hf (σ : Field.absoluteGaloisGroup k) x : f (σ • x) = σ • f x := by
    rw [DiagonalizableGroup.smul_geometricCharacterGroup_eq_self]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (e x).property
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    change _ = σ • ((e x : Subgroup.zpowers χ) : CommHopfAlgCat.geometricCharacterGroup H.obj)
    rw [← hn, smul_zpow', hχ]
  obtain ⟨φ, hφ⟩ := (existsUnique_geometricCharacterMap_eq_of_multiplicativeType
    (DiagonalizableGroup.multiplicativeType_coordinateRing k G) hH f hf).exists
  -- The tautological character of `D(⟨χ⟩)` is defined over `k`; its image is the descent of `χ`.
  let x₀ : _root_.GroupLike k (DiagonalizableGroup.coordinateRing k G).obj :=
    ⟨_root_.MonoidAlgebra.single ⟨χ, Subgroup.mem_zpowers χ⟩ 1,
      _root_.MonoidAlgebra.isGroupLikeElem_single_one _⟩
  have hx₀ : groupLikeBaseChange x₀ = e.symm ⟨χ, Subgroup.mem_zpowers χ⟩ := by
    apply _root_.GroupLike.val_injective
    rw [val_groupLikeBaseChange, DiagonalizableGroup.geometricCharacterGroupEquiv_symm_apply_val]
  refine ⟨φ.hom.mapGroupLike x₀, ?_⟩
  rw [← CommHopfAlgCat.geometricCharacterMap_groupLikeBaseChange, hφ, hx₀]
  simp [f]

/-- **Characters over the ground field are the Galois-fixed geometric characters.** A geometric
character of a group of multiplicative type is the scalar extension of a character over `k`
exactly when it is fixed by the absolute Galois group. -/
theorem exists_groupLikeBaseChange_eq_iff (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (χ : CommHopfAlgCat.geometricCharacterGroup H.obj) :
    (∃ g : _root_.GroupLike k H.obj, groupLikeBaseChange g = χ) ↔
      ∀ σ : Field.absoluteGaloisGroup k, σ • χ = χ := by
  refine ⟨?_, hH.exists_groupLikeBaseChange_eq_of_forall_smul_eq⟩
  rintro ⟨g, rfl⟩ σ
  exact CommHopfAlgCat.smul_groupLikeBaseChange σ g

/-- The characters of a group of multiplicative type defined over the ground field, identified
by scalar extension with the Galois-fixed geometric characters. -/
noncomputable def groupLikeEquivFixedPoints (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    _root_.GroupLike k H.obj ≃*
      FixedPoints.subgroup (Field.absoluteGaloisGroup k)
        (CommHopfAlgCat.geometricCharacterGroup H.obj) :=
  MulEquiv.ofBijective
    ((groupLikeBaseChange (R := k) (K := AlgebraicClosure k) (A := H.obj)).codRestrict
      (FixedPoints.subgroup (Field.absoluteGaloisGroup k)
        (CommHopfAlgCat.geometricCharacterGroup H.obj))
      fun g ↦ (FixedPoints.mem_subgroup _ _ _).mpr fun σ ↦
        CommHopfAlgCat.smul_groupLikeBaseChange σ g)
    ⟨fun _ _ h ↦ groupLikeBaseChange_injective (congrArg Subtype.val h), fun χ ↦
      let ⟨g, hg⟩ := hH.exists_groupLikeBaseChange_eq_of_forall_smul_eq χ.property
      ⟨g, Subtype.ext hg⟩⟩

/-- The identification of characters over `k` with Galois-fixed geometric characters is scalar
extension. -/
@[simp]
theorem coe_groupLikeEquivFixedPoints_apply (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (g : _root_.GroupLike k H.obj) :
    (hH.groupLikeEquivFixedPoints g : CommHopfAlgCat.geometricCharacterGroup H.obj) =
      groupLikeBaseChange g := by
  rw [groupLikeEquivFixedPoints]
  rfl

/-- **A group of multiplicative type is diagonalizable exactly when the absolute Galois group
acts trivially on its geometric characters.** This holds over every field. -/
theorem groupLikeSpannedProperty_iff_forall_smul_eq
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    DiagonalizableGroup.groupLikeSpannedProperty k H ↔
      ∀ (σ : Field.absoluteGaloisGroup k) (χ : CommHopfAlgCat.geometricCharacterGroup H.obj),
        σ • χ = χ := by
  rw [DiagonalizableGroup.groupLikeSpannedProperty_iff,
    Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  constructor
  · intro hspan σ χ
    obtain ⟨g, rfl⟩ :=
      (groupLikeBaseChange_bijective (K := AlgebraicClosure k) hspan).2 χ
    exact CommHopfAlgCat.smul_groupLikeBaseChange σ g
  · intro htriv
    refine span_groupLike_eq_top_of_surjective (K := AlgebraicClosure k)
      (fun χ ↦ hH.exists_groupLikeBaseChange_eq_of_forall_smul_eq (htriv · χ)) ?_
    exact Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top.mp
      ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
        ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH))

end multiplicativeTypeCommHopfAlgProperty

namespace torusCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **A torus is split exactly when the absolute Galois group acts trivially on its character
lattice.** This holds over every field. -/
theorem splitTorusCommHopfAlgProperty_iff_forall_smul_eq (hH : torusCommHopfAlgProperty k H) :
    splitTorusCommHopfAlgProperty k H ↔
      ∀ (σ : Field.absoluteGaloisGroup k) (χ : CommHopfAlgCat.geometricCharacterGroup H.obj),
        σ • χ = χ := by
  rw [← (hH.multiplicativeType k H).groupLikeSpannedProperty_iff_forall_smul_eq]
  refine ⟨splitTorusCommHopfAlgProperty.groupLikeSpanned k H, fun hspan ↦ ?_⟩
  rw [← DiagonalizableGroup.essImage_coordinateRingFunctor] at hspan
  obtain ⟨G, ⟨i⟩⟩ := hspan
  -- The character group of the diagonalizable presentation is torsion-free, since `H` is a torus.
  have : IsMulTorsionFree G :=
    (torus_iff_isMulTorsionFree_of_baseChange_iso_coordinateRing
      G ((DiagonalizableGroup.baseChangeCoordinateRingIso k (AlgebraicClosure k) G).symm ≪≫
        (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).mapIso i)).mp hH
  exact (splitTorusCommHopfAlgProperty k).prop_of_iso i
    (splitTorusCommHopfAlgProperty_coordinateRing k G)

end torusCommHopfAlgProperty

namespace MultiplicativeTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- An absolute Galois element fixing every geometric character of a group of multiplicative type
fixes every cocharacter, since the Galois action on cocharacters is contragredient. -/
theorem smul_cocharacter_eq_of_forall_smul_eq (T : MultiplicativeTypeCommHopfAlgCat k)
    {σ : Field.absoluteGaloisGroup k}
    (hσ : ∀ χ : CommHopfAlgCat.geometricCharacterGroup T.obj.obj, σ • χ = χ)
    (f : cocharacterLattice T) : σ • f = f := by
  apply cocharacterLattice_ext
  intro x
  have hx : σ⁻¹ • x = x := by
    apply Additive.toMul.injective
    rw [CommHopfAlgCat.toMul_smul, inv_smul_eq_iff, hσ]
  rw [cocharacterLattice_smul_def, cocharacterGaloisRepresentation_apply_apply, hx]

end MultiplicativeTypeCommHopfAlgCat

namespace TorusCommHopfAlgCat

variable {k : Type u} [Field k]

/-- An absolute Galois element fixes every cocharacter of a torus exactly when it fixes every
character: the two lattices are in perfect, Galois-invariant duality. -/
theorem forall_smul_cocharacter_eq_iff (T : TorusCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k) :
    (∀ f : MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
        (toMultiplicativeTypeCommHopfAlgCat T), σ • f = f) ↔
      ∀ χ : CommHopfAlgCat.geometricCharacterGroup T.obj.obj, σ • χ = χ := by
  refine ⟨fun hf χ ↦ ?_, fun hχ ↦
    MultiplicativeTypeCommHopfAlgCat.smul_cocharacter_eq_of_forall_smul_eq _ hχ⟩
  let P := MultiplicativeTypeCommHopfAlgCat.characterCocharacterPairing
    (toMultiplicativeTypeCommHopfAlgCat T)
  -- The pairing is perfect for a torus, so a character is determined by its pairings.
  apply Additive.ofMul.injective
  apply P.toPerfPair.injective
  apply LinearMap.ext
  intro f
  have hσχ : Additive.ofMul (σ • χ) = σ • Additive.ofMul χ := by
    apply Additive.toMul.injective
    rw [CommHopfAlgCat.toMul_smul, toMul_ofMul, toMul_ofMul]
  have hP : P (σ • Additive.ofMul χ) (σ • f) = P (Additive.ofMul χ) f :=
    MultiplicativeTypeCommHopfAlgCat.characterCocharacterPairing_galois_invariant _ σ _ f
  simpa only [LinearMap.toPerfPair_apply, hf, hσχ] using hP

/-- **A torus is split exactly when the absolute Galois group acts trivially on its cocharacter
lattice.** This holds over every field. -/
theorem splitTorusCommHopfAlgProperty_iff_forall_smul_cocharacter_eq (T : TorusCommHopfAlgCat k) :
    splitTorusCommHopfAlgProperty k T.obj ↔
      ∀ (σ : Field.absoluteGaloisGroup k) (f : MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
        (toMultiplicativeTypeCommHopfAlgCat T)), σ • f = f := by
  simp only [forall_smul_cocharacter_eq_iff,
    T.property.splitTorusCommHopfAlgProperty_iff_forall_smul_eq]

end TorusCommHopfAlgCat

end TauCeti
