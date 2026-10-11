/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.Algebra.GroupAction.AlgHom
public import TauCeti.FieldTheory.GaloisGroups.NormalClosure
public import TauCeti.FieldTheory.IntermediateField.Adjoin.Embeddings

/-!
# Embeddings of a simple field indexed by root-stabilizer cosets

Let `x` lie in a normal extension of `F`, and put `N` for the normal closure of `F⟮x⟯` in
that extension.  The `F`-embeddings of `F⟮x⟯` into `N` are determined by the image of the
generator, which is a root of `minpoly F x`.  By orbit-stabilizer, they are therefore indexed by
the cosets `G / H` of a root stabilizer `H`, either in `G = Gal(N/F)` or in the polynomial
Galois group of `minpoly F x`.  These identifications respect the Galois action by
postcomposition.

## Main results

* `TauCeti.quotientStabilizerEquivAlgHomSimpleField`: the quotient of the normal-closure Galois
  group by a root stabilizer is the set of embeddings of the simple field.
* `TauCeti.quotientGalStabilizerEquivAlgHomSimpleField`: the corresponding quotient of the
  polynomial Galois group indexes those embeddings.
* `TauCeti.quotientStabilizerEquivAlgHomSimpleField_smul`: this equivalence respects the
  Galois action by postcomposition.
-/

public section

namespace TauCeti

open _root_.IntermediateField MulAction Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E]

/-- The cosets of the stabilizer of a root are in bijection with the `F`-embeddings of `F⟮x⟯`
into its normal closure. -/
noncomputable def quotientStabilizerEquivAlgHomSimpleField (x : E)
    (y : (minpoly F x).rootSet (normalClosure F F⟮x⟯ E)) :
    Gal(normalClosure F F⟮x⟯ E/F) ⧸
        stabilizer Gal(normalClosure F F⟮x⟯ E/F)
          (y : normalClosure F F⟮x⟯ E) ≃
      (F⟮x⟯ →ₐ[F] normalClosure F F⟮x⟯ E) :=
  (rootSetEquivQuotientStabilizer
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)) y.2).symm.trans
    (rootSetEquivAlgHomAdjoin F (normalClosure F F⟮x⟯ E) x
      (Algebra.IsIntegral.isIntegral x))

/-- The embedding indexed by the coset of `σ` sends the generator to `σ • y`. -/
@[simp]
theorem quotientStabilizerEquivAlgHomSimpleField_mk_gen (x : E)
    (y : (minpoly F x).rootSet (normalClosure F F⟮x⟯ E))
    (σ : Gal(normalClosure F F⟮x⟯ E/F)) :
    quotientStabilizerEquivAlgHomSimpleField x y (QuotientGroup.mk σ)
      (AdjoinSimple.gen F x) = σ • (y : normalClosure F F⟮x⟯ E) := by
  simp only [quotientStabilizerEquivAlgHomSimpleField, Equiv.trans_apply,
    rootSetEquivAlgHomAdjoin_apply_gen,
    coe_rootSetEquivQuotientStabilizer_symm_apply_mk]

/-- The coset-to-embedding correspondence intertwines the Galois action on cosets with
postcomposition on embeddings. -/
@[simp]
theorem quotientStabilizerEquivAlgHomSimpleField_smul (x : E)
    (y : (minpoly F x).rootSet (normalClosure F F⟮x⟯ E))
    (σ : Gal(normalClosure F F⟮x⟯ E/F))
    (c : Gal(normalClosure F F⟮x⟯ E/F) ⧸
      stabilizer Gal(normalClosure F F⟮x⟯ E/F) (y : normalClosure F F⟮x⟯ E)) :
    quotientStabilizerEquivAlgHomSimpleField x y (σ • c) =
      σ • quotientStabilizerEquivAlgHomSimpleField x y c := by
  apply adjoin_algHom_ext F
  intro a ha
  simp only [Set.mem_singleton_iff] at ha
  subst a
  -- Extensionality gives evaluation at the singleton generator; `change` exposes that
  -- generator through the `AdjoinSimple.gen` coercion used by the evaluation lemmas below.
  change (quotientStabilizerEquivAlgHomSimpleField x y (σ • c))
      (AdjoinSimple.gen F x) =
    (σ • quotientStabilizerEquivAlgHomSimpleField x y c) (AdjoinSimple.gen F x)
  let e := rootSetEquivQuotientStabilizer
    (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)) y.2
  have he : e.symm (σ • c) = σ • e.symm c := by
    apply e.injective
    rw [e.apply_symm_apply, rootSetEquivQuotientStabilizer_smul,
      e.apply_symm_apply]
  simpa only [quotientStabilizerEquivAlgHomSimpleField, Equiv.trans_apply,
    rootSetEquivAlgHomAdjoin_apply_gen, AlgEquiv.smul_algHom_apply, e, rootSet.coe_smul,
    AlgEquiv.smul_def] using
    congrArg Subtype.val he

/-- The polynomial Galois group equivalence sends a point stabilizer to the stabilizer of the
transported root. -/
private theorem map_stabilizer_galEquivNormalClosure_eq_stabilizer (x : E)
    (y : (minpoly F x).rootSet (minpoly F x).SplittingField) :
    (stabilizer (minpoly F x).Gal y).map
      ((galEquivNormalClosure (F := F) (E := E) x) : _ →* _) =
      stabilizer Gal(normalClosure F F⟮x⟯ E/F)
        (splittingFieldEquivNormalClosure x (y : (minpoly F x).SplittingField)) := by
  simpa only [MulEquiv.toMonoidHom_eq_coe, fixingSubgroup_adjoin_simple] using
    map_stabilizer_galEquivNormalClosure (F := F) (E := E) x y

/-- Cosets in the polynomial Galois group of a root stabilizer index the embeddings of
the simple field into its normal closure. -/
noncomputable def quotientGalStabilizerEquivAlgHomSimpleField (x : E)
    (y : (minpoly F x).rootSet (minpoly F x).SplittingField) :
    (minpoly F x).Gal ⧸ stabilizer (minpoly F x).Gal y ≃
      (F⟮x⟯ →ₐ[F] normalClosure F F⟮x⟯ E) := by
  let e := splittingFieldEquivNormalClosure (F := F) (E := E) x
  let y' : (minpoly F x).rootSet (normalClosure F F⟮x⟯ E) :=
    ⟨e y, rootSet_mapsTo e.toAlgHom y.2⟩
  exact (QuotientGroup.congrOfMapEq (galEquivNormalClosure (F := F) (E := E) x)
    (map_stabilizer_galEquivNormalClosure_eq_stabilizer x y)).trans
      (quotientStabilizerEquivAlgHomSimpleField x y')

/-- A polynomial Galois coset represented by `σ` sends the generator to the image of `y`
under `σ`, transported to the normal closure. -/
@[simp]
theorem quotientGalStabilizerEquivAlgHomSimpleField_mk_gen (x : E)
    (y : (minpoly F x).rootSet (minpoly F x).SplittingField)
    (σ : (minpoly F x).Gal) :
    quotientGalStabilizerEquivAlgHomSimpleField x y (QuotientGroup.mk σ)
      (AdjoinSimple.gen F x) =
      splittingFieldEquivNormalClosure (F := F) (E := E) x (σ • y :
        (minpoly F x).SplittingField) := by
  let y' : (minpoly F x).rootSet (normalClosure F F⟮x⟯ E) :=
    ⟨splittingFieldEquivNormalClosure x y,
      rootSet_mapsTo (splittingFieldEquivNormalClosure x).toAlgHom y.2⟩
  -- The composite equivalence is defined with local transports, so `rw` cannot see its
  -- final component until the application is exposed.
  change quotientStabilizerEquivAlgHomSimpleField x y'
      (QuotientGroup.congrOfMapEq (galEquivNormalClosure x)
        (map_stabilizer_galEquivNormalClosure_eq_stabilizer x y)
        (QuotientGroup.mk σ)) (AdjoinSimple.gen F x) = _
  rw [QuotientGroup.congrOfMapEq_mk]
  rw [quotientStabilizerEquivAlgHomSimpleField_mk_gen]
  exact galEquivNormalClosure_apply x σ y

/-- The polynomial Galois coset-to-embedding equivalence respects postcomposition. -/
@[simp]
theorem quotientGalStabilizerEquivAlgHomSimpleField_smul (x : E)
    (y : (minpoly F x).rootSet (minpoly F x).SplittingField)
    (σ : (minpoly F x).Gal)
    (q : (minpoly F x).Gal ⧸ stabilizer (minpoly F x).Gal y) :
    quotientGalStabilizerEquivAlgHomSimpleField x y (σ • q) =
      galEquivNormalClosure x σ • quotientGalStabilizerEquivAlgHomSimpleField x y q := by
  induction q using Quotient.inductionOn' with
  | _ τ =>
    apply adjoin_algHom_ext F
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    -- The quotient action on representatives reduces definitionally to multiplication.
    change quotientGalStabilizerEquivAlgHomSimpleField x y
        (QuotientGroup.mk (σ * τ)) (AdjoinSimple.gen F x) =
      (galEquivNormalClosure x σ • quotientGalStabilizerEquivAlgHomSimpleField x y
        (QuotientGroup.mk τ)) (AdjoinSimple.gen F x)
    simp [quotientGalStabilizerEquivAlgHomSimpleField_mk_gen,
      AlgEquiv.smul_algHom_apply, mul_smul]


end TauCeti
