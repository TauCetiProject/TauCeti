/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-!
# Abelian schemes over a field are abelian varieties

Over `Spec K` for a field `K`, the abelian schemes of `TauCeti.AlgebraicGeometry.AbelianScheme`
and Tau Ceti's abelian varieties `TauCeti.AlgebraicGeometry.AbelianVariety K` are the same objects.
An abelian variety is a proper geometrically integral group scheme; it is smooth by the
group-scheme smoothness theorem and geometrically connected because it is geometrically
irreducible. Conversely a smooth morphism with geometrically connected fibres is geometrically
integral (`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`): after base change to a field
its local rings are regular, hence domains, and a connected locally Noetherian scheme with domain
local rings is irreducible.

## Main declarations

* `AbelianScheme.ofAbelianVariety`: an abelian variety over `K` as an abelian scheme over
  `Spec K`.
* `AbelianScheme.toAbelianVariety`: an abelian scheme over `Spec K` as an abelian variety.
* `AbelianScheme.equivAbelianVariety`: the two adapters are inverse bijections; both keep the
  underlying group scheme `toOver` and its group law.
* `AbelianScheme.ofAbelianVariety_baseChange`: the adapters commute with base change along a field
  extension.
* `AbelianScheme.fieldEquivalence`: the adapters extend to an equivalence between the category of
  abelian schemes over `Spec K` and the category of abelian varieties over `K`; both categories
  have the homomorphisms of the underlying group schemes as morphisms.

## References

* G. Faltings and C.-L. Chai, *Degeneration of abelian varieties*, Chapter I, §1.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

namespace AbelianScheme

universe u

variable {K : Type u} [Field K]

/-- An abelian variety over `K` as an abelian scheme over `Spec K`: the same group scheme, which
is smooth and geometrically connected. -/
@[expose] noncomputable def ofAbelianVariety (A : AbelianVariety K) :
    AbelianScheme (Spec (.of K)) where
  toOver := A.toOver
  grpObj := A.grpObj
  isProper := A.isProper
  smooth := inferInstance
  geometricallyConnected := inferInstance

@[simp]
lemma ofAbelianVariety_toOver (A : AbelianVariety K) : (ofAbelianVariety A).toOver = A.toOver :=
  (rfl)

/-- An abelian scheme over `Spec K` as an abelian variety over `K`: the same group scheme, which
is geometrically integral because it is smooth with geometrically connected fibres. -/
@[expose] noncomputable def toAbelianVariety (A : AbelianScheme (Spec (.of K))) :
    AbelianVariety K where
  toOver := A.toOver
  grpObj := A.grpObj
  isProper := A.isProper
  geometricallyIntegral := inferInstance

@[simp]
lemma toAbelianVariety_toOver (A : AbelianScheme (Spec (.of K))) :
    A.toAbelianVariety.toOver = A.toOver :=
  (rfl)

@[simp]
lemma toAbelianVariety_ofAbelianVariety (A : AbelianVariety K) :
    (ofAbelianVariety A).toAbelianVariety = A :=
  (rfl)

@[simp]
lemma ofAbelianVariety_toAbelianVariety (A : AbelianScheme (Spec (.of K))) :
    ofAbelianVariety A.toAbelianVariety = A :=
  (rfl)

/-- Abelian schemes over `Spec K` are the same as abelian varieties over `K`. -/
noncomputable def equivAbelianVariety : AbelianScheme (Spec (.of K)) ≃ AbelianVariety K where
  toFun := toAbelianVariety
  invFun := ofAbelianVariety
  left_inv := ofAbelianVariety_toAbelianVariety
  right_inv := toAbelianVariety_ofAbelianVariety

@[simp]
lemma equivAbelianVariety_apply (A : AbelianScheme (Spec (.of K))) :
    equivAbelianVariety A = A.toAbelianVariety :=
  (rfl)

@[simp]
lemma equivAbelianVariety_symm_apply (A : AbelianVariety K) :
    equivAbelianVariety.symm A = ofAbelianVariety A :=
  (rfl)

/-- The adapter `ofAbelianVariety` commutes with base change along a field extension `L / K`. -/
lemma ofAbelianVariety_baseChange (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    ofAbelianVariety (A.baseChange L) =
      (ofAbelianVariety A).baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  -- Both adapters keep `toOver` and the group law, so the `Grp.mk` of each side unfolds to the
  -- underlying group object of `A.baseChange L` (`grpMk_baseChange_toOver` on the right); and
  -- `CommGrp.toGrp` of `mapCommGrp.obj` is by definition `mapGrp.obj` of `CommGrp.toGrp`.
  ext (congrArg CommGrp.toGrp (A.commGrpMk_baseChange_toOver L))

/-- The adapter `toAbelianVariety` commutes with base change along a field extension `L / K`. -/
lemma toAbelianVariety_baseChange (A : AbelianScheme (Spec (.of K))) (L : Type u) [Field L]
    [Algebra K L] :
    (A.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).toAbelianVariety =
      A.toAbelianVariety.baseChange L := by
  conv_lhs => rw [← ofAbelianVariety_toAbelianVariety A, ← ofAbelianVariety_baseChange]
  exact toAbelianVariety_ofAbelianVariety _

/-! ### The equivalence of categories

The adapters are exposed so that `A.toAbelianVariety.toOver` and `(ofAbelianVariety A).toOver`
are definitionally the underlying group scheme `A.toOver`; this is what lets the two functors
below act as the identity on underlying morphisms. -/

noncomputable section

/-- The functor from abelian schemes over `Spec K` to abelian varieties over `K`, the identity on
underlying group-scheme homomorphisms. -/
@[expose] def toAbelianVarietyFunctor : AbelianScheme (Spec (.of K)) ⥤ AbelianVariety K where
  obj := toAbelianVariety
  map f := AbelianVariety.Hom.mk' (toOverHom f) (one_hom f) (mul_hom f)
  -- `rw` cannot use `AbelianVariety.Hom.toOverHom_mk'` here: its implicit objects are
  -- `A.toAbelianVariety`, whose `toOver` is `A.toOver` only after unfolding the exposed adapter.
  map_id A := AbelianVariety.Hom.toOverHom_injective <|
    (AbelianVariety.Hom.toOverHom_mk' _ _ _).trans <|
      (toOverHom_id A).trans (AbelianVariety.Hom.toOverHom_id A.toAbelianVariety).symm
  map_comp f g := AbelianVariety.Hom.toOverHom_injective <|
    (AbelianVariety.Hom.toOverHom_mk' _ _ _).trans <| (toOverHom_comp f g).trans <|
      .symm <| (AbelianVariety.Hom.toOverHom_comp _ _).trans <|
        congrArg₂ (· ≫ ·) (AbelianVariety.Hom.toOverHom_mk' _ _ _)
          (AbelianVariety.Hom.toOverHom_mk' _ _ _)

@[simp]
lemma toAbelianVarietyFunctor_obj (A : AbelianScheme (Spec (.of K))) :
    toAbelianVarietyFunctor.obj A = A.toAbelianVariety :=
  (rfl)

/-- `toAbelianVarietyFunctor` does not change the underlying morphism of a homomorphism. -/
@[simp]
lemma toOverHom_toAbelianVarietyFunctor_map {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    AbelianVariety.Hom.toOverHom (toAbelianVarietyFunctor.map f) = toOverHom f :=
  AbelianVariety.Hom.toOverHom_mk' _ _ _

/-- The functor from abelian varieties over `K` to abelian schemes over `Spec K`, the identity on
underlying group-scheme homomorphisms. -/
@[expose] def ofAbelianVarietyFunctor : AbelianVariety K ⥤ AbelianScheme (Spec (.of K)) where
  obj := ofAbelianVariety
  map g := homMk (AbelianVariety.Hom.toOverHom g) (AbelianVariety.Hom.one_hom g)
    (AbelianVariety.Hom.mul_hom g)
  -- As above, `toOverHom_homMk` is applied as a term rather than by `rw`.
  map_id A := toOverHom_injective <|
    (toOverHom_homMk _ _ _).trans <|
      (AbelianVariety.Hom.toOverHom_id A).trans (toOverHom_id (ofAbelianVariety A)).symm
  map_comp f g := toOverHom_injective <|
    (toOverHom_homMk _ _ _).trans <| (AbelianVariety.Hom.toOverHom_comp f g).trans <|
      .symm <| (toOverHom_comp _ _).trans <|
        congrArg₂ (· ≫ ·) (toOverHom_homMk _ _ _) (toOverHom_homMk _ _ _)

@[simp]
lemma ofAbelianVarietyFunctor_obj (A : AbelianVariety K) :
    ofAbelianVarietyFunctor.obj A = ofAbelianVariety A :=
  (rfl)

/-- `ofAbelianVarietyFunctor` does not change the underlying morphism of a homomorphism. -/
@[simp]
lemma toOverHom_ofAbelianVarietyFunctor_map {A B : AbelianVariety K} (g : A ⟶ B) :
    toOverHom (ofAbelianVarietyFunctor.map g) = AbelianVariety.Hom.toOverHom g :=
  toOverHom_homMk _ _ _

/-- `ofAbelianVarietyFunctor` undoes `toAbelianVarietyFunctor` on homomorphisms: both keep the
underlying morphism, and the source and target objects agree by definition. -/
private lemma ofAbelianVarietyFunctor_map_toAbelianVarietyFunctor_map
    {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    ofAbelianVarietyFunctor.map (toAbelianVarietyFunctor.map f) = f :=
  toOverHom_injective <| (toOverHom_ofAbelianVarietyFunctor_map _).trans
    (toOverHom_toAbelianVarietyFunctor_map f)

/-- `toAbelianVarietyFunctor` undoes `ofAbelianVarietyFunctor` on homomorphisms: both keep the
underlying morphism, and the source and target objects agree by definition. -/
private lemma toAbelianVarietyFunctor_map_ofAbelianVarietyFunctor_map {A B : AbelianVariety K}
    (g : A ⟶ B) : toAbelianVarietyFunctor.map (ofAbelianVarietyFunctor.map g) = g :=
  AbelianVariety.Hom.toOverHom_injective <| (toOverHom_toAbelianVarietyFunctor_map _).trans
    (toOverHom_ofAbelianVarietyFunctor_map g)

/-- **Field boundary of abelian schemes.** Over `Spec K` the adapters `toAbelianVariety` and
`ofAbelianVariety` form an equivalence between the category of abelian schemes over `Spec K` and
the category of abelian varieties over `K`, each with group-scheme homomorphisms as morphisms. -/
def fieldEquivalence : AbelianScheme (Spec (.of K)) ≌ AbelianVariety K where
  functor := toAbelianVarietyFunctor
  inverse := ofAbelianVarietyFunctor
  -- Each naturality square is `f ≫ 𝟙 = 𝟙 ≫ f'` with `f' = f` by the helper lemmas above.
  unitIso := NatIso.ofComponents (fun A ↦ Iso.refl A) fun f ↦ (Category.comp_id f).trans <|
    ((Category.id_comp _).trans (ofAbelianVarietyFunctor_map_toAbelianVarietyFunctor_map f)).symm
  counitIso := NatIso.ofComponents (fun A ↦ Iso.refl A) fun f ↦ (Category.comp_id _).trans <|
    (toAbelianVarietyFunctor_map_ofAbelianVarietyFunctor_map f).trans (Category.id_comp f).symm
  functor_unitIso_comp A := AbelianVariety.Hom.toOverHom_injective <| by
    rw [AbelianVariety.Hom.toOverHom_comp, toOverHom_toAbelianVarietyFunctor_map]
    -- Unit and counit components are identities of the same underlying group scheme.
    exact Category.comp_id _

@[simp]
lemma fieldEquivalence_functor : fieldEquivalence.functor = toAbelianVarietyFunctor (K := K) :=
  (rfl)

@[simp]
lemma fieldEquivalence_inverse : fieldEquivalence.inverse = ofAbelianVarietyFunctor (K := K) :=
  (rfl)

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
