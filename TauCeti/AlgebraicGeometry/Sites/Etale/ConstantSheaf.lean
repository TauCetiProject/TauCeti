/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Category.ModuleCat.ForgetCorepresentable
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
public import TauCeti.AlgebraicGeometry.Sites.Etale.Subcanonical
public import TauCeti.AlgebraicGeometry.Sites.Small
public import TauCeti.CategoryTheory.Sites.Grothendieck
public import TauCeti.Topology.LocallyConstant.Basic

/-!
# The constant étale sheaf is the sheaf of locally constant functions

For a scheme `S` and a set `M`, the presheaf on the small étale site of `S` sending an étale
`S`-scheme `U` to the locally constant functions `U → M` is an étale sheaf
(`AlgebraicGeometry.Scheme.etaleLocallyConstantSheaf`): with the discrete topology on `M`, these
are the continuous maps to `M`, which form a sheaf even for the fpqc topology by Mathlib's
`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`.

This sheaf is the constant étale sheaf with value `M`
(`AlgebraicGeometry.Scheme.constantSheafIsoEtaleLocallyConstantSheaf`), naturally in `M`. The
comparison is induced by the map from the constant presheaf sending `m` to the constant
function `m`, which is locally bijective:

* it is locally injective, since two different constants agree only on an empty scheme, which is
  covered by the empty family (`AlgebraicGeometry.Scheme.bot_mem_smallGrothendieckTopology`);
* it is locally surjective, since a locally constant function is constant on each of its fibres,
  and these fibres are open subschemes, hence étale, covering the source.

So the sections of the constant étale sheaf over `U` are the locally constant functions on the
underlying space of `U`, and its global sections are the locally constant functions on `S`. This
is the concrete description used to recognise constant and locally constant étale sheaves, for
example the sheaves of sections of split finite étale covers.

In addition, for any concrete category `A` whose constant-presheaf sheafification map is locally
injective, `toSheafify` is injective on sections over any nonempty étale `S`-scheme
(`AlgebraicGeometry.Scheme.injective_toSheafify_app_const_smallEtaleTopology`). For a ring `Λ`,
any morphism between constant étale sheaves of `Λ`-modules whose source is finitely generated
comes étale-locally from a constant `Λ`-linear map
(`CategoryTheory.Sheaf.exists_etaleCover_map_constantSheaf`).

## Main definitions

* `AlgebraicGeometry.Scheme.etaleLocallyConstantSheaf S`: the étale sheaf of locally constant
  functions `U ↦ LocallyConstant U M`, as a functor of `M`.
* `AlgebraicGeometry.Scheme.constToEtaleLocallyConstantPresheaf S`: the map from the constant
  presheaf sending `m` to the constant function `m`.
* `AlgebraicGeometry.Scheme.constantSheafIsoEtaleLocallyConstantSheaf S`: the constant étale sheaf
  functor is isomorphic to `etaleLocallyConstantSheaf S`.
* `AlgebraicGeometry.Scheme.etaleConstantSheafSectionsEquiv S M U`: the sections over `U` of the
  constant étale sheaf with value `M` are the locally constant functions `U → M`.

## Main results

* `AlgebraicGeometry.Scheme.isSheaf_etaleLocallyConstantPresheaf`: locally constant functions form
  an étale sheaf.
* `AlgebraicGeometry.Scheme.toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom`: the
  comparison sends the class of `m` to the constant function `m`.
* `AlgebraicGeometry.Scheme.injective_toSheafify_app_const_smallEtaleTopology`: over a nonempty
  étale `S`-scheme, `toSheafify` on a constant presheaf is injective.
* `CategoryTheory.Sheaf.exists_etaleCover_map_constantSheaf`: a morphism between constant étale
  sheaves of `Λ`-modules whose source is finitely generated is étale-locally constant.
* The sheaf of locally constant functions with values in `M` is a constant sheaf in the sense of
  `CategoryTheory.Sheaf.IsConstant`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.0 and §2.7, for constant and
  locally constant étale sheaves.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The presheaf on the small étale site of `S` of locally constant functions with values in `M`,
`U ↦ LocallyConstant U M`, as a functor of `M`. Restriction is composition with the underlying
continuous map, and a map `M → M'` acts by composition. -/
@[expose, implicit_reducible, simps]
def etaleLocallyConstantPresheaf : Type u ⥤ S.Etaleᵒᵖ ⥤ Type u where
  obj M :=
    { obj U := LocallyConstant U.unop.left M
      map f := TypeCat.ofHom fun g ↦ g.comap f.unop.left.base.hom }
  map φ := { app U := TypeCat.ofHom fun g ↦ g.map φ }

/-- **Locally constant functions form an étale sheaf.** For the discrete topology on `M`, these
are the continuous maps to `M`, which form a sheaf for the fpqc topology, a fortiori for the
étale topology. -/
theorem isSheaf_etaleLocallyConstantPresheaf (M : Type u) :
    Presheaf.IsSheaf (smallEtaleTopology S) ((etaleLocallyConstantPresheaf S).obj M) := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have := Functor.isContinuous_comp (Etale.forget S) (Over.forget S) (smallEtaleTopology S)
    (etaleTopology.over S) etaleTopology
  have h := (Etale.forget S ⋙ Over.forget S).op_comp_isSheaf_of_isSheaf
    (smallEtaleTopology S) etaleTopology (continuousMapPresheaf M)
    ((isSheaf_fpqcTopology_continuousMapPresheaf M).of_le
      (etaleTopology_le_proetaleTopology.trans proetaleTopology_le_fpqcTopology))
  -- For the discrete topology on `M`, locally constant functions are continuous maps.
  refine (Presheaf.isSheaf_of_iso_iff (NatIso.ofComponents (fun U ↦ Equiv.toIso
    (LocallyConstant.equivContinuousMap U.unop.left M)) fun _ ↦ rfl)).2 h

/-- The étale sheaf of locally constant functions with values in `M`, `U ↦ LocallyConstant U M`,
as a functor of `M`. It is the constant étale sheaf, by
`constantSheafIsoEtaleLocallyConstantSheaf`. -/
@[expose, implicit_reducible, simps! obj_obj map_hom]
def etaleLocallyConstantSheaf : Type u ⥤ Sheaf (smallEtaleTopology S) (Type u) :=
  ObjectProperty.lift _ (etaleLocallyConstantPresheaf S)
    (isSheaf_etaleLocallyConstantPresheaf S)

/-- The map from the constant presheaf with value `M` to the locally constant functions, sending
`m` to the constant function `m`, naturally in `M`. -/
def constToEtaleLocallyConstantPresheaf :
    Functor.const S.Etaleᵒᵖ ⟶ etaleLocallyConstantPresheaf S where
  app M := { app U := TypeCat.ofHom fun m ↦ LocallyConstant.const _ m }

/-- The component of `constToEtaleLocallyConstantPresheaf` at `M` and `U` sends `m` to the
constant function `m`. -/
@[simp]
theorem constToEtaleLocallyConstantPresheaf_app_app (M : Type u) (U : S.Etaleᵒᵖ) :
    ((constToEtaleLocallyConstantPresheaf S).app M).app U =
      TypeCat.ofHom fun m ↦ LocallyConstant.const U.unop.left m :=
  (rfl)

/-- Constant sections that agree are locally equal: two different constants agree only over an
empty étale `S`-scheme, which is covered by the empty sieve. -/
instance (M : Type u) : Presheaf.IsLocallyInjective (smallEtaleTopology S)
    ((constToEtaleLocallyConstantPresheaf S).app M) where
  equalizerSieve_mem {U} m m' h := by
    by_cases hm : m = m'
    · subst hm
      simp
    · have : IsEmpty U.unop.left := ⟨fun x ↦ hm ?_⟩
      · exact (smallEtaleTopology S).superset_covering bot_le
          (bot_mem_smallGrothendieckTopology _)
      -- By definition, the sections of `(etaleLocallyConstantPresheaf S).obj M` over `U` are
      -- `LocallyConstant U.unop.left M`, and the component of `constToEtaleLocallyConstantPresheaf`
      -- at `U` is `TypeCat.ofHom` of `LocallyConstant.const`, so `h` is this equation.
      have h' : LocallyConstant.const U.unop.left m = LocallyConstant.const U.unop.left m' := h
      simpa using congr($h' x)

/-- Every locally constant function is locally constant in the strict sense: it is constant on
each of its fibres, and these are open subschemes covering the source. -/
instance (M : Type u) : Presheaf.IsLocallySurjective (smallEtaleTopology S)
    ((constToEtaleLocallyConstantPresheaf S).app M) where
  imageSieve_mem {U} s' := by
    -- By definition, the sections of `(etaleLocallyConstantPresheaf S).obj M` over `U` are
    -- `LocallyConstant U.left M`.
    let s : LocallyConstant U.left M := s'
    -- The fibre of `s` over `m`, an open subscheme of `U`, hence étale over `S`.
    let V (m : M) : U.left.Opens := ⟨s ⁻¹' {m}, s.isLocallyConstant.isOpen_fiber m⟩
    let f (m : M) : Etale.mk ((V m).ι ≫ U.hom) ⟶ U := MorphismProperty.Over.homMk (V m).ι
    refine (smallEtaleTopology S).superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff f).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      -- Restriction along `f m` is `LocallyConstant.comap` of the inclusion of the fibre `V m`, on
      -- which `s` is the constant `m`.
      exact fun m ↦ ⟨m, LocallyConstant.ext fun x ↦ x.property.symm⟩
    · exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨s x, ⟨x, rfl⟩, rfl⟩

/-- The map from the constant étale sheaf with value `M`, written as the sheafification of the
constant presheaf, to the sheaf of locally constant functions, induced by
`constToEtaleLocallyConstantPresheaf`. -/
noncomputable def constantSheafToEtaleLocallyConstantSheaf (M : Type u) :
    (presheafToSheaf (smallEtaleTopology S) (Type u)).obj ((Functor.const _).obj M) ⟶
      (etaleLocallyConstantSheaf S).obj M :=
  ⟨sheafifyLift _ ((constToEtaleLocallyConstantPresheaf S).app M)
    (isSheaf_etaleLocallyConstantPresheaf S M)⟩

/-- The class in the constant sheaf of an element `m` is sent to the constant function `m`. -/
@[reassoc (attr := simp)]
theorem toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom (M : Type u) :
    toSheafify (smallEtaleTopology S) ((Functor.const _).obj M) ≫
      (constantSheafToEtaleLocallyConstantSheaf S M).hom =
      (constToEtaleLocallyConstantPresheaf S).app M :=
  toSheafify_sheafifyLift _ _ _

/-- The map from the constant sheaf to the sheaf of locally constant functions is natural. -/
@[reassoc (attr := simp)]
theorem constantSheafToEtaleLocallyConstantSheaf_naturality {M M' : Type u} (φ : M ⟶ M') :
    (presheafToSheaf (smallEtaleTopology S) (Type u)).map ((Functor.const _).map φ) ≫
      constantSheafToEtaleLocallyConstantSheaf S M' =
      constantSheafToEtaleLocallyConstantSheaf S M ≫ (etaleLocallyConstantSheaf S).map φ := by
  refine Sheaf.hom_ext (sheafify_hom_ext _ _ _ (isSheaf_etaleLocallyConstantPresheaf S M') ?_)
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ← toSheafify_naturality_assoc,
    toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom,
    toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom_assoc]
  exact (constToEtaleLocallyConstantPresheaf S).naturality φ

instance (M : Type u) : IsIso (constantSheafToEtaleLocallyConstantSheaf S M) :=
  -- On presheaves, the map precomposed with `toSheafify` is the locally bijective
  -- `constToEtaleLocallyConstantPresheaf`, so it is a weak equivalence by two-out-of-three.
  ((smallEtaleTopology S).W_sheafToPresheaf_map_iff_isIso _).1 <|
    (smallEtaleTopology S).W.of_precomp _ _ ((smallEtaleTopology S).W_toSheafify _) <| by
      rw [ObjectProperty.ι_map, toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom]
      exact (smallEtaleTopology S).W_of_isLocallyBijective
        ((constToEtaleLocallyConstantPresheaf S).app M)

/-- The constant function `m` is sent back to the class of `m` in the constant sheaf. -/
@[reassoc (attr := simp)]
theorem
    constToEtaleLocallyConstantPresheaf_app_comp_inv_constantSheafToEtaleLocallyConstantSheaf_hom
    (M : Type u) :
    (constToEtaleLocallyConstantPresheaf S).app M ≫
        inv (constantSheafToEtaleLocallyConstantSheaf S M).hom =
      toSheafify (smallEtaleTopology S) ((Functor.const _).obj M) :=
  (IsIso.comp_inv_eq (α := (constantSheafToEtaleLocallyConstantSheaf S M).hom)).2
    (toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom S M).symm

/-- **The constant étale sheaf is the sheaf of locally constant functions**: for every set `M`,
the constant sheaf with value `M` on the small étale site of `S` is the sheaf
`U ↦ LocallyConstant U M`, naturally in `M`. -/
noncomputable def constantSheafIsoEtaleLocallyConstantSheaf :
    constantSheaf (smallEtaleTopology S) (Type u) ≅ etaleLocallyConstantSheaf S :=
  -- `constantSheaf` is by definition the sheafification of the constant presheaf; elaborating
  -- `asIso` without the expected type lets the `IsIso` instance be found in that form.
  NatIso.ofComponents (fun M ↦ (asIso (constantSheafToEtaleLocallyConstantSheaf S M) :))
    (constantSheafToEtaleLocallyConstantSheaf_naturality S)

/-- The components of the comparison isomorphism are the comparison maps. This and
`constantSheafIsoEtaleLocallyConstantSheaf_inv_app` are not `simp` lemmas: their right-hand sides
have source the sheafification of the constant presheaf rather than `constantSheaf`, so rewriting
with them would stop `simp` from cancelling the components of the isomorphism. -/
theorem constantSheafIsoEtaleLocallyConstantSheaf_hom_app (M : Type u) :
    (constantSheafIsoEtaleLocallyConstantSheaf S).hom.app M =
      constantSheafToEtaleLocallyConstantSheaf S M :=
  (rfl)

/-- The components of the inverse of the comparison isomorphism are the inverses of the comparison
maps. -/
theorem constantSheafIsoEtaleLocallyConstantSheaf_inv_app (M : Type u) :
    (constantSheafIsoEtaleLocallyConstantSheaf S).inv.app M =
      inv (constantSheafToEtaleLocallyConstantSheaf S M) :=
  (rfl)

/-- The comparison isomorphism sends the class of a constant to that constant function. -/
@[simp]
theorem toSheafify_comp_constantSheafIsoEtaleLocallyConstantSheaf_hom_app_hom (M : Type u) :
    toSheafify (smallEtaleTopology S) ((Functor.const _).obj M) ≫
        ((constantSheafIsoEtaleLocallyConstantSheaf S).hom.app M).hom =
      (constToEtaleLocallyConstantPresheaf S).app M :=
  toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom S M

/-- The comparison isomorphism sends the class of a constant to that constant function,
followed by any presheaf morphism. -/
-- Written explicitly because `sheafify` and `constantSheaf` do not agree at the transparency
-- used by `reassoc`.
@[simp]
theorem toSheafify_comp_constantSheafIsoEtaleLocallyConstantSheaf_hom_app_hom_assoc
    (M : Type u) {F : S.Etaleᵒᵖ ⥤ Type u}
    (f : ((etaleLocallyConstantSheaf S).obj M).obj ⟶ F) :
    toSheafify (smallEtaleTopology S) ((Functor.const _).obj M) ≫
        ((constantSheafIsoEtaleLocallyConstantSheaf S).hom.app M).hom ≫ f =
      (constToEtaleLocallyConstantPresheaf S).app M ≫ f :=
  toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom_assoc S M f

/-- The inverse comparison isomorphism sends a constant function back to its class. -/
@[reassoc (attr := simp)]
theorem
  constToEtaleLocallyConstantPresheaf_app_comp_constantSheafIsoEtaleLocallyConstantSheaf_inv_app_hom
    (M : Type u) :
    (constToEtaleLocallyConstantPresheaf S).app M ≫
        ((constantSheafIsoEtaleLocallyConstantSheaf S).inv.app M).hom =
      toSheafify (smallEtaleTopology S) ((Functor.const _).obj M) := by
  apply (cancel_mono ((constantSheafIsoEtaleLocallyConstantSheaf S).hom.app M).hom).1
  simp only [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.inv_hom_id_app, ObjectProperty.FullSubcategory.id_hom]
  exact (toSheafify_comp_constantSheafIsoEtaleLocallyConstantSheaf_hom_app_hom S M).symm

/-- The inverse of the comparison map is natural. -/
@[reassoc (attr := simp)]
theorem inv_constantSheafToEtaleLocallyConstantSheaf_naturality {M M' : Type u} (φ : M ⟶ M') :
    (etaleLocallyConstantSheaf S).map φ ≫ inv (constantSheafToEtaleLocallyConstantSheaf S M') =
      inv (constantSheafToEtaleLocallyConstantSheaf S M) ≫
        (presheafToSheaf (smallEtaleTopology S) (Type u)).map ((Functor.const _).map φ) := by
  rw [IsIso.eq_inv_comp, ← constantSheafToEtaleLocallyConstantSheaf_naturality_assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The sheaf of locally constant functions with values in `M` is a constant étale sheaf. -/
instance (M : Type u) : ((etaleLocallyConstantSheaf S).obj M).IsConstant (smallEtaleTopology S) :=
  Sheaf.isConstant_of_iso _ ((constantSheafIsoEtaleLocallyConstantSheaf S).app M).symm

/-- **Sections of the constant étale sheaf**: the sections over an étale `S`-scheme `U` of the
constant sheaf with value `M` are the locally constant functions `U → M`. -/
noncomputable def etaleConstantSheafSectionsEquiv (M : Type u) (U : S.Etale) :
    ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U) ≃
      LocallyConstant U.left M :=
  (((sheafToPresheaf _ _).mapIso ((constantSheafIsoEtaleLocallyConstantSheaf S).app M)).app
    (op U)).toEquiv

/-- The sections equivalence is the component at `U` of the comparison map. -/
theorem etaleConstantSheafSectionsEquiv_apply (M : Type u) (U : S.Etale)
    (x : ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U)) :
    etaleConstantSheafSectionsEquiv S M U x =
      ((constantSheafIsoEtaleLocallyConstantSheaf S).hom.app M).hom.app (op U) x :=
  (rfl)

/-- Evaluating the comparison isomorphism on a section gives its locally constant function. -/
@[simp]
theorem constantSheafIsoEtaleLocallyConstantSheaf_hom_app_hom_app_apply (M : Type u) (U : S.Etale)
    (x : ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U)) :
    (dsimp% ((constantSheafIsoEtaleLocallyConstantSheaf S).hom.app M).hom.app (op U) x) =
      etaleConstantSheafSectionsEquiv S M U x :=
  (etaleConstantSheafSectionsEquiv_apply S M U x).symm

/-- The class of `m` in the constant étale sheaf corresponds to the constant function `m`. -/
@[simp]
theorem etaleConstantSheafSectionsEquiv_toSheafify_app (M : Type u) (U : S.Etale) (m : M) :
    -- The source is written as `M` rather than `((Functor.const _).obj M).obj (op U)`, the form
    -- `simp` reaches through `Functor.const_obj_obj`.
    etaleConstantSheafSectionsEquiv S M U (ConcreteCategory.hom (X := M)
      ((toSheafify (smallEtaleTopology S) ((Functor.const _).obj M)).app (op U)) m) =
      LocallyConstant.const _ m :=
  congr($(toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom S M).app (op U) m)

/-- Restricting a section of the constant étale sheaf along `f : V ⟶ U` corresponds to composing
the locally constant function with `f`. -/
@[simp]
theorem etaleConstantSheafSectionsEquiv_map (M : Type u) {U V : S.Etale} (f : V ⟶ U)
    (x : ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U)) :
    etaleConstantSheafSectionsEquiv S M V
      (((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.map f.op x) =
      (etaleConstantSheafSectionsEquiv S M U x).comap f.left.base.hom :=
  congr($(((constantSheafToEtaleLocallyConstantSheaf S M).hom.naturality f.op)) x)

/-- The map of constant étale sheaves induced by `φ : M ⟶ M'` corresponds to composing locally
constant functions with `φ`. -/
@[simp]
theorem etaleConstantSheafSectionsEquiv_naturality {M M' : Type u} (φ : M ⟶ M') (U : S.Etale)
    (x : ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U)) :
    etaleConstantSheafSectionsEquiv S M' U
      (((constantSheaf (smallEtaleTopology S) (Type u)).map φ).hom.app (op U) x) =
      (etaleConstantSheafSectionsEquiv S M U x).map φ :=
  congr($(constantSheafToEtaleLocallyConstantSheaf_naturality S φ).hom.app (op U) x)

/-- The inverse of the sections equivalence is the component at `U` of the inverse of the
comparison map. -/
theorem etaleConstantSheafSectionsEquiv_symm_apply (M : Type u) (U : S.Etale)
    (g : LocallyConstant U.left M) :
    (etaleConstantSheafSectionsEquiv S M U).symm g =
      ((constantSheafIsoEtaleLocallyConstantSheaf S).inv.app M).hom.app (op U) g :=
  (rfl)

/-- Evaluating the inverse comparison isomorphism gives the section attached to a locally
constant function. -/
@[simp]
theorem constantSheafIsoEtaleLocallyConstantSheaf_inv_app_hom_app_apply (M : Type u) (U : S.Etale)
    (g : LocallyConstant U.left M) :
    (dsimp% ((constantSheafIsoEtaleLocallyConstantSheaf S).inv.app M).hom.app (op U) g) =
      (etaleConstantSheafSectionsEquiv S M U).symm g :=
  (etaleConstantSheafSectionsEquiv_symm_apply S M U g).symm

/-- The constant function `m` corresponds to the class of `m` in the constant étale sheaf. -/
@[simp]
theorem etaleConstantSheafSectionsEquiv_symm_const (M : Type u) (U : S.Etale) (m : M) :
    (etaleConstantSheafSectionsEquiv S M U).symm (LocallyConstant.const _ m) =
      ConcreteCategory.hom (X := M)
        ((toSheafify (smallEtaleTopology S) ((Functor.const _).obj M)).app (op U)) m :=
  (Equiv.symm_apply_eq _).2 (etaleConstantSheafSectionsEquiv_toSheafify_app S M U m).symm

/-- Restricting the section of the constant étale sheaf attached to a locally constant function
along `f : V ⟶ U` corresponds to composing the function with `f`. -/
@[simp]
theorem map_etaleConstantSheafSectionsEquiv_symm (M : Type u) {U V : S.Etale} (f : V ⟶ U)
    (g : LocallyConstant U.left M) :
    ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.map f.op
      ((etaleConstantSheafSectionsEquiv S M U).symm g) =
      (etaleConstantSheafSectionsEquiv S M V).symm (g.comap f.left.base.hom) := by
  rw [Equiv.eq_symm_apply, etaleConstantSheafSectionsEquiv_map, Equiv.apply_symm_apply]

/-- The map of constant étale sheaves induced by `φ : M ⟶ M'` sends the section attached to a
locally constant function `g` to the section attached to `g` composed with `φ`. -/
@[simp]
theorem etaleConstantSheafSectionsEquiv_symm_naturality {M M' : Type u} (φ : M ⟶ M') (U : S.Etale)
    (g : LocallyConstant U.left M) :
    ((constantSheaf (smallEtaleTopology S) (Type u)).map φ).hom.app (op U)
      ((etaleConstantSheafSectionsEquiv S M U).symm g) =
      (etaleConstantSheafSectionsEquiv S M' U).symm (g.map φ) := by
  rw [Equiv.eq_symm_apply, etaleConstantSheafSectionsEquiv_naturality, Equiv.apply_symm_apply]

/-- On a nonempty étale `S`-scheme `U`, the canonical map from `M` into the sections over `U` of
the constant étale sheaf on `M` is injective: two elements agreeing there agree on a covering
sieve, which must contain an étale scheme over `U`. -/
theorem injective_toSheafify_app_const_smallEtaleTopology {S : Scheme.{u}}
    {A : Type*} [Category* A] [HasWeakSheafify (smallEtaleTopology S) A]
    {FA : A → A → Type*} {CD : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory A FA] (M : A)
    [Presheaf.IsLocallyInjective (smallEtaleTopology S)
      (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M))]
    {U : S.Etale} (hU : Nonempty U.left) :
    Function.Injective
      ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app (op U)) := by
  intro m₁ m₂ hm
  have hmem : Presheaf.equalizerSieve (F := (Functor.const S.Etaleᵒᵖ).obj M) (X := op U) m₁ m₂ ∈
      smallEtaleTopology S U :=
    Presheaf.equalizerSieve_mem (smallEtaleTopology S) _ m₁ m₂ hm
  obtain ⟨ι, V, g, hR⟩ := (Presheaf.equalizerSieve (F := (Functor.const S.Etaleᵒᵖ).obj M)
    (X := op U) m₁ m₂).exists_eq_ofArrows
  have hcov := (ofArrows_mem_smallEtaleTopology_iff g).mp (hR ▸ hmem)
  obtain ⟨x⟩ := hU
  have hx : x ∈ ⋃ i, Set.range (g i).left := hcov ▸ Set.mem_univ x
  obtain ⟨i, _, -⟩ := Set.mem_iUnion.mp hx
  have hg : Presheaf.equalizerSieve (F := (Functor.const S.Etaleᵒᵖ).obj M) (X := op U)
      m₁ m₂ (g i) :=
    hR.symm ▸ Sieve.ofArrows_mk V g i
  simpa using hg

namespace Hom

/-- If a morphism `φ : const M ⟶ const N` of constant étale sheaves on `S` agrees on constant
sections over an étale `S`-scheme `u : U ⟶ S` with a morphism `f : M ⟶ N`, then its pullback to
`U` identifies with `const f`. -/
lemma smallEtalePullback_map_constantSheaf_eq_of_app {S U : Scheme.{u}} (u : U ⟶ S) [Etale u]
    {A : Type*} [Category* A] [HasWeakSheafify (smallEtaleTopology S) A]
    [HasWeakSheafify (smallEtaleTopology U) A]
    {FA : A → A → Type*} {CD : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory A FA]
    [(u.smallEtalePushforward A).IsRightAdjoint]
    {M N : A} (φ : (constantSheaf (smallEtaleTopology S) A).obj M ⟶
      (constantSheaf (smallEtaleTopology S) A).obj N) (f : M ⟶ N)
    (hf : ∀ x : ToType M,
      φ.hom.app (op (Etale.mk u))
          ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
            (op (Etale.mk u)) x) =
        (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app
          (op (Etale.mk u)) (f x)) :
    (u.smallEtalePullbackConstantSheafIso A M).inv ≫
        (u.smallEtalePullback A).map φ ≫
        (u.smallEtalePullbackConstantSheafIso A N).hom =
      (constantSheaf (smallEtaleTopology U) A).map f := by
  let T_U : U.Etale := Etale.mk (𝟙 U)
  let hterm_U : IsTerminal T_U :=
    IsTerminal.isTerminalOfObj (Etale.forget U) _ CategoryTheory.Over.mkIdTerminal
  apply ((constantSheafAdj (smallEtaleTopology U) A hterm_U).homEquiv M _).injective
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  rw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_map]
  simp only [ConcreteCategory.comp_apply, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app]
  have he := u.smallEtalePullback_map_comp_constantSheafIso_evalUnitSelf φ (hf x)
  rw [← ConcreteCategory.comp_apply (g := u.evalUnitSelf _),
    u.toSheafify_comp_evalUnitSelf A M, ConcreteCategory.comp_apply] at he
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] using he

end Hom

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf

open AlgebraicGeometry Scheme

section ConstantSheafLocal

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- Given a surjective linear map `p : (Fin r → Λ) →ₗ[Λ] M` whose basis images land in the image
of `toSheafify` over a nonempty étale `S`-scheme `u : U ⟶ S`, factor the evaluation of
`φ : const M ⟶ const N` at `Etale.mk (𝟙 S)` through a `Λ`-linear map `f : M ⟶ N` over `U`. -/
private lemma exists_hom_of_imageSieve_constantSheaf
    {M N : ModuleCat.{u} Λ} {r : ℕ} {m : Fin r → M}
    (hm : Function.Surjective (Fintype.linearCombination Λ m))
    (φ : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M ⟶
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N)
    {U : Scheme.{u}} (u : U ⟶ S) [Etale u] (hUne : Nonempty U)
    (g : Etale.mk u ⟶ Etale.mk (𝟙 S)) {n : Fin r → N}
    (hn : ∀ k : Fin r,
      (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app
          (op (Etale.mk u)) (n k) =
        ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N).obj.map g.op
          (φ.hom.app (op (Etale.mk (𝟙 S)))
            ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
              (op (Etale.mk (𝟙 S))) (m k)))) :
    ∃ f : M ⟶ N, ∀ x : M,
      φ.hom.app (op (Etale.mk u))
          ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
            (op (Etale.mk u)) x) =
        (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app
          (op (Etale.mk u)) (f x) := by
  let p : (Fin r → Λ) →ₗ[Λ] M := Fintype.linearCombination Λ m
  let q : (Fin r → Λ) →ₗ[Λ] N := Fintype.linearCombination Λ n
  have hker : LinearMap.ker p ≤ LinearMap.ker q := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    apply injective_toSheafify_app_const_smallEtaleTopology N (U := Etale.mk u) hUne
    have hnat : ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N).obj.map g.op
        (φ.hom.app (op (Etale.mk (𝟙 S)))
          ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
            (op (Etale.mk (𝟙 S))) (p c))) = 0 := by
      rw [hc, map_zero, map_zero, map_zero]
    rw [map_zero, ← hnat]
    simp only [p, q, Fintype.linearCombination_apply, map_sum, map_smul]
    exact Finset.sum_congr rfl fun k _ ↦ congrArg (c k • ·) (hn k)
  let f : M →ₗ[Λ] N :=
    ((LinearMap.ker p).liftQ q hker).comp (p.quotKerEquivOfSurjective hm).symm.toLinearMap
  have hf_eq (c : Fin r → Λ) : f (p c) = q c := by
    have hq : (p.quotKerEquivOfSurjective hm).symm (p c) = Submodule.Quotient.mk c :=
      (p.quotKerEquivOfSurjective hm).symm_apply_eq.mpr rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.liftQ_apply]
  refine ⟨ModuleCat.ofHom f, fun x ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hm x
  have hnat : φ.hom.app (op (Etale.mk u))
      (((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M).obj.map g.op
        ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
          (op (Etale.mk (𝟙 S))) (p c))) =
      ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N).obj.map g.op
        (φ.hom.app (op (Etale.mk (𝟙 S)))
          ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
            (op (Etale.mk (𝟙 S))) (p c))) := by
    rw [← ConcreteCategory.comp_apply, φ.hom.naturality g.op, ConcreteCategory.comp_apply]
  rw [toSheafify_app_const_map_apply] at hnat
  rw [hnat, ConcreteCategory.hom_ofHom, hf_eq c]
  simp only [p, q, Fintype.linearCombination_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl fun k _ ↦ congrArg (c k • ·) (hn k).symm

/-- **Local constancy of morphisms between constant sheaves.** Let `φ : const M ⟶ const N` be a
morphism of constant étale sheaves of `Λ`-modules on `S`, with `M` finitely generated. Then there
exists a `Type u`-indexed jointly surjective étale cover `u : ∀ i, U i ⟶ S` such that over each
`U i`, the pullback of `φ` identifies (under `smallEtalePullbackConstantSheafIso`) with the constant
sheaf on a `Λ`-linear map `f i : M ⟶ N`. -/
theorem exists_etaleCover_map_constantSheaf {M N : ModuleCat.{u} Λ} [Module.Finite Λ M]
    (φ : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M ⟶
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ f : M ⟶ N,
          ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv ≫
            ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫
            ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom =
              (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map f := by
  obtain ⟨r, p_hom, hm⟩ := Module.Finite.exists_fin' Λ M
  let m : Fin r → M := fun k ↦ p_hom (Pi.single k 1)
  have hm' : Function.Surjective (Fintype.linearCombination Λ m) := by
    intro y
    obtain ⟨c, rfl⟩ := hm y
    refine ⟨c, ?_⟩
    conv_rhs => rw [pi_eq_sum_univ' c]
    simp [m, map_sum, map_smul, Fintype.linearCombination_apply]
  let T_S : S.Etale := Etale.mk (𝟙 S)
  let σ : M → ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N).obj.obj
      (op T_S) :=
    fun a ↦ φ.hom.app (op T_S)
      ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app (op T_S) a)
  let R := ⨅ k : Fin r, Presheaf.imageSieve
    (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)) (σ (m k))
  have hR : R ∈ smallEtaleTopology S T_S :=
    (smallEtaleTopology S).iInf_mem fun k ↦
      Presheaf.imageSieve_mem (smallEtaleTopology S) _ (σ (m k))
  obtain ⟨ι, U, u, hu_et, hUne, hgR, hcov⟩ :=
    exists_etaleCover_of_mem_smallEtaleTopology_terminal hR
  refine ⟨ι, U, u, hu_et, hcov, fun i ↦ ?_⟩
  have := hu_et i
  obtain ⟨gi, hgi⟩ := hgR i
  choose n hn using fun k : Fin r ↦ (iInf_le _ k : R ≤ _) _ hgi
  obtain ⟨f, hf⟩ := exists_hom_of_imageSieve_constantSheaf hm' φ (u i) (hUne i) gi hn
  exact ⟨f, (u i).smallEtalePullback_map_constantSheaf_eq_of_app φ f hf⟩

end ConstantSheafLocal

end CategoryTheory.Sheaf
