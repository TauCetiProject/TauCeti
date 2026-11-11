/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import TauCeti.AlgebraicGeometry.Sites.Etale.Subcanonical
public import TauCeti.Topology.ContinuousMap.LocallyConstant

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
  covered by the empty family;
* it is locally surjective, since a locally constant function is constant on each of its fibres,
  and these fibres are open subschemes, hence étale, covering the source.

So the sections of the constant étale sheaf over `U` are the locally constant functions on the
underlying space of `U`, and its global sections are the locally constant functions on `S`. This
is the concrete description used to recognise constant and locally constant étale sheaves, for
example the sheaves of sections of split finite étale covers.

## Main definitions

* `AlgebraicGeometry.Scheme.etaleLocallyConstantSheaf S`: the étale sheaf of locally constant
  functions `U ↦ LocallyConstant U M`, as a functor of `M`.
* `AlgebraicGeometry.Scheme.constToEtaleLocallyConstantPresheaf S`: the map from the constant
  presheaf sending `m` to the constant function `m`.
* `AlgebraicGeometry.Scheme.constantSheafIsoEtaleLocallyConstantSheaf S`: the constant étale sheaf
  functor is isomorphic to `etaleLocallyConstantSheaf S`.
* `AlgebraicGeometry.Scheme.constantSheafSectionsEquiv S M U`: the sections over `U` of the
  constant étale sheaf with value `M` are the locally constant functions `U → M`.

## Main results

* `AlgebraicGeometry.Scheme.isSheaf_etaleLocallyConstantPresheaf`: locally constant functions form
  an étale sheaf.
* `AlgebraicGeometry.Scheme.bot_mem_smallGrothendieckTopology`: on a small site of `S`, such as
  the small étale site, an object with empty underlying space is covered by the empty sieve.
* `AlgebraicGeometry.Scheme.toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom`: the
  comparison sends the class of `m` to the constant function `m`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.0, for constant and locally
  constant étale sheaves.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The presheaf on the small étale site of `S` of locally constant functions with values in `M`,
`U ↦ LocallyConstant U M`, as a functor of `M`. Restriction is composition with the underlying
continuous map, and a map `M → M'` acts by composition. -/
@[expose, simps]
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
    (smallEtaleTopology S) etaleTopology (continuousMapPresheaf M) (by
      rw [isSheaf_iff_isSheaf_of_type]
      refine Presieve.isSheaf_of_le _ (etaleTopology_le_proetaleTopology.trans
        proetaleTopology_le_fpqcTopology) ?_
      rw [← isSheaf_iff_isSheaf_of_type]
      exact isSheaf_fpqcTopology_continuousMapPresheaf M)
  -- For the discrete topology on `M`, locally constant functions are continuous maps.
  refine (Presheaf.isSheaf_of_iso_iff (NatIso.ofComponents (fun U ↦ Equiv.toIso
    (LocallyConstant.equivContinuousMap U.unop.left M)) fun _ ↦ rfl)).2 h

/-- The étale sheaf of locally constant functions with values in `M`, `U ↦ LocallyConstant U M`,
as a functor of `M`. It is the constant étale sheaf, by
`constantSheafIsoEtaleLocallyConstantSheaf`. -/
@[expose, simps! obj_obj map_hom]
def etaleLocallyConstantSheaf : Type u ⥤ Sheaf (smallEtaleTopology S) (Type u) :=
  ObjectProperty.lift _ (etaleLocallyConstantPresheaf S)
    (isSheaf_etaleLocallyConstantPresheaf S)

/-- The map from the constant presheaf with value `M` to the locally constant functions, sending
`m` to the constant function `m`, naturally in `M`. -/
@[expose, simps]
def constToEtaleLocallyConstantPresheaf :
    Functor.const S.Etaleᵒᵖ ⟶ etaleLocallyConstantPresheaf S where
  app M := { app U := TypeCat.ofHom fun m ↦ LocallyConstant.const _ m }

variable {S} in
/-- On the small site of `S` defined by a morphism property `P`, for example the small étale
site, an object with empty underlying space is covered by the empty sieve. -/
theorem bot_mem_smallGrothendieckTopology {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsMultiplicative] (U : P.Over ⊤ S) [IsEmpty U.left] :
    ⊥ ∈ S.smallGrothendieckTopology P U := by
  rw [Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff,
    Sieve.functorPushforward_bot, map_bot]
  exact bot_mem_grothendieckTopology (P := P) U.left

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
      exact fun m ↦ ⟨m, LocallyConstant.ext fun x ↦ x.2.symm⟩
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

instance (M : Type u) : IsIso (constantSheafToEtaleLocallyConstantSheaf S M) := by
  -- On presheaves the map is the sheafification of the locally bijective
  -- `constToEtaleLocallyConstantPresheaf`, followed by the inverse of the identification of a
  -- sheaf with its sheafification.
  have e : (constantSheafToEtaleLocallyConstantSheaf S M).hom =
      sheafifyMap _ ((constToEtaleLocallyConstantPresheaf S).app M) ≫
        (isoSheafify _ (isSheaf_etaleLocallyConstantPresheaf S M)).inv := by
    rw [isoSheafify_inv, sheafifyMap_sheafifyLift, Category.comp_id]
    exact sheafifyLift_unique _ _ _ _
      (toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom S M)
  have : IsIso ((presheafToSheaf (smallEtaleTopology S) (Type u)).map
      ((constToEtaleLocallyConstantPresheaf S).app M)) :=
    ((smallEtaleTopology S).W_iff _).1 ((smallEtaleTopology S).W_of_isLocallyBijective _)
  have : IsIso ((sheafToPresheaf _ _).map (constantSheafToEtaleLocallyConstantSheaf S M)) := by
    rw [ObjectProperty.ι_map, e]
    -- The two factors are given explicitly: instance search does not identify `sheafifyMap`
    -- with the image of a sheaf morphism here.
    exact IsIso.comp_isIso' (inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
      ((presheafToSheaf _ _).map _)))) (Iso.isIso_inv _)
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **The constant étale sheaf is the sheaf of locally constant functions**: for every set `M`,
the constant sheaf with value `M` on the small étale site of `S` is the sheaf
`U ↦ LocallyConstant U M`, naturally in `M`. -/
noncomputable def constantSheafIsoEtaleLocallyConstantSheaf :
    constantSheaf (smallEtaleTopology S) (Type u) ≅ etaleLocallyConstantSheaf S :=
  -- `constantSheaf` is by definition the sheafification of the constant presheaf; elaborating
  -- `asIso` without the expected type lets the `IsIso` instance be found in that form.
  NatIso.ofComponents (fun M ↦ (asIso (constantSheafToEtaleLocallyConstantSheaf S M) :))
    (constantSheafToEtaleLocallyConstantSheaf_naturality S)

@[simp]
theorem constantSheafIsoEtaleLocallyConstantSheaf_hom_app (M : Type u) :
    (constantSheafIsoEtaleLocallyConstantSheaf S).hom.app M =
      constantSheafToEtaleLocallyConstantSheaf S M :=
  (rfl)

/-- **Sections of the constant étale sheaf**: the sections over an étale `S`-scheme `U` of the
constant sheaf with value `M` are the locally constant functions `U → M`. -/
noncomputable def constantSheafSectionsEquiv (M : Type u) (U : S.Etale) :
    ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U) ≃
      LocallyConstant U.left M :=
  (((sheafToPresheaf _ _).mapIso ((constantSheafIsoEtaleLocallyConstantSheaf S).app M)).app
    (op U)).toEquiv

/-- The sections equivalence is the component at `U` of the comparison map. -/
theorem constantSheafSectionsEquiv_apply (M : Type u) (U : S.Etale)
    (x : ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U)) :
    constantSheafSectionsEquiv S M U x =
      (constantSheafToEtaleLocallyConstantSheaf S M).hom.app (op U) x :=
  (rfl)

/-- The class of `m` in the constant étale sheaf corresponds to the constant function `m`. -/
@[simp]
theorem constantSheafSectionsEquiv_toSheafify_app (M : Type u) (U : S.Etale) (m : M) :
    -- The source is written as `M` rather than `((Functor.const _).obj M).obj (op U)`, the form
    -- `simp` reaches through `Functor.const_obj_obj`.
    constantSheafSectionsEquiv S M U (ConcreteCategory.hom (X := M)
      ((toSheafify (smallEtaleTopology S) ((Functor.const _).obj M)).app (op U)) m) =
      LocallyConstant.const _ m :=
  congr($(toSheafify_comp_constantSheafToEtaleLocallyConstantSheaf_hom S M).app (op U) m)

/-- Restricting a section of the constant étale sheaf along `f : V ⟶ U` corresponds to composing
the locally constant function with `f`. -/
@[simp]
theorem constantSheafSectionsEquiv_map (M : Type u) {U V : S.Etale} (f : V ⟶ U)
    (x : ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U)) :
    constantSheafSectionsEquiv S M V
      (((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.map f.op x) =
      (constantSheafSectionsEquiv S M U x).comap f.left.base.hom :=
  congr($(((constantSheafToEtaleLocallyConstantSheaf S M).hom.naturality f.op)) x)

/-- The map of constant étale sheaves induced by `φ : M ⟶ M'` corresponds to composing locally
constant functions with `φ`. -/
@[simp]
theorem constantSheafSectionsEquiv_naturality {M M' : Type u} (φ : M ⟶ M') (U : S.Etale)
    (x : ((constantSheaf (smallEtaleTopology S) (Type u)).obj M).obj.obj (op U)) :
    constantSheafSectionsEquiv S M' U
      (((constantSheaf (smallEtaleTopology S) (Type u)).map φ).hom.app (op U) x) =
      (constantSheafSectionsEquiv S M U x).map φ :=
  congr($(constantSheafToEtaleLocallyConstantSheaf_naturality S φ).hom.app (op U) x)

end AlgebraicGeometry.Scheme
