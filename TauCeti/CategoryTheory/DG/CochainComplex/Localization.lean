/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution
public import TauCeti.AlgebraicTopology.DGNerve.Nerve
public import TauCeti.CategoryTheory.DG.CochainComplex.KInjective

/-!
# Complexes in the K-injective enhancement of the derived category

Let `C` be an `R`-linear Grothendieck abelian category. The differential graded nerve of the
K-injective complexes, `dgNerve R (KInjectiveDGCategory C)`, is a quasicategory whose homotopy
category is `DerivedCategory C` (`TauCeti.KInjectiveDGCategory.dgNerveHomotopyCategoryEquiv`). This
file constructs the map of simplicial sets from the nerve of the category of all unbounded cochain
complexes to this quasicategory which sends a complex to its K-injective replacement, and shows
that it behaves like the localization functor at the quasi-isomorphisms:

* an edge `f : K ⟶ L` of the nerve becomes an equivalence exactly when `f` is a
  quasi-isomorphism (`TauCeti.KInjectiveDGCategory.isEquivalence_edgeMk_map_fromNerve_iff`);
* every vertex is equivalent to the image of a complex, so the map is essentially surjective on
  homotopy categories (`TauCeti.KInjectiveDGCategory.essSurj_mapHomotopyCategory_fromNerve`);
* under the identification of the homotopy category with `DerivedCategory C`, the class of the
  image of `f` is `DerivedCategory.Q.map f`
  (`TauCeti.KInjectiveDGCategory.dgNerveHomotopyCategoryEquiv_functor_map_homMk_fromNerve`), so two
  maps of complexes give homotopic edges exactly when they agree in the derived category.

The replacement is `TauCeti.injectiveReplacement`, from the functorial factorization of the
injective model structure on unbounded complexes: the morphism from a complex to zero factors as a
monomorphic quasi-isomorphism into a K-injective complex of injective objects, followed by a
fibration. Functoriality of the factorization is what allows the replacement to act on simplices
of every dimension, rather than on objects and morphisms one at a time.

These are the properties of a localization functor that can be read off on homotopy categories
and on edges. The universal property of `TauCeti.KInjectiveDGCategory.fromNerve` as a localization
of quasicategories at the quasi-isomorphisms is not proved here.

## Main definitions

* `TauCeti.KInjectiveDGCategory.replacementFunctor R C`: the K-injective replacement as a functor
  into the underlying category of closed degree-zero morphisms of `KInjectiveDGCategory C`.
* `TauCeti.KInjectiveDGCategory.fromNerve R C`: the induced map from the nerve of
  `CochainComplex C ℤ` to the differential graded nerve of the K-injective complexes.
* `TauCeti.KInjectiveDGCategory.fromNerveObjIso R K`: the identification of the image of `K` in
  `DerivedCategory C` with `DerivedCategory.Q.obj K`.

## Main results

* `TauCeti.KInjectiveDGCategory.isEquivalence_edgeMk_map_fromNerve_iff`: detection of
  quasi-isomorphisms.
* `TauCeti.KInjectiveDGCategory.essSurj_mapHomotopyCategory_fromNerve`: essential surjectivity.
* `TauCeti.KInjectiveDGCategory.dgNerveHomotopyCategoryEquiv_functor_map_homMk_fromNerve` and
  `TauCeti.KInjectiveDGCategory.mapHomotopyCategory_fromNerve_map_homMk_eq_iff`: compatibility
  with `DerivedCategory.Q`.

## References

* J. Lurie, *Higher Algebra*, Definition 1.3.5.8 and Proposition 1.3.5.15.
* [Stacks: Theorem 079P](https://stacks.math.columbia.edu/tag/079P).
-/

public section

noncomputable section

open CategoryTheory DerivedCategory

universe w w' v u

namespace TauCeti

open CochainComplex CochainComplex.HomComplex Opposite Simplicial SSet

namespace KInjectiveDGCategory

section

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The K-injective replacement of a complex, as an object of the K-injective DG category. -/
-- Reducible so that the underlying complex reduces to the replacement, also when instances are
-- unfolded: the Hom complexes out of and into this object are those of the replacement.
abbrev replacement (K : CochainComplex C ℤ) : KInjectiveDGCategory C :=
  ⟨(injectiveReplacement C).obj K, inferInstance⟩

end

section

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [IsGrothendieckAbelian.{w} C]

variable (C) in
/-- The K-injective replacement as a functor from cochain complexes to the underlying category of
closed degree-zero morphisms of the K-injective DG category. It sends a cochain map `f` to the
closed morphism `Cochain.ofHom` of its replacement. -/
-- Exposed so that its objects reduce to `TauCeti.KInjectiveDGCategory.replacement`: the
-- vertices and edges of `TauCeti.KInjectiveDGCategory.fromNerve` are stated in those terms.
@[expose] def replacementFunctor :
    CochainComplex C ℤ ⥤
      ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) (KInjectiveDGCategory C) where
  obj K := ForgetEnrichment.of _ (replacement K)
  map {K L} f := dgClosedHomOf R (X := replacement K) (Y := replacement L)
    (cochainHomLinearEquivDGCycles R _ _ ((injectiveReplacement C).map f)).val
    (DGFullSubcategory.mem_dgCycles_iff.2
      (cochainHomLinearEquivDGCycles R _ _ ((injectiveReplacement C).map f)).property)
  map_id K := dgClosedHom_injective R <| (dgClosedHom_dgClosedHomOf R _ _).trans <| by
    rw [CategoryTheory.Functor.map_id, cochainHomLinearEquivDGCycles_id, dgClosedHom_id]
    exact (DGFullSubcategory.dgId_eq R (replacement K)).symm
  map_comp f g := dgClosedHom_injective R <| (dgClosedHom_dgClosedHomOf R _ _).trans <| by
    rw [CategoryTheory.Functor.map_comp, ← dgCompZero_cochainHomLinearEquivDGCycles,
      dgClosedHom_comp, dgClosedHom_dgClosedHomOf, dgClosedHom_dgClosedHomOf, dgCompZero_def,
      dgCompZero_def, DGFullSubcategory.dgComp_eq]

/-- The replacement functor sends a complex to its K-injective replacement. -/
@[simp]
theorem replacementFunctor_obj (K : CochainComplex C ℤ) :
    (replacementFunctor R C).obj K = ForgetEnrichment.of _ (replacement K) :=
  rfl

/-- The closed degree-zero morphism given by the replacement functor on a cochain map `f` is
`Cochain.ofHom` of the replacement of `f`. -/
@[simp]
theorem dgClosedHom_replacementFunctor_map {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    dgClosedHom R ((replacementFunctor R C).map f) =
      (Cochain.ofHom ((injectiveReplacement C).map f) :
        DGHom R 0 (replacement K) (replacement L)) :=
  (dgClosedHom_dgClosedHomOf R _ _).trans (cochainHomLinearEquivDGCycles_apply_coe R _)

variable (C) in
/-- **The K-injective enhancement as a target for complexes.** The map from the nerve of the
category of unbounded cochain complexes to the differential graded nerve of the K-injective
complexes which replaces each string of cochain maps by its K-injective replacement, with all
higher coherences zero. It inverts exactly the quasi-isomorphisms
(`TauCeti.KInjectiveDGCategory.isEquivalence_edgeMk_map_fromNerve_iff`) and induces
`DerivedCategory.Q` on homotopy categories
(`TauCeti.KInjectiveDGCategory.dgNerveHomotopyCategoryEquiv_functor_map_homMk_fromNerve`). -/
def fromNerve : nerve (CochainComplex C ℤ) ⟶ dgNerve R (KInjectiveDGCategory C) :=
  nerveMap (replacementFunctor R C) ≫ dgNerve.fromNerve R (KInjectiveDGCategory C)

/-- The map `TauCeti.KInjectiveDGCategory.fromNerve` sends a string of cochain maps to the simplex
given by the string of its K-injective replacements. -/
theorem fromNerve_app_apply {Δ : SimplexCategoryᵒᵖ} (x : (nerve (CochainComplex C ℤ)).obj Δ) :
    (fromNerve R C).app Δ x =
      DGNerve.Simplex.ofComposableArrows ((nerveMap (replacementFunctor R C)).app Δ x) :=
  dgNerve.fromNerve_app_apply R _ _

/-- The vertex of a complex `K` is sent to the vertex of its K-injective replacement. -/
@[simp]
theorem fromNerve_app_nerveEquiv_symm (K : CochainComplex C ℤ) :
    (fromNerve R C).app (op ⦋0⦌) (nerveEquiv.symm K) =
      (dgNerveEquiv R (KInjectiveDGCategory C)).symm (replacement K) :=
  -- The object of the image vertex is the replacement of `K` by definition of
  -- `DGNerve.Simplex.ofComposableArrows` and `TauCeti.KInjectiveDGCategory.replacementFunctor`.
  (fromNerve_app_apply R _).trans <| DGNerve.Simplex.ext_zero <|
    Eq.trans (b := replacement K) rfl
      (by rw [dgNerveEquiv_symm_apply, DGNerve.Simplex.vertex_obj])

/-- The edge of a cochain map `f` is sent to the edge of the closed morphism given by the
replacement of `f`. -/
theorem fromNerve_app_mk₁ {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (fromNerve R C).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      DGNerve.Simplex.edge (R := R)
        ⟨_, ofHom_mem_dgCycles R C ((injectiveReplacement C).map f)⟩ := by
  refine (fromNerve_app_apply R _).trans ?_
  rw [nerveMap_app_mk₁]
  exact (DGNerve.Simplex.eq_edge _).trans (congrArg DGNerve.Simplex.edge (Subtype.ext
    ((DGNerve.Simplex.ofComposableArrows_coh_empty _ _).trans
      (dgClosedHom_replacementFunctor_map R f))))

/-- **Quasi-isomorphisms are detected in the K-injective enhancement.** The edge of a cochain map
`f` becomes an equivalence of the differential graded nerve of K-injective complexes exactly when
`f` is a quasi-isomorphism. -/
theorem isEquivalence_edgeMk_map_fromNerve_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    ((nerve.edgeMk f).map (fromNerve R C)).IsEquivalence ↔ QuasiIso f := by
  rw [Edge.isEquivalence_iff_of_edge_eq (e := (nerve.edgeMk f).map (fromNerve R C))
      (e' := dgNerve.edgeMk R (KInjectiveDGCategory C)
        ⟨_, ofHom_mem_dgCycles R C ((injectiveReplacement C).map f)⟩)
      ((fromNerve_app_mk₁ R f).trans (dgNerve.edgeMk_edge R _ _).symm),
    isEquivalence_edgeMk_iff_quasiIso R C, quasiIso_injectiveReplacement_map_iff]

/-- **Every object of the K-injective enhancement is the image of a complex**, up to equivalence:
a K-injective complex `K` is equivalent to its replacement through the quasi-isomorphism
`TauCeti.ιInjectiveReplacement`. Hence `TauCeti.KInjectiveDGCategory.fromNerve` is
essentially surjective on homotopy categories. -/
instance essSurj_mapHomotopyCategory_fromNerve :
    (mapHomotopyCategory (fromNerve R C)).EssSurj := by
  rw [essSurj_mapHomotopyCategory_iff]
  intro y
  obtain ⟨K, rfl⟩ := (dgNerveEquiv R (KInjectiveDGCategory C)).symm.surjective y
  have := K.property
  refine ⟨nerveEquiv.symm K.obj, ?_⟩
  rw [fromNerve_app_nerveEquiv_symm, ← HomotopyCategory.nonempty_iso_mk_iff]
  obtain ⟨i⟩ := HomotopyCategory.nonempty_iso_mk_iff.2
    ⟨dgNerve.edgeMk R _ ⟨_, ofHom_mem_dgCycles R C (K := K.obj)
      ((ιInjectiveReplacement C).app K.obj)⟩,
      (isEquivalence_edgeMk_iff_quasiIso R C (K := K.obj) _).2 inferInstance⟩
  exact ⟨i.symm⟩

/-! ### Comparison with the localization functor -/

variable [HasDerivedCategory.{w'} C]

/-- The image in `DerivedCategory C` of the vertex of the K-injective replacement of a complex `K`
is the image of that replacement under `HomotopyCategory.quotient C _ ⋙ Qh`. -/
theorem dgNerveHomotopyCategoryEquiv_functor_obj_mk_replacement (K : CochainComplex C ℤ) :
    (dgNerveHomotopyCategoryEquiv R C).functor.obj
        (HomotopyCategory.mk ((dgNerveEquiv R _).symm (replacement K))) =
      (HomotopyCategory.quotient C _ ⋙ Qh).obj ((injectiveReplacement C).obj K) := by
  rw [dgNerveHomotopyCategoryEquiv_functor, Functor.comp_obj,
    dgNerve.fromHomotopyCategory_obj_mk, Equiv.apply_symm_apply, toDerivedCategory_obj,
    DGHomotopyCategory.underlying_of, Functor.comp_obj]

/-- The identification of the image in `DerivedCategory C` of a vertex equal to the vertex of the
replacement of `K` with `DerivedCategory.Q.obj K`. Stating it for an arbitrary vertex `x` lets the
naturality computation substitute `x`. -/
private def objIsoOfEq {K : CochainComplex C ℤ} {x : (dgNerve R (KInjectiveDGCategory C)) _⦋0⦌}
    (hx : x = (dgNerveEquiv R _).symm (replacement K)) :
    (dgNerveHomotopyCategoryEquiv R C).functor.obj (HomotopyCategory.mk x) ≅ Q.obj K :=
  eqToIso (hx ▸ dgNerveHomotopyCategoryEquiv_functor_obj_mk_replacement R K) ≪≫
    (quotientCompQhIso C).app ((injectiveReplacement C).obj K) ≪≫
      (asIso (Q.map ((ιInjectiveReplacement C).app K))).symm

private lemma map_homMk_comp_objIsoOfEq_hom {K L : CochainComplex C ℤ} (f : K ⟶ L)
    {x y : (dgNerve R (KInjectiveDGCategory C)) _⦋0⦌}
    (hx : x = (dgNerveEquiv R _).symm (replacement K))
    (hy : y = (dgNerveEquiv R _).symm (replacement L)) (e : Edge x y)
    (he : e.edge = (dgNerve.edgeMk R (KInjectiveDGCategory C)
      ⟨_, ofHom_mem_dgCycles R C ((injectiveReplacement C).map f)⟩).edge) :
    (dgNerveHomotopyCategoryEquiv R C).functor.map (HomotopyCategory.homMk e) ≫
      (objIsoOfEq R hy).hom = (objIsoOfEq R hx).hom ≫ Q.map f := by
  subst hx hy
  obtain rfl := Edge.ext he
  rw [Functor.congr_hom (dgNerveHomotopyCategoryEquiv_functor R C), Functor.comp_map,
    dgNerve.fromHomotopyCategory_map_homMk_edgeMk, Functor.map_comp, Functor.map_comp,
    eqToHom_map, eqToHom_map]
  simp only [objIsoOfEq, Iso.trans_hom, eqToIso.hom, Iso.app_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, eqToHom_trans_assoc]
  rw [toDerivedCategory_map_homOf]
  -- `toDerivedCategory` sends `of R (replacement K)` to `Qh` of the class of the replacement of
  -- `K` by definition, so the transports differ only in these presentations of their endpoints.
  change eqToHom _ ≫ (Qh.map ((HomotopyCategory.quotient C _).map
      ((injectiveReplacement C).map f)) ≫ 𝟙 _ ≫ (quotientCompQhIso C).hom.app _ ≫ _) =
    eqToHom _ ≫ (quotientCompQhIso C).hom.app _ ≫ _
  rw [Category.id_comp, quotientCompQhIso_hom_naturality_assoc]
  congr 2
  rw [IsIso.eq_inv_comp, ← Functor.map_comp_assoc, ← (ιInjectiveReplacement C).naturality f,
    Functor.id_map, Functor.map_comp_assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The image in `DerivedCategory C` of the vertex of a complex `K` is `DerivedCategory.Q.obj K`:
the identification is the inverse of `Q` of the quasi-isomorphism from `K` to its K-injective
replacement. -/
def fromNerveObjIso (K : CochainComplex C ℤ) :
    (dgNerveHomotopyCategoryEquiv R C).functor.obj
        ((mapHomotopyCategory (fromNerve R C)).obj (HomotopyCategory.mk (nerveEquiv.symm K))) ≅
      Q.obj K :=
  objIsoOfEq R (fromNerve_app_nerveEquiv_symm R K)

/-- The identification `TauCeti.KInjectiveDGCategory.fromNerveObjIso R K` identifies the image of
`K` with the class of its K-injective replacement, and then applies `quotientCompQhIso` and the
inverse of `DerivedCategory.Q` of the quasi-isomorphism from `K` to its replacement. -/
theorem fromNerveObjIso_hom (K : CochainComplex C ℤ) :
    (fromNerveObjIso R K).hom =
      eqToHom ((congrArg (fun x ↦ (dgNerveHomotopyCategoryEquiv R C).functor.obj
          (HomotopyCategory.mk x)) (fromNerve_app_nerveEquiv_symm R K)).trans
            (dgNerveHomotopyCategoryEquiv_functor_obj_mk_replacement R K)) ≫
        (quotientCompQhIso C).hom.app ((injectiveReplacement C).obj K) ≫
          inv (Q.map ((ιInjectiveReplacement C).app K)) := by
  simp only [fromNerveObjIso, objIsoOfEq, Iso.trans_hom, eqToIso.hom, Iso.app_hom, Iso.symm_hom,
    asIso_inv]
  -- The two transports differ only in how the class of the replacement of `K` is presented.
  rfl

/-- **The K-injective enhancement induces the localization functor on homotopy categories.**
Under the identification of the homotopy category of the differential graded nerve of K-injective
complexes with `DerivedCategory C`, the class of the edge of a cochain map `f` is
`DerivedCategory.Q.map f`. -/
theorem dgNerveHomotopyCategoryEquiv_functor_map_homMk_fromNerve {K L : CochainComplex C ℤ}
    (f : K ⟶ L) :
    (dgNerveHomotopyCategoryEquiv R C).functor.map
        ((mapHomotopyCategory (fromNerve R C)).map (HomotopyCategory.homMk (nerve.edgeMk f))) ≫
      (fromNerveObjIso R L).hom = (fromNerveObjIso R K).hom ≫ Q.map f :=
  map_homMk_comp_objIsoOfEq_hom R f _ _ ((nerve.edgeMk f).map (fromNerve R C))
    ((fromNerve_app_mk₁ R f).trans (dgNerve.edgeMk_edge R _ _).symm)

/-- Two cochain maps give the same morphism in the homotopy category of the K-injective
enhancement exactly when they agree in the derived category. -/
theorem mapHomotopyCategory_fromNerve_map_homMk_eq_iff {K L : CochainComplex C ℤ}
    (f g : K ⟶ L) :
    (mapHomotopyCategory (fromNerve R C)).map (HomotopyCategory.homMk (nerve.edgeMk f)) =
        (mapHomotopyCategory (fromNerve R C)).map (HomotopyCategory.homMk (nerve.edgeMk g)) ↔
      Q.map f = Q.map g := by
  rw [← (dgNerveHomotopyCategoryEquiv R C).functor.map_injective.eq_iff,
    ← cancel_mono (fromNerveObjIso R L).hom,
    dgNerveHomotopyCategoryEquiv_functor_map_homMk_fromNerve,
    dgNerveHomotopyCategoryEquiv_functor_map_homMk_fromNerve, cancel_epi]

end

end KInjectiveDGCategory

end TauCeti
