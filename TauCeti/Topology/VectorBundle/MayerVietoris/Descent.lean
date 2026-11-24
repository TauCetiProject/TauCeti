/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Morphisms out of the rank-degree homology of a Thom pair from morphisms out of the fibres

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, `E₀` the complement of
the zero section. Every fibre pair `(E_b, E_b ∖ {0})` maps into `(E, E₀)`, and the images of
`Hᵣ(E_b, E_b ∖ {0})` generate `Hᵣ(E, E₀)` (`TauCeti.singularHomology_thomPair_hom_ext`). This file
proves the matching existence statement: `Hᵣ(E, E₀)` is glued from the fibre groups along the
local trivializations. A family of morphisms `g b : Hᵣ(E_b, E_b ∖ {0}) ⟶ T` extends to a morphism
`Hᵣ(E, E₀) ⟶ T`, necessarily unique, as soon as it is constant along paths when read in the
trivializations of the atlas: for the trivialization `e` at any point and points `x`, `y` joined
by a path in its base set, `g x` and `g y` agree after the identifications
`(F, F ∖ {0}) ≅ (E_x, E_x ∖ {0})` and `(F, F ∖ {0}) ≅ (E_y, E_y ∖ {0})` given by `e`
(`TauCeti.existsUnique_singularHomology_thomPair_fac`).

No orientation of the bundle and no condition on the base is needed, and the coefficients lie in
any abelian category with exact filtered colimits. This is the existence half of a presentation of
`Hᵣ(E, E₀)` as a colimit of the fibre groups; it identifies the rank-degree homology of the Thom
pair with the zeroth homology of the base twisted by the orientation local system
(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀`).

## The proof

Over a subset `W` of the base set of a trivialization `e`, the trivialization identifies
`Hᵣ(E|_W, E₀|_W)` with `Hᵣ(W × F, W × (F ∖ {0})) ≅ H₀(W)`, and a morphism out of `H₀(W)` is given
by morphisms out of the coefficients at the points of `W` that are constant along paths in `W`
(`TauCeti.singularHomology₀Desc`). Over the union of two open sets `U` and `V` the morphisms over
`U` and over `V` glue by the Mayer–Vietoris sequence of the Thom pairs
(`TauCeti.exists_singularHomology_thomPairOver_union_desc`), which ends in degree `r` because the
homology over `U ∩ V` vanishes below the rank, and they agree over `U ∩ V` because morphisms there
are determined on the fibres. By induction this gives the morphism over every finite union of
trivializing open sets. The homology of the Thom pair is the filtered colimit of its homology over
these finite unions (`TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion`),
and the morphisms over the finite unions are compatible, since each is determined on the fibres.

## Main results

* `TauCeti.existsUnique_singularHomology_thomPair_fac`: a family of morphisms out of the fibre
  groups `Hᵣ(E_b, E_b ∖ {0})` that is constant along paths in the trivializations of the atlas
  factors uniquely through `Hᵣ(E, E₀)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and the passage to a directed union).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E]

variable {R} {T : C}
  (g : ∀ b, (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology R
    (finrank ℝ F) ⟶ T)

/-- The fibre morphisms `g` factor through the Thom pair over `W`. -/
private def FactorsOver (W : Set B) : Prop :=
  ∃ Φ : (thomPairOver F E W).singularHomology R (finrank ℝ F) ⟶ T, ∀ x (hx : x ∈ W),
    TopPair.singularHomologyMap (fiberThomPairOverMap F E hx) R (finrank ℝ F) ≫ Φ = g x

/-- The fibre morphisms `g`, read in the trivialization at `z`, agree at points joined by a path
in its base set. -/
private def CompatibleAt (z : B) : Prop :=
  ∀ ⦃x y : B⦄ (hx : x ∈ (trivializationAt F E z).baseSet)
    (hy : y ∈ (trivializationAt F E z).baseSet), JoinedIn (trivializationAt F E z).baseSet x y →
    TopPair.singularHomologyMap ((trivializationAt F E z).continuousLinearEquivAt ℝ x
        hx).complZeroPairIso.inv R (finrank ℝ F) ≫ g x =
      TopPair.singularHomologyMap ((trivializationAt F E z).continuousLinearEquivAt ℝ y
        hy).complZeroPairIso.inv R (finrank ℝ F) ≫ g y

/-- **Over a trivializing set**: if `g` is compatible in the trivialization at `z`, it factors
through the Thom pair over any subset of its base set. -/
private theorem factorsOver_of_subset {z : B} (hg : CompatibleAt g z) {W : Set B}
    (hW : W ⊆ (trivializationAt F E z).baseSet) : FactorsOver g W := by
  set e := trivializationAt F E z
  -- The value at `x` of the morphism out of `H₀(W)`.
  let v : TopCat.of W → (R ⟶ T) := fun x ↦ complZeroPairPointHom R F (finrank ℝ F) rfl ≫
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x (hW x.property)).complZeroPairIso.inv
      R (finrank ℝ F) ≫ g x
  have hv ⦃x y : TopCat.of W⦄ (γ : Path x y) : v x = v y := by
    have h : JoinedIn e.baseSet (x : B) y := by
      refine ⟨γ.map continuous_subtypeVal, fun t ↦ hW (γ t).property⟩
    simp only [v]
    rw [hg (hW x.property) (hW y.property) h]
  refine ⟨TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom R (finrank ℝ F) ≫
    (prodThomPairSingularHomologyIso R W F 0 (finrank ℝ F)).hom ≫
      singularHomology₀Desc R v hv, fun x hx ↦ ?_⟩
  -- Compare both sides after the isomorphism `R ≅ Hᵣ(F, F ∖ {0}) ≅ Hᵣ(E_x, E_x ∖ {0})`.
  have hiso : IsIso (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x
      (hW hx)).complZeroPairIso.inv R (finrank ℝ F)) :=
    (TopPair.singularHomologyMapIso R (e.continuousLinearEquivAt ℝ x
      (hW hx)).complZeroPairIso.symm (finrank ℝ F)).isIso_hom
  rw [← cancel_epi (complZeroPairPointHom R F (finrank ℝ F) rfl ≫
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x (hW hx)).complZeroPairIso.inv R
      (finrank ℝ F))]
  have hfib : (e.continuousLinearEquivAt ℝ x (hW hx)).complZeroPairIso.inv ≫
      fiberThomPairOverMap F E hx ≫ (e.thomPairOverIso ℝ hW).hom =
        prodThomPairFiberMap F (⟨x, hx⟩ : W) := by
    rw [e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW hx, Iso.inv_hom_id_assoc]
  simp only [Category.assoc]
  rw [← TopPair.singularHomologyMap_comp_assoc, ← TopPair.singularHomologyMap_comp_assoc,
    Category.assoc, hfib, complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap_assoc,
    Iso.inv_hom_id_assoc, singularHomology₀Section_singularHomology₀Desc]

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- Over the empty set the fibre morphisms factor trivially. -/
private theorem factorsOver_empty : FactorsOver g (∅ : Set B) :=
  ⟨0, fun _ hx ↦ hx.elim⟩

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- **The Mayer–Vietoris step**: if `g` factors over the open sets `U` and `V`, morphisms out of the
homology over `U ∩ V` are determined on the fibres, and that homology vanishes in degree `r - 1`,
then `g` factors over `U ∪ V`. -/
private theorem factorsOver_union {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hgU : FactorsOver g U) (hgV : FactorsOver g V)
    (hext : ∀ φ φ' : (thomPairOver F E (U ∩ V)).singularHomology R (finrank ℝ F) ⟶ T,
      (∀ x (hx : x ∈ U ∩ V), TopPair.singularHomologyMap (fiberThomPairOverMap F E hx) R _ ≫ φ =
        TopPair.singularHomologyMap (fiberThomPairOverMap F E hx) R _ ≫ φ') → φ = φ')
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).singularHomology R m)) :
    FactorsOver g (U ∪ V) := by
  obtain ⟨ΦU, hΦU⟩ := hgU
  obtain ⟨ΦV, hΦV⟩ := hgV
  -- Both restrictions to `U ∩ V` agree, since morphisms over `U ∩ V` are determined on the fibres.
  obtain ⟨Φ, hΦU', hΦV'⟩ := exists_singularHomology_thomPairOver_union_desc hU hV hUV ΦU ΦV
    (hext _ _ fun x hx ↦ by
      rw [← TopPair.singularHomologyMap_comp_assoc, ← TopPair.singularHomologyMap_comp_assoc,
        fiberThomPairOverMap_comp_thomPairOverMap, fiberThomPairOverMap_comp_thomPairOverMap,
        hΦU, hΦV])
  refine ⟨Φ, fun x hx ↦ ?_⟩
  -- A point of `U ∪ V` lies in `U` or in `V`, through which its fibre inclusion factors.
  rcases hx with hx | hx
  · rw [← fiberThomPairOverMap_comp_thomPairOverMap F E subset_union_left hx,
      TopPair.singularHomologyMap_comp, Category.assoc, hΦU', hΦU]
  · rw [← fiberThomPairOverMap_comp_thomPairOverMap F E subset_union_right hx,
      TopPair.singularHomologyMap_comp, Category.assoc, hΦV', hΦV]

/-- **Finite unions of trivializing open sets**: if `g` is compatible in the trivializations of
the atlas, it factors over every finite union of open sets each lying in the base set of one of
them. -/
private theorem factorsOver_biUnion (hg : ∀ z, CompatibleAt g z) {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ z, W i ⊆ (trivializationAt F E z).baseSet) :
    FactorsOver g (⋃ i ∈ s, W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using factorsOver_empty g
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    obtain ⟨z, hz⟩ := hWe a ha
    -- `W a ∩ ⋃ i ∈ s, W i` lies in `W a`, which lies in the base set of the trivialization at `z`.
    exact factorsOver_union g (hWo a ha)
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi))
      (factorsOver_of_subset g (hg z) hz) (ih (fun i hi ↦ hWo i (hs i hi))
        fun i hi ↦ hWe i (hs i hi))
      (fun _ _ h ↦ (trivializationAt F E z).singularHomology_thomPairOver_hom_ext
        (inter_subset_left.trans hz) h)
      fun m hm ↦ (trivializationAt F E z).isZero_singularHomology_thomPairOver
        (inter_subset_left.trans hz) R (by omega)

/-- Over a finite union of the chosen trivializing open sets, `g` factors uniquely. -/
private theorem existsUnique_factorsOver_finiteTrivializingUnion (hg : ∀ z, CompatibleAt g z)
    (s : Finset B) :
    ∃! Φ : (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology R
        (finrank ℝ F) ⟶ T, ∀ x (hx : x ∈ ⋃ b ∈ s, (trivializationAt F E b).baseSet),
      TopPair.singularHomologyMap (fiberThomPairOverMap F E hx) R (finrank ℝ F) ≫ Φ = g x := by
  obtain ⟨Φ, hΦ⟩ := factorsOver_biUnion g hg s (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ ⟨b, subset_rfl⟩
  refine ⟨Φ, hΦ, fun Φ' hΦ' ↦ ?_⟩
  exact singularHomology_thomPairOver_biUnion_hom_ext s
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) fun x hx ↦ by
      rw [hΦ x hx, hΦ' x hx]

variable [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]

/-- **Morphisms out of the rank-degree homology of the Thom pair from morphisms out of the
fibres.** Let `E → B` be a real vector bundle of rank `r` and `g b : Hᵣ(E_b, E_b ∖ {0}) ⟶ T`
morphisms out of the fibre groups. Suppose that for the trivialization `e` of the atlas at any
point and any two points `x` and `y` joined by a path in its base set, `g x` and `g y` agree after
the identifications of `Hᵣ(F, F ∖ {0})` with `Hᵣ(E_x, E_x ∖ {0})` and with `Hᵣ(E_y, E_y ∖ {0})`
given by `e`. Then there is a unique morphism `Hᵣ(E, E₀) ⟶ T` whose composite with the inclusion
of each fibre pair is `g b`. The base is arbitrary, the bundle need not be orientable, and the
coefficients lie in an abelian category with exact filtered colimits. -/
theorem existsUnique_singularHomology_thomPair_fac
    (hg : ∀ (z : B) ⦃x y : B⦄ (hx : x ∈ (trivializationAt F E z).baseSet)
      (hy : y ∈ (trivializationAt F E z).baseSet), JoinedIn (trivializationAt F E z).baseSet x y →
      TopPair.singularHomologyMap ((trivializationAt F E z).continuousLinearEquivAt ℝ x
          hx).complZeroPairIso.inv R (finrank ℝ F) ≫ g x =
        TopPair.singularHomologyMap ((trivializationAt F E z).continuousLinearEquivAt ℝ y
          hy).complZeroPairIso.inv R (finrank ℝ F) ≫ g y) :
    ∃! Φ : (thomPair F E).singularHomology R (finrank ℝ F) ⟶ T, ∀ b,
      TopPair.singularHomologyMap (fiberThomPairMap F E b) R (finrank ℝ F) ≫ Φ = g b := by
  let P := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E) R
    (finrank ℝ F)
  -- The morphisms over the finite unions of the chosen trivializing sets.
  choose Φ hΦ hΦu using existsUnique_factorsOver_finiteTrivializingUnion g hg
  have hobj (s : Finset B) : (thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
      TopPair.singularHomologyFunctor R (finrank ℝ F)).obj s =
        (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology R
          (finrank ℝ F) :=
    singularHomologyFunctor_obj_thomPairFiniteTrivializingUnionDiagram_obj R (finrank ℝ F) s
  -- They are compatible, since each is determined on the fibres.
  let c : Cocone (thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
      TopPair.singularHomologyFunctor R (finrank ℝ F)) :=
    { pt := T
      ι :=
        { app s := eqToHom (hobj s) ≫ Φ s
          naturality s t f := by
            have h := hΦu s (TopPair.singularHomologyMap (thomPairOverMap F E
              (biUnion_subset_biUnion_left f.le)) R (finrank ℝ F) ≫ Φ t) fun x hx ↦ by
                rw [← TopPair.singularHomologyMap_comp_assoc,
                  fiberThomPairOverMap_comp_thomPairOverMap, hΦ]
            simp [TopPair.singularHomologyMap_comp, h] } }
  have hpt : ((TopPair.singularHomologyFunctor R (finrank ℝ F)).mapCocone
      (thomPairFiniteTrivializingUnionCocone (F := F) (E := E))).pt =
        (thomPair F E).singularHomology R (finrank ℝ F) :=
    singularHomologyFunctor_obj_thomPairFiniteTrivializingUnionCocone_pt R (finrank ℝ F)
  -- On each finite union, the glued morphism restricts to the morphism over the union.
  have hres (s : Finset B) : TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ _) ≫
      (thomPairOverUnivIso F E).hom) R (finrank ℝ F) ≫ eqToHom hpt.symm ≫ P.desc c = Φ s := by
    have hlem :=
      singularHomologyFunctor_mapCocone_thomPairFiniteTrivializingUnionCocone_ι_app_assoc
        (F := F) (E := E) R (finrank ℝ F) s (eqToHom hpt.symm ≫ P.desc c)
    rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, P.fac] at hlem
    rw [← cancel_epi (eqToHom (hobj s)), ← hlem]
  have hfac (b : B) : TopPair.singularHomologyMap (fiberThomPairMap F E b) R (finrank ℝ F) ≫
      eqToHom hpt.symm ≫ P.desc c = g b := by
    -- The fibre over `b` lies in the trivializing set of `b`.
    have hb : b ∈ ⋃ z ∈ ({b} : Finset B), (trivializationAt F E z).baseSet := by
      simpa using FiberBundle.mem_baseSet_trivializationAt' b
    rw [← fiberThomPairOverMap_comp_thomPairOverUnivIso_hom,
      ← fiberThomPairOverMap_comp_thomPairOverMap F E (subset_univ _) hb, Category.assoc,
      TopPair.singularHomologyMap_comp, Category.assoc, hres, hΦ]
  exact ⟨eqToHom hpt.symm ≫ P.desc c, hfac, fun Φ' hΦ' ↦
    singularHomology_thomPair_hom_ext fun b ↦ by rw [hΦ', hfac]⟩

end TauCeti
