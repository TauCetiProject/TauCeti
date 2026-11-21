/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Morphisms out of the top homology of a Thom pair from morphisms out of the fibres

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
`Hᵣ(E, E₀)` as a colimit of the fibre groups; it identifies the top homology of the Thom pair with
the zeroth homology of the base twisted by the orientation local system
(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀`). The fibre
groups are themselves constant along paths in a trivialization: the inclusions of
`(F, F ∖ {0})` through the fibres over the points of a path in its base set are homotopic maps of
pairs
(`Bundle.Trivialization.singularHomologyMap_fiberThomPairMap_eq_of_joinedIn`).

## The proof

Over a subset `W` of the base set of a trivialization `e`, the trivialization identifies
`Hᵣ(E|_W, E₀|_W)` with `Hᵣ(W × F, W × (F ∖ {0})) ≅ H₀(W)`, and a morphism out of `H₀(W)` is given
by morphisms out of the coefficients at the points of `W` that are constant along paths in `W`
(`TauCeti.singularHomology₀Desc`). Over the union of two open sets `U` and `V` the morphisms over
`U` and over `V` glue by the Mayer–Vietoris sequence of the Thom pairs, which ends in degree `r`
because the homology over `U ∩ V` vanishes below the rank, and they agree over `U ∩ V` because
morphisms there are determined on the fibres. By induction this gives the morphism over every
finite union of trivializing open sets. The homology of the Thom pair is the filtered colimit of
its homology over these finite unions
(`TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion`), and the morphisms
over the finite unions are compatible, since each is determined on the fibres.

## Main results

* `Bundle.Trivialization.singularHomologyMap_fiberThomPairMap_eq_of_joinedIn`:
  the fibre inclusions read through a trivialization are homotopic along paths in its base set.
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

section Model

variable (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The coefficients mapped into `Hᵣ(F, F ∖ {0})` as the class of the point in `H₀(pt)`, read
through the Thom pair `(pt × F, pt × (F ∖ {0}))` of the product bundle over a point. -/
private def modelFiberMap :
    R ⟶ (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology R (finrank ℝ F) :=
  singularHomology₀Section R (X := TopCat.of PUnit.{w + 1}) PUnit.unit ≫
    (prodThomPairSingularHomologyIso R PUnit.{w + 1} F 0 (finrank ℝ F)).inv ≫
      TopPair.singularHomologyMap (complZeroPairIsoProdThomPair F).inv R (finrank ℝ F)

private instance : IsIso (modelFiberMap R F) := by
  have : IsIso (singularHomology₀Section R (X := TopCat.of PUnit.{w + 1}) PUnit.unit) :=
    ⟨(TopCat.of PUnit.{w + 1}).singularHomology₀ε R,
      singularHomology₀Section_singularHomology₀ε R _,
      singularHomology₀ε_singularHomology₀Section R _⟩
  have : IsIso (TopPair.singularHomologyMap (complZeroPairIsoProdThomPair F).inv R
      (finrank ℝ F)) := (TopPair.singularHomologyMapIso R (complZeroPairIsoProdThomPair F).symm
        (finrank ℝ F)).isIso_hom
  rw [modelFiberMap]
  infer_instance

/-- The fibre inclusion over `x` carries the model class to the class of `x` in `H₀(W)`, read in
`Hᵣ(W × F, W × (F ∖ {0}))`. -/
private theorem modelFiberMap_comp_singularHomologyMap_prodThomPairFiberMap {W : Type w}
    [TopologicalSpace W] (x : W) :
    modelFiberMap R F ≫ TopPair.singularHomologyMap (prodThomPairFiberMap F x) R (finrank ℝ F) =
      singularHomology₀Section R (X := TopCat.of W) x ≫
        (prodThomPairSingularHomologyIso R W F 0 (finrank ℝ F)).inv := by
  -- The fibre over `x` is the Thom pair over a point, mapped in by the constant map at `x`.
  let c : C(PUnit.{w + 1}, W) := ContinuousMap.const _ x
  have hc : (complZeroPairIsoProdThomPair F).inv ≫ prodThomPairFiberMap F x =
      prodThomPairMap F c := by
    rw [Iso.inv_comp_eq, complZeroPairIsoProdThomPair_hom,
      prodThomPairFiberMap_comp_prodThomPairMap]
    -- `c` is constant at `x`.
    rfl
  rw [modelFiberMap, Category.assoc, Category.assoc, ← TopPair.singularHomologyMap_comp, hc,
    prodThomPairSingularHomologyIso_inv_naturality R PUnit.{w + 1} F c 0 (finrank ℝ F),
    ← Category.assoc, singularHomology₀Section_naturality]
  -- `c` is constant at `x`.
  rfl

end Model

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E]

omit [FiniteDimensional ℝ F] [VectorBundle ℝ F E] in
/-- **Fibre inclusions along a path in a trivialization**: for a linear trivialization `e` and
points `x` and `y` joined by a path in its base set, the inclusions
`(F, F ∖ {0}) ≅ (E_x, E_x ∖ {0}) ⟶ (E, E₀)` and `(F, F ∖ {0}) ≅ (E_y, E_y ∖ {0}) ⟶ (E, E₀)` given
by `e` induce the same map on relative singular homology, in every degree: they are homotopic as
maps of pairs, through the inclusions of the fibres over the path. -/
theorem _root_.Bundle.Trivialization.singularHomologyMap_fiberThomPairMap_eq_of_joinedIn
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x y : B} (hx : x ∈ e.baseSet)
    (hy : y ∈ e.baseSet) (hxy : JoinedIn e.baseSet x y) (n : ℕ) :
    TopPair.singularHomologyMap ((e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv ≫
        fiberThomPairMap F E x) R n =
      TopPair.singularHomologyMap ((e.continuousLinearEquivAt ℝ y hy).complZeroPairIso.inv ≫
        fiberThomPairMap F E y) R n := by
  obtain ⟨γ, hγ⟩ := hxy
  -- Over a point `b` of the base set the map of pairs is `v ↦ e⁻¹ (b, v)`.
  have hcont (b : B) (hb : b ∈ e.baseSet) :
      Continuous fun v : F ↦ TotalSpace.mk' F b (e.symm b v) :=
    e.continuousOn_symm.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ ↦ ⟨hb, trivial⟩
  have hmaps (b : B) (hb : b ∈ e.baseSet) : MapsTo (fun v : F ↦ TotalSpace.mk' F b (e.symm b v))
      ({0}ᶜ : Set F) (zeroSectionCompl F E) := fun v hv ↦
    mem_zeroSectionCompl.2 <| by
      simpa [hb] using (e.continuousLinearEquivAt ℝ b hb).symm.map_ne_zero_iff.2 hv
  have heq (b : B) (hb : b ∈ e.baseSet) :
      (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv ≫ fiberThomPairMap F E b =
        TopPair.ofSubsetMap (TopCat.ofHom ⟨_, hcont b hb⟩) (hmaps b hb) := by
    rw [ContinuousLinearEquiv.complZeroPairIso_inv, fiberThomPairMap_eq_ofSubsetMap]
    -- `(e.continuousLinearEquivAt ℝ b hb).symm` is `e.symm b` by definition.
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (TopCat.ext fun _ ↦ rfl)
  -- The homotopy through the fibres over the path.
  let H : (TopCat.ofHom ⟨_, hcont x hx⟩).hom.Homotopy (TopCat.ofHom ⟨_, hcont y hy⟩).hom :=
    { toFun p := TotalSpace.mk' F (γ p.1) (e.symm (γ p.1) p.2)
      continuous_toFun := e.continuousOn_symm.comp_continuous
        ((γ.continuous.comp continuous_fst).prodMk continuous_snd) fun p ↦ ⟨hγ p.1, trivial⟩
      map_zero_left v := congrArg (fun b ↦ TotalSpace.mk' F b (e.symm b v)) γ.source
      map_one_left v := congrArg (fun b ↦ TotalSpace.mk' F b (e.symm b v)) γ.target }
  rw [heq x hx, heq y hy]
  exact (TopPair.ofSubsetHomotopy H fun τ v hv ↦ hmaps _ (hγ τ) hv).congr_singularHomologyMap R n

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
  let v : TopCat.of W → (R ⟶ T) := fun x ↦ modelFiberMap R F ≫
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x (hW x.2)).complZeroPairIso.inv R
      (finrank ℝ F) ≫ g x
  have hv ⦃x y : TopCat.of W⦄ (γ : Path x y) : v x = v y := by
    have h : JoinedIn e.baseSet (x : B) y := by
      refine ⟨γ.map continuous_subtype_val, fun t ↦ hW (γ t).2⟩
    simp only [v]
    rw [hg (hW x.2) (hW y.2) h]
  refine ⟨TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom R (finrank ℝ F) ≫
    (prodThomPairSingularHomologyIso R W F 0 (finrank ℝ F)).hom ≫
      singularHomology₀Desc R v hv, fun x hx ↦ ?_⟩
  -- Compare both sides after the isomorphism `R ≅ Hᵣ(F, F ∖ {0}) ≅ Hᵣ(E_x, E_x ∖ {0})`.
  have hiso : IsIso (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x
      (hW hx)).complZeroPairIso.inv R (finrank ℝ F)) :=
    (TopPair.singularHomologyMapIso R (e.continuousLinearEquivAt ℝ x
      (hW hx)).complZeroPairIso.symm (finrank ℝ F)).isIso_hom
  rw [← cancel_epi (modelFiberMap R F ≫ TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x
    (hW hx)).complZeroPairIso.inv R (finrank ℝ F))]
  have hfib : (e.continuousLinearEquivAt ℝ x (hW hx)).complZeroPairIso.inv ≫
      fiberThomPairOverMap F E hx ≫ (e.thomPairOverIso ℝ hW).hom =
        prodThomPairFiberMap F (⟨x, hx⟩ : W) := by
    rw [e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW hx, Iso.inv_hom_id_assoc]
  simp only [Category.assoc]
  rw [← TopPair.singularHomologyMap_comp_assoc, ← TopPair.singularHomologyMap_comp_assoc,
    Category.assoc, hfib, reassoc_of% modelFiberMap_comp_singularHomologyMap_prodThomPairFiberMap,
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
  let S := ShortComplex.mk _ _ (singularHomology_thomPairOver_mayerVietoris_comp_eq_zero
    (F := F) (E := E) (U := U) (V := V) R (finrank ℝ F))
  have hS : S.Exact := singularHomology_thomPairOver_mayerVietoris_exact R hU hV _
  have : Epi S.g := epi_singularHomology_thomPairOver_union R hU hV hUV
  -- The two morphisms over `U` and `V`, on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ T := biprod.desc ΦU ΦV
  -- It vanishes on the image of the first map: both restrictions of a class over `U ∩ V` have the
  -- same image, since morphisms over `U ∩ V` are determined on the fibres.
  have hφ : S.f ≫ φ = 0 := by
    have h := hext
      (TopPair.singularHomologyMap (thomPairOverMap F E inter_subset_left) R _ ≫ ΦU)
      (TopPair.singularHomologyMap (thomPairOverMap F E inter_subset_right) R _ ≫ ΦV)
      fun x hx ↦ by
        rw [← TopPair.singularHomologyMap_comp_assoc, ← TopPair.singularHomologyMap_comp_assoc,
          fiberThomPairOverMap_comp_thomPairOverMap, fiberThomPairOverMap_comp_thomPairOverMap,
          hΦU, hΦV]
    simp only [S, φ, biprod.lift_desc, Preadditive.neg_comp, h, add_neg_cancel]
  let Φ := hS.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := hS.gIsCokernel.fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  refine ⟨Φ, fun x hx ↦ ?_⟩
  -- A point of `U ∪ V` lies in `U` or in `V`, through which its fibre inclusion factors.
  rcases hx with hx | hx
  · have hfac : TopPair.singularHomologyMap (fiberThomPairOverMap F E (subset_union_left hx)) R _ =
        TopPair.singularHomologyMap (fiberThomPairOverMap F E hx) R _ ≫ biprod.inl ≫ S.g := by
      simp [S, ← TopPair.singularHomologyMap_comp]
    rw [hfac, Category.assoc, Category.assoc, hgΦ, biprod.inl_desc, hΦU]
  · have hfac : TopPair.singularHomologyMap (fiberThomPairOverMap F E (subset_union_right hx)) R _ =
        TopPair.singularHomologyMap (fiberThomPairOverMap F E hx) R _ ≫ biprod.inr ≫ S.g := by
      simp [S, ← TopPair.singularHomologyMap_comp]
    rw [hfac, Category.assoc, Category.assoc, hgΦ, biprod.inr_desc, hΦV]

/-- **Finite unions of trivializing open sets**: if `g` is compatible in the trivializations of
the atlas, it factors over every finite union of open sets each lying in the base set of one of
them. -/
private theorem factorsOver_biUnion (hg : ∀ z, CompatibleAt g z) {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ z, W i ⊆ (trivializationAt F E z).baseSet) :
    FactorsOver g (⋃ i ∈ s, W i) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty => simpa using factorsOver_empty g
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    obtain ⟨z, hz⟩ := hWe a ha
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    have hinter : W a ∩ ⋃ i ∈ s, W i = ⋃ i ∈ s, (W a ∩ W i) := inter_iUnion₂ _ _
    have hinterO : ∀ i ∈ s, IsOpen (W a ∩ W i) := fun i hi ↦ (hWo a ha).inter (hWo i (hs i hi))
    have hinterE : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ),
        W a ∩ W i ⊆ e.baseSet := fun _ _ ↦
      ⟨trivializationAt F E z, inferInstance, inter_subset_left.trans hz⟩
    refine factorsOver_union g (hWo a ha)
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi))
      (factorsOver_of_subset g (hg z) hz) (ih (fun i hi ↦ hWo i (hs i hi))
        fun i hi ↦ hWe i (hs i hi)) (fun φ φ' h ↦ ?_) fun m hm ↦ ?_
    · revert φ φ'
      rw [hinter]
      exact fun φ φ' h ↦ singularHomology_thomPairOver_biUnion_hom_ext s hinterO hinterE h
    · rw [hinter]
      exact isZero_singularHomology_thomPairOver_biUnion R s hinterO hinterE (by omega)

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

/-- **Morphisms out of the top homology of the Thom pair from morphisms out of the fibres.** Let
`E → B` be a real vector bundle of rank `r` and `g b : Hᵣ(E_b, E_b ∖ {0}) ⟶ T` morphisms out of the
fibre groups. Suppose that for the trivialization `e` of the atlas at any point and any two points
`x` and `y` joined by a path in its base set, `g x` and `g y` agree after the identifications of
`Hᵣ(F, F ∖ {0})` with `Hᵣ(E_x, E_x ∖ {0})` and with `Hᵣ(E_y, E_y ∖ {0})` given by `e`. Then there is
a unique morphism `Hᵣ(E, E₀) ⟶ T` whose composite with the inclusion of each fibre pair is `g b`.
The base is arbitrary, the bundle need not be orientable, and the coefficients lie in an abelian
category with exact filtered colimits. -/
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
          (finrank ℝ F) := by
    simp
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
            simp only [Functor.comp_map, thomPairFiniteTrivializingUnionDiagram_map,
              TopPair.singularHomologyFunctor_map, TopPair.singularHomologyMap_comp,
              TopPair.singularHomologyMap_eqToHom, Functor.const_obj_map,
              Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← h]
            simp } }
  have hpt : ((TopPair.singularHomologyFunctor R (finrank ℝ F)).mapCocone
      (thomPairFiniteTrivializingUnionCocone (F := F) (E := E))).pt =
        (thomPair F E).singularHomology R (finrank ℝ F) := by
    simp
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
