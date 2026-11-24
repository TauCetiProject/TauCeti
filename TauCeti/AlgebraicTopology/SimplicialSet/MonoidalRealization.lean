/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.Realization
public import TauCeti.Topology.Category.CompactlyGenerated.CartesianClosed
public import TauCeti.Topology.Convenient.CartesianClosed

/-!
# Geometric realization of finite products of simplicial sets

Geometric realization `SSet.toTop : SSet.{u} ⥤ TopCat.{u}` does not preserve arbitrary binary
products in `TopCat.{u}`: Dowker's example of a countably infinite wedge and an uncountable wedge
of intervals shows that the product topology on `|K| × |L|` need not be a CW topology.
Nevertheless, realization preserves binary products of standard simplices
(`SSet.prodStdSimplex.instPreservesLimitPairToTop`), and every simplicial set is a canonical
colimit of standard simplices indexed by its category of elements
(`CategoryTheory.Functor.Elements.isColimitUliftYonedaCocone`). Therefore `|K ⊗ L|` agrees with the
product of `|K|` and `|L|` whenever binary product in the target category commutes with colimits in
each variable:

* **Locally compact factor in `TopCat`**: when either `|K|` or `|L|` is locally compact (in
  particular whenever one factor is a standard simplex `Δ[q]`), `TopCat.closed` makes left and right
  product with that space preserve colimits in `TopCat.{u}`, so `SSet.toTop` preserves `K ⨯ L` on
  the nose (`SSet.instPreservesLimitPairToTopOfLocallyCompactRight`,
  `SSet.instPreservesLimitPairToTopOfLocallyCompactLeft`, `SSet.toTopProdHomeo`). Specializing to
  `Δ[1]` yields the cylinder homeomorphism
  `SSet.toTopCylinderHomeo : |X ⊗ Δ[1]| ≃ₜ |X| × unitInterval`.
* **Convenient categories of `G`-generated spaces**: every standard topological simplex
  `StdSimplex ℝ (Fin (p + 1))` is pseudometrizable, hence first-countable, sequential, and
  `v`-compactly generated for every universe `v`, so every geometric realization `|X|` is
  `v`-compactly generated (`SSet.instUCompactlyGeneratedSpaceToTopObj`). More generally, whenever
  every finite-dimensional standard simplex is `G`-generated, every realization `|X|` is
  `G`-generated (`SSet.instIsGeneratedByToTopObj`), giving a colimit-preserving lift
  `SSet.toGeneratedByTopCat G : SSet.{u} ⥤ GeneratedByTopCat.{u} G`. If each generator `G i` is
  locally compact and each product `G i × G j` is `G`-generated, `SSet.toGeneratedByTopCat G` and
  `SSet.toTop ⋙ TopCat.toGeneratedByTopCat` preserve finite products, and `|K ⊗ L|` is homeomorphic
  to `WithGeneratedByTopology G (|K| × |L|)` (`SSet.toTopProdGeneratedByHomeo`), specializing to
  the Kelley product `SSet.toTopProdKelleyHomeo` for `G = CompHaus.{u}`.
* **Compactly generated spaces**: for any right adjoint `k : TopCat.{u} ⥤ CompactlyGenerated.{v, u}`
  to `CompactlyGenerated.compactlyGeneratedToTop.{v, u}` (and in particular for
  `TopCat.toCompactlyGenerated.{v, u}`), the composite `SSet.toTop.{u} ⋙ k` is naturally
  isomorphic to the colimit-preserving lift `SSet.toCompactlyGenerated.{v, u}` and preserves finite
  products, yielding the canonical comparison isomorphism
  `TauCeti.realizationProductKelleyComparison : k(|K ⨯ L|) ≅ k(|K|) ⨯ k(|L|)` and the Kelley
  homeomorphism `SSet.toTopProdCompactlyGeneratedHomeo : |K ⊗ L| ≃ₜ k(|K| × |L|)`.

## References

* C. H. Dowker, *Topology of metric complexes*, Amer. J. Math. 74 (1952), 555–577.
* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. 65 (1957),
  357–362, Lemma 2 and Theorem 2.
* P. Gabriel and M. Zisman, *Calculus of Fractions and Homotopy Theory*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 35, Springer, 1967, Chapter III, Section 3.
* Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed categories of
  (core) compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
-/

public section

universe w w' v t u

open CategoryTheory Convexity Limits MonoidalCategory Simplicial Topology

/-- Symmetry of `IsIso (Limits.prodComparison F K L)` in `K` and `L` for any functor between
categories with binary products. -/
theorem CategoryTheory.Limits.isIso_prodComparison_of_isIso_prodComparison_swap
    {C D : Type*} [Category* C] [Category* D] [HasBinaryProducts C] [HasBinaryProducts D]
    (F : C ⥤ D) {K L : C} [IsIso (Limits.prodComparison F L K)] :
    IsIso (Limits.prodComparison F K L) := by
  have hbr : (Limits.prod.braiding (F.obj K) (F.obj L)).hom ≫
      (Limits.prod.braiding (F.obj L) (F.obj K)).hom = 𝟙 _ := by
    ext <;> simp
  have hcomp : F.map (Limits.prod.braiding K L).hom ≫ Limits.prodComparison F L K ≫
      (Limits.prod.braiding (F.obj L) (F.obj K)).hom = Limits.prodComparison F K L := by
    rw [Limits.map_braiding_hom_comp_prodComparison_assoc, hbr, Category.comp_id]
  rw [← hcomp]
  infer_instance

namespace SSet

/-! ### Topological generation properties of geometric realizations -/

/-- The geometric realization of a standard simplex is first-countable. -/
instance stdSimplex.instFirstCountableTopologyToTopObj (p : ℕ) :
    FirstCountableTopology |(Δ[p] : SSet.{u})| :=
  ⦋p⦌.toTopHomeo.isInducing.firstCountableTopology

/-- If every finite-dimensional standard simplex is `G`-generated, then the geometric realization of
every simplicial set is `G`-generated. -/
instance instIsGeneratedByToTopObj {ι : Type t} (G : ι → Type v)
    [∀ i, TopologicalSpace (G i)] [∀ p : ℕ, IsGeneratedBy G (StdSimplex ℝ (Fin (p + 1)))]
    (X : SSet.{u}) : IsGeneratedBy G |X| := by
  have hΔ (n : SimplexCategory) : IsGeneratedBy G |(stdSimplex.{u}.obj n)| :=
    n.toTopHomeo.symm.isQuotientMap.isGeneratedBy
  have : ∀ j : X.Elementsᵒᵖ,
      IsGeneratedBy G ((((Functor.Elements.π X).leftOp ⋙ uliftYoneda.{u}) ⋙ toTop).obj j) :=
    fun j ↦ hΔ j.unop.obj.unop
  exact TauCeti.TopCat.isGeneratedBy_of_isColimit
    (isColimitOfPreserves toTop (Functor.Elements.isColimitUliftYonedaCocone.{u} X))

/-- The geometric realization of every simplicial set is `v`-compactly generated for every universe
`v`, since each standard simplex is pseudometrizable (hence sequential and `v`-compactly generated)
and `SSet.toTop` preserves colimits. -/
instance instUCompactlyGeneratedSpaceToTopObj (X : SSet.{u}) :
    UCompactlyGeneratedSpace.{v} |X| :=
  (Topology.isGeneratedBy_compHaus_iff.{v} |X|).1
    (instIsGeneratedByToTopObj (fun S : CompHaus.{v} ↦ S) X)

/-! ### Colimit-density criteria for product preservation out of `SSet` -/

section Density

variable {D : Type*} [Category* D] [HasBinaryProducts D] (F : SSet.{u} ⥤ D)

/-- If `F : SSet.{u} ⥤ D` preserves colimits of size `{0, u}` and left binary product with `F.obj K`
preserves colimits of size `{0, u}` in `D`, then `Limits.prodComparison F K L` is an isomorphism for
every `L` as soon as it is an isomorphism whenever `L = Δ[q]`. -/
theorem isIso_prodComparison_of_stdSimplex [PreservesColimitsOfSize.{0, u} F] (K : SSet.{u})
    [PreservesColimitsOfSize.{0, u} (Limits.prod.functor.obj (F.obj K))]
    (H : ∀ q : ℕ, IsIso (Limits.prodComparison F K Δ[q])) (L : SSet.{u}) :
    IsIso (Limits.prodComparison F K L) := by
  let G : L.Elementsᵒᵖ ⥤ SSet.{u} := (Functor.Elements.π L).leftOp ⋙ uliftYoneda.{u}
  have : IsIso (Functor.whiskerLeft G (Limits.prodComparisonNatTrans F K)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun x ↦ H x.unop.obj.unop.len
  exact isIso_app_coconePt_of_preservesColimit G (Limits.prodComparisonNatTrans F K) _
    (Functor.Elements.isColimitUliftYonedaCocone.{u} L)

/-- If `F : SSet.{u} ⥤ D` preserves colimits of size `{0, u}`, binary products in `D` preserve
colimits of size `{0, u}` in each variable, and `F` preserves binary products of standard simplices,
then `Limits.prodComparison F K L` is an isomorphism for all simplicial sets `K` and `L`. -/
theorem isIso_prodComparison_of_preservesColimits_prod_functor [PreservesColimitsOfSize.{0, u} F]
    [∀ Y : D, PreservesColimitsOfSize.{0, u} (Limits.prod.functor.obj Y)]
    (hΔ : ∀ p q : ℕ, IsIso (Limits.prodComparison F Δ[p] Δ[q])) (K L : SSet.{u}) :
    IsIso (Limits.prodComparison F K L) := by
  refine isIso_prodComparison_of_stdSimplex F K (fun q ↦ ?_) L
  have : IsIso (Limits.prodComparison F Δ[q] K) :=
    isIso_prodComparison_of_stdSimplex F Δ[q] (hΔ q) K
  exact isIso_prodComparison_of_isIso_prodComparison_swap F

/-- Under the hypotheses of `SSet.isIso_prodComparison_of_preservesColimits_prod_functor`, `F`
preserves all binary products. -/
theorem preservesBinaryProducts_of_stdSimplex [PreservesColimitsOfSize.{0, u} F]
    [∀ Y : D, PreservesColimitsOfSize.{0, u} (Limits.prod.functor.obj Y)]
    (hΔ : ∀ p q : ℕ, IsIso (Limits.prodComparison F Δ[p] Δ[q])) :
    PreservesLimitsOfShape (Discrete WalkingPair) F where
  preservesLimit {G} :=
    have (K L : SSet.{u}) : IsIso (Limits.prodComparison F K L) :=
      isIso_prodComparison_of_preservesColimits_prod_functor F hΔ K L
    have (K L : SSet.{u}) : PreservesLimit (Limits.pair K L) F :=
      PreservesLimitPair.of_iso_prod_comparison F K L
    preservesLimit_of_iso_diagram F (diagramIsoPair G).symm

/-- Under the hypotheses of `SSet.preservesBinaryProducts_of_stdSimplex`, if `F` also preserves the
terminal object, then `F` preserves all finite products. -/
theorem preservesFiniteProducts_of_stdSimplex [PreservesColimitsOfSize.{0, u} F]
    [PreservesLimit (Functor.empty.{0} SSet.{u}) F]
    [∀ Y : D, PreservesColimitsOfSize.{0, u} (Limits.prod.functor.obj Y)]
    (hΔ : ∀ p q : ℕ, IsIso (Limits.prodComparison F Δ[p] Δ[q])) :
    PreservesFiniteProducts F :=
  have := preservesBinaryProducts_of_stdSimplex F hΔ
  have := preservesLimitsOfShape_pempty_of_preservesTerminal F
  PreservesFiniteProducts.of_preserves_binary_and_terminal F

end Density

/-! ### Terminal and locally compact product preservation in `TopCat` -/

/-- Geometric realization preserves the terminal object, since `|Δ[0]|` has a unique point. -/
instance instPreservesTerminalToTop :
    PreservesLimit (Functor.empty.{0} SSet.{u}) SSet.toTop.{u} :=
  preservesTerminal_of_iso SSet.toTop.{u} <|
    SSet.toTop.mapIso (terminalIsTerminal.uniqueUpToIso stdSimplex.isTerminalObj₀) ≪≫
      TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique |(Δ[0] : SSet.{u})| PUnit.{u + 1}) ≪≫
      TopCat.terminalIsoPUnit.{u}.symm

/-- Geometric realization preserves `K ⨯ L` in `TopCat` whenever `|L|` is locally compact. -/
instance instPreservesLimitPairToTopOfLocallyCompactRight (K L : SSet.{u})
    [LocallyCompactSpace |L|] :
    PreservesLimit (Limits.pair K L) SSet.toTop.{u} := by
  have hΔL (p : ℕ) : IsIso (Limits.prodComparison SSet.toTop.{u} Δ[p] L) :=
    isIso_prodComparison_of_stdSimplex SSet.toTop.{u} Δ[p] (fun q ↦ inferInstance) L
  have hLΔ (p : ℕ) : IsIso (Limits.prodComparison SSet.toTop.{u} L Δ[p]) :=
    have := hΔL p
    isIso_prodComparison_of_isIso_prodComparison_swap SSet.toTop.{u}
  have hLK : IsIso (Limits.prodComparison SSet.toTop.{u} L K) :=
    isIso_prodComparison_of_stdSimplex SSet.toTop.{u} L hLΔ K
  have hKL : IsIso (Limits.prodComparison SSet.toTop.{u} K L) :=
    isIso_prodComparison_of_isIso_prodComparison_swap SSet.toTop.{u}
  exact PreservesLimitPair.of_iso_prod_comparison SSet.toTop.{u} K L

/-- Geometric realization preserves `K ⨯ L` in `TopCat` whenever `|K|` is locally compact. -/
instance instPreservesLimitPairToTopOfLocallyCompactLeft (K L : SSet.{u})
    [LocallyCompactSpace |K|] :
    PreservesLimit (Limits.pair K L) SSet.toTop.{u} := by
  have : IsIso (Limits.prodComparison SSet.toTop.{u} L K) := inferInstance
  have : IsIso (Limits.prodComparison SSet.toTop.{u} K L) :=
    isIso_prodComparison_of_isIso_prodComparison_swap SSet.toTop.{u}
  exact PreservesLimitPair.of_iso_prod_comparison SSet.toTop.{u} K L

/-- Whenever `SSet.toTop` preserves `K ⨯ L` (in particular when either `|K|` or `|L|` is locally
compact), `|K ⊗ L|` is homeomorphic to `|K| × |L|` via the pair of realized projections. -/
noncomputable def toTopProdHomeo (K L : SSet.{u})
    [PreservesLimit (Limits.pair K L) SSet.toTop.{u}] :
    |K ⊗ L| ≃ₜ |K| × |L| :=
  TopCat.homeoOfIso
    (CartesianMonoidalCategory.prodComparisonIso SSet.toTop.{u} K L : |K ⊗ L| ≅ |K| ⊗ |L|)

@[simp]
theorem toTopProdHomeo_apply (K L : SSet.{u})
    [PreservesLimit (Limits.pair K L) SSet.toTop.{u}] (u : |K ⊗ L|) :
    toTopProdHomeo K L u =
      (toTop.map (CartesianMonoidalCategory.fst K L) u,
        toTop.map (CartesianMonoidalCategory.snd K L) u) := by
  -- `TopCat.homeoOfIso` evaluates `prodComparisonIso.hom = prodComparison`, which in `TopCat`
  -- acts componentwise by `TopCat.lift_apply`.
  change (CartesianMonoidalCategory.prodComparison SSet.toTop.{u} K L) u = _
  exact TopCat.lift_apply

/-! ### Homeomorphism for the simplicial cylinder `|X ⊗ Δ[1]| ≃ₜ |X| × unitInterval` -/

/-- The geometric realization `|X ⊗ Δ[1]|` of the simplicial cylinder on `X` is homeomorphic to
`|X| × unitInterval`, since `|Δ[1]|` is compact Hausdorff (hence locally compact). -/
noncomputable def toTopCylinderHomeo (X : SSet.{u}) :
    |X ⊗ Δ[1]| ≃ₜ |X| × unitInterval :=
  (toTopProdHomeo X Δ[1]).trans
    ((Homeomorph.refl |X|).prodCongr (⦋1⦌.toTopHomeo.trans StdSimplex.homeomorphI))

@[simp]
theorem toTopCylinderHomeo_fst (X : SSet.{u}) (u : |X ⊗ Δ[1]|) :
    (toTopCylinderHomeo X u).1 = toTop.map (CartesianMonoidalCategory.fst X Δ[1]) u := by
  simp [toTopCylinderHomeo]

@[simp]
theorem toTopCylinderHomeo_snd (X : SSet.{u}) (u : |X ⊗ Δ[1]|) :
    (toTopCylinderHomeo X u).2 =
      StdSimplex.homeomorphI
        (⦋1⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.snd X Δ[1]) u)) := by
  simp [toTopCylinderHomeo]

private lemma toTopCylinderHomeo_symm_const {X : SSet.{u}} (ι : X ⟶ X ⊗ Δ[1]) (i v : Fin 2)
    (t : unitInterval) (hfst : ι ≫ CartesianMonoidalCategory.fst X Δ[1] = 𝟙 X)
    (hsnd : ι ≫ CartesianMonoidalCategory.snd X Δ[1] =
      stdSimplex.isTerminalObj₀.from X ≫ stdSimplex.δ i)
    (hv : i.succAbove 0 = v) (ht : StdSimplex.homeomorphI (StdSimplex.single v) = t)
    (z : |X|) :
    (toTopCylinderHomeo X).symm (z, t) = toTop.map ι z := by
  apply (toTopCylinderHomeo X).injective
  rw [Homeomorph.apply_symm_apply]
  refine (Prod.ext ?_ ?_).symm
  · simp [← ConcreteCategory.comp_apply, ← toTop.map_comp, hfst]
  · dsimp only
    rw [toTopCylinderHomeo_snd, ← ConcreteCategory.comp_apply, ← toTop.map_comp, hsnd,
      toTop.map_comp, ConcreteCategory.comp_apply, ← ht, ← hv]
    congr 1
    refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo _) (StdSimplex.single 0), StdSimplex.map_single]
    -- On `SimplexCategory`, `SimplexCategory.δ i` acts on vertices by `i.succAbove`.
    rfl

@[simp]
theorem toTopCylinderHomeo_symm_zero (X : SSet.{u}) (z : |X|) :
    (toTopCylinderHomeo X).symm (z, 0) = toTop.map ι₀ z :=
  toTopCylinderHomeo_symm_const ι₀ 1 0 0 (ι₀_fst X)
    (by rw [ι₀_snd, stdSimplex.δ_one_eq_const, SSet.comp_const]) rfl
    StdSimplex.homeomorphI_single_zero z

@[simp]
theorem toTopCylinderHomeo_symm_one (X : SSet.{u}) (z : |X|) :
    (toTopCylinderHomeo X).symm (z, 1) = toTop.map ι₁ z :=
  toTopCylinderHomeo_symm_const ι₁ 0 1 1 (ι₁_fst X)
    (by rw [ι₁_snd, stdSimplex.δ_zero_eq_const, SSet.comp_const]) rfl
    StdSimplex.homeomorphI_single_one z

theorem toTopCylinderHomeo_symm_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (z : |X|)
    (t : unitInterval) :
    (toTopCylinderHomeo Y).symm (toTop.map f z, t) =
      toTop.map (f ▷ Δ[1]) ((toTopCylinderHomeo X).symm (z, t)) := by
  apply (toTopCylinderHomeo Y).injective
  rw [Homeomorph.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [toTopCylinderHomeo_fst, ← ConcreteCategory.comp_apply, ← toTop.map_comp,
      CartesianMonoidalCategory.whiskerRight_fst, toTop.map_comp, ConcreteCategory.comp_apply,
      ← toTopCylinderHomeo_fst X, Homeomorph.apply_symm_apply]
  · dsimp only
    rw [toTopCylinderHomeo_snd, ← ConcreteCategory.comp_apply, ← toTop.map_comp,
      CartesianMonoidalCategory.whiskerRight_snd, ← toTopCylinderHomeo_snd X,
      Homeomorph.apply_symm_apply]

/-! ### Product preservation in convenient categories of `G`-generated spaces -/

section GeneratedBy

variable {ι : Type t} (G : ι → Type v) [∀ i, TopologicalSpace (G i)]
  [∀ p : ℕ, IsGeneratedBy G (StdSimplex ℝ (Fin (p + 1)))]

/-- Geometric realization lifted to the full subcategory `GeneratedByTopCat.{u} G` when every
finite-dimensional standard simplex is `G`-generated. -/
@[expose, simps! obj]
noncomputable def toGeneratedByTopCat : SSet.{u} ⥤ GeneratedByTopCat.{u} G :=
  ObjectProperty.lift _ SSet.toTop.{u} (instIsGeneratedByToTopObj G)

@[simp]
theorem toGeneratedByTopCat_map_hom {X Y : SSet.{u}} (f : X ⟶ Y) :
    ((toGeneratedByTopCat G).map f).hom = SSet.toTop.map f :=
  (rfl)

/-- `SSet.toGeneratedByTopCat G` preserves colimits of all sizes, since its composite with the
fully faithful inclusion `GeneratedByTopCat.toTopCat` is `SSet.toTop`. -/
noncomputable instance instPreservesColimitsOfSizeToGeneratedByTopCat :
    PreservesColimitsOfSize.{w', w} (toGeneratedByTopCat G : SSet.{u} ⥤ _) := by
  have : PreservesColimitsOfSize.{w', w}
      ((toGeneratedByTopCat G : SSet.{u} ⥤ _) ⋙ GeneratedByTopCat.toTopCat (X := G)) :=
    preservesColimits_of_natIso
      (ObjectProperty.liftCompιIso _ SSet.toTop.{u} (instIsGeneratedByToTopObj G)).symm
  exact preservesColimits_of_reflects_of_preserves (toGeneratedByTopCat G)
    (GeneratedByTopCat.toTopCat (X := G))

/-- Since `GeneratedByTopCat.toTopCat` is fully faithful, `SSet.toGeneratedByTopCat G` is naturally
isomorphic to `SSet.toTop ⋙ TopCat.toGeneratedByTopCat`. -/
noncomputable def toGeneratedByTopCatIso :
    (toGeneratedByTopCat G : SSet.{u} ⥤ _) ≅
      SSet.toTop.{u} ⋙ TopCat.toGeneratedByTopCat (X := G) :=
  Functor.isoWhiskerLeft (toGeneratedByTopCat G) (GeneratedByTopCat.adjUnitIso (X := G))

/-- `SSet.toGeneratedByTopCat G` preserves the terminal object. -/
noncomputable instance instPreservesTerminalToGeneratedByTopCat :
    PreservesLimit (Functor.empty.{0} SSet.{u}) (toGeneratedByTopCat G : SSet.{u} ⥤ _) :=
  preservesLimit_of_natIso _ (toGeneratedByTopCatIso G).symm

private lemma isIso_prodComparison_toGeneratedByTopCat_stdSimplex (p q : ℕ) :
    IsIso (Limits.prodComparison (toGeneratedByTopCat G : SSet.{u} ⥤ _) Δ[p] Δ[q]) := by
  have : PreservesLimit (Limits.pair (Δ[p] : SSet.{u}) Δ[q])
      (SSet.toTop.{u} ⋙ TopCat.toGeneratedByTopCat (X := G)) := inferInstance
  have : PreservesLimit (Limits.pair (Δ[p] : SSet.{u}) Δ[q])
      (toGeneratedByTopCat G : SSet.{u} ⥤ _) :=
    preservesLimit_of_natIso _ (toGeneratedByTopCatIso G).symm
  infer_instance

section Convenient

variable [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]

/-- When each generator `G i` is locally compact and each `G i × G j` is `G`-generated,
`SSet.toGeneratedByTopCat G` preserves binary products. -/
noncomputable instance instPreservesBinaryProductsToGeneratedByTopCat :
    PreservesLimitsOfShape (Discrete WalkingPair) (toGeneratedByTopCat G : SSet.{u} ⥤ _) :=
  preservesBinaryProducts_of_stdSimplex (toGeneratedByTopCat G)
    (isIso_prodComparison_toGeneratedByTopCat_stdSimplex G)

/-- When each generator `G i` is locally compact and each `G i × G j` is `G`-generated,
`SSet.toGeneratedByTopCat G` preserves finite products. -/
noncomputable instance instPreservesFiniteProductsToGeneratedByTopCat :
    PreservesFiniteProducts (toGeneratedByTopCat G : SSet.{u} ⥤ _) :=
  preservesFiniteProducts_of_stdSimplex (toGeneratedByTopCat G)
    (isIso_prodComparison_toGeneratedByTopCat_stdSimplex G)

/-- Under the convenient-category hypotheses on `G`, `SSet.toTop ⋙ TopCat.toGeneratedByTopCat`
preserves binary products. -/
noncomputable instance instPreservesBinaryProductsToTopCompToGeneratedByTopCat :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (SSet.toTop.{u} ⋙ TopCat.toGeneratedByTopCat (X := G)) :=
  preservesLimitsOfShape_of_natIso (toGeneratedByTopCatIso G)

/-- Under the convenient-category hypotheses on `G`, `SSet.toTop ⋙ TopCat.toGeneratedByTopCat`
preserves finite products. -/
noncomputable instance instPreservesFiniteProductsToTopCompToGeneratedByTopCat :
    PreservesFiniteProducts (SSet.toTop.{u} ⋙ TopCat.toGeneratedByTopCat (X := G)) :=
  have := preservesLimitsOfShape_pempty_of_preservesTerminal
    (SSet.toTop.{u} ⋙ TopCat.toGeneratedByTopCat (X := G))
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-- For any convenient generating family `G` such that standard simplices are `G`-generated,
`|K ⊗ L|` is homeomorphic to `WithGeneratedByTopology G (|K| × |L|)`. -/
noncomputable def toTopProdGeneratedByHomeo (K L : SSet.{u}) :
    |K ⊗ L| ≃ₜ WithGeneratedByTopology G (|K| × |L|) :=
  TopCat.homeoOfIso <| (GeneratedByTopCat.toTopCat (X := G)).mapIso <|
    CartesianMonoidalCategory.prodComparisonIso (toGeneratedByTopCat G : SSet.{u} ⥤ _) K L

@[simp]
theorem toTopProdGeneratedByHomeo_apply (K L : SSet.{u}) (u : |K ⊗ L|) :
    toTopProdGeneratedByHomeo G K L u =
      WithGeneratedByTopology.equiv.symm
        (toTop.map (CartesianMonoidalCategory.fst K L) u,
          toTop.map (CartesianMonoidalCategory.snd K L) u) := by
  -- `TopCat.homeoOfIso` evaluates `prodComparisonIso.hom = prodComparison`, which in
  -- `GeneratedByTopCat G` acts via `GeneratedByTopCat.lift_apply`.
  change (CartesianMonoidalCategory.prodComparison
    (toGeneratedByTopCat G : SSet.{u} ⥤ _) K L) u = _
  exact GeneratedByTopCat.lift_apply
    ((toGeneratedByTopCat G).map (CartesianMonoidalCategory.fst K L))
    ((toGeneratedByTopCat G).map (CartesianMonoidalCategory.snd K L)) u

theorem equiv_toTopProdGeneratedByHomeo_apply (K L : SSet.{u}) (u : |K ⊗ L|) :
    WithGeneratedByTopology.equiv (toTopProdGeneratedByHomeo G K L u) =
      (toTop.map (CartesianMonoidalCategory.fst K L) u,
        toTop.map (CartesianMonoidalCategory.snd K L) u) := by
  rw [toTopProdGeneratedByHomeo_apply, Equiv.apply_symm_apply]

end Convenient

end GeneratedBy

/-- Milnor's theorem in Kelley form: for any two simplicial sets `K` and `L`, the geometric
realization `|K ⊗ L|` is homeomorphic to the compactly generated (`CompHaus.{u}`-generated)
refinement of `|K| × |L|`. -/
noncomputable def toTopProdKelleyHomeo (K L : SSet.{u}) :
    |K ⊗ L| ≃ₜ WithGeneratedByTopology (fun S : CompHaus.{u} ↦ S) (|K| × |L|) :=
  toTopProdGeneratedByHomeo (fun S : CompHaus.{u} ↦ S) K L

theorem equiv_toTopProdKelleyHomeo_apply (K L : SSet.{u}) (u : |K ⊗ L|) :
    WithGeneratedByTopology.equiv (toTopProdKelleyHomeo K L u) =
      (toTop.map (CartesianMonoidalCategory.fst K L) u,
        toTop.map (CartesianMonoidalCategory.snd K L) u) :=
  equiv_toTopProdGeneratedByHomeo_apply (fun S : CompHaus.{u} ↦ S) K L u

@[simp]
theorem toTopProdKelleyHomeo_apply (K L : SSet.{u}) (u : |K ⊗ L|) :
    toTopProdKelleyHomeo K L u =
      WithGeneratedByTopology.equiv.symm
        (toTop.map (CartesianMonoidalCategory.fst K L) u,
          toTop.map (CartesianMonoidalCategory.snd K L) u) :=
  toTopProdGeneratedByHomeo_apply (fun S : CompHaus.{u} ↦ S) K L u

/-! ### Realization into `CompactlyGenerated` and Kelley product comparison -/

/-- Geometric realization lifted to `CompactlyGenerated.{v, u}`, obtained by composing
`SSet.toGeneratedByTopCat (fun S : CompHaus.{v} ↦ S)` with
`CompactlyGenerated.ofGeneratedByTopCat`. -/
@[expose]
noncomputable def toCompactlyGenerated : SSet.{u} ⥤ CompactlyGenerated.{v, u} :=
  toGeneratedByTopCat (fun S : CompHaus.{v} ↦ S) ⋙ CompactlyGenerated.ofGeneratedByTopCat.{v, u}

@[simp]
theorem toCompactlyGenerated_obj_toTop (X : SSet.{u}) :
    (toCompactlyGenerated.{v, u}.obj X).toTop = |X| :=
  (rfl)

@[simp]
theorem toCompactlyGenerated_map_hom {X Y : SSet.{u}} (f : X ⟶ Y) :
    (toCompactlyGenerated.{v, u}.map f).hom = SSet.toTop.map f :=
  (rfl)

/-- `SSet.toCompactlyGenerated` preserves colimits of all sizes. -/
noncomputable instance instPreservesColimitsOfSizeToCompactlyGenerated :
    PreservesColimitsOfSize.{w', w} (toCompactlyGenerated.{v, u}) := by
  dsimp only [toCompactlyGenerated]
  infer_instance

/-- For any right adjoint `k` to `CompactlyGenerated.compactlyGeneratedToTop.{v, u}`, the composite
`SSet.toTop ⋙ k` is naturally isomorphic to `SSet.toCompactlyGenerated.{v, u}`, since every
geometric realization is already `v`-compactly generated and `compactlyGeneratedToTop` is fully
faithful. -/
noncomputable def toCompactlyGeneratedIsoCompRightAdjoint
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) :
    toCompactlyGenerated.{v, u} ≅ SSet.toTop.{u} ⋙ k :=
  have : IsIso hk.unit := hk.unit_isIso_of_L_fully_faithful
  NatIso.ofComponents (fun X ↦ (asIso hk.unit).app (toCompactlyGenerated.{v, u}.obj X))
    fun f ↦ hk.unit.naturality (toCompactlyGenerated.{v, u}.map f)

@[simp]
theorem toCompactlyGeneratedIsoCompRightAdjoint_hom_app
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (X : SSet.{u}) :
    (toCompactlyGeneratedIsoCompRightAdjoint k hk).hom.app X =
      hk.unit.app (toCompactlyGenerated.{v, u}.obj X) := by
  -- `toCompactlyGenerated ⋙ compactlyGeneratedToTop` is definitionally `SSet.toTop`.
  rfl

/-- `SSet.toTop ⋙ k` preserves colimits of all sizes for any right adjoint `k` to
`CompactlyGenerated.compactlyGeneratedToTop.{v, u}`. -/
theorem preservesColimitsOfSize_toTop_comp_compactlyGenerated
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) :
    PreservesColimitsOfSize.{w', w} (SSet.toTop.{u} ⋙ k) :=
  preservesColimits_of_natIso (toCompactlyGeneratedIsoCompRightAdjoint k hk)

/-- `SSet.toTop ⋙ k` preserves the terminal object. -/
theorem preservesTerminal_toTop_comp_compactlyGenerated
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) :
    PreservesLimit (Functor.empty.{0} SSet.{u}) (SSet.toTop.{u} ⋙ k) :=
  have := hk.isRightAdjoint
  inferInstance

/-- For any right adjoint `k` to `CompactlyGenerated.compactlyGeneratedToTop.{v, u}`, the binary
product comparison morphism for `SSet.toTop ⋙ k` is an isomorphism on all simplicial sets `K` and
`L`. -/
theorem isIso_prodComparison_toTop_comp_compactlyGenerated
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    IsIso (Limits.prodComparison (SSet.toTop.{u} ⋙ k) K L) := by
  have : PreservesColimitsOfSize.{0, u} (SSet.toTop.{u} ⋙ k) :=
    preservesColimitsOfSize_toTop_comp_compactlyGenerated k hk
  have := hk.isRightAdjoint
  exact isIso_prodComparison_of_preservesColimits_prod_functor (SSet.toTop.{u} ⋙ k)
    (fun p q ↦ inferInstance) K L

/-- `SSet.toTop ⋙ k` preserves the binary product of any two simplicial sets `K` and `L`. -/
theorem preservesLimit_pair_toTop_comp_compactlyGenerated
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    PreservesLimit (Limits.pair K L) (SSet.toTop.{u} ⋙ k) :=
  have := isIso_prodComparison_toTop_comp_compactlyGenerated k hk K L
  PreservesLimitPair.of_iso_prod_comparison (SSet.toTop.{u} ⋙ k) K L

/-- `SSet.toTop ⋙ k` preserves all binary products. -/
theorem preservesBinaryProducts_toTop_comp_compactlyGenerated
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) :
    PreservesLimitsOfShape (Discrete WalkingPair) (SSet.toTop.{u} ⋙ k) := by
  have : PreservesColimitsOfSize.{0, u} (SSet.toTop.{u} ⋙ k) :=
    preservesColimitsOfSize_toTop_comp_compactlyGenerated k hk
  have := hk.isRightAdjoint
  exact preservesBinaryProducts_of_stdSimplex (SSet.toTop.{u} ⋙ k) fun p q ↦ inferInstance

/-- `SSet.toTop ⋙ k` preserves all finite products. -/
theorem preservesFiniteProducts_toTop_comp_compactlyGenerated
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) :
    PreservesFiniteProducts (SSet.toTop.{u} ⋙ k) := by
  have := hk.isRightAdjoint
  have := preservesBinaryProducts_toTop_comp_compactlyGenerated k hk
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (SSet.toTop.{u} ⋙ k)
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal (SSet.toTop.{u} ⋙ k)

/-- `SSet.toTop ⋙ TopCat.toCompactlyGenerated` preserves colimits of all sizes. -/
noncomputable instance instPreservesColimitsOfSizeToTopCompToCompactlyGenerated :
    PreservesColimitsOfSize.{w', w} (SSet.toTop.{u} ⋙ TopCat.toCompactlyGenerated.{v, u}) :=
  preservesColimitsOfSize_toTop_comp_compactlyGenerated _ CompactlyGenerated.adj.{v, u}

/-- `SSet.toTop ⋙ TopCat.toCompactlyGenerated` preserves binary products. -/
noncomputable instance instPreservesBinaryProductsToTopCompToCompactlyGenerated :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (SSet.toTop.{u} ⋙ TopCat.toCompactlyGenerated.{v, u}) :=
  preservesBinaryProducts_toTop_comp_compactlyGenerated _ CompactlyGenerated.adj.{v, u}

/-- `SSet.toTop ⋙ TopCat.toCompactlyGenerated` preserves finite products. -/
noncomputable instance instPreservesFiniteProductsToTopCompToCompactlyGenerated :
    PreservesFiniteProducts (SSet.toTop.{u} ⋙ TopCat.toCompactlyGenerated.{v, u}) :=
  preservesFiniteProducts_toTop_comp_compactlyGenerated _ CompactlyGenerated.adj.{v, u}

/-- Milnor's theorem via the coreflector `TopCat.toCompactlyGenerated`: `|K ⊗ L|` is homeomorphic to
`TopCat.toCompactlyGenerated.{u, u}.obj (TopCat.of (|K| × |L|))` via the pair of realized
projections. -/
noncomputable def toTopProdCompactlyGeneratedHomeo (K L : SSet.{u}) :
    |K ⊗ L| ≃ₜ TopCat.toCompactlyGenerated.{u, u}.obj (TopCat.of (|K| × |L|)) :=
  (toTopProdKelleyHomeo K L).trans <|
    (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u, u}
      (TopCat.of (|K| × |L|))).symm

@[simp]
theorem toTopProdCompactlyGeneratedHomeo_apply (K L : SSet.{u}) (u : |K ⊗ L|) :
    (toTopProdCompactlyGeneratedHomeo K L u : |K| × |L|) =
      (toTop.map (CartesianMonoidalCategory.fst K L) u,
        toTop.map (CartesianMonoidalCategory.snd K L) u) := by
  dsimp only [toTopProdCompactlyGeneratedHomeo, Homeomorph.trans_apply]
  rw [toTopProdKelleyHomeo_apply]
  exact (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy_symm_apply.{u, u}
    (TopCat.of (|K| × |L|)) _).trans (Equiv.apply_symm_apply _ _)

end SSet

namespace TauCeti

/-- The canonical isomorphism `k(|K ⨯ L|) ≅ k(|K|) ⨯ k(|L|)` in `CompactlyGenerated.{v, u}` for any
right adjoint `k` to `CompactlyGenerated.compactlyGeneratedToTop.{v, u}`, whose forward morphism is
the categorical binary product comparison `Limits.prodComparison (SSet.toTop ⋙ k) K L`. -/
noncomputable def realizationProductKelleyComparison
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    k.obj (SSet.toTop.obj (Limits.prod K L)) ≅
      Limits.prod (k.obj (SSet.toTop.obj K)) (k.obj (SSet.toTop.obj L)) :=
  have := SSet.isIso_prodComparison_toTop_comp_compactlyGenerated k hk K L
  asIso (Limits.prodComparison (SSet.toTop.{u} ⋙ k) K L)

@[simp]
theorem realizationProductKelleyComparison_hom
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    (realizationProductKelleyComparison k hk K L).hom =
      Limits.prodComparison (SSet.toTop.{u} ⋙ k) K L :=
  (rfl)

@[reassoc]
theorem realizationProductKelleyComparison_hom_fst
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    (realizationProductKelleyComparison k hk K L).hom ≫ Limits.prod.fst =
      k.map (SSet.toTop.map Limits.prod.fst) :=
  Limits.prod.lift_fst _ _

@[reassoc]
theorem realizationProductKelleyComparison_hom_snd
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    (realizationProductKelleyComparison k hk K L).hom ≫ Limits.prod.snd =
      k.map (SSet.toTop.map Limits.prod.snd) :=
  Limits.prod.lift_snd _ _

@[reassoc (attr := simp)]
theorem realizationProductKelleyComparison_inv_map_fst
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    (realizationProductKelleyComparison k hk K L).inv ≫
      k.map (SSet.toTop.map Limits.prod.fst) = Limits.prod.fst := by
  have := SSet.isIso_prodComparison_toTop_comp_compactlyGenerated k hk K L
  exact Limits.inv_prodComparison_map_fst (SSet.toTop.{u} ⋙ k)

@[reassoc (attr := simp)]
theorem realizationProductKelleyComparison_inv_map_snd
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    (realizationProductKelleyComparison k hk K L).inv ≫
      k.map (SSet.toTop.map Limits.prod.snd) = Limits.prod.snd := by
  have := SSet.isIso_prodComparison_toTop_comp_compactlyGenerated k hk K L
  exact Limits.inv_prodComparison_map_snd (SSet.toTop.{u} ⋙ k)

@[reassoc]
theorem realizationProductKelleyComparison_natural
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k)
    {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    k.map (SSet.toTop.map (Limits.prod.map f g)) ≫
      (realizationProductKelleyComparison k hk K' L').hom =
      (realizationProductKelleyComparison k hk K L).hom ≫
        Limits.prod.map (k.map (SSet.toTop.map f)) (k.map (SSet.toTop.map g)) :=
  Limits.prodComparison_natural (SSet.toTop.{u} ⋙ k) f g

@[reassoc]
theorem realizationProductKelleyComparison_inv_natural
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k)
    {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    (realizationProductKelleyComparison k hk K L).inv ≫
      k.map (SSet.toTop.map (Limits.prod.map f g)) =
      Limits.prod.map (k.map (SSet.toTop.map f)) (k.map (SSet.toTop.map g)) ≫
        (realizationProductKelleyComparison k hk K' L').inv := by
  have := SSet.isIso_prodComparison_toTop_comp_compactlyGenerated k hk K L
  have := SSet.isIso_prodComparison_toTop_comp_compactlyGenerated k hk K' L'
  exact Limits.prodComparison_inv_natural (SSet.toTop.{u} ⋙ k) f g

@[reassoc]
theorem map_braiding_hom_comp_realizationProductKelleyComparison_hom
    (k : TopCat.{u} ⥤ CompactlyGenerated.{v, u})
    (hk : CompactlyGenerated.compactlyGeneratedToTop.{v, u} ⊣ k) (K L : SSet.{u}) :
    k.map (SSet.toTop.map (Limits.prod.braiding K L).hom) ≫
      (realizationProductKelleyComparison k hk L K).hom =
      (realizationProductKelleyComparison k hk K L).hom ≫
        (Limits.prod.braiding (k.obj |K|) (k.obj |L|)).hom :=
  Limits.map_braiding_hom_comp_prodComparison (SSet.toTop.{u} ⋙ k)

end TauCeti
