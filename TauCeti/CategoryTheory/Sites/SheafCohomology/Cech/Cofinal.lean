/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Colimit

/-!
# Čech cohomology of families refined by a system, and cofinal systems

Let `C` be a category with finite products and `E : J → FormalCoproduct C` a system of families
indexed by a preorder `J`, such that `E j` admits a morphism of families to `E i` whenever
`i ≤ j`. The Čech cohomology for the system, `TauCeti.CategoryTheory.cechCohomology A E hE n`, is
the colimit over `J` of the degree `n` Čech cohomologies of the families `E j`.

A morphism of families `φ : U ⟶ V` induces a map `Hⁿ(Č(V, P)) ⟶ Hⁿ(Č(U, P))`, natural in the
presheaf `P` (`cechComplexHomologyMap`), and any two morphisms of families induce the same map
(`cechComplexHomologyMap_eq`). Hence, when `J` is directed, every family `U` refined by some
member of the system has a canonical map `toCechCohomology` from its Čech cohomology to the Čech
cohomology for the system, which does not depend on the refining member nor on the refinement
(`toCechCohomology_eq`) and is natural in morphisms of families. If each of two directed systems
refines the other, their Čech cohomologies are canonically isomorphic (`cechCohomologyIso`),
compatibly with these maps.

## Main definitions

* `TauCeti.CategoryTheory.cechComplexHomologyMap A n φ`: the map on degree `n` Čech cohomology
  induced by a morphism of families, as a natural transformation of functors of the presheaf.
* `TauCeti.CategoryTheory.toCechCohomology A E hE n U hU`: the map from the Čech cohomology of a
  family refined by the system to the Čech cohomology for the system.
* `TauCeti.CategoryTheory.cechCohomologyComparison A E hE F hF n h`: the map between the Čech
  cohomologies for two systems when every member of the first is refined by one of the second.
* `TauCeti.CategoryTheory.cechCohomologyIso A E hE F hF n h h'`: the isomorphism for two mutually
  cofinal systems.

## Main results

* `TauCeti.CategoryTheory.cechComplexHomologyMap_eq`: any two morphisms of families induce the
  same map on Čech cohomology.
* `TauCeti.CategoryTheory.toCechCohomology_eq`: `toCechCohomology` may be computed through any
  member of the system refining the family and any refinement.
* `TauCeti.CategoryTheory.cechComplexHomologyMap_comp_toCechCohomology`: `toCechCohomology` is
  natural in morphisms of families.
* `TauCeti.CategoryTheory.toCechCohomology_comp_cechCohomologyComparison`: the comparison maps are
  compatible with `toCechCohomology`.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY), for the refinement maps and
  their independence of the refinement function on cohomology.
* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4, Čech cohomology as a colimit over refinements of open covers.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w t t' v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] (A : Type u') [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] [CategoryWithHomology A]
  {J : Type t} [Preorder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i))
  {K : Type t'} [Preorder K] (F : K → FormalCoproduct.{w} C)
  (hF : ∀ ⦃i j : K⦄, i ≤ j → Nonempty (F j ⟶ F i)) (n : ℕ)

/-! ### Maps induced by morphisms of families -/

/-- The map on degree `n` Čech cohomology induced by a morphism of families `φ : U ⟶ V`, for open
covers a refinement map, as a natural transformation of functors of the presheaf: its component
at `P` is the map `Hⁿ(Č(V, P)) ⟶ Hⁿ(Č(U, P))` induced by `cechComplexMap P φ`. -/
@[expose, simps]
def cechComplexHomologyMap {U V : FormalCoproduct.{w} C} (φ : U ⟶ V) :
    cechComplexFunctor V.obj ⋙ HomologicalComplex.homologyFunctor A _ n ⟶
      cechComplexFunctor U.obj ⋙ HomologicalComplex.homologyFunctor A _ n where
  app P := HomologicalComplex.homologyMap (cechComplexMap P φ) n
  naturality P _ α := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n) (cechComplexMap_naturality P α _)).trans
      (HomologicalComplex.homologyMap_comp _ _ n)

/-- **Any two morphisms of families induce the same map on Čech cohomology.** For open covers:
the map on Čech cohomology induced by a refinement does not depend on the refinement map. -/
theorem cechComplexHomologyMap_eq {U V : FormalCoproduct.{w} C} (φ ψ : U ⟶ V) :
    cechComplexHomologyMap A n φ = cechComplexHomologyMap A n ψ := by
  ext P
  exact (cechComplexMapHomotopy P φ ψ).homologyMap_eq n

@[simp]
theorem cechComplexHomologyMap_id (U : FormalCoproduct.{w} C) :
    cechComplexHomologyMap A n (𝟙 U) = 𝟙 _ := by
  ext P
  exact (congrArg (HomologicalComplex.homologyMap · n) (cechComplexMap_id P)).trans
    (HomologicalComplex.homologyMap_id _ n)

@[simp]
theorem cechComplexHomologyMap_comp {U V W : FormalCoproduct.{w} C} (φ : U ⟶ V) (ψ : V ⟶ W) :
    cechComplexHomologyMap A n (φ ≫ ψ) =
      cechComplexHomologyMap A n ψ ≫ cechComplexHomologyMap A n φ := by
  ext P
  exact (congrArg (HomologicalComplex.homologyMap · n) (cechComplexMap_comp P φ ψ)).trans
    (HomologicalComplex.homologyMap_comp _ _ n)

/-! ### Families refined by a system -/

/-- The transition map of `cechCohomologyDiagram` along `i ≤ j` is the map induced by any
morphism of families `E j ⟶ E i`. -/
theorem cechCohomologyDiagram_map {i j : J} (f : i ⟶ j) (φ : E j ⟶ E i) :
    (cechCohomologyDiagram A E hE n).map f = cechComplexHomologyMap A n φ := by
  ext P
  exact cechCohomologyDiagram_map_app E hE n f φ P

variable [HasColimitsOfShape J A]

/-- The structure maps of the Čech cohomology for the system are compatible with the map induced
by any morphism of families `E j ⟶ E i`, for `i ≤ j`. -/
@[reassoc]
theorem cechComplexHomologyMap_comp_cechCohomologyι {i j : J} (h : i ≤ j) (φ : E j ⟶ E i) :
    cechComplexHomologyMap A n φ ≫ cechCohomologyι E hE n j = cechCohomologyι E hE n i := by
  ext P
  exact homologyMap_cechComplexMap_comp_cechCohomologyι_app E hE n h φ P

/-- Two maps out of the Čech cohomology for the system agree as soon as they agree after every
structure map. -/
theorem cechCohomology_hom_ext {G : (Cᵒᵖ ⥤ A) ⥤ A} {f g : cechCohomology A E hE n ⟶ G}
    (h : ∀ j, cechCohomologyι E hE n j ≫ f = cechCohomologyι E hE n j ≫ g) : f = g :=
  NatTrans.ext <| funext fun P ↦ cechCohomology_obj_hom_ext fun j ↦ by
    simpa only [NatTrans.comp_app] using NatTrans.congr_app (h j) P

/-- For a family `U` refined by some member of the system `E`, the map from the degree `n` Čech
cohomology of `U` to the Čech cohomology for the system, natural in the presheaf: the map induced
by a refinement of `U` by a member of the system, followed by the structure map of that member.
For a directed system it depends on neither choice (`toCechCohomology_eq`). -/
def toCechCohomology (U : FormalCoproduct.{w} C) (hU : ∃ j, Nonempty (E j ⟶ U)) :
    cechComplexFunctor U.obj ⋙ HomologicalComplex.homologyFunctor A _ n ⟶
      cechCohomology A E hE n :=
  cechComplexHomologyMap A n hU.choose_spec.some ≫ cechCohomologyι E hE n hU.choose

variable [IsDirectedOrder J]

/-- `toCechCohomology` may be computed through any member of the system refining the family, and
any refinement. -/
theorem toCechCohomology_eq (U : FormalCoproduct.{w} C) (j : J) (φ : E j ⟶ U) :
    toCechCohomology A E hE n U ⟨j, ⟨φ⟩⟩ =
      cechComplexHomologyMap A n φ ≫ cechCohomologyι E hE n j := by
  have hU : ∃ j, Nonempty (E j ⟶ U) := ⟨j, ⟨φ⟩⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge hU.choose j
  -- both composites factor through the structure map at a common refinement `E k`
  rw [toCechCohomology, ← cechComplexHomologyMap_comp_cechCohomologyι A E hE n hik (hE hik).some,
    ← cechComplexHomologyMap_comp_cechCohomologyι A E hE n hjk (hE hjk).some]
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ cechCohomologyι E hE n k)
    ((cechComplexHomologyMap_comp A n _ _).symm.trans <| (cechComplexHomologyMap_eq A n _ _).trans
      (cechComplexHomologyMap_comp A n _ _))).trans (Category.assoc _ _ _)

/-- On a member of the system, `toCechCohomology` is the structure map. -/
@[simp]
theorem toCechCohomology_self (j : J) (hj : ∃ i, Nonempty (E i ⟶ E j)) :
    toCechCohomology A E hE n (E j) hj = cechCohomologyι E hE n j := by
  rw [toCechCohomology_eq A E hE n (E j) j (𝟙 _), cechComplexHomologyMap_id]
  exact Category.id_comp _

/-- `toCechCohomology` is natural in morphisms of families. -/
@[reassoc (attr := simp)]
theorem cechComplexHomologyMap_comp_toCechCohomology {U V : FormalCoproduct.{w} C} (φ : V ⟶ U)
    (hV : ∃ j, Nonempty (E j ⟶ V)) :
    cechComplexHomologyMap A n φ ≫ toCechCohomology A E hE n V hV =
      toCechCohomology A E hE n U (hV.imp fun _ ⟨ψ⟩ ↦ ⟨ψ ≫ φ⟩) := by
  obtain ⟨j, ⟨ψ⟩⟩ := hV
  rw [toCechCohomology_eq A E hE n V j ψ, toCechCohomology_eq A E hE n U j (ψ ≫ φ),
    cechComplexHomologyMap_comp]
  exact (Category.assoc _ _ _).symm

/-! ### Comparison of mutually cofinal systems -/

variable [IsDirectedOrder K] [HasColimitsOfShape K A]

/-- If every member of the directed system `E` is refined by a member of the directed system `F`,
the map from the Čech cohomology for `E` to the Čech cohomology for `F` whose composite with the
structure map at `j` is `toCechCohomology` of the family `E j`. -/
def cechCohomologyComparison (h : ∀ j, ∃ k, Nonempty (F k ⟶ E j)) :
    cechCohomology A E hE n ⟶ cechCohomology A F hF n where
  app P := colimit.desc _
    { pt := (cechCohomology A F hF n).obj P
      ι :=
        { app j := (toCechCohomology A F hF n (E j) (h j)).app P
          naturality i j f := by
            have := NatTrans.congr_app (cechComplexHomologyMap_comp_toCechCohomology A F hF n
              (hE (leOfHom f)).some (h j)) P
            rw [NatTrans.comp_app] at this
            exact (congrArg (· ≫ _) (cechCohomologyDiagram_map_app E hE n f _ P)).trans
              (this.trans (Category.comp_id _).symm) } }
  naturality P Q α := cechCohomology_obj_hom_ext fun j ↦ by
    -- the structure maps and `toCechCohomology` are both natural in the presheaf
    have h₁ := (cechCohomologyι E hE n j).naturality α
    have h₂ : ((cechCohomologyDiagram A E hE n).obj j).map α ≫
        (toCechCohomology A F hF n (E j) (h j)).app Q =
          (toCechCohomology A F hF n (E j) (h j)).app P ≫ (cechCohomology A F hF n).map α :=
      (toCechCohomology A F hF n (E j) (h j)).naturality α
    rw [cechCohomologyι_app, cechCohomologyι_app] at h₁
    rw [cechCohomologyι_app]
    exact ((Category.assoc _ _ _).symm.trans <| (h₁.symm =≫ _).trans <|
      (Category.assoc _ _ _).trans <|
        (((cechCohomologyDiagram A E hE n).obj j).map α ≫= colimit.ι_desc _ j).trans h₂).trans
          (by erw [colimit.ι_desc_assoc]; rfl)

omit [IsDirectedOrder J] in
/-- The comparison map sends the structure map at `j` to `toCechCohomology` of the family `E j`.
-/
@[reassoc (attr := simp)]
theorem cechCohomologyι_comp_cechCohomologyComparison (h : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (j : J) :
    cechCohomologyι E hE n j ≫ cechCohomologyComparison A E hE F hF n h =
      toCechCohomology A F hF n (E j) (h j) := by
  ext P
  rw [NatTrans.comp_app, cechCohomologyι_app]
  exact colimit.ι_desc _ j

/-- The comparison map is compatible with `toCechCohomology` for every family refined by the
first system. -/
@[reassoc (attr := simp)]
theorem toCechCohomology_comp_cechCohomologyComparison (h : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (U : FormalCoproduct.{w} C) (hU : ∃ j, Nonempty (E j ⟶ U)) :
    toCechCohomology A E hE n U hU ≫ cechCohomologyComparison A E hE F hF n h =
      toCechCohomology A F hF n U (hU.elim fun j ⟨φ⟩ ↦ (h j).imp fun _ ⟨ψ⟩ ↦ ⟨ψ ≫ φ⟩) := by
  obtain ⟨j, ⟨φ⟩⟩ := hU
  rw [toCechCohomology_eq A E hE n U j φ]
  exact (Category.assoc _ _ _).trans <|
    (_ ≫= cechCohomologyι_comp_cechCohomologyComparison A E hE F hF n h j).trans
      (cechComplexHomologyMap_comp_toCechCohomology A F hF n φ (h j))

/-- **Mutually cofinal systems of families have canonically isomorphic Čech cohomology.** If every
member of each of two directed systems of families is refined by a member of the other, their
Čech cohomologies are isomorphic, naturally in the presheaf and compatibly with
`toCechCohomology` (`toCechCohomology_comp_cechCohomologyComparison`). -/
@[expose, simps]
def cechCohomologyIso (h : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (h' : ∀ k, ∃ j, Nonempty (E j ⟶ F k)) :
    cechCohomology A E hE n ≅ cechCohomology A F hF n where
  hom := cechCohomologyComparison A E hE F hF n h
  inv := cechCohomologyComparison A F hF E hE n h'
  hom_inv_id := cechCohomology_hom_ext A E hE n fun j ↦
    (cechCohomologyι_comp_cechCohomologyComparison_assoc A E hE F hF n h j _).trans <|
      (toCechCohomology_comp_cechCohomologyComparison A F hF E hE n h' (E j) (h j)).trans <|
        (toCechCohomology_self A E hE n j _).trans (Category.comp_id _).symm
  inv_hom_id := cechCohomology_hom_ext A F hF n fun k ↦
    (cechCohomologyι_comp_cechCohomologyComparison_assoc A F hF E hE n h' k _).trans <|
      (toCechCohomology_comp_cechCohomologyComparison A E hE F hF n h (F k) (h' k)).trans <|
        (toCechCohomology_self A F hF n k _).trans (Category.comp_id _).symm

end TauCeti.CategoryTheory
