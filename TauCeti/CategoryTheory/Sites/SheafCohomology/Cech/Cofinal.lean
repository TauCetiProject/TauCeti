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

* `TauCeti.CategoryTheory.toCechCohomology A E hE n U hU`: the map from the Čech cohomology of a
  family refined by the system to the Čech cohomology for the system.
* `TauCeti.CategoryTheory.cechCohomologyComparison A E hE F hF n h`: the map between the Čech
  cohomologies for two systems when every member of the first is refined by one of the second.
* `TauCeti.CategoryTheory.cechCohomologyIso A E hE F hF n h h'`: the isomorphism for two mutually
  cofinal systems.

## Main results

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

/-! ### Families refined by a system -/

variable [HasColimitsOfShape J A]

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
  -- both composites factor through the structure map at a common refinement `E k`, and the two
  -- refinements of `U` by `E k` induce the same map
  have hk : cechComplexHomologyMap A n hU.choose_spec.some ≫
      cechComplexHomologyMap A n (hE hik).some =
        cechComplexHomologyMap A n φ ≫ cechComplexHomologyMap A n (hE hjk).some := by
    rw [← cechComplexHomologyMap_comp, ← cechComplexHomologyMap_comp]
    exact cechComplexHomologyMap_eq A n _ _
  rw [toCechCohomology, ← cechComplexHomologyMap_comp_cechCohomologyι A E hE n hik (hE hik).some,
    ← cechComplexHomologyMap_comp_cechCohomologyι A E hE n hjk (hE hjk).some]
  exact (Category.assoc _ _ _).symm.trans ((hk =≫ _).trans (Category.assoc _ _ _))

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
    cechCohomology A E hE n ⟶ cechCohomology A F hF n :=
  (isColimitCechCohomologyCocone A E hE n).desc
    { pt := cechCohomology A F hF n
      ι :=
        { app j := toCechCohomology A F hF n (E j) (h j)
          -- the transition maps are induced by refinements, along which `toCechCohomology` is
          -- natural
          naturality _ j f :=
            (congrArg (· ≫ toCechCohomology A F hF n (E j) (h j))
              (cechCohomologyDiagram_map A E hE n f (hE (leOfHom f)).some)).trans <|
                (cechComplexHomologyMap_comp_toCechCohomology A F hF n _ (h j)).trans
                  (Category.comp_id _).symm } }

omit [IsDirectedOrder J] in
/-- The comparison map sends the structure map at `j` to `toCechCohomology` of the family `E j`.
-/
@[reassoc (attr := simp)]
theorem cechCohomologyι_comp_cechCohomologyComparison (h : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (j : J) :
    cechCohomologyι E hE n j ≫ cechCohomologyComparison A E hE F hF n h =
      toCechCohomology A F hF n (E j) (h j) :=
  (isColimitCechCohomologyCocone A E hE n).fac _ j

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

/-- The forward map of `cechCohomologyIso` is the comparison map. -/
@[simp]
theorem cechCohomologyIso_hom (h : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (h' : ∀ k, ∃ j, Nonempty (E j ⟶ F k)) :
    (cechCohomologyIso A E hE F hF n h h').hom = cechCohomologyComparison A E hE F hF n h :=
  (rfl)

/-- The backward map of `cechCohomologyIso` is the comparison map in the other direction. -/
@[simp]
theorem cechCohomologyIso_inv (h : ∀ j, ∃ k, Nonempty (F k ⟶ E j))
    (h' : ∀ k, ∃ j, Nonempty (E j ⟶ F k)) :
    (cechCohomologyIso A E hE F hF n h h').inv = cechCohomologyComparison A F hF E hE n h' :=
  (rfl)

end TauCeti.CategoryTheory
