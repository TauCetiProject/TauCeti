/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.Directed
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Čech cohomology along refinements, and its colimits over directed systems of families

Let `C` be a category with finite products and `P : Cᵒᵖ ⥤ A` a presheaf with values in a
preadditive category with products and homology. Taking the degree `n` cohomology of the Čech
complex `Č(U, P)` is a functor `cechCohomologyFunctor P n` of the family `U`, regarded as a
formal coproduct: a morphism of families `U ⟶ V`, for open covers a refinement map, induces
`Hⁿ(Č(V, P)) ⟶ Hⁿ(Č(U, P))`. Any two morphisms of families induce the same map on cohomology
(`cechCohomologyFunctor_map_eq`), because they induce homotopic maps of Čech complexes.

Hence the cohomology of a system of families indexed by a preorder `I`, through a map
`c : I → FormalCoproduct C` such that `i ≤ j` exactly when some morphism `c j ⟶ c i` exists,
is a functor `cechCohomologyDiagram P n c hc : I ⥤ A`, without a choice of refinement maps
mattering. Only the existence of refinements enters the order; the category of actual
refinement maps is not filtered in general, but a directed preorder is. When `I` is directed,
every family `U` refined by some `c i` has a canonical map `toCechCohomologyColimit` from its
cohomology to the colimit of this diagram, natural in morphisms of families. Two systems each of
which refines the other have canonically isomorphic colimits (`cechCohomologyColimitIso`).

For open covers of a topological space, these colimits over small cofinal cover systems define
Čech cohomology (`TauCeti.Topology.cechCohomology`).

## Main definitions

* `TauCeti.CategoryTheory.cechCohomologyFunctor P n`: the degree `n` cohomology of the Čech
  complex of `P`, as a functor `(FormalCoproduct C)ᵒᵖ ⥤ A`.
* `TauCeti.CategoryTheory.cechCohomologyDiagram P n c hc`: its restriction to a preorder of
  families ordered by existence of refinements.
* `TauCeti.CategoryTheory.toCechCohomologyColimit P n c hc U hU`: for a directed preorder, the map
  from the cohomology of a family refined by the system to the colimit.
* `TauCeti.CategoryTheory.cechCohomologyColimitIso`: the comparison isomorphism of the colimits
  over two mutually cofinal directed systems of families.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY), for the refinement maps and
  their independence of the refinement function on cohomology.
* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4, Čech cohomology as a colimit over refinements of open covers.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u' t t'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] [CategoryWithHomology A] (P : Cᵒᵖ ⥤ A) (n : ℕ)

/-- The degree `n` Čech cohomology `Hⁿ(Č(U, P))` of `P` for a family `U`, as a contravariant
functor of the family: a morphism of families `U ⟶ V` induces the map `Hⁿ(Č(V, P)) ⟶ Hⁿ(Č(U, P))`
of `cechComplexMap`. -/
@[expose, simps -isSimp]
def cechCohomologyFunctor : (FormalCoproduct.{w} C)ᵒᵖ ⥤ A where
  obj U := ((cechComplexFunctor U.unop.obj).obj P).homology n
  map φ := HomologicalComplex.homologyMap (cechComplexMap P φ.unop) n
  map_id U := by simp [cechComplexMap_id (U := U.unop.obj)]
  map_comp φ ψ := by simp [HomologicalComplex.homologyMap_comp]

/-- **Any two morphisms of families induce the same map on Čech cohomology.** For open covers:
the map on Čech cohomology induced by a refinement does not depend on the refinement map. -/
theorem cechCohomologyFunctor_map_eq {U V : (FormalCoproduct.{w} C)ᵒᵖ} (φ ψ : U ⟶ V) :
    (cechCohomologyFunctor P n).map φ = (cechCohomologyFunctor P n).map ψ :=
  (cechComplexMapHomotopy P φ.unop ψ.unop).homologyMap_eq n

/-! ### Systems of families ordered by refinement -/

section Diagram

variable {I : Type t} [Preorder I] (c : I → FormalCoproduct.{w} C)
  (hc : ∀ ⦃i j : I⦄, i ≤ j → Nonempty (c j ⟶ c i))

/-- The Čech cohomology of a system of families `c : I → FormalCoproduct C`, as a functor on a
preorder in which `i ≤ j` provides a morphism of families `c j ⟶ c i`, for instance a
refinement of open covers. The transition maps are induced by any such morphism
(`cechCohomologyDiagram_map`). -/
-- Reducible so that the coprojections of its colimit compose, without casts, with the maps
-- `(cechCohomologyFunctor P n).map φ.op` between the objects `(cechCohomologyFunctor P n).obj _`.
@[expose, reducible]
def cechCohomologyDiagram : I ⥤ A where
  obj i := (cechCohomologyFunctor P n).obj (op (c i))
  map f := (cechCohomologyFunctor P n).map (hc f.le).some.op
  map_id i := by
    rw [cechCohomologyFunctor_map_eq P n _ (𝟙 _), CategoryTheory.Functor.map_id]
  map_comp f g := by
    rw [← CategoryTheory.Functor.map_comp]
    exact cechCohomologyFunctor_map_eq P n _ _

/-- The value of `cechCohomologyDiagram` at `i` is the Čech cohomology of the family `c i`. -/
theorem cechCohomologyDiagram_obj (i : I) :
    (cechCohomologyDiagram P n c hc).obj i = (cechCohomologyFunctor P n).obj (op (c i)) := (rfl)

/-- The transition map of `cechCohomologyDiagram` along `i ≤ j` is induced by any morphism of
families `c j ⟶ c i`. -/
theorem cechCohomologyDiagram_map {i j : I} (f : i ⟶ j) (φ : c j ⟶ c i) :
    (cechCohomologyDiagram P n c hc).map f = (cechCohomologyFunctor P n).map φ.op :=
  cechCohomologyFunctor_map_eq P n _ _

variable [HasColimit (cechCohomologyDiagram P n c hc)]

/-- The coprojections of the colimit of `cechCohomologyDiagram` are compatible with the maps
induced by every morphism of families between members of the system. -/
@[reassoc]
theorem cechCohomologyFunctor_map_comp_colimit_ι {i j : I} (φ : c j ⟶ c i) (h : i ≤ j) :
    (cechCohomologyFunctor P n).map φ.op ≫ colimit.ι (cechCohomologyDiagram P n c hc) j =
      colimit.ι (cechCohomologyDiagram P n c hc) i := by
  rw [← cechCohomologyDiagram_map P n c hc (homOfLE h) φ]
  exact colimit.w _ _

variable [IsDirectedOrder I]

/-- For a family `U` refined by some member `c i` of a directed system, the map from the Čech
cohomology of `U` to the colimit over the system: the map induced by a refinement `c i ⟶ U`,
followed by the coprojection at `i`. It does not depend on the choice of `i` and of the
refinement (`toCechCohomologyColimit_eq`). -/
def toCechCohomologyColimit (U : FormalCoproduct.{w} C) (hU : ∃ i, Nonempty (c i ⟶ U)) :
    (cechCohomologyFunctor P n).obj (op U) ⟶ colimit (cechCohomologyDiagram P n c hc) :=
  (cechCohomologyFunctor P n).map hU.choose_spec.some.op ≫
    colimit.ι (cechCohomologyDiagram P n c hc) hU.choose

/-- `toCechCohomologyColimit` may be computed through any member of the system refining the
family, and any refinement map. -/
theorem toCechCohomologyColimit_eq (U : FormalCoproduct.{w} C) (i : I) (φ : c i ⟶ U) :
    toCechCohomologyColimit P n c hc U ⟨i, ⟨φ⟩⟩ =
      (cechCohomologyFunctor P n).map φ.op ≫ colimit.ι (cechCohomologyDiagram P n c hc) i := by
  have hU : ∃ i, Nonempty (c i ⟶ U) := ⟨i, ⟨φ⟩⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge hU.choose i
  -- both composites factor through the coprojection at a common refinement `c k`
  rw [toCechCohomologyColimit, ← cechCohomologyFunctor_map_comp_colimit_ι P n c hc
      (hc hik).some hik, ← cechCohomologyFunctor_map_comp_colimit_ι P n c hc (hc hjk).some hjk,
    ← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp,
    cechCohomologyFunctor_map_eq P n ((hc hik).some ≫ hU.choose_spec.some).op]

/-- On a member of the system, `toCechCohomologyColimit` is the coprojection. -/
@[simp]
theorem toCechCohomologyColimit_self (i : I) (hi : ∃ j, Nonempty (c j ⟶ c i)) :
    toCechCohomologyColimit P n c hc (c i) hi = colimit.ι (cechCohomologyDiagram P n c hc) i := by
  rw [toCechCohomologyColimit_eq P n c hc (c i) i (𝟙 _), op_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- `toCechCohomologyColimit` is natural in morphisms of families. -/
@[reassoc (attr := simp)]
theorem cechCohomologyFunctor_map_comp_toCechCohomologyColimit {U V : FormalCoproduct.{w} C}
    (φ : V ⟶ U) (hV : ∃ i, Nonempty (c i ⟶ V)) :
    (cechCohomologyFunctor P n).map φ.op ≫ toCechCohomologyColimit P n c hc V hV =
      toCechCohomologyColimit P n c hc U (hV.imp fun _ ⟨ψ⟩ ↦ ⟨ψ ≫ φ⟩) := by
  obtain ⟨i, ⟨ψ⟩⟩ := hV
  rw [toCechCohomologyColimit_eq P n c hc V i ψ, toCechCohomologyColimit_eq P n c hc U i (ψ ≫ φ),
    op_comp, CategoryTheory.Functor.map_comp, Category.assoc]

/-! ### Comparison of mutually cofinal systems -/

variable {J : Type t'} [Preorder J] [IsDirectedOrder J] (d : J → FormalCoproduct.{w} C)
  (hd : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (d j ⟶ d i)) [HasColimit (cechCohomologyDiagram P n d hd)]

/-- If every member of the directed system `c` is refined by a member of the directed system
`d`, the map from the colimit over `c` to the colimit over `d` sending the coprojection at `i`
to `toCechCohomologyColimit` of `c i`. -/
def cechCohomologyColimitMap (h : ∀ i, ∃ j, Nonempty (d j ⟶ c i)) :
    colimit (cechCohomologyDiagram P n c hc) ⟶ colimit (cechCohomologyDiagram P n d hd) :=
  colimit.desc _
    { pt := colimit (cechCohomologyDiagram P n d hd)
      ι :=
        { app i := toCechCohomologyColimit P n d hd (c i) (h i)
          naturality i j f := by
            rw [cechCohomologyDiagram_map P n c hc f (hc f.le).some]
            exact (cechCohomologyFunctor_map_comp_toCechCohomologyColimit P n d hd
              (hc f.le).some (h j)).trans (Category.comp_id _).symm } }

omit [IsDirectedOrder I] in
@[reassoc (attr := simp)]
theorem colimit_ι_cechCohomologyColimitMap (h : ∀ i, ∃ j, Nonempty (d j ⟶ c i)) (i : I) :
    colimit.ι _ i ≫ cechCohomologyColimitMap P n c hc d hd h =
      toCechCohomologyColimit P n d hd (c i) (h i) :=
  colimit.ι_desc _ _

/-- The comparison map of colimits is compatible with `toCechCohomologyColimit` for every family
refined by the first system. -/
@[reassoc (attr := simp)]
theorem toCechCohomologyColimit_comp_cechCohomologyColimitMap
    (h : ∀ i, ∃ j, Nonempty (d j ⟶ c i)) (U : FormalCoproduct.{w} C)
    (hU : ∃ i, Nonempty (c i ⟶ U)) :
    toCechCohomologyColimit P n c hc U hU ≫ cechCohomologyColimitMap P n c hc d hd h =
      toCechCohomologyColimit P n d hd U
        (hU.elim fun i ⟨φ⟩ ↦ (h i).imp fun _ ⟨ψ⟩ ↦ ⟨ψ ≫ φ⟩) := by
  obtain ⟨i, ⟨φ⟩⟩ := hU
  rw [toCechCohomologyColimit_eq P n c hc U i φ, Category.assoc,
    colimit_ι_cechCohomologyColimitMap, cechCohomologyFunctor_map_comp_toCechCohomologyColimit]

/-- **Mutually cofinal systems of families have canonically isomorphic Čech cohomology
colimits.** If every member of each of two directed systems of families is refined by a member
of the other, the colimits of their Čech cohomology diagrams are isomorphic, compatibly with
`toCechCohomologyColimit` (`toCechCohomologyColimit_comp_cechCohomologyColimitMap`). -/
def cechCohomologyColimitIso (h : ∀ i, ∃ j, Nonempty (d j ⟶ c i))
    (h' : ∀ j, ∃ i, Nonempty (c i ⟶ d j)) :
    colimit (cechCohomologyDiagram P n c hc) ≅ colimit (cechCohomologyDiagram P n d hd) where
  hom := cechCohomologyColimitMap P n c hc d hd h
  inv := cechCohomologyColimitMap P n d hd c hc h'
  hom_inv_id := colimit.hom_ext fun i ↦ by simp
  inv_hom_id := colimit.hom_ext fun j ↦ by simp

@[simp]
theorem cechCohomologyColimitIso_hom (h : ∀ i, ∃ j, Nonempty (d j ⟶ c i))
    (h' : ∀ j, ∃ i, Nonempty (c i ⟶ d j)) :
    (cechCohomologyColimitIso P n c hc d hd h h').hom = cechCohomologyColimitMap P n c hc d hd h :=
  (rfl)

@[simp]
theorem cechCohomologyColimitIso_inv (h : ∀ i, ∃ j, Nonempty (d j ⟶ c i))
    (h' : ∀ j, ∃ i, Nonempty (c i ⟶ d j)) :
    (cechCohomologyColimitIso P n c hc d hd h h').inv = cechCohomologyColimitMap P n d hd c hc h' :=
  (rfl)

end Diagram

end TauCeti.CategoryTheory
