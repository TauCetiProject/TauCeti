/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom

/-!
# CoCartesian sections

The section category used in the coCartesian dual of Lurie's *Higher Topos Theory*,
Corollary 3.3.3.2, is the full subcategory of `SSet.coherentSections p` spanned by sections
carrying base edges to `SSet.Edge.IsCoCartesian` edges over `p`.

## Main declarations

* `SSet.coCartesianSections` constructs that subcategory using `SSet.fullEnhancedSubcategory`.
* `SSet.mem_coCartesianSections_obj_iff` tests a family over the base at each parameter vertex,
  using `SSet.ihomOver.objEquiv` and Mathlib's `SSet.stdSimplex.map`.
* `SSet.coCartesianSections.quasicategory` gives the quasicategory for an inner fibration, and
  `SSet.coCartesianSections.isTerminalId` identifies the section category of the identity as
  terminal.

## References

* J. Lurie, *Higher Topos Theory*, Corollary 3.3.3.2 (coCartesian dual).
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial

namespace SSet

universe u

variable {E B : SSet.{u}} (p : E ⟶ B)

/-- The full subcomplex of sections of `p` which send all edges of `B` to edges
coCartesian over `p`, as in the coCartesian dual of *Higher Topos Theory*, Corollary 3.3.3.2. -/
def coCartesianSections : (coherentSections p : SSet).Subcomplex :=
  (coherentSections p : SSet).fullEnhancedSubcategory fun s ↦
    ∀ ⦃x y : B _⦋0⦌⦄ (e : Edge x y), (e.map (ihomOver.obj₀Equiv s).val).IsCoCartesian p

/-- The defining full-subcategory presentation, for applying the full-subcategory API
without unfolding the section complex. -/
lemma coCartesianSections_eq_fullEnhancedSubcategory :
    coCartesianSections p = (coherentSections p : SSet).fullEnhancedSubcategory
      (fun s ↦ ∀ ⦃x y : B _⦋0⦌⦄ (e : Edge x y),
        (e.map (ihomOver.obj₀Equiv s).val).IsCoCartesian p) :=
  (rfl)

variable {p} in
/-- A vertex of the section complex belongs to the coCartesian section complex exactly when
the section it represents sends each base edge to a coCartesian edge. -/
@[simp]
lemma mem_coCartesianSections_obj_zero_iff {s : (coherentSections p : SSet) _⦋0⦌} :
    s ∈ (coCartesianSections p).obj (op ⦋0⦌) ↔
      ∀ ⦃x y : B _⦋0⦌⦄ (e : Edge x y), (e.map (ihomOver.obj₀Equiv s).val).IsCoCartesian p := by
  rw [coCartesianSections_eq_fullEnhancedSubcategory,
    mem_fullEnhancedSubcategory_obj_zero_iff]

variable {p} in
/-- A simplex of the section complex is coCartesian exactly when each of its restrictions
along a vertex of the parameter simplex sends base edges to coCartesian edges. -/
@[simp low]
lemma mem_coCartesianSections_obj_iff {n : ℕ} {s : (coherentSections p : SSet) _⦋n⦌} :
    s ∈ (coCartesianSections p).obj (op ⦋n⦌) ↔
      ∀ (i : Fin (n + 1)) ⦃x y : B _⦋0⦌⦄ (e : Edge x y),
        (e.map ((fstStdSimplexZeroIso B).inv ≫
          (B ◁ stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) ≫
          (ihomOver.objEquiv s).val)).IsCoCartesian p := by
  rw [coCartesianSections_eq_fullEnhancedSubcategory,
    mem_fullEnhancedSubcategory_obj_iff_forall_fin]
  exact forall_congr' fun i ↦ by rw [ihomOver.obj₀Equiv_map]

/-- For an isomorphism, every section is coCartesian. -/
@[simp]
lemma coCartesianSections_eq_top_of_isIso [IsIso p] : coCartesianSections p = ⊤ := by
  rw [coCartesianSections_eq_fullEnhancedSubcategory]
  refine top_unique ((le_fullEnhancedSubcategory_iff _ _).2 fun s _ _ _ e ↦ ?_)
  exact Edge.isCoCartesian_of_isIso _ p

namespace coCartesianSections

/-- The vertices of the coCartesian section complex are the coCartesian sections of `p`. -/
def obj₀Equiv :
    (coCartesianSections p).obj (op ⦋0⦌) ≃
      {s : {g : B ⟶ E // g ≫ p = 𝟙 B} //
        ∀ ⦃x y : B _⦋0⦌⦄ (e : Edge x y), (e.map s.val).IsCoCartesian p} :=
  (fullEnhancedSubcategory.verticesEquiv _).trans
    ((ihomOver.obj₀Equiv (p := p) (f := 𝟙 B)).subtypeEquiv (fun _ ↦ Iff.rfl))

/-- The projection of the vertex equivalence is the underlying coherent section, a formula
for using the equivalence without unfolding it. -/
@[simp]
lemma obj₀Equiv_apply_val (s : (coCartesianSections p).obj (op ⦋0⦌)) :
    (obj₀Equiv p s).val = ihomOver.obj₀Equiv s.val :=
  congrArg (ihomOver.obj₀Equiv (p := p) (f := 𝟙 B))
    (fullEnhancedSubcategory.verticesEquiv_apply_coe _ _)

/-- The vertex represented by a coCartesian section projects to its coherent section vertex. -/
@[simp]
lemma obj₀Equiv_symm_apply_val
    (s : {s : {g : B ⟶ E // g ≫ p = 𝟙 B} //
      ∀ ⦃x y : B _⦋0⦌⦄ (e : Edge x y), (e.map s.val).IsCoCartesian p}) :
    ((obj₀Equiv p).symm s).val = ihomOver.obj₀Equiv.symm s.val :=
  fullEnhancedSubcategory.verticesEquiv_symm_apply_coe _ _

/-- If `p` is an inner fibration, its coCartesian sections form a quasicategory. -/
instance quasicategory [InnerFibration p] : Quasicategory (coCartesianSections p : SSet) :=
  inferInstanceAs (Quasicategory ((coherentSections p : SSet).fullEnhancedSubcategory _ : SSet))

/-- The quasicategory of coCartesian sections of the identity is terminal. -/
def isTerminalId (B : SSet.{u}) : IsTerminal (coCartesianSections (𝟙 B) : SSet) :=
  (ihomOver.isTerminalId (𝟙 B)).ofIso ((Subcomplex.topIso (coherentSections (𝟙 B) : SSet)).symm ≪≫
    eqToIso (by rw [coCartesianSections_eq_top_of_isIso]))

/-- The unique map into the coCartesian sections of the identity projects to the unique
map into the coherent sections of the identity. -/
@[reassoc (attr := simp)]
lemma isTerminalId_from_ι (B Z : SSet.{u}) :
    (isTerminalId B).from Z ≫ (coCartesianSections (𝟙 B)).ι =
      (ihomOver.isTerminalId (𝟙 B)).from Z :=
  (ihomOver.isTerminalId (𝟙 B)).hom_ext _ _

end coCartesianSections

end SSet
