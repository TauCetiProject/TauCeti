/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Restriction of complexes and the connecting maps of the homology sequence

Let `e : c.Embedding c'` be an embedding of complex shapes and `S` a short exact sequence of
homological complexes of shape `c'` in an abelian category. Restricting `S` along `e` gives a short
exact sequence of complexes of shape `c` (`CategoryTheory.ShortComplex.ShortExact.restriction`),
and the connecting maps of the two homology sequences agree through the comparison isomorphisms of
`Mathlib.Algebra.Homology.Embedding.RestrictionHomology`.

The comparison of the homology of `K.restriction e` in degree `j` with that of `K` in degree
`e.f j` needs the neighbours of `j` to be sent to the neighbours of `e.f j`. At the target of the
connecting map only the predecessor matters if the homology is read in the opcycles, through the
monomorphism `homologyι`. This is the form needed at the end of a truncation, where the successor
of `e.f j` is not in the image of `e`
(`CategoryTheory.ShortComplex.ShortExact.restriction_δ_comp_homologyι`). When both neighbours are
in the image, the connecting maps commute with the comparison isomorphisms on homology
(`CategoryTheory.ShortComplex.ShortExact.restriction_δ_comp_restrictionHomologyIso_hom`).

The proof compares the two connecting maps through the description of
`CategoryTheory.ShortComplex.ShortExact.δ_eq`, evaluated on the pullback of the projection of the
middle complex along the cycles of the third one: the two short exact sequences have the same
objects and maps in the degrees concerned.
-/

public section

open CategoryTheory Limits HomologicalComplex

variable {C ι ι' : Type*} [Category* C] [Abelian C] {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace CategoryTheory.ShortComplex.ShortExact

variable {S : ShortComplex (HomologicalComplex C c')} (hS : S.ShortExact)
  (e : c.Embedding c') [e.IsRelIff]

include hS in
/-- The restriction of a short exact sequence of complexes along an embedding of complex shapes
is short exact. -/
theorem restriction : (S.map (e.restrictionFunctor C)).ShortExact := by
  rw [shortExact_iff_degreewise_shortExact] at hS ⊢
  exact fun i ↦ hS (e.f i)

/-- **Restriction commutes with the connecting map, read in the opcycles of the target.** For
`c.Rel i j`, the connecting map `H_i ⟶ H_j` of the restriction of `S`, followed by the inclusion of
homology into the opcycles of the restricted first complex, agrees with the connecting map
`H_{i'} ⟶ H_{j'}` of `S` for `i' = e.f i` and `j' = e.f j`, followed by the inclusion into
opcycles, through the comparison isomorphisms on the cycles of the third complex and on the
opcycles of the first complex. -/
theorem homologyπ_restriction_δ_comp_homologyι (i j : ι) (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hij' : c'.Rel i' j') :
    (S.X₃.restriction e).homologyπ i ≫ (hS.restriction e).δ i j hij ≫
        (S.X₁.restriction e).homologyι j ≫
          (S.X₁.restrictionOpcyclesIso e i j (c.prev_eq' hij) hi' hj' (c'.prev_eq' hij')).hom =
      (S.X₃.restrictionCyclesIso e i j (c.next_eq' hij) hi' hj' (c'.next_eq' hij')).hom ≫
        S.X₃.homologyπ i' ≫ hS.δ i' j' hij' ≫ S.X₁.homologyι j' := by
  subst hi' hj'
  have hi := (shortExact_iff_degreewise_shortExact S).1 hS (e.f i)
  have hj := (shortExact_iff_degreewise_shortExact S).1 hS (e.f j)
  have : Epi (S.g.f (e.f i)) := hi.epi_g
  have := hj.mono_f
  -- After pulling back along the projection of the middle complex, a cycle `x₃` of the third
  -- complex lifts to the middle complex, and the boundary of the lift comes from the first complex.
  obtain ⟨P, y, x₂, _, hx₂⟩ : ∃ (P : C) (y : P ⟶ S.X₃.cycles (e.f i))
      (x₂ : P ⟶ S.X₂.X (e.f i)), Epi y ∧ x₂ ≫ S.g.f (e.f i) = y ≫ S.X₃.iCycles (e.f i) :=
    ⟨_, pullback.snd _ _, pullback.fst _ _, inferInstance, pullback.condition⟩
  have hx₃ : (y ≫ S.X₃.iCycles (e.f i)) ≫ S.X₃.d (e.f i) (e.f j) = 0 := by
    rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : P ⟶ S.X₁.X (e.f j),
      x₁ ≫ S.f.f (e.f j) = x₂ ≫ S.X₂.d (e.f i) (e.f j) :=
    ⟨hj.exact.lift (x₂ ≫ S.X₂.d (e.f i) (e.f j)) (by
      simp only [ShortComplex.map_X₂, eval_obj, ShortComplex.map_X₃, ShortComplex.map_g, eval_map,
        Category.assoc, ← S.g.comm, reassoc_of% hx₂, HomologicalComplex.iCycles_d, comp_zero]),
      hj.exact.lift_f _ _⟩
  have hδ := hS.δ_eq (e.f i) (e.f j) (e.rel hij) _ hx₃ x₂ hx₂ x₁ hx₁ _ rfl
  -- The same morphisms, read in the restricted complexes. The associativity steps are applied as
  -- terms: the restricted short complex has objects only definitionally equal to the restricted
  -- complexes.
  have hδ' : (S.X₃.restriction e).liftCycles (y ≫ S.X₃.iCycles (e.f i)) j (c.next_eq' hij) hx₃ ≫
      (S.X₃.restriction e).homologyπ i ≫ (hS.restriction e).δ i j hij ≫
        (S.X₁.restriction e).homologyι j ≫ (S.X₁.restrictionOpcyclesIso e i j (c.prev_eq' hij) rfl
          rfl (c'.prev_eq' (e.rel hij))).hom =
      (S.X₁.restriction e).liftCycles x₁ (c.next j) rfl _ ≫ (S.X₁.restriction e).homologyπ j ≫
        (S.X₁.restriction e).homologyι j ≫ (S.X₁.restrictionOpcyclesIso e i j (c.prev_eq' hij) rfl
          rfl (c'.prev_eq' (e.rel hij))).hom :=
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).trans
      ((((hS.restriction e).δ_eq i j hij _ hx₃ x₂ hx₂ x₁ hx₁ _ rfl) =≫ _).trans
        (Category.assoc _ _ _))
  -- Both sides send the cycle `y` to the class of `x₁` in the opcycles of the first complex.
  -- The comparison isomorphisms of the restricted objects are identities.
  have hy : y ≫ (S.X₃.restrictionCyclesIso e i j (c.next_eq' hij) rfl rfl
      (c'.next_eq' (e.rel hij))).inv =
      (S.X₃.restriction e).liftCycles (y ≫ S.X₃.iCycles (e.f i)) j (c.next_eq' hij) hx₃ := by
    rw [← cancel_mono ((S.X₃.restriction e).iCycles i), Category.assoc,
      restrictionCyclesIso_inv_iCycles]
    exact (congrArg (y ≫ ·) (Category.comp_id _)).trans
      (HomologicalComplex.liftCycles_i _ _ _ _ _).symm
  have hy' : y = S.X₃.liftCycles (y ≫ S.X₃.iCycles (e.f i)) (e.f j)
      (c'.next_eq' (e.rel hij)) hx₃ := by
    rw [← cancel_mono (S.X₃.iCycles (e.f i)), HomologicalComplex.liftCycles_i]
  rw [← Iso.inv_comp_eq]
  refine (cancel_epi y).1 ?_
  rw [reassoc_of% hy, hδ', HomologicalComplex.homology_π_ι_assoc,
    pOpcycles_restrictionOpcyclesIso_hom]
  refine (HomologicalComplex.liftCycles_i_assoc ..).trans ?_
  rw [hy', reassoc_of% hδ, HomologicalComplex.homology_π_ι, HomologicalComplex.liftCycles_i_assoc]
  exact congrArg (x₁ ≫ ·) (Category.id_comp _)

/-- **Restriction commutes with the connecting map, read in the opcycles of the target.** When the
predecessor of `i` is sent to the predecessor of `i' = e.f i`, the homology of the third complex
in the source degree is compared through `restrictionHomologyIso`, and the connecting map of the
restriction of `S`, followed by the inclusion into the opcycles of the restricted first complex, is
the connecting map of `S` followed by the inclusion into its opcycles. -/
@[reassoc]
theorem restriction_δ_comp_homologyι (i j : ι) (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hij' : c'.Rel i' j') (h : ι) {h' : ι'}
    (hh : c.prev i = h) (hh₁ : e.f h = h') (hh' : c'.prev i' = h') :
    (hS.restriction e).δ i j hij ≫ (S.X₁.restriction e).homologyι j ≫
        (S.X₁.restrictionOpcyclesIso e i j (c.prev_eq' hij) hi' hj' (c'.prev_eq' hij')).hom =
      (S.X₃.restrictionHomologyIso e h i j hh (c.next_eq' hij) hh₁ hi' hj' hh'
          (c'.next_eq' hij')).hom ≫ hS.δ i' j' hij' ≫ S.X₁.homologyι j' := by
  refine (cancel_epi ((S.X₃.restriction e).homologyπ i)).1 ?_
  rw [homologyπ_restrictionHomologyIso_hom_assoc]
  exact homologyπ_restriction_δ_comp_homologyι hS e i j hij hi' hj' hij'

/-- **Restriction commutes with the connecting map.** When the neighbours of `i` and `j` are sent
to the neighbours of `i' = e.f i` and `j' = e.f j`, the connecting map `H_i ⟶ H_j` of the
restriction of `S` is the connecting map `H_{i'} ⟶ H_{j'}` of `S`, through the comparison
isomorphisms of homology. -/
@[reassoc]
theorem restriction_δ_comp_restrictionHomologyIso_hom (i j : ι) (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hij' : c'.Rel i' j') (h k : ι) {h' k' : ι'}
    (hh : c.prev i = h) (hk : c.next j = k) (hh₁ : e.f h = h') (hk₁ : e.f k = k')
    (hh' : c'.prev i' = h') (hk' : c'.next j' = k') :
    (hS.restriction e).δ i j hij ≫
        (S.X₁.restrictionHomologyIso e i j k (c.prev_eq' hij) hk hi' hj' hk₁ (c'.prev_eq' hij')
          hk').hom =
      (S.X₃.restrictionHomologyIso e h i j hh (c.next_eq' hij) hh₁ hi' hj' hh'
          (c'.next_eq' hij')).hom ≫ hS.δ i' j' hij' := by
  refine (cancel_mono (S.X₁.homologyι j')).1 ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (restrictionHomologyIso_hom_homologyι ..)).trans
      ((restriction_δ_comp_homologyι hS e i j hij hi' hj' hij' h hh hh₁ hh').trans
        (Category.assoc _ _ _).symm))

end CategoryTheory.ShortComplex.ShortExact
