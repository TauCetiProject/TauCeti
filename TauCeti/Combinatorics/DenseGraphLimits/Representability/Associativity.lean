/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Representability.LabeledGraph
public import TauCeti.Combinatorics.SimpleGraph.Maps

/-!
# Associativity of labeled-graph gluing

The product of labeled graphs identifies equally numbered labels and retains all other
vertices. Its two three-factor parenthesizations are isomorphic by the equivalence that fixes
each vertex of each factor. The isomorphism preserves the labels, so it can be used inside
further gluings. This supplies associativity for the gluing algebra used by connection matrices.

## References

* L. Lovász and B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), Section 2.
-/

public section

namespace TauCeti.DenseGraphLimits

namespace LabeledGraph

variable {k : ℕ}

/-- The unlabeled vertices of a gluing are exactly the disjoint union of the unlabeled vertices
of its two factors. -/
private noncomputable def glueUnlabeledEquiv (A B : LabeledGraph k) :
    A.Unlabeled ⊕ B.Unlabeled ≃ (A.glue B).Unlabeled := by
  let f : A.Unlabeled ⊕ B.Unlabeled → (A.glue B).Unlabeled := fun s =>
    ⟨A.glueEquiv B (Sum.inr s), by
      intro i h
      have hi := A.glueEquiv_inl B i
      have heq := (A.glueEquiv B).injective (hi.trans h)
      cases heq⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro s t h
    exact Sum.inr_injective ((A.glueEquiv B).injective (congrArg Subtype.val h))
  · intro x
    obtain ⟨i | s, hs⟩ := (A.glueEquiv B).surjective x.1
    · exact False.elim (x.2 i ((A.glueEquiv_inl B i).symm.trans hs))
    · exact ⟨s, Subtype.ext hs⟩

@[simp]
private theorem glueUnlabeledEquiv_inl (A B : LabeledGraph k) (a : A.Unlabeled) :
    ((A.glueUnlabeledEquiv B (Sum.inl a) : (A.glue B).Unlabeled) : Fin (A.glue B).n) =
      A.glueInl B a := by
  exact glueEquiv_inr_inl A B a

@[simp]
private theorem glueUnlabeledEquiv_inr (A B : LabeledGraph k) (b : B.Unlabeled) :
    ((A.glueUnlabeledEquiv B (Sum.inr b) : (A.glue B).Unlabeled) : Fin (A.glue B).n) =
      A.glueInr B b := by
  exact glueEquiv_inr_inr A B b

/-- Canonical three-factor coordinates for the left-associated gluing. -/
private noncomputable def glueTripleLeftEquiv (A B C : LabeledGraph k) :
    Fin k ⊕ (A.Unlabeled ⊕ (B.Unlabeled ⊕ C.Unlabeled)) ≃
      Fin ((A.glue B).glue C).n :=
  ((Equiv.refl (Fin k)).sumCongr
    (((Equiv.sumAssoc A.Unlabeled B.Unlabeled C.Unlabeled).symm).trans
      ((A.glueUnlabeledEquiv B).sumCongr (Equiv.refl C.Unlabeled)))).trans
    ((A.glue B).glueEquiv C)

/-- Canonical three-factor coordinates for the right-associated gluing. -/
private noncomputable def glueTripleRightEquiv (A B C : LabeledGraph k) :
    Fin k ⊕ (A.Unlabeled ⊕ (B.Unlabeled ⊕ C.Unlabeled)) ≃
      Fin (A.glue (B.glue C)).n :=
  ((Equiv.refl (Fin k)).sumCongr
    ((Equiv.refl A.Unlabeled).sumCongr (B.glueUnlabeledEquiv C))).trans
    (A.glueEquiv (B.glue C))

@[simp]
private theorem glueTripleLeftEquiv_inl (A B C : LabeledGraph k) (i : Fin k) :
    A.glueTripleLeftEquiv B C (Sum.inl i) = ((A.glue B).glue C).label i :=
  (A.glue B).glueEquiv_inl C i

@[simp]
private theorem glueTripleRightEquiv_inl (A B C : LabeledGraph k) (i : Fin k) :
    A.glueTripleRightEquiv B C (Sum.inl i) = (A.glue (B.glue C)).label i :=
  A.glueEquiv_inl (B.glue C) i

@[simp]
private theorem glueTripleLeftEquiv_A (A B C : LabeledGraph k) (a : A.Unlabeled) :
    A.glueTripleLeftEquiv B C (Sum.inr (Sum.inl a)) =
      (A.glue B).glueInl C (A.glueInl B a) := by
  simp [glueTripleLeftEquiv]

@[simp]
private theorem glueTripleLeftEquiv_B (A B C : LabeledGraph k) (b : B.Unlabeled) :
    A.glueTripleLeftEquiv B C (Sum.inr (Sum.inr (Sum.inl b))) =
      (A.glue B).glueInl C (A.glueInr B b) := by
  simp [glueTripleLeftEquiv]

@[simp]
private theorem glueTripleLeftEquiv_C (A B C : LabeledGraph k) (c : C.Unlabeled) :
    A.glueTripleLeftEquiv B C (Sum.inr (Sum.inr (Sum.inr c))) =
      (A.glue B).glueInr C c := by
  simp [glueTripleLeftEquiv]

@[simp]
private theorem glueTripleRightEquiv_A (A B C : LabeledGraph k) (a : A.Unlabeled) :
    A.glueTripleRightEquiv B C (Sum.inr (Sum.inl a)) =
      A.glueInl (B.glue C) a := by
  simp [glueTripleRightEquiv]

@[simp]
private theorem glueTripleRightEquiv_B (A B C : LabeledGraph k) (b : B.Unlabeled) :
    A.glueTripleRightEquiv B C (Sum.inr (Sum.inr (Sum.inl b))) =
      A.glueInr (B.glue C) (B.glueInl C b) := by
  simp [glueTripleRightEquiv]

@[simp]
private theorem glueTripleRightEquiv_C (A B C : LabeledGraph k) (c : C.Unlabeled) :
    A.glueTripleRightEquiv B C (Sum.inr (Sum.inr (Sum.inr c))) =
      A.glueInr (B.glue C) (B.glueInr C c) := by
  simp [glueTripleRightEquiv]

/-- Reassociate the vertex coordinates of a three-factor gluing. -/
private noncomputable def glueAssocEquiv (A B C : LabeledGraph k) :
    Fin ((A.glue B).glue C).n ≃ Fin (A.glue (B.glue C)).n :=
  (A.glueTripleLeftEquiv B C).symm.trans (A.glueTripleRightEquiv B C)

@[simp]
private theorem glueAssocEquiv_label (A B C : LabeledGraph k) (i : Fin k) :
    A.glueAssocEquiv B C (((A.glue B).glue C).label i) =
      (A.glue (B.glue C)).label i := by
  rw [← glueTripleLeftEquiv_inl A B C i]
  simp only [glueAssocEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    glueTripleRightEquiv_inl]

private theorem glueAssocEquiv_A (A B C : LabeledGraph k) (a : Fin A.n) :
    A.glueAssocEquiv B C ((A.glue B).glueInl C (A.glueInl B a)) =
      A.glueInl (B.glue C) a := by
  obtain ⟨i | u, hu⟩ := A.labelSumUnlabeledEquiv.surjective a
  · rw [← hu, labelSumUnlabeledEquiv_inl]
    have h₁ : (A.glue B).label i = A.glueInl B (A.label i) :=
      congrFun (glueInl_label A B) i
    have h₂ : ((A.glue B).glue C).label i =
        (A.glue B).glueInl C ((A.glue B).label i) :=
      congrFun (glueInl_label (A.glue B) C) i
    have h₃ : (A.glue (B.glue C)).label i = A.glueInl (B.glue C) (A.label i) :=
      congrFun (glueInl_label A (B.glue C)) i
    rw [← h₁, ← h₂, ← h₃]
    exact glueAssocEquiv_label A B C i
  · rw [← hu, labelSumUnlabeledEquiv_inr]
    rw [← glueTripleLeftEquiv_A A B C u]
    simp only [glueAssocEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
      glueTripleRightEquiv_A]

private theorem glueAssocEquiv_B (A B C : LabeledGraph k) (b : Fin B.n) :
    A.glueAssocEquiv B C ((A.glue B).glueInl C (A.glueInr B b)) =
      A.glueInr (B.glue C) (B.glueInl C b) := by
  obtain ⟨i | u, hu⟩ := B.labelSumUnlabeledEquiv.surjective b
  · rw [← hu, labelSumUnlabeledEquiv_inl]
    have h₁ : (A.glue B).label i = A.glueInr B (B.label i) :=
      congrFun (glueInr_label A B) i
    have h₂ : ((A.glue B).glue C).label i =
        (A.glue B).glueInl C ((A.glue B).label i) :=
      congrFun (glueInl_label (A.glue B) C) i
    have h₃ : (B.glue C).label i = B.glueInl C (B.label i) :=
      congrFun (glueInl_label B C) i
    have h₄ : (A.glue (B.glue C)).label i =
        A.glueInr (B.glue C) ((B.glue C).label i) :=
      congrFun (glueInr_label A (B.glue C)) i
    rw [← h₁, ← h₂, ← h₃, ← h₄]
    exact glueAssocEquiv_label A B C i
  · rw [← hu, labelSumUnlabeledEquiv_inr]
    rw [← glueTripleLeftEquiv_B A B C u]
    simp only [glueAssocEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
      glueTripleRightEquiv_B]

private theorem glueAssocEquiv_C (A B C : LabeledGraph k) (c : Fin C.n) :
    A.glueAssocEquiv B C ((A.glue B).glueInr C c) =
      A.glueInr (B.glue C) (B.glueInr C c) := by
  obtain ⟨i | u, hu⟩ := C.labelSumUnlabeledEquiv.surjective c
  · rw [← hu, labelSumUnlabeledEquiv_inl]
    have h₁ : ((A.glue B).glue C).label i = (A.glue B).glueInr C (C.label i) :=
      congrFun (glueInr_label (A.glue B) C) i
    have h₂ : (B.glue C).label i = B.glueInr C (C.label i) :=
      congrFun (glueInr_label B C) i
    have h₃ : (A.glue (B.glue C)).label i =
        A.glueInr (B.glue C) ((B.glue C).label i) :=
      congrFun (glueInr_label A (B.glue C)) i
    rw [← h₁, ← h₂, ← h₃]
    exact glueAssocEquiv_label A B C i
  · rw [← hu, labelSumUnlabeledEquiv_inr]
    rw [← glueTripleLeftEquiv_C A B C u]
    simp only [glueAssocEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
      glueTripleRightEquiv_C]

/-- Reassociation sends the graph of the left parenthesization to the graph of the right
parenthesization; each edge comes from one of the three factors. -/
private theorem glue_graph_map_glueAssocEquiv (A B C : LabeledGraph k) :
    ((A.glue B).glue C).graph.map (A.glueAssocEquiv B C) =
      (A.glue (B.glue C)).graph := by
  let leftA : Fin A.n → Fin ((A.glue B).glue C).n :=
    (A.glue B).glueInl C ∘ A.glueInl B
  let leftB : Fin B.n → Fin ((A.glue B).glue C).n :=
    (A.glue B).glueInl C ∘ A.glueInr B
  let leftC : Fin C.n → Fin ((A.glue B).glue C).n := (A.glue B).glueInr C
  let rightA : Fin A.n → Fin (A.glue (B.glue C)).n := A.glueInl (B.glue C)
  let rightB : Fin B.n → Fin (A.glue (B.glue C)).n :=
    A.glueInr (B.glue C) ∘ B.glueInl C
  let rightC : Fin C.n → Fin (A.glue (B.glue C)).n :=
    A.glueInr (B.glue C) ∘ B.glueInr C
  have hA : (A.glueAssocEquiv B C) ∘ leftA = rightA :=
    funext (A.glueAssocEquiv_A B C)
  have hB : (A.glueAssocEquiv B C) ∘ leftB = rightB :=
    funext (A.glueAssocEquiv_B B C)
  have hC : (A.glueAssocEquiv B C) ∘ leftC = rightC :=
    funext (A.glueAssocEquiv_C B C)
  have hleft : ((A.glue B).glue C).graph =
      (A.graph.map leftA ⊔ B.graph.map leftB) ⊔ C.graph.map leftC := by
    simp only [glue_graph, SimpleGraph.map_sup, SimpleGraph.map_map]
    rfl
  have hright : (A.glue (B.glue C)).graph =
      A.graph.map rightA ⊔ (B.graph.map rightB ⊔ C.graph.map rightC) := by
    simp only [glue_graph, SimpleGraph.map_sup, SimpleGraph.map_map]
    rfl
  rw [hleft, hright, SimpleGraph.map_sup, SimpleGraph.map_sup]
  simp only [SimpleGraph.map_map, hA, hB, hC]
  exact sup_assoc (A.graph.map rightA) (B.graph.map rightB) (C.graph.map rightC)

/-- Gluing three labeled graphs is associative up to a label-preserving graph isomorphism. -/
noncomputable def glueAssocIso (A B C : LabeledGraph k) :
    ((A.glue B).glue C).graph ≃g (A.glue (B.glue C)).graph where
  toEquiv := A.glueAssocEquiv B C
  map_rel_iff' {u v} := by
    rw [← A.glue_graph_map_glueAssocEquiv B C]
    exact SimpleGraph.map_adj_apply (f := (A.glueAssocEquiv B C).toEmbedding)

/-- The associativity isomorphism fixes the label with each index. -/
@[simp]
theorem glueAssocIso_label (A B C : LabeledGraph k) (i : Fin k) :
    A.glueAssocIso B C (((A.glue B).glue C).label i) =
      (A.glue (B.glue C)).label i :=
  A.glueAssocEquiv_label B C i

/-- Reassociation fixes vertices coming from the first factor. -/
@[simp]
theorem glueAssocIso_inl_inl (A B C : LabeledGraph k) (a : Fin A.n) :
    A.glueAssocIso B C ((A.glue B).glueInl C (A.glueInl B a)) =
      A.glueInl (B.glue C) a :=
  A.glueAssocEquiv_A B C a

/-- Reassociation fixes vertices coming from the middle factor. -/
@[simp]
theorem glueAssocIso_inl_inr (A B C : LabeledGraph k) (b : Fin B.n) :
    A.glueAssocIso B C ((A.glue B).glueInl C (A.glueInr B b)) =
      A.glueInr (B.glue C) (B.glueInl C b) :=
  A.glueAssocEquiv_B B C b

/-- Reassociation fixes vertices coming from the final factor. -/
@[simp]
theorem glueAssocIso_inr (A B C : LabeledGraph k) (c : Fin C.n) :
    A.glueAssocIso B C ((A.glue B).glueInr C c) =
      A.glueInr (B.glue C) (B.glueInr C c) :=
  A.glueAssocEquiv_C B C c

end LabeledGraph

end TauCeti.DenseGraphLimits
