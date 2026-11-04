/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.Topology.Order.Sublevel

/-!
# Singular homology of a sublevel pair covering the whole space

Let `f : X → β` be any function to a preorder. If `a < f ≤ b` everywhere, the sublevel pair
`TauCeti.sublevelPair f : ({f ≤ b}, {f ≤ a})` is `(X, ∅)`, so its relative singular homology is
the singular homology of `X` (`TauCeti.nonempty_singularHomology_iso_sublevelPair`). No continuity
or regularity of `f` is needed. Since the subspace is empty, the comparison is the quotient map
`TopPair.singularHomologyπ`, an isomorphism by `TauCeti.AlgebraicTopology.Singular.Empty`.
-/

public section

noncomputable section

open CategoryTheory Limits Set

universe u v w

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {β : Type*} [Preorder β] {f : X → β} {a b : β}
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]

/-- **The sublevel pair of a band covering `X`.** If `a < f ≤ b` everywhere, the relative singular
homology of `({f ≤ b}, {f ≤ a}) = (X, ∅)` is the singular homology of `X`. -/
theorem nonempty_singularHomology_iso_sublevelPair (hab : a ≤ b) (ha : ∀ x, a < f x)
    (hb : ∀ x, f x ≤ b) (R : C) (n : ℕ) :
    Nonempty (((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
      (sublevelPair f hab).singularHomology R n) := by
  have : IsEmpty (sublevelPair f hab).snd := ⟨fun (x : {x : X | f x ≤ a}) ↦ (ha x).not_ge x.2⟩
  have hπ : IsIso ((sublevelPair f hab).singularHomologyπ R n) := inferInstance
  exact ⟨((AlgebraicTopology.singularHomologyFunctor C n).obj R).mapIso
    (TopCat.isoOfHomeo ((Homeomorph.setCongr (eq_univ_of_forall hb)).trans
      (Homeomorph.Set.univ X))).symm ≪≫ @asIso _ _ _ _ _ hπ⟩

end TauCeti
