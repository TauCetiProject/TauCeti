/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Gorenstein-projective objects have no higher extensions by projectives

Let `C` be an abelian category and `G` a Gorenstein-projective object of `C`. Then
`Ext^{n+1}(G, Q) = 0` for every projective object `Q` of `C`.

A complete resolution `P` of `G` is acyclic, so its cycles fit into short exact sequences
`0 ⟶ Zⁱ ⟶ Pⁱ ⟶ Zⁱ⁺¹ ⟶ 0` (`HomologicalComplex.cyclesShortComplex_shortExact`). Since the middle
terms are projective, the long exact sequence of `Ext(-, Q)` shifts dimension:
`Ext^{n+1}(Zⁱ⁺¹, Q)` is a quotient of `Ext^n(Zⁱ, Q)`. In degree `1`, the obstruction is a
morphism `Zⁱ ⟶ Q` which does not extend to `Pⁱ`, and every such morphism extends because `P` is
totally acyclic.

## Main results

* `CochainComplex.IsTotallyAcyclicProjective.exists_comp_iCycles_eq`: a morphism from the cycles of
  a totally acyclic complex of projectives to a projective object extends to the term.
* `CategoryTheory.isGorensteinProjective.ext_eq_zero`: `Ext^{n+1}(G, Q) = 0` for `G`
  Gorenstein-projective and `Q` projective.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace IsTotallyAcyclicProjective

variable {P : CochainComplex C ℤ} (hP : P.IsTotallyAcyclicProjective)
include hP

/-- **Morphisms from cycles to projectives extend**: a morphism from the cycles of a totally
acyclic complex of projectives to a projective object extends to the term containing them. -/
lemma exists_comp_iCycles_eq (n : ℤ) {Q : C} [Projective Q] (φ : P.cycles n ⟶ Q) :
    ∃ g : P.X n ⟶ Q, P.iCycles n ≫ g = φ := by
  have := HomologicalComplex.epi_toCycles_of_exactAt (hP.acyclic n) (i := n - 1) (by simp)
  obtain ⟨g, hg⟩ := (isTotallyAcyclicProjective_iff_factor.1 hP).2.2 (n - 1) n (by lia) Q
    (P.toCycles (n - 1) n ≫ φ) (by rw [P.d_toCycles_assoc, zero_comp])
  refine ⟨g, ?_⟩
  rw [← cancel_epi (P.toCycles (n - 1) n), P.toCycles_i_assoc, hg]

variable [HasExt.{w} C]

/-- The cycles of a totally acyclic complex of projectives have no higher extensions by
projective objects. -/
lemma ext_cycles_eq_zero (Q : C) [Projective Q] (n : ℕ) :
    ∀ (m : ℤ) (e : Ext.{w} (P.cycles m) Q (n + 1)), e = 0 := by
  have := hP.projective
  induction n with
  | zero =>
    intro m e
    have hS := P.cyclesShortComplex_shortExact (m - 1) m (by simp) (hP.acyclic m)
    rw [HomologicalComplex.cyclesShortComplex_def] at hS
    obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Q e (Ext.eq_zero_of_projective _)
      (n₀ := 0) rfl
    obtain ⟨g, hg⟩ := hP.exists_comp_iCycles_eq (m - 1) (Ext.addEquiv₀ x)
    rw [← Ext.mk₀_addEquiv₀_apply x, ← hg, ← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc _
  | succ n ih =>
    intro m e
    have hS := P.cyclesShortComplex_shortExact (m - 1) m (by simp) (hP.acyclic m)
    rw [HomologicalComplex.cyclesShortComplex_def] at hS
    obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Q e (Ext.eq_zero_of_projective _)
      (n₀ := n + 1) (by lia)
    rw [ih (m - 1) x, Ext.comp_zero]

end IsTotallyAcyclicProjective

end CochainComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **Gorenstein-projective objects have no higher extensions by projectives**:
`Ext^{n+1}(G, Q) = 0` for a Gorenstein-projective object `G` and a projective object `Q`. -/
theorem isGorensteinProjective.ext_eq_zero {G : C} (hG : isGorensteinProjective C G) (Q : C)
    [Projective Q] {n : ℕ} (e : Ext.{w} G Q (n + 1)) : e = 0 := by
  obtain ⟨P, hP, ⟨i⟩⟩ := (isGorensteinProjective_iff G).1 hG
  rw [← Ext.mk₀_id_comp e, ← i.inv_hom_id, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    hP.ext_cycles_eq_zero Q n 0 ((Ext.mk₀ i.hom).comp e (zero_add _)), Ext.comp_zero]

end CategoryTheory
