/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import TauCeti.Algebra.Homology.Ext.Presentation

/-!
# Gorenstein-projective objects have no higher extensions by projectives

Let `C` be an abelian category and `G` a Gorenstein-projective object of `C`. Then
`Ext^{n+1}(G, Q) = 0` for every projective object `Q` of `C`.

A complete resolution `P` of `G` is acyclic, so its cycles fit into short exact sequences
`0 ⟶ Zⁱ ⟶ Pⁱ ⟶ Zⁱ⁺¹ ⟶ 0` (`HomologicalComplex.shortExact_mk_iCycles_toCycles`). Since the middle
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
  intro m
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
  exact TauCeti.ext_X₃_eq_zero_of_forall_exists_f_comp_eq
    (S := fun m ↦ ShortComplex.mk (P.iCycles m) (P.toCycles m (m + 1)) (P.iCycles_toCycles _ _))
    (fun m ↦ P.shortExact_mk_iCycles_toCycles m (m + 1) (by simp) (hP.acyclic (m + 1)))
    (fun _ ↦ Iso.refl _) (fun m φ ↦ hP.exists_comp_iCycles_eq m φ) n k

end IsTotallyAcyclicProjective

end CochainComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **Gorenstein-projective objects have no higher extensions by projectives**:
`Ext^{n+1}(G, Q) = 0` for a Gorenstein-projective object `G` and a projective object `Q`. -/
theorem isGorensteinProjective.ext_eq_zero {G : C} (hG : isGorensteinProjective C G) (Q : C)
    [Projective Q] {n : ℕ} (e : Ext.{w} G Q (n + 1)) : e = 0 := by
  obtain ⟨P, hP, ⟨i⟩⟩ := (isGorensteinProjective_iff G).1 hG
  exact TauCeti.ext_eq_zero_of_iso i.symm (hP.ext_cycles_eq_zero Q n 0) e

end CategoryTheory
