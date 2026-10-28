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
`0 ⟶ Zⁱ ⟶ Pⁱ ⟶ Zⁱ⁺¹ ⟶ 0` (`CochainComplex.shortExact_cyclesShortComplex`). Since the middle terms
are projective, the long exact sequence of `Ext(-, Q)` shifts dimension:
`Ext^{n+1}(Zⁱ⁺¹, Q)` is a quotient of `Ext^n(Zⁱ, Q)`. In degree `1`, the obstruction is a
morphism `Zⁱ ⟶ Q` which does not extend to `Pⁱ`, and every such morphism extends because `P` is
totally acyclic.

## Main results

* `CochainComplex.shortExact_cyclesShortComplex`: for a cochain complex `K` exact in degree
  `j = i + 1`, the sequence `0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Zʲ ⟶ 0` is short exact.
* `CochainComplex.IsTotallyAcyclicProjective.exists_comp_iCycles_eq`: a morphism from the cycles of
  a totally acyclic complex of projectives to a projective object extends to the term.
* `CategoryTheory.isGorensteinProjective.ext_eq_zero`: `Ext^{n+1}(G, Q) = 0` for `G`
  Gorenstein-projective and `Q` projective.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ)

/-- The short complex `Zⁱ ⟶ Kⁱ ⟶ Zʲ` formed by the inclusion of the cycles and the differential
`Kⁱ ⟶ Kʲ` corestricted to the cycles. -/
noncomputable abbrev cyclesShortComplex (i j : ℤ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (by
    rw [← cancel_mono (K.iCycles j), Category.assoc, K.toCycles_i, K.iCycles_d, zero_comp])

/-- If `K` is exact in degree `j = i + 1`, then the differential `Kⁱ ⟶ Kʲ` corestricted to the
cycles is an epimorphism. -/
lemma epi_toCycles {i j : ℤ} (hij : i + 1 = j) (hj : K.ExactAt j) : Epi (K.toCycles i j) := by
  obtain rfl : i = (ComplexShape.up ℤ).prev j := by simp; lia
  have ht : K.toCycles _ j = (K.sc j).toCycles := by
    apply (cancel_mono (K.iCycles j)).1
    rw [K.toCycles_i]
    exact (K.sc j).toCycles_i.symm
  rw [ht]
  exact hj.epi_toCycles

/-- **The short exact sequence of cycles**: if `K` is exact in degree `j = i + 1`, then
`0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Zʲ ⟶ 0` is short exact. -/
lemma shortExact_cyclesShortComplex {i j : ℤ} (hij : i + 1 = j) (hj : K.ExactAt j) :
    (K.cyclesShortComplex i j).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (isKernelOfComp (K.iCycles j) (K.d i j) (K.cyclesIsKernel i j (by simp; lia)) _
      (K.toCycles_i i j))
  mono_f := by dsimp; infer_instance
  epi_g := K.epi_toCycles hij hj

namespace IsTotallyAcyclicProjective

variable {P : CochainComplex C ℤ} (hP : P.IsTotallyAcyclicProjective)
include hP

/-- **Morphisms from cycles to projectives extend**: a morphism from the cycles of a totally
acyclic complex of projectives to a projective object extends to the term containing them. -/
lemma exists_comp_iCycles_eq (n : ℤ) {Q : C} [Projective Q] (φ : P.cycles n ⟶ Q) :
    ∃ g : P.X n ⟶ Q, P.iCycles n ≫ g = φ := by
  have := P.epi_toCycles (show n - 1 + 1 = n by lia) (hP.acyclic n)
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
    have hS := P.shortExact_cyclesShortComplex (show m - 1 + 1 = m by lia) (hP.acyclic m)
    obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Q e (Ext.eq_zero_of_projective _)
      (n₀ := 0) rfl
    obtain ⟨g, hg⟩ := hP.exists_comp_iCycles_eq (m - 1) (Ext.addEquiv₀ x)
    rw [← Ext.mk₀_addEquiv₀_apply x, ← hg, ← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc _
  | succ n ih =>
    intro m e
    have hS := P.shortExact_cyclesShortComplex (show m - 1 + 1 = m by lia) (hP.acyclic m)
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
