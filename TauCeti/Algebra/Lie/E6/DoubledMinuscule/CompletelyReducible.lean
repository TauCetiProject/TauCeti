/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.StandardComodule
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import TauCeti.Data.List.Involutive
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate

/-!
# Complete reducibility of the doubled minuscule E₆ representation

Over every field, the standard representation of the doubled minuscule carrier is completely
reducible. Its fifty-four distinct torus characters separate the coordinate lines. Positive and
negative simple-root elements connect the twenty-seven lines in each of the two minuscule blocks.
Thus a subcomodule contains either all or none of the lines in each block, and the remaining
blocks give a complementary subcomodule. This supplies the representation-theoretic input for
eliminating normal smooth unipotent subgroups through faithfulness.

The argument uses the scheme-theoretic torus coaction, so it also applies over finite fields,
where the rational torus points need not separate weights. The dual block's root coefficients
are `-1`, which remain invertible in every characteristic.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

The weight-extraction and reflection argument follows
`TauCeti.Algebra.Lie.D4.Tripled.StandardComodule` and
`TauCeti.Algebra.Lie.E6.Minuscule.StandardComodule`.
-/

public section

open Module WithConv
open TauCeti.DynkinType
open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

universe u

section Ring

variable (k : Type u) [CommRing k]

attribute [local instance] standardComodule

private theorem minusculeCharacter_injective : Function.Injective minusculeCharacter := by
  intro a b h
  apply matrixIndexEquiv.symm.injective
  apply e6DoubledMinusculeWeight_injective
  funext i
  simpa only [minusculeCharacter, SplitTorus.toAdd_weightCharacter, matrixWeight_apply] using
    congrArg (fun χ : Multiplicative (Fin 6 →₀ ℤ) ↦ Multiplicative.toAdd χ i) h

private theorem root_mulVec_single_sub (j : Fin 6 ⊕ Fin 6) (a : Fin 54)
    (ha : matrixWeight a (Sum.elim id id j) =
      (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) j : ℤ)) :
    (((rootSubgroupPoints j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 54) k) : Matrix (Fin 54) (Fin 54) k) *ᵥ
          Pi.single a 1) - Pi.single a 1 =
      (summandSign (matrixIndexEquiv.symm a) : k) •
        Pi.single (matrixIndexEquiv (reflection (Sum.elim id id j)
          (matrixIndexEquiv.symm a))) 1 := by
  rw [coe_rootSubgroupPoints_eq_one_add_smul, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  simp only [toAdd_ofAdd, one_smul, add_sub_cancel_left,
    Matrix.mulVec_single_one]
  ext b
  simp [Matrix.map_apply, rootIntMatrix_apply, ha, Pi.single_apply]

/-- Root points propagate membership of a coordinate vector along a simple reflection. -/
private theorem single_reflection_mem
    (N : Submodule k (Fin 54 → k))
    (hroot : ∀ j v, v ∈ N →
      ((rootSubgroupPoints j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 54) k) : Matrix (Fin 54) (Fin 54) k) *ᵥ v ∈ N)
    (a : Fin 27 ⊕ Fin 27) (i : Fin 6) (ha : Pi.single (matrixIndexEquiv a) 1 ∈ N) :
    Pi.single (matrixIndexEquiv (reflection i a)) 1 ∈ N := by
  have hcases : e6DoubledMinusculeWeight a i = -1 ∨
      e6DoubledMinusculeWeight a i = 0 ∨ e6DoubledMinusculeWeight a i = 1 := by
    cases a with
    | inl a =>
      simpa only [e6DoubledMinusculeWeight_inl] using
        e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i
    | inr a =>
      rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
      · exact Or.inr (Or.inr (by simp [h]))
      · exact Or.inr (Or.inl (by simp [h]))
      · exact Or.inl (by simp [h])
  rcases hcases with hneg | hzero | hpos
  · have hsub := N.sub_mem (hroot (.inl i) _ ha) ha
    rw [root_mulVec_single_sub k (.inl i) _ (by simpa [matrixWeight_apply] using hneg)] at hsub
    cases a <;> simpa using hsub
  · have hfix : reflection i a = a := by
      cases a with
      | inl a =>
        rw [reflection_inl, (e6MinusculeReflection_eq_self_iff i a).2
          (by simpa only [e6DoubledMinusculeWeight_inl] using hzero)]
      | inr a =>
        have hz : e6MinusculeWeight a i = 0 := by simpa using hzero
        rw [reflection_inr, (e6MinusculeReflection_eq_self_iff i a).2 hz]
    rwa [hfix]
  · have hsub := N.sub_mem (hroot (.inr i) _ ha) ha
    rw [root_mulVec_single_sub k (.inr i) _ (by simpa [matrixWeight_apply] using hpos)] at hsub
    cases a <;> simpa using hsub

private theorem single_mem_of_summand_eq
    (N : Submodule k (Fin 54 → k))
    (hroot : ∀ j v, v ∈ N →
      ((rootSubgroupPoints j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 54) k) : Matrix (Fin 54) (Fin 54) k) *ᵥ v ∈ N)
    {a b : Fin 54} (hab : matrixSummand a = matrixSummand b)
    (hb : Pi.single b 1 ∈ N) : Pi.single a 1 ∈ N := by
  obtain ⟨a, rfl⟩ := matrixIndexEquiv.surjective a
  obtain ⟨b, rfl⟩ := matrixIndexEquiv.surjective b
  have hbase (c : Fin 27 ⊕ Fin 27) :
      Pi.single (matrixIndexEquiv c) 1 ∈ N ↔
        Pi.single (matrixIndexEquiv (if c.isRight then .inr 0 else .inl 0)) 1 ∈ N := by
    cases c with
    | inl c =>
      obtain ⟨l, hl⟩ := exists_e6MinusculeReflections_eq c
      have h := predicate_foldl_iff_of_involutive
        (fun d ↦ Pi.single (matrixIndexEquiv (.inl d)) (1 : k) ∈ N)
        (fun i ↦ e6MinusculeReflection i) (fun i ↦ e6MinusculeReflection_apply_apply i)
        (fun d i hd ↦ by simpa only [reflection_inl] using
          single_reflection_mem k N hroot (.inl d) i hd) l 0
      simpa [hl] using h
    | inr c =>
      obtain ⟨l, hl⟩ := exists_e6MinusculeReflections_eq c
      have h := predicate_foldl_iff_of_involutive
        (fun d ↦ Pi.single (matrixIndexEquiv (.inr d)) (1 : k) ∈ N)
        (fun i ↦ e6MinusculeReflection i) (fun i ↦ e6MinusculeReflection_apply_apply i)
        (fun d i hd ↦ by simpa only [reflection_inr] using
          single_reflection_mem k N hroot (.inr d) i hd) l 0
      simpa [hl] using h
  cases a <;> cases b <;> simp_all

end Ring

variable (k : Type u) [Field k]

attribute [local instance] standardComodule

/-- A comodule with the doubled minuscule torus weights, the numbered root actions, and no
coefficients mixing the two minuscule blocks is completely reducible. -/
theorem isCompletelyReducible_of_minusculeWeights_of_rootSubgroupPoints
    {H : Type*} [AddCommGroup H] [Module k H] [Coalgebra k H]
    [Comodule k H (Fin 54 → k)]
    (τ : H →ₗc[k] (DiagonalizableGroup.coordinateRing k
      (SplitTorus.characterGroup (Fin 6))).obj)
    (hτ : Comodule.Corestrict τ =
      Comodule.ofWeights (Pi.basisFun k (Fin 54)) minusculeCharacter)
    (hroot : ∀ (N : Subcomodule k H (Fin 54 → k)) j v, v ∈ N →
      ((rootSubgroupPoints j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 54) k) : Matrix (Fin 54) (Fin 54) k) *ᵥ v ∈ N)
    (hblock : ∀ a b, matrixSummand a ≠ matrixSummand b →
      Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin 54)) a b = 0) :
    Comodule.IsCompletelyReducible k H (Fin 54 → k) := by
  classical
  apply Comodule.IsCompletelyReducible.of_exists_isCompl
  intro N
  let s : Set (Fin 54) := {a | Pi.single a (1 : k) ∈ N}
  have hs : ∀ a b, matrixSummand a = matrixSummand b → b ∈ s → a ∈ s :=
    fun _ _ hab hb ↦ single_mem_of_summand_eq k N.toSubmodule (hroot N) hab hb
  -- The coordinate lines absent from N form a union of the two preserved blocks.
  let M := (Pi.basisFun k (Fin 54)).coordinateSpanSubcomodule sᶜ <|
    ((Pi.basisFun k (Fin 54)).coordinateSpanIsStable_iff
      (C := H) sᶜ).2 <| by
      intro a ha b hb
      have hab : matrixSummand a ≠ matrixSummand b :=
        fun h ↦ hb (hs b a h.symm (Set.notMem_compl_iff.mp ha))
      exact hblock a b hab
  have hM : M.toSubmodule = Submodule.span k ((Pi.basisFun k (Fin 54)) '' sᶜ) :=
    Module.Basis.coordinateSpanSubcomodule_toSubmodule _ _ _
  refine ⟨M, ?_⟩
  rw [hM, Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights
    τ minusculeCharacter minusculeCharacter_injective hτ N]
  exact (Pi.basisFun k (Fin 54)).linearIndependent.isCompl_span_image
    (Pi.basisFun k (Fin 54)).span_eq isCompl_compl

/-- The standard comodule of the doubled minuscule E₆ carrier is completely reducible over every
field, including fields of characteristic two and three. -/
theorem isCompletelyReducible_standardComodule :
    Comodule.IsCompletelyReducible k (coordinateHopfAlgebra k) (Fin 54 → k) :=
  isCompletelyReducible_of_minusculeWeights_of_rootSubgroupPoints k
    (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom
    (torusCorestrict_eq_ofWeights k)
    (fun N j _ hw ↦ points_mulVec_mem k N
      (rootSubgroupPoints j k (Multiplicative.ofAdd 1)) hw)
    (fun a b hab ↦ by
      rw [coefficientMatrix_basisFun]
      exact coordinateMap_X_eq_zero k hab)

end TauCeti.E6DoubledMinuscule
