/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.GradedPair.Centralizer.Basic
public import TauCeti.RepresentationTheory.Quiver.GradedPair.Standard
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Commuting block coordinates on standard interval pairs

In the standard raising pair `m.standardPair StepDirection.up` of a multisegment `m`, a degree-`-1`
operator commuting with the raising operator is completely determined by one scalar entry for each
ordered pair `(i, j)` of occurrence labels whose intervals satisfy the precedence relation
`I ≺ J`, i.e. `I.fst < J.fst ≤ I.snd + 1 ≤ J.snd` (`TauCeti.IntInterval.Precedes`).

On such an allowed pair `(i, j)`, the block operator `TauCeti.Multisegment.blockOperator`
sends each standard vector of block `j` of degree `a` to the standard vector of block `i` of degree
`a - 1` (and `0` outside the overlap or on other blocks). Along the overlap `{a ∈ J | a - 1 ∈ I}`,
commutation with the raising operator forces all matrix entries `(i, a - 1) ← (j, a)` of any
`L ∈ (m.standardPair .up).centralizer` to be constant and equal to the cut entry at `a = J.fst`; on
every non-preceding pair `(i, j)`, all such entries vanish.

This yields an explicit complex linear equivalence
`TauCeti.Multisegment.centralizerEquivCoords` identifying `(m.standardPair .up).centralizer`
with `m.AllowedPair → ℂ`.

## Main definitions

* `TauCeti.Multisegment.AllowedPair m`: ordered occurrence pairs `(i, j)` with
  `(m.occurrenceInterval i).Precedes (m.occurrenceInterval j)`.
* `TauCeti.Multisegment.blockOperator m i j`: the degree-`-1` block shift from occurrence `j` to
  occurrence `i`.
* `TauCeti.Multisegment.centralizerEquivCoords m`: the linear equivalence identifying
  `(m.standardPair .up).centralizer` with `m.AllowedPair → ℂ`.

## Main results

* `TauCeti.Multisegment.blockOperator_mem_centralizer_and_ne_zero_iff`: `blockOperator m i j` is a
  nonzero element of `(m.standardPair .up).centralizer` if and only if
  `(m.occurrenceInterval i).Precedes (m.occurrenceInterval j)`.
* `TauCeti.Multisegment.standardBasis_repr_centralizer_apply`: explicit cut-entry formula for
  `(m.standardPair .up).centralizer` in `m.standardBasis`.
* `TauCeti.Multisegment.finrank_centralizer_standardPair_up`: the dimension of
  `(m.standardPair .up).centralizer` equals `Fintype.card m.AllowedPair`.
* `TauCeti.Multisegment.centralizer_standardPair_up_eq_bot_iff`: `(m.standardPair .up).centralizer`
  is trivial if and only if `m` has no allowed pairs.
* `TauCeti.Multisegment.centralizer_standardPair_up_singleton`: for a single interval, the
  centralizer of `({s} : Multisegment).standardPair .up` is trivial.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1 and Lemma 3.2.
* C. Mœglin, J.-L. Waldspurger, *Sur l'involution de Zelevinski*, J. reine angew. Math. 372
  (1986), 136–177, §II.1 and Lemma II.4 (pp. 160–161).
-/

public section

open Module

namespace TauCeti

/-! ### Allowed pairs and commuting block operators -/

namespace Multisegment

variable (m : Multisegment)

/-- Ordered pairs `(i, j)` of occurrence labels of `m` for which the target interval `i` strictly
precedes the source interval `j`. -/
abbrev AllowedPair : Type :=
  {p : Fin m.card × Fin m.card // (m.occurrenceInterval p.1).Precedes (m.occurrenceInterval p.2)}

/-- Constructor for `Multisegment.AllowedPair`. -/
abbrev AllowedPair.mk {m : Multisegment} {i j : Fin m.card}
    (h : (m.occurrenceInterval i).Precedes (m.occurrenceInterval j)) : AllowedPair m :=
  ⟨(i, j), h⟩

/-- The target occurrence has interval preceding the source occurrence. -/
theorem AllowedPair.precedes {m : Multisegment} (p : AllowedPair m) :
    (m.occurrenceInterval p.val.fst).Precedes (m.occurrenceInterval p.val.snd) :=
  p.property

/-- The degree-`-1` block shift operator sending each standard vector `(j, a)` of block `j` to
`standardVector m i (a - 1)` (which vanishes when `a - 1` lies outside occurrence interval `i`),
and sending all other source blocks `k ≠ j` to `0`. -/
noncomputable def blockOperator (i j : Fin m.card) :
    Module.End ℂ (standardSpace m).Carrier :=
  (standardBasis m).constr ℂ fun x ↦
    if x.1 = j then standardVector m i ((x.2 : ℤ) - 1) else 0

variable {m}

@[simp]
theorem blockOperator_standardBasis (i j : Fin m.card) (x : StandardIndex m) :
    blockOperator m i j (standardBasis m x) =
      if x.1 = j then standardVector m i ((x.2 : ℤ) - 1) else 0 :=
  (standardBasis m).constr_basis ℂ _ x

theorem blockOperator_standardVector_of_mem {i j k : Fin m.card} {a : ℤ}
    (hk : a ∈ occurrenceInterval m k) :
    blockOperator m i j (standardVector m k a) =
      if k = j then standardVector m i (a - 1) else 0 := by
  rw [standardVector_of_mem hk, blockOperator_standardBasis]
  simp only [StandardIndex.fst_mk, StandardIndex.coe_snd_mk]

@[simp]
theorem blockOperator_standardVector_self (i : Fin m.card) {j : Fin m.card} {a : ℤ}
    (hj : a ∈ occurrenceInterval m j) :
    blockOperator m i j (standardVector m j a) = standardVector m i (a - 1) := by
  simp [blockOperator_standardVector_of_mem hj]

@[simp]
theorem blockOperator_standardVector_of_ne (i : Fin m.card) {j k : Fin m.card}
    (hk : k ≠ j) (a : ℤ) :
    blockOperator m i j (standardVector m k a) = 0 := by
  by_cases ha : a ∈ occurrenceInterval m k
  · simp [blockOperator_standardVector_of_mem ha, hk]
  · rw [standardVector_of_notMem ha, map_zero]

/-- Every `blockOperator` is homogeneous of degree `-1` (`-StepDirection.up.step`). -/
theorem isHomogeneous_blockOperator (m : Multisegment) (i j : Fin m.card) :
    LinearMap.IsHomogeneous (blockOperator m i j) (standardSpace m).grade
      (standardSpace m).grade (-StepDirection.up.step) := by
  rw [LinearMap.isHomogeneous_def]
  intro a v hv
  rw [grade_standardSpace] at hv
  refine (Submodule.image_span_subset _ _ _).2 ?_ ⟨v, hv, rfl⟩
  rintro _ ⟨k, rfl⟩
  dsimp only
  by_cases ha : a ∈ occurrenceInterval m k
  · rw [blockOperator_standardVector_of_mem ha]
    split_ifs
    · simpa only [StepDirection.step_up, sub_eq_add_neg] using standardVector_mem_grade i (a - 1)
    · exact zero_mem _
  · rw [standardVector_of_notMem ha, map_zero]
    exact zero_mem _

/-- When interval `i` precedes interval `j`, `blockOperator m i j` commutes with the standard
raising operator and lies in `(standardPair m .up).centralizer`. -/
theorem blockOperator_mem_centralizer {i j : Fin m.card}
    (h : (occurrenceInterval m i).Precedes (occurrenceInterval m j)) :
    blockOperator m i j ∈ (standardPair m .up).centralizer := by
  refine GradedPair.mem_centralizer_iff.2 ⟨isHomogeneous_blockOperator m i j, ?_⟩
  refine (standardBasis m).ext fun x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, standardBasis_eq_standardVector]
  have hx : (x.2 : ℤ) ∈ occurrenceInterval m x.1 := x.mem_occurrenceInterval
  by_cases hxj : x.1 = j
  · subst hxj
    rw [blockOperator_standardVector_self i hx, standardPair_operator_standardVector .up hx,
      StepDirection.step_up]
    by_cases hxi : (x.2 : ℤ) - 1 ∈ occurrenceInterval m i
    · rw [standardPair_operator_standardVector .up hxi, StepDirection.step_up, sub_add_cancel]
      by_cases hx1 : (x.2 : ℤ) + 1 ∈ occurrenceInterval m x.1
      · rw [blockOperator_standardVector_self i hx1, add_sub_cancel_right]
      · rw [standardVector_of_notMem hx1, map_zero]
        symm
        rw [standardVector_eq_zero_iff]
        rw [NonemptyInterval.mem_def] at hx hxi hx1 ⊢
        have h2 := (IntInterval.precedes_def.1 h).2.2
        omega
    · rw [standardVector_of_notMem hxi, map_zero]
      by_cases hx1 : (x.2 : ℤ) + 1 ∈ occurrenceInterval m x.1
      · rw [blockOperator_standardVector_self i hx1, add_sub_cancel_right,
          standardVector_eq_zero_iff]
        rw [NonemptyInterval.mem_def] at hx hxi hx1 ⊢
        have h1 := h.fst_lt
        omega
      · rw [standardVector_of_notMem hx1, map_zero]
  · rw [blockOperator_standardVector_of_ne i hxj, standardPair_operator_standardVector .up hx,
      StepDirection.step_up, map_zero, blockOperator_standardVector_of_ne i hxj]

/-- When interval `i` precedes interval `j`, `blockOperator m i j` is nonzero. -/
theorem blockOperator_ne_zero_of_precedes {i j : Fin m.card}
    (h : (occurrenceInterval m i).Precedes (occurrenceInterval m j)) :
    blockOperator m i j ≠ 0 := by
  intro h0
  have hv := congrFun (congrArg DFunLike.coe h0)
    (standardVector m j (occurrenceInterval m j).fst)
  rw [blockOperator_standardVector_self i
      (Set.left_mem_Icc.mpr (occurrenceInterval m j).fst_le_snd),
    LinearMap.zero_apply, standardVector_eq_zero_iff] at hv
  exact hv h.fst_sub_one_mem

/-! ### Block entry extraction and constancy along the overlap -/

open Classical in
/-- The `(i, j)`-th matrix entry of `L` from `(j, a)` to `(i, a - 1)`, or `0` if invalid. -/
private noncomputable def blockEntry (m : Multisegment)
    (L : Module.End ℂ (standardSpace m).Carrier) (i j : Fin m.card) (a : ℤ) : ℂ :=
  if h : a ∈ occurrenceInterval m j ∧ a - 1 ∈ occurrenceInterval m i then
    (standardBasis m).repr (L (standardVector m j a)) (StandardIndex.mk i (a - 1) h.2)
  else 0

private theorem blockEntry_of_mem {L : Module.End ℂ (standardSpace m).Carrier}
    {i j : Fin m.card} {a : ℤ} (hj : a ∈ occurrenceInterval m j)
    (hi : a - 1 ∈ occurrenceInterval m i) :
    blockEntry m L i j a =
      (standardBasis m).repr (L (standardVector m j a)) (StandardIndex.mk i (a - 1) hi) := by
  simp [blockEntry, hj, hi]

private theorem blockEntry_of_notMem_source {L : Module.End ℂ (standardSpace m).Carrier}
    {i j : Fin m.card} {a : ℤ} (hj : a ∉ occurrenceInterval m j) :
    blockEntry m L i j a = 0 := by
  simp [blockEntry, hj]

private theorem blockEntry_of_notMem_target {L : Module.End ℂ (standardSpace m).Carrier}
    {i j : Fin m.card} {a : ℤ} (hi : a - 1 ∉ occurrenceInterval m i) :
    blockEntry m L i j a = 0 := by
  simp [blockEntry, hi]

private theorem expand_of_isHomogeneous {L : Module.End ℂ (standardSpace m).Carrier}
    (hL : LinearMap.IsHomogeneous L (standardSpace m).grade (standardSpace m).grade
      (-StepDirection.up.step))
    {j : Fin m.card} {a : ℤ} (ha : a ∈ occurrenceInterval m j) :
    L (standardVector m j a) =
      ∑ i : Fin m.card, blockEntry m L i j a • standardVector m i (a - 1) := by
  refine (standardBasis m).repr.injective (Finsupp.ext fun x ↦ ?_)
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hLmem : L (standardVector m j a) ∈ (standardSpace m).grade (a - 1) := by
    simpa only [StepDirection.step_up, sub_eq_add_neg] using
      hL.map_mem (standardVector_mem_grade j a)
  by_cases hx : (x.2 : ℤ) = a - 1
  · have hxa : a - 1 ∈ occurrenceInterval m x.1 := hx ▸ x.mem_occurrenceInterval
    have hxeq : x = StandardIndex.mk x.1 (a - 1) hxa := by
      simp [Sigma.subtype_ext_iff, hx]
    rw [hxeq]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul,
      standardBasis_repr_standardVector_same_deg hxa, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, blockEntry_of_mem ha hxa]
  · rw [mem_grade_standardSpace_iff.1 hLmem x hx]
    refine (Finset.sum_eq_zero fun i _ ↦ ?_).symm
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hai : a - 1 ∈ occurrenceInterval m i
    · rw [standardVector_of_mem hai, Basis.repr_self_apply]
      have hne : StandardIndex.mk i (a - 1) hai ≠ x := fun heq ↦ hx (by
        simpa only [StandardIndex.coe_snd_mk] using
          congrArg (fun y : StandardIndex m ↦ (y.2 : ℤ)) heq.symm)
      simp [hne]
    · rw [standardVector_of_notMem hai, map_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero]

/-- Applying the standard raising operator shifts the `(i, a)` coordinate from `(i, a - 1)`. -/
private theorem standardBasis_repr_operator_apply (v : (standardSpace m).Carrier)
    {i : Fin m.card} {a : ℤ} (haI : a ∈ occurrenceInterval m i) :
    (standardBasis m).repr ((standardPair m .up).operator v) (StandardIndex.mk i a haI) =
      if h : a - 1 ∈ occurrenceInterval m i then
        (standardBasis m).repr v (StandardIndex.mk i (a - 1) h)
      else 0 := by
  conv_lhs => rw [← (standardBasis m).sum_repr v]
  rw [map_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hterm (x : StandardIndex m) :
      (standardBasis m).repr
          ((standardBasis m).repr v x • (standardPair m .up).operator (standardBasis m x))
          (StandardIndex.mk i a haI) =
        if x.1 = i ∧ (x.2 : ℤ) + 1 = a then (standardBasis m).repr v x else 0 := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, standardPair_operator_standardBasis,
      StepDirection.step_up]
    by_cases hxa : (x.2 : ℤ) + 1 = a
    · rw [hxa, standardBasis_repr_standardVector_same_deg haI]
      split_ifs <;> simp_all
    · rw [standardBasis_repr_standardVector_eq_zero_of_degree_ne hxa haI, mul_zero]
      split_ifs with hcond
      · exact absurd hcond.2 hxa
      · rfl
  simp only [LinearMap.map_smul, hterm]
  by_cases ha1 : a - 1 ∈ occurrenceInterval m i
  · simp only [ha1, ↓reduceDIte]
    rw [Finset.sum_eq_single (StandardIndex.mk i (a - 1) ha1)]
    · simp
    · intro x _ hxne
      split_ifs with hcond
      · exact absurd (by simp [Sigma.subtype_ext_iff, hcond.1]; omega) hxne
      · rfl
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · simp only [ha1, ↓reduceDIte]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    split_ifs with hcond
    · have hmem : (x.2 : ℤ) ∈ occurrenceInterval m i := hcond.1 ▸ x.mem_occurrenceInterval
      have heq : (x.2 : ℤ) = a - 1 := by omega
      exact absurd (heq ▸ hmem) ha1
    · rfl

/-- Matrix entry of `T ∘ L` at `(i, a) ← (j, a)`. -/
private theorem standardBasis_repr_operator_comp_standardVector
    (L : (standardPair m .up).centralizer) {i j : Fin m.card} {a : ℤ}
    (haJ : a ∈ occurrenceInterval m j) (haI : a ∈ occurrenceInterval m i) :
    (standardBasis m).repr
        ((standardPair m .up).operator ((L : Module.End ℂ (standardSpace m).Carrier)
          (standardVector m j a))) (StandardIndex.mk i a haI) =
      if a - 1 ∈ occurrenceInterval m i then blockEntry m L i j a else 0 := by
  rw [standardBasis_repr_operator_apply _ haI]
  split_ifs with ha1
  · exact (blockEntry_of_mem haJ ha1).symm
  · rfl

/-- Matrix entry of `L ∘ T` at `(i, a) ← (j, a)`. -/
private theorem standardBasis_repr_comp_operator_standardVector
    (L : (standardPair m .up).centralizer) {i j : Fin m.card} {a : ℤ}
    (haJ : a ∈ occurrenceInterval m j) (haI : a ∈ occurrenceInterval m i) :
    (standardBasis m).repr
        ((L : Module.End ℂ (standardSpace m).Carrier)
          ((standardPair m .up).operator (standardVector m j a)))
        (StandardIndex.mk i a haI) =
      if a + 1 ∈ occurrenceInterval m j then blockEntry m L i j (a + 1) else 0 := by
  rw [standardPair_operator_standardVector .up haJ, StepDirection.step_up]
  by_cases ha1 : a + 1 ∈ occurrenceInterval m j
  · simp only [ha1, ↓reduceIte]
    simpa only [add_sub_cancel_right] using
      (blockEntry_of_mem ha1 (by simpa only [add_sub_cancel_right] using haI)).symm
  · simp [ha1]

private theorem centralizer_blockEntry_step_eq (L : (standardPair m .up).centralizer)
    {i j : Fin m.card} {a : ℤ}
    (haJ : a ∈ occurrenceInterval m j) (haI : a ∈ occurrenceInterval m i) :
    (if a - 1 ∈ occurrenceInterval m i then blockEntry m L i j a else 0) =
      (if a + 1 ∈ occurrenceInterval m j then blockEntry m L i j (a + 1) else 0) := by
  have hNL := congrArg (fun v ↦ (standardBasis m).repr v (StandardIndex.mk i a haI))
    (GradedPair.coe_centralizer_operator_apply_comm L (standardVector m j a)).symm
  rw [← standardBasis_repr_operator_comp_standardVector L haJ haI,
    ← standardBasis_repr_comp_operator_standardVector L haJ haI, hNL]

private theorem blockEntry_succ_eq (L : (standardPair m .up).centralizer)
    {i j : Fin m.card} {a : ℤ}
    (haJ : a ∈ occurrenceInterval m j) (ha1J : a + 1 ∈ occurrenceInterval m j)
    (ha1I : a - 1 ∈ occurrenceInterval m i) (haI : a ∈ occurrenceInterval m i) :
    blockEntry m L i j (a + 1) = blockEntry m L i j a := by
  have h := centralizer_blockEntry_step_eq L haJ haI
  simpa only [ha1I, ↓reduceIte, ha1J] using h.symm

private theorem blockEntry_eq_of_le (L : (standardPair m .up).centralizer)
    {i j : Fin m.card} {a b : ℤ} (hab : a ≤ b)
    (haJ : a ∈ occurrenceInterval m j) (haI : a - 1 ∈ occurrenceInterval m i)
    (hbJ : b ∈ occurrenceInterval m j) (hbI : b - 1 ∈ occurrenceInterval m i) :
    blockEntry m L i j b = blockEntry m L i j a := by
  induction b, hab using Int.leInduction with
  | base => rfl
  | succ k hak ih =>
    have hkJ : k ∈ occurrenceInterval m j := by
      rw [NonemptyInterval.mem_def] at haJ hbJ ⊢
      omega
    have hk1I : k - 1 ∈ occurrenceInterval m i := by
      rw [NonemptyInterval.mem_def] at haI hbI ⊢
      omega
    have hkI : k ∈ occurrenceInterval m i := by
      simpa only [add_sub_cancel_right] using hbI
    exact (blockEntry_succ_eq L hkJ hbJ hk1I hkI).trans (ih hkJ hk1I)

private theorem blockEntry_fst_add_one_eq_zero (L : (standardPair m .up).centralizer)
    {i j : Fin m.card}
    (h1 : (occurrenceInterval m i).fst ∈ occurrenceInterval m j)
    (h2 : (occurrenceInterval m i).fst + 1 ∈ occurrenceInterval m j) :
    blockEntry m L i j ((occurrenceInterval m i).fst + 1) = 0 := by
  have hnot : (occurrenceInterval m i).fst - 1 ∉ occurrenceInterval m i := by
    rw [NonemptyInterval.mem_def]
    omega
  have h := centralizer_blockEntry_step_eq L h1
    (Set.left_mem_Icc.mpr (occurrenceInterval m i).fst_le_snd)
  simpa only [hnot, ↓reduceIte, h2] using h.symm

private theorem blockEntry_snd_eq_zero (L : (standardPair m .up).centralizer)
    {i j : Fin m.card}
    (h1 : (occurrenceInterval m j).snd - 1 ∈ occurrenceInterval m i)
    (h2 : (occurrenceInterval m j).snd ∈ occurrenceInterval m i) :
    blockEntry m L i j (occurrenceInterval m j).snd = 0 := by
  have hnot : (occurrenceInterval m j).snd + 1 ∉ occurrenceInterval m j := by
    rw [NonemptyInterval.mem_def]
    omega
  have h := centralizer_blockEntry_step_eq L
    (Set.right_mem_Icc.mpr (occurrenceInterval m j).fst_le_snd) h2
  simpa only [h1, ↓reduceIte, hnot] using h

private theorem blockEntry_eq_zero_of_not_precedes (L : (standardPair m .up).centralizer)
    {i j : Fin m.card}
    (hn : ¬ (occurrenceInterval m i).Precedes (occurrenceInterval m j)) (a : ℤ) :
    blockEntry m L i j a = 0 := by
  by_cases ha : a ∈ occurrenceInterval m j ∧ a - 1 ∈ occurrenceInterval m i
  · obtain ⟨haJ, haI⟩ := ha
    rw [IntInterval.precedes_def, not_and, not_and] at hn
    have haJ' := NonemptyInterval.mem_def.1 haJ
    have haI' := NonemptyInterval.mem_def.1 haI
    by_cases hfst : (occurrenceInterval m i).fst < (occurrenceInterval m j).fst
    · have hsnd : (occurrenceInterval m j).snd ≤ (occurrenceInterval m i).snd := by
        have := hn hfst (by omega)
        omega
      have h1 : (occurrenceInterval m j).snd - 1 ∈ occurrenceInterval m i := by
        rw [NonemptyInterval.mem_def]
        omega
      have h2 : (occurrenceInterval m j).snd ∈ occurrenceInterval m i := by
        rw [NonemptyInterval.mem_def]
        omega
      rw [← blockEntry_eq_of_le L haJ'.2 haJ haI
          (Set.right_mem_Icc.mpr (occurrenceInterval m j).fst_le_snd) h1,
        blockEntry_snd_eq_zero L h1 h2]
    · have h1 : (occurrenceInterval m i).fst ∈ occurrenceInterval m j := by
        rw [NonemptyInterval.mem_def]
        omega
      have h2 : (occurrenceInterval m i).fst + 1 ∈ occurrenceInterval m j := by
        rw [NonemptyInterval.mem_def]
        omega
      have heq := blockEntry_eq_of_le L (by omega) h2
        (by rw [add_sub_cancel_right]
            exact Set.left_mem_Icc.mpr (occurrenceInterval m i).fst_le_snd)
        haJ haI
      rw [heq, blockEntry_fst_add_one_eq_zero L h1 h2]
  · by_cases hj : a ∈ occurrenceInterval m j
    · exact blockEntry_of_notMem_target (fun hi ↦ ha ⟨hj, hi⟩)
    · exact blockEntry_of_notMem_source hj

private theorem blockEntry_eq_fst_of_precedes (L : (standardPair m .up).centralizer)
    {i j : Fin m.card} (h : (occurrenceInterval m i).Precedes (occurrenceInterval m j))
    {a : ℤ} (haJ : a ∈ occurrenceInterval m j) (haI : a - 1 ∈ occurrenceInterval m i) :
    blockEntry m L i j a = blockEntry m L i j (occurrenceInterval m j).fst :=
  blockEntry_eq_of_le L (NonemptyInterval.mem_def.1 haJ).1
    (Set.left_mem_Icc.mpr (occurrenceInterval m j).fst_le_snd) h.fst_sub_one_mem haJ haI

/-! ### Characterization of nonzero commuting block operators -/

/-- If `blockOperator m i j` is a nonzero element of `(standardPair m .up).centralizer`, then
interval `i` precedes interval `j`. -/
theorem precedes_of_blockOperator_mem_centralizer_of_ne_zero {i j : Fin m.card}
    (hmem : blockOperator m i j ∈ (standardPair m .up).centralizer)
    (hne : blockOperator m i j ≠ 0) :
    (occurrenceInterval m i).Precedes (occurrenceInterval m j) := by
  by_contra hn
  apply hne
  refine (standardBasis m).ext fun x ↦ ?_
  rw [LinearMap.zero_apply, standardBasis_eq_standardVector]
  by_cases hxj : x.1 = j
  · subst hxj
    have haJ : (x.2 : ℤ) ∈ occurrenceInterval m x.1 := x.mem_occurrenceInterval
    rw [blockOperator_standardVector_self i haJ]
    by_cases haI : (x.2 : ℤ) - 1 ∈ occurrenceInterval m i
    · have hnot := blockEntry_eq_zero_of_not_precedes ⟨blockOperator m i x.1, hmem⟩ hn (x.2 : ℤ)
      simp only [blockEntry_of_mem haJ haI, blockOperator_standardVector_self i haJ,
        standardBasis_repr_standardVector_same_deg haI, ↓reduceIte] at hnot
      exact absurd hnot one_ne_zero
    · exact standardVector_of_notMem haI
  · exact blockOperator_standardVector_of_ne i hxj (x.2 : ℤ)

/-- `blockOperator m i j` is a nonzero element of `(standardPair m .up).centralizer` if and only
if the target occurrence interval `i` strictly precedes the source occurrence interval `j`. -/
theorem blockOperator_mem_centralizer_and_ne_zero_iff (i j : Fin m.card) :
    (blockOperator m i j ∈ (standardPair m .up).centralizer ∧ blockOperator m i j ≠ 0) ↔
      (occurrenceInterval m i).Precedes (occurrenceInterval m j) :=
  ⟨fun ⟨hm, hne⟩ ↦ precedes_of_blockOperator_mem_centralizer_of_ne_zero hm hne,
    fun h ↦ ⟨blockOperator_mem_centralizer h, blockOperator_ne_zero_of_precedes h⟩⟩

/-! ### Coordinate equivalence for `(standardPair m .up).centralizer` -/

private theorem sum_allowedPair {M : Type*} [AddCommMonoid M] (f : AllowedPair m → M) :
    (∑ p : AllowedPair m, f p) =
      ∑ i : Fin m.card, ∑ j : Fin m.card,
        if h : (occurrenceInterval m i).Precedes (occurrenceInterval m j) then
          f (AllowedPair.mk h)
        else 0 := by
  have hsum := Finset.sum_congr_set
    {p : Fin m.card × Fin m.card | (occurrenceInterval m p.1).Precedes (occurrenceInterval m p.2)}
    (fun p ↦ if h : (occurrenceInterval m p.1).Precedes (occurrenceInterval m p.2) then
      f ⟨p, h⟩ else 0)
    f (fun _ hp ↦ by simp only [Set.mem_ofPred_eq] at hp; simp [hp])
    (fun _ hp ↦ by simp only [Set.mem_ofPred_eq] at hp; simp [hp])
  exact (by convert hsum.symm : (∑ p : AllowedPair m, f p) = _).trans (Fintype.sum_prod_type' _)

/-- The cut-entry coordinate of an endomorphism `L` at an allowed pair `p`. -/
private noncomputable def centralizerCoord (L : Module.End ℂ (standardSpace m).Carrier)
    (p : AllowedPair m) : ℂ :=
  (standardBasis m).repr
    (L (standardVector m p.val.snd (occurrenceInterval m p.val.snd).fst))
    (StandardIndex.mk p.val.fst ((occurrenceInterval m p.val.snd).fst - 1)
      p.property.fst_sub_one_mem)

/-- Evaluating an allowed-pair linear combination of block operators on `standardVector m j a`
(with `a ∈ occurrenceInterval m j`) sums over preceding target blocks. -/
private theorem sum_smul_blockOperator_apply_standardVector (c : AllowedPair m → ℂ)
    {j : Fin m.card} {a : ℤ} (ha : a ∈ occurrenceInterval m j) :
    (∑ p : AllowedPair m, c p • blockOperator m p.val.fst p.val.snd) (standardVector m j a) =
      ∑ i : Fin m.card,
        if h : (occurrenceInterval m i).Precedes (occurrenceInterval m j) then
          c (AllowedPair.mk h) • standardVector m i (a - 1)
        else 0 := by
  rw [LinearMap.coe_sum, Finset.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [sum_allowedPair (fun p ↦
    c p • blockOperator m p.val.fst p.val.snd (standardVector m j a))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single j]
  · split_ifs with h
    · simp only [blockOperator_standardVector_self i ha]
    · rfl
  · intro k _ hkj
    dsimp only
    rw [blockOperator_standardVector_of_ne i hkj.symm]
    split_ifs <;> simp
  · intro hjmem
    exact absurd (Finset.mem_univ j) hjmem

/-- Every element of `(standardPair m .up).centralizer` acts on `standardVector m j a` via its
cut-entry coordinates `centralizerCoord`. -/
private theorem centralizer_apply_standardVector_coord
    (L : (standardPair m .up).centralizer) {j : Fin m.card} {a : ℤ}
    (ha : a ∈ occurrenceInterval m j) :
    (L : Module.End ℂ (standardSpace m).Carrier) (standardVector m j a) =
      ∑ i : Fin m.card,
        if h : (occurrenceInterval m i).Precedes (occurrenceInterval m j) then
          centralizerCoord (L : Module.End ℂ (standardSpace m).Carrier) (AllowedPair.mk h) •
            standardVector m i (a - 1)
        else 0 := by
  rw [expand_of_isHomogeneous (GradedPair.isHomogeneous_coe_centralizer L) ha]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : (occurrenceInterval m i).Precedes (occurrenceInterval m j)
  · simp only [h, ↓reduceDIte]
    by_cases haI : a - 1 ∈ occurrenceInterval m i
    · rw [blockEntry_eq_fst_of_precedes L h ha haI,
        blockEntry_of_mem (Set.left_mem_Icc.mpr (occurrenceInterval m j).fst_le_snd)
          h.fst_sub_one_mem]
      rfl
    · simp [standardVector_of_notMem haI]
  · simp [h, blockEntry_eq_zero_of_not_precedes L h a]

/-- Left-inverse law for `centralizerEquivCoords`: reconstructing `L` from its cut entries. -/
private theorem sum_blockOperator_centralizer_eq (L : (standardPair m .up).centralizer) :
    (∑ p : AllowedPair m,
        centralizerCoord (L : Module.End ℂ (standardSpace m).Carrier) p •
          blockOperator m p.val.fst p.val.snd) = L := by
  refine (standardBasis m).ext fun x ↦ ?_
  rw [standardBasis_eq_standardVector,
    sum_smul_blockOperator_apply_standardVector _ x.mem_occurrenceInterval,
    centralizer_apply_standardVector_coord L x.mem_occurrenceInterval]

/-- Right-inverse law for `centralizerEquivCoords`: extracting the cut entry at `p` from
`∑ q, c q • blockOperator m q.1 q.2`. -/
private theorem repr_sum_smul_blockOperator (c : AllowedPair m → ℂ) (p : AllowedPair m) :
    centralizerCoord (∑ q : AllowedPair m, c q • blockOperator m q.val.fst q.val.snd) p = c p := by
  rw [centralizerCoord, LinearMap.coe_sum, Finset.sum_apply, map_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finset.sum_eq_single p]
  · rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
      blockOperator_standardVector_self p.val.fst
        (Set.left_mem_Icc.mpr (occurrenceInterval m p.val.snd).fst_le_snd),
      standardBasis_repr_standardVector_same_deg p.property.fst_sub_one_mem]
    simp
  · intro q _ hqp
    rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hqs : q.val.snd = p.val.snd
    · have hqf : q.val.fst ≠ p.val.fst := fun hqf ↦
        hqp (Subtype.ext (Prod.ext hqf hqs))
      rw [blockOperator_standardVector_of_mem
        (Set.left_mem_Icc.mpr (occurrenceInterval m p.val.snd).fst_le_snd)]
      split_ifs with heq
      · rw [standardBasis_repr_standardVector_same_deg p.property.fst_sub_one_mem]
        simp [hqf]
      · exact absurd hqs.symm heq
    · rw [blockOperator_standardVector_of_ne q.val.fst (Ne.symm hqs), map_zero,
        Finsupp.coe_zero, Pi.zero_apply, mul_zero]
  · intro hpmem
    exact absurd (Finset.mem_univ p) hpmem

variable (m) in
/-- Coordinate equivalence identifying `(standardPair m .up).centralizer` with functions on
`AllowedPair m`. -/
noncomputable def centralizerEquivCoords :
    (standardPair m .up).centralizer ≃ₗ[ℂ] (AllowedPair m → ℂ) where
  toFun L := centralizerCoord (L : Module.End ℂ (standardSpace m).Carrier)
  map_add' L₁ L₂ := funext fun p ↦ by simp [centralizerCoord]
  map_smul' c L := funext fun p ↦ by simp [centralizerCoord]
  invFun c :=
    ⟨∑ p : AllowedPair m, c p • blockOperator m p.val.fst p.val.snd,
      Submodule.sum_mem _ fun p _ ↦
        Submodule.smul_mem _ _ (blockOperator_mem_centralizer p.property)⟩
  left_inv L := Subtype.ext (sum_blockOperator_centralizer_eq L)
  right_inv c := funext (repr_sum_smul_blockOperator c)

/-- Extracting the coordinate at `p = (i, j)` evaluates `L` on the left-endpoint standard vector
of source block `j` and reads the cut entry at `(i, j.fst - 1)`. -/
@[simp]
theorem centralizerEquivCoords_apply (L : (standardPair m .up).centralizer) (p : AllowedPair m) :
    centralizerEquivCoords m L p =
      (standardBasis m).repr
        ((L : Module.End ℂ (standardSpace m).Carrier)
          (standardVector m p.val.snd (occurrenceInterval m p.val.snd).fst))
        (StandardIndex.mk p.val.fst ((occurrenceInterval m p.val.snd).fst - 1)
          p.property.fst_sub_one_mem) :=
  (rfl)

/-- Reconstructing a centralizer element from a coordinate function `c` yields the weighted sum
of `blockOperator m p.val.fst p.val.snd` over all allowed pairs `p`. -/
@[simp]
theorem coe_centralizerEquivCoords_symm_apply (c : AllowedPair m → ℂ) :
    ((centralizerEquivCoords m).symm c : Module.End ℂ (standardSpace m).Carrier) =
      ∑ p : AllowedPair m, c p • blockOperator m p.val.fst p.val.snd :=
  (rfl)

open Classical in
/-- Every basis coordinate function `Pi.single p 1` corresponds under `centralizerEquivCoords` to
the commuting block operator `blockOperator m p.val.fst p.val.snd`. -/
theorem coe_centralizerEquivCoords_symm_single (p : AllowedPair m) :
    ((centralizerEquivCoords m).symm (Pi.single p 1) :
        Module.End ℂ (standardSpace m).Carrier) =
      blockOperator m p.val.fst p.val.snd := by
  simp

/-- Every element of `(standardPair m .up).centralizer` acts on standard vectors by its block
coordinates along allowed pairs. -/
theorem centralizer_standardPair_up_apply_standardVector (L : (standardPair m .up).centralizer)
    {j : Fin m.card} {a : ℤ} (ha : a ∈ occurrenceInterval m j) :
    (L : Module.End ℂ (standardSpace m).Carrier) (standardVector m j a) =
      ∑ i : Fin m.card,
        if h : (occurrenceInterval m i).Precedes (occurrenceInterval m j) then
          centralizerEquivCoords m L (AllowedPair.mk h) • standardVector m i (a - 1)
        else 0 := by
  exact centralizer_apply_standardVector_coord L ha

private theorem standardBasis_repr_standardVector_of_deg_eq {i : Fin m.card} {a : ℤ}
    {y : StandardIndex m} (hy : (y.2 : ℤ) = a) :
    (standardBasis m).repr (standardVector m i a) y = if i = y.1 then 1 else 0 := by
  have hya : a ∈ occurrenceInterval m y.1 := hy ▸ y.mem_occurrenceInterval
  have hyeq : y = StandardIndex.mk y.1 a hya := by
    simp [Sigma.subtype_ext_iff, hy]
  conv_lhs => rw [hyeq, standardBasis_repr_standardVector_same_deg hya]

open Classical in
/-- Cut-entry formula for `(standardPair m .up).centralizer` in `standardBasis m`: the `(y, x)`
matrix entry of `L` is nonzero only when `y` has degree `x.2 - 1` and interval `y.1` precedes
interval `x.1`, in which case it equals `centralizerEquivCoords m L (AllowedPair.mk h)`. -/
theorem standardBasis_repr_centralizer_apply (L : (standardPair m .up).centralizer)
    (x y : StandardIndex m) :
    (standardBasis m).repr
        ((L : Module.End ℂ (standardSpace m).Carrier) (standardBasis m x)) y =
      if (y.2 : ℤ) = (x.2 : ℤ) - 1 then
        if h : (occurrenceInterval m y.1).Precedes (occurrenceInterval m x.1) then
          centralizerEquivCoords m L (AllowedPair.mk h)
        else 0
      else 0 := by
  rw [standardBasis_eq_standardVector,
    centralizer_standardPair_up_apply_standardVector L x.mem_occurrenceInterval,
    map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases hy : (y.2 : ℤ) = (x.2 : ℤ) - 1
  · simp only [hy, ↓reduceIte]
    rw [Finset.sum_eq_single y.1]
    · split_ifs <;> simp [standardBasis_repr_standardVector_of_deg_eq hy]
    · intro i _ hiy
      split_ifs
      · simp [standardBasis_repr_standardVector_of_deg_eq hy, hiy]
      · simp
    · intro hymem
      exact absurd (Finset.mem_univ y.1) hymem
  · simp only [hy, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    split_ifs
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← StandardIndex.mk_fst_snd y,
        standardBasis_repr_standardVector_eq_zero_of_degree_ne (Ne.symm hy)
          y.mem_occurrenceInterval, mul_zero]
    · simp

/-- The dimension of `(standardPair m .up).centralizer` equals the number of allowed interval
pairs of `m`. -/
theorem finrank_centralizer_standardPair_up (m : Multisegment) :
    Module.finrank ℂ (standardPair m .up).centralizer = Fintype.card (AllowedPair m) := by
  rw [(centralizerEquivCoords m).finrank_eq, Module.finrank_pi]

/-- `(standardPair m .up).centralizer` is trivial if and only if `m` has no allowed pairs. -/
theorem centralizer_standardPair_up_eq_bot_iff (m : Multisegment) :
    (standardPair m .up).centralizer = ⊥ ↔ IsEmpty (AllowedPair m) := by
  have : Module.Finite ℂ (standardPair m .up).centralizer :=
    Module.Finite.equiv (centralizerEquivCoords m).symm
  rw [← Submodule.finrank_eq_zero, finrank_centralizer_standardPair_up, Fintype.card_eq_zero_iff]

/-- The centralizer of the zero multisegment's standard raising pair is trivial. -/
@[simp]
theorem centralizer_standardPair_up_zero :
    (standardPair (0 : Multisegment) .up).centralizer = ⊥ := by
  refine (centralizer_standardPair_up_eq_bot_iff 0).2 ⟨fun p ↦ ?_⟩
  exact Fin.elim0 p.val.fst

/-- The centralizer of a single-interval multisegment's standard raising pair is trivial. -/
@[simp]
theorem centralizer_standardPair_up_singleton (s : IntInterval) :
    (standardPair ({s} : Multisegment) .up).centralizer = ⊥ := by
  refine (centralizer_standardPair_up_eq_bot_iff {s}).2 ⟨fun p ↦ ?_⟩
  have hcard : ({s} : Multisegment).card = 1 := Multiset.card_singleton s
  have heq : p.val.fst = p.val.snd := by
    omega
  exact IntInterval.precedes_irrefl _ (heq ▸ p.property)

end Multisegment

end TauCeti
