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

* `TauCeti.IntInterval.Precedes`: the strict precedence relation `s.fst < t.fst ≤ s.snd + 1 ≤ t.snd`
  on integral intervals.
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
* `TauCeti.Multisegment.centralizer_standardPair_up_singleton_interval`: for a single interval, the
  centralizer of `({s} : Multisegment).standardPair .up` is trivial.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1 and Lemma 3.2.
* C. Mœglin, J.-L. Waldspurger, *Sur l'involution de Zelevinski*, J. reine angew. Math. 372
  (1986), 136–177, §II.1.
-/

public section

open Module

namespace TauCeti

/-! ### Interval precedence -/

namespace IntInterval

/-- An integral interval `s = [b, e]` precedes `t = [b', e']` when `b < b' ≤ e + 1 ≤ e'`. -/
def Precedes (s t : IntInterval) : Prop :=
  s.fst < t.fst ∧ t.fst ≤ s.snd + 1 ∧ s.snd + 1 ≤ t.snd

instance : DecidableRel Precedes := fun s t ↦
  inferInstanceAs (Decidable (s.fst < t.fst ∧ t.fst ≤ s.snd + 1 ∧ s.snd + 1 ≤ t.snd))

theorem precedes_def {s t : IntInterval} :
    s.Precedes t ↔ s.fst < t.fst ∧ t.fst ≤ s.snd + 1 ∧ s.snd + 1 ≤ t.snd :=
  Iff.rfl

theorem precedes_irrefl (s : IntInterval) : ¬ s.Precedes s := by
  intro h
  exact lt_irrefl _ h.1

theorem precedes_asymm {s t : IntInterval} (h : s.Precedes t) : ¬ t.Precedes s := by
  intro h'
  exact lt_asymm h.1 h'.1

namespace Precedes

theorem fst_lt {s t : IntInterval} (h : s.Precedes t) : s.fst < t.fst :=
  h.1

theorem snd_lt {s t : IntInterval} (h : s.Precedes t) : s.snd < t.snd := by
  have := h.2.2
  omega

/-- The cut degree `t.fst - 1` lies in `s` whenever `s` precedes `t`. -/
theorem fst_sub_one_mem {s t : IntInterval} (h : s.Precedes t) : t.fst - 1 ∈ s := by
  rw [NonemptyInterval.mem_def]
  have := h.1
  have := h.2.1
  omega

/-- The step above `s.snd` lies in `t` whenever `s` precedes `t`. -/
theorem snd_add_one_mem {s t : IntInterval} (h : s.Precedes t) : s.snd + 1 ∈ t := by
  rw [NonemptyInterval.mem_def]
  have := h.2.1
  have := h.2.2
  omega

end Precedes

@[simp]
theorem precedes_shift_iff {s t : IntInterval} {c : ℤ} :
    (s.shift c).Precedes (t.shift c) ↔ s.Precedes t := by
  simp only [precedes_def, fst_shift, snd_shift]
  omega

end IntInterval

/-! ### Allowed pairs and commuting block operators -/

namespace Multisegment

variable (m : Multisegment)

/-- Ordered pairs `(i, j)` of occurrence labels of `m` for which the target interval `i` strictly
precedes the source interval `j`. -/
abbrev AllowedPair : Type :=
  {p : Fin m.card × Fin m.card // (m.occurrenceInterval p.1).Precedes (m.occurrenceInterval p.2)}

open Classical in
noncomputable instance : Fintype (AllowedPair m) :=
  Subtype.fintype _

/-- Constructor for `Multisegment.AllowedPair`. -/
abbrev AllowedPair.mk {m : Multisegment} {i j : Fin m.card}
    (h : (m.occurrenceInterval i).Precedes (m.occurrenceInterval j)) : AllowedPair m :=
  ⟨(i, j), h⟩

/-- The target occurrence has interval preceding the source occurrence. -/
theorem AllowedPair.precedes {m : Multisegment} (p : AllowedPair m) :
    (m.occurrenceInterval p.val.fst).Precedes (m.occurrenceInterval p.val.snd) :=
  p.property

/-- The degree-`-1` block shift operator sending each standard vector `(j, a)` of block `j` to
`(i, a - 1)` in block `i`, and killing all other occurrence blocks. -/
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
        have h2 := h.2.2
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
  have hj : (occurrenceInterval m j).fst ∈ occurrenceInterval m j :=
    NonemptyInterval.mem_def.2 ⟨le_rfl, (occurrenceInterval m j).fst_le_snd⟩
  have hv := congrFun (congrArg DFunLike.coe h0)
    (standardVector m j (occurrenceInterval m j).fst)
  rw [blockOperator_standardVector_self i hj, LinearMap.zero_apply,
    standardVector_eq_zero_iff] at hv
  exact hv h.fst_sub_one_mem

/-! ### Block entry extraction and constancy along the overlap -/

private theorem standardBasis_repr_standardVector_same_deg {i' i : Fin m.card} {b : ℤ}
    (hb : b ∈ occurrenceInterval m i) :
    (standardBasis m).repr (standardVector m i' b) (StandardIndex.mk i b hb) =
      if i' = i then 1 else 0 := by
  by_cases heq : i' = i
  · subst heq
    simp [standardVector_of_mem hb]
  · by_cases hb' : b ∈ occurrenceInterval m i'
    · simp [standardVector_of_mem hb', Sigma.subtype_ext_iff, heq]
    · simp [standardVector_of_notMem hb', heq]

private theorem standardBasis_repr_standardVector_of_ne {i' i : Fin m.card} {a b : ℤ}
    (hab : a ≠ b) (hb : b ∈ occurrenceInterval m i) :
    (standardBasis m).repr (standardVector m i' a) (StandardIndex.mk i b hb) = 0 := by
  by_cases ha : a ∈ occurrenceInterval m i'
  · rw [standardVector_of_mem ha, Basis.repr_self_apply]
    simp [Sigma.subtype_ext_iff, hab]
  · rw [standardVector_of_notMem ha, map_zero, Finsupp.coe_zero, Pi.zero_apply]

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

private theorem centralizer_blockEntry_step_eq (L : (standardPair m .up).centralizer)
    {i j : Fin m.card} {a : ℤ}
    (haJ : a ∈ occurrenceInterval m j) (haI : a ∈ occurrenceInterval m i) :
    (if a - 1 ∈ occurrenceInterval m i then blockEntry m L i j a else 0) =
      (if a + 1 ∈ occurrenceInterval m j then blockEntry m L i j (a + 1) else 0) := by
  have hhom := GradedPair.centralizer_isHomogeneous L
  have hcomm : (standardPair m .up).operator ((L : Module.End ℂ (standardSpace m).Carrier)
      (standardVector m j a)) =
      (L : Module.End ℂ (standardSpace m).Carrier)
        ((standardPair m .up).operator (standardVector m j a)) :=
    (GradedPair.centralizer_operator_apply L (standardVector m j a)).symm
  have hNL := congrArg (fun v ↦ (standardBasis m).repr v (StandardIndex.mk i a haI)) hcomm
  have lhs_eq :
      (standardBasis m).repr
          ((standardPair m .up).operator ((L : Module.End ℂ (standardSpace m).Carrier)
            (standardVector m j a))) (StandardIndex.mk i a haI) =
        if a - 1 ∈ occurrenceInterval m i then blockEntry m L i j a else 0 := by
    rw [expand_of_isHomogeneous hhom haJ, map_sum, map_sum, Finsupp.coe_finsetSum,
      Finset.sum_apply]
    have hterm (k : Fin m.card) :
        (standardBasis m).repr
            (blockEntry m L k j a •
              (standardPair m .up).operator (standardVector m k (a - 1)))
            (StandardIndex.mk i a haI) =
          if k = i ∧ a - 1 ∈ occurrenceInterval m i then blockEntry m L i j a else 0 := by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      by_cases hk : a - 1 ∈ occurrenceInterval m k
      · rw [standardPair_operator_standardVector .up hk, StepDirection.step_up, sub_add_cancel,
          standardBasis_repr_standardVector_same_deg haI]
        split_ifs with hki h1 h2 <;> simp_all
      · rw [standardVector_of_notMem hk, map_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply,
          mul_zero]
        split_ifs with hcond
        · exfalso
          exact hk (hcond.1 ▸ hcond.2)
        · rfl
    simp only [LinearMap.map_smul, hterm]
    rw [Finset.sum_eq_single i] <;> simp_all
  have rhs_eq :
      (standardBasis m).repr
          ((L : Module.End ℂ (standardSpace m).Carrier)
            ((standardPair m .up).operator (standardVector m j a)))
          (StandardIndex.mk i a haI) =
        if a + 1 ∈ occurrenceInterval m j then blockEntry m L i j (a + 1) else 0 := by
    rw [standardPair_operator_standardVector .up haJ, StepDirection.step_up]
    by_cases ha1 : a + 1 ∈ occurrenceInterval m j
    · simp only [ha1, ↓reduceIte]
      rw [expand_of_isHomogeneous hhom ha1, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, add_sub_cancel_right,
        standardBasis_repr_standardVector_same_deg haI, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · simp only [ha1, ↓reduceIte, standardVector_of_notMem ha1, map_zero, Finsupp.coe_zero,
        Pi.zero_apply]
  rw [← lhs_eq, ← rhs_eq, hNL]

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
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hab)
  have hb : b = a + k := by omega
  subst hb
  clear hab hk
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have ha1J : a + 1 ∈ occurrenceInterval m j := by
      rw [NonemptyInterval.mem_def] at haJ hbJ ⊢
      omega
    have haI' : a ∈ occurrenceInterval m i := by
      rw [NonemptyInterval.mem_def] at haI hbI ⊢
      omega
    have heq : a + ↑(k + 1) = (a + 1) + k := by
      push_cast
      ring
    rw [heq]
    exact (ih ha1J (by simpa only [add_sub_cancel_right] using haI')
      (by rwa [← heq]) (by rwa [← heq])).trans (blockEntry_succ_eq L haJ ha1J haI haI')

private theorem blockEntry_fst_add_one_eq_zero (L : (standardPair m .up).centralizer)
    {i j : Fin m.card}
    (h1 : (occurrenceInterval m i).fst ∈ occurrenceInterval m j)
    (h2 : (occurrenceInterval m i).fst + 1 ∈ occurrenceInterval m j) :
    blockEntry m L i j ((occurrenceInterval m i).fst + 1) = 0 := by
  have hI : (occurrenceInterval m i).fst ∈ occurrenceInterval m i :=
    NonemptyInterval.mem_def.2 ⟨le_rfl, (occurrenceInterval m i).fst_le_snd⟩
  have hnot : (occurrenceInterval m i).fst - 1 ∉ occurrenceInterval m i := by
    rw [NonemptyInterval.mem_def]
    omega
  have h := centralizer_blockEntry_step_eq L h1 hI
  simpa only [hnot, ↓reduceIte, h2] using h.symm

private theorem blockEntry_snd_eq_zero (L : (standardPair m .up).centralizer)
    {i j : Fin m.card}
    (h1 : (occurrenceInterval m j).snd - 1 ∈ occurrenceInterval m i)
    (h2 : (occurrenceInterval m j).snd ∈ occurrenceInterval m i) :
    blockEntry m L i j (occurrenceInterval m j).snd = 0 := by
  have hJ : (occurrenceInterval m j).snd ∈ occurrenceInterval m j :=
    NonemptyInterval.mem_def.2 ⟨(occurrenceInterval m j).fst_le_snd, le_rfl⟩
  have hnot : (occurrenceInterval m j).snd + 1 ∉ occurrenceInterval m j := by
    rw [NonemptyInterval.mem_def]
    omega
  have h := centralizer_blockEntry_step_eq L hJ h2
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
      have hJ : (occurrenceInterval m j).snd ∈ occurrenceInterval m j :=
        NonemptyInterval.mem_def.2 ⟨(occurrenceInterval m j).fst_le_snd, le_rfl⟩
      rw [← blockEntry_eq_of_le L haJ'.2 haJ haI hJ h1, blockEntry_snd_eq_zero L h1 h2]
    · have h1 : (occurrenceInterval m i).fst ∈ occurrenceInterval m j := by
        rw [NonemptyInterval.mem_def]
        omega
      have h2 : (occurrenceInterval m i).fst + 1 ∈ occurrenceInterval m j := by
        rw [NonemptyInterval.mem_def]
        omega
      have hI : (occurrenceInterval m i).fst ∈ occurrenceInterval m i :=
        NonemptyInterval.mem_def.2 ⟨le_rfl, (occurrenceInterval m i).fst_le_snd⟩
      have heq := blockEntry_eq_of_le L (by omega) h2
        (by simpa only [add_sub_cancel_right] using hI) haJ haI
      rw [heq, blockEntry_fst_add_one_eq_zero L h1 h2]
  · by_cases hj : a ∈ occurrenceInterval m j
    · exact blockEntry_of_notMem_target (fun hi ↦ ha ⟨hj, hi⟩)
    · exact blockEntry_of_notMem_source hj

private theorem blockEntry_eq_fst_of_precedes (L : (standardPair m .up).centralizer)
    {i j : Fin m.card} (h : (occurrenceInterval m i).Precedes (occurrenceInterval m j))
    {a : ℤ} (haJ : a ∈ occurrenceInterval m j) (haI : a - 1 ∈ occurrenceInterval m i) :
    blockEntry m L i j a = blockEntry m L i j (occurrenceInterval m j).fst := by
  have hjfst : (occurrenceInterval m j).fst ∈ occurrenceInterval m j :=
    NonemptyInterval.mem_def.2 ⟨le_rfl, (occurrenceInterval m j).fst_le_snd⟩
  exact blockEntry_eq_of_le L (NonemptyInterval.mem_def.1 haJ).1
    hjfst h.fst_sub_one_mem haJ haI

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
  let P : Fin m.card × Fin m.card → Prop := fun p ↦
    (occurrenceInterval m p.1).Precedes (occurrenceInterval m p.2)
  have hsub := Fintype.sum_subtype_add_sum_subtype P
    (fun p ↦ if h : P p then f ⟨p, h⟩ else 0)
  have h1 : (∑ p : {p // P p}, if h : P p.val then f ⟨p.val, h⟩ else 0) =
      ∑ p : AllowedPair m, f p :=
    Finset.sum_congr rfl fun p _ ↦ by simp [p.property]
  have h2 : (∑ p : {p // ¬ P p}, if h : P p.val then f ⟨p.val, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun p _ ↦ by simp [p.property]
  rw [h1, h2, add_zero] at hsub
  rw [hsub, ← Fintype.sum_prod_type']

private theorem centralizer_apply_standardVector_blockEntry
    (L : (standardPair m .up).centralizer) {j : Fin m.card} {a : ℤ}
    (ha : a ∈ occurrenceInterval m j) :
    (L : Module.End ℂ (standardSpace m).Carrier) (standardVector m j a) =
      ∑ i : Fin m.card,
        if h : (occurrenceInterval m i).Precedes (occurrenceInterval m j) then
          (standardBasis m).repr
              ((L : Module.End ℂ (standardSpace m).Carrier)
                (standardVector m j (occurrenceInterval m j).fst))
              (StandardIndex.mk i ((occurrenceInterval m j).fst - 1) h.fst_sub_one_mem) •
            standardVector m i (a - 1)
        else 0 := by
  rw [expand_of_isHomogeneous (GradedPair.centralizer_isHomogeneous L) ha]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : (occurrenceInterval m i).Precedes (occurrenceInterval m j)
  · simp only [h, ↓reduceDIte]
    by_cases haI : a - 1 ∈ occurrenceInterval m i
    · have hj : (occurrenceInterval m j).fst ∈ occurrenceInterval m j :=
        NonemptyInterval.mem_def.2 ⟨le_rfl, (occurrenceInterval m j).fst_le_snd⟩
      rw [blockEntry_eq_fst_of_precedes L h ha haI, blockEntry_of_mem hj h.fst_sub_one_mem]
    · simp [standardVector_of_notMem haI]
  · simp [h, blockEntry_eq_zero_of_not_precedes L h a]

variable (m) in
/-- Coordinate equivalence identifying `(standardPair m .up).centralizer` with functions on
`AllowedPair m`. -/
@[expose]
noncomputable def centralizerEquivCoords :
    (standardPair m .up).centralizer ≃ₗ[ℂ] (AllowedPair m → ℂ) where
  toFun L p :=
    (standardBasis m).repr
      ((L : Module.End ℂ (standardSpace m).Carrier)
        (standardVector m p.val.snd (occurrenceInterval m p.val.snd).fst))
      (StandardIndex.mk p.val.fst ((occurrenceInterval m p.val.snd).fst - 1)
        p.property.fst_sub_one_mem)
  map_add' L₁ L₂ := funext fun p ↦ by simp
  map_smul' c L := funext fun p ↦ by simp
  invFun c :=
    ⟨∑ p : AllowedPair m, c p • blockOperator m p.val.fst p.val.snd,
      Submodule.sum_mem _ fun p _ ↦
        Submodule.smul_mem _ _ (blockOperator_mem_centralizer p.property)⟩
  left_inv L := by
    refine Subtype.ext ((standardBasis m).ext fun x ↦ ?_)
    rw [standardBasis_eq_standardVector]
    have hx : (x.2 : ℤ) ∈ occurrenceInterval m x.1 := x.mem_occurrenceInterval
    rw [LinearMap.coe_sum, Finset.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [sum_allowedPair (fun p ↦
      (standardBasis m).repr
          ((L : Module.End ℂ (standardSpace m).Carrier)
            (standardVector m p.val.snd (occurrenceInterval m p.val.snd).fst))
          (StandardIndex.mk p.val.fst ((occurrenceInterval m p.val.snd).fst - 1)
            p.property.fst_sub_one_mem) •
        blockOperator m p.val.fst p.val.snd (standardVector m x.1 x.2)),
      centralizer_apply_standardVector_blockEntry L hx]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single x.1]
    · split_ifs with hp
      · dsimp only
        rw [blockOperator_standardVector_self i hx]
      · rfl
    · intro j _ hjx
      dsimp only
      rw [blockOperator_standardVector_of_ne i hjx.symm]
      split_ifs <;> simp
    · intro hxmem
      exact absurd (Finset.mem_univ x.1) hxmem
  right_inv c := by
    ext p
    dsimp only
    rw [LinearMap.coe_sum, Finset.sum_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finset.sum_eq_single p]
    · have hj : (occurrenceInterval m p.val.snd).fst ∈ occurrenceInterval m p.val.snd :=
        NonemptyInterval.mem_def.2 ⟨le_rfl, (occurrenceInterval m p.val.snd).fst_le_snd⟩
      rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
        blockOperator_standardVector_self p.val.fst hj,
        standardBasis_repr_standardVector_same_deg p.property.fst_sub_one_mem]
      simp
    · intro q _ hqp
      rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
      by_cases hqs : q.val.snd = p.val.snd
      · have hj : (occurrenceInterval m p.val.snd).fst ∈ occurrenceInterval m p.val.snd :=
          NonemptyInterval.mem_def.2 ⟨le_rfl, (occurrenceInterval m p.val.snd).fst_le_snd⟩
        have hqf : q.val.fst ≠ p.val.fst := fun hqf ↦
          hqp (Subtype.ext (Prod.ext hqf hqs))
        rw [blockOperator_standardVector_of_mem hj]
        split_ifs with heq
        · rw [standardBasis_repr_standardVector_same_deg p.property.fst_sub_one_mem]
          simp [hqf]
        · exact absurd hqs.symm heq
      · rw [blockOperator_standardVector_of_ne q.val.fst (Ne.symm hqs), map_zero,
          Finsupp.coe_zero, Pi.zero_apply, mul_zero]
    · intro hpmem
      exact absurd (Finset.mem_univ p) hpmem

@[simp]
theorem centralizerEquivCoords_apply (L : (standardPair m .up).centralizer) (p : AllowedPair m) :
    centralizerEquivCoords m L p =
      (standardBasis m).repr
        ((L : Module.End ℂ (standardSpace m).Carrier)
          (standardVector m p.val.snd (occurrenceInterval m p.val.snd).fst))
        (StandardIndex.mk p.val.fst ((occurrenceInterval m p.val.snd).fst - 1)
          p.property.fst_sub_one_mem) :=
  rfl

@[simp]
theorem coe_centralizerEquivCoords_symm_apply (c : AllowedPair m → ℂ) :
    ((centralizerEquivCoords m).symm c : Module.End ℂ (standardSpace m).Carrier) =
      ∑ p : AllowedPair m, c p • blockOperator m p.val.fst p.val.snd :=
  rfl

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
        else 0 :=
  centralizer_apply_standardVector_blockEntry L ha

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
    have hyi : (x.2 : ℤ) - 1 ∈ occurrenceInterval m y.1 := hy ▸ y.mem_occurrenceInterval
    have hyeq : y = StandardIndex.mk y.1 ((x.2 : ℤ) - 1) hyi := by
      simp [Sigma.subtype_ext_iff, hy]
    rw [Finset.sum_eq_single y.1]
    · split_ifs with h
      · conv_lhs => rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
          show (standardBasis m).repr (standardVector m y.1 ((x.2 : ℤ) - 1)) y = 1 by
            rw [hyeq, standardBasis_repr_standardVector_same_deg hyi]; simp]
        simp
      · simp
    · intro i _ hiy
      split_ifs
      · rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
          show (standardBasis m).repr (standardVector m i ((x.2 : ℤ) - 1)) y = 0 by
            rw [hyeq, standardBasis_repr_standardVector_same_deg hyi]; simp [hiy],
          mul_zero]
      · simp
    · intro hymem
      exact absurd (Finset.mem_univ y.1) hymem
  · simp only [hy, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    split_ifs
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← StandardIndex.mk_fst_snd y,
        standardBasis_repr_standardVector_of_ne (Ne.symm hy) y.mem_occurrenceInterval, mul_zero]
    · simp

/-- The dimension of `(standardPair m .up).centralizer` equals the number of allowed interval
pairs of `m`. -/
theorem finrank_centralizer_standardPair_up (m : Multisegment) :
    Module.finrank ℂ (standardPair m .up).centralizer = Fintype.card (AllowedPair m) := by
  rw [(centralizerEquivCoords m).finrank_eq, Module.finrank_pi]

/-- `(standardPair m .up).centralizer` is trivial if and only if `m` has no allowed pairs. -/
theorem centralizer_standardPair_up_eq_bot_iff (m : Multisegment) :
    (standardPair m .up).centralizer = ⊥ ↔ IsEmpty (AllowedPair m) := by
  constructor
  · intro hbot
    rw [← Fintype.card_eq_zero_iff, ← finrank_centralizer_standardPair_up, hbot, finrank_bot]
  · intro hempty
    have : Subsingleton (AllowedPair m → ℂ) := inferInstance
    have : Subsingleton (standardPair m .up).centralizer :=
      (centralizerEquivCoords m).toEquiv.subsingleton
    exact (Submodule.eq_bot_iff _).2 fun x hx ↦
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : (standardPair m .up).centralizer) 0)

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
