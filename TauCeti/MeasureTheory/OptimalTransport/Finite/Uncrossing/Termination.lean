/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Prod.Lex
public import TauCeti.MeasureTheory.OptimalTransport.Finite.Monotone

/-!
# Finite uncrossing of transportation matrices

Every transportation matrix on finite linear orders can be transformed into the monotone
matrix by finitely many four-cell transfers of the smaller crossing mass. The strategy
processes corners in row-major order. At a fixed corner, every transfer removes a positive
entry from its row to the right or its column below, without creating another such entry.
Once that corner is settled, subsequent corners preserve it.

This proves termination of this pivot strategy for arbitrary nonnegative real probability
masses. It makes no termination claim for arbitrary choices of crossing pairs. Every transfer
decreases any Monge cost weakly, so the finite sequence also gives a cost comparison with its
endpoint. The main result is `TransportMatrix.exists_uncrossSteps_isMonotone`; the uncrossing
relation and its cost comparison lemmas are defined in `Uncrossing.Basic`.
-/

public section

noncomputable section

namespace TauCeti.TransportMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : PMF ι} {ν : PMF κ}

variable [LinearOrder ι] [LinearOrder κ]

/-- A settled corner has no crossing pair in its row to the right and column below. -/
private def Settled (A : TransportMatrix μ ν) (q : ι × κ) : Prop :=
  ∀ i j, q.1 < i → q.2 < j →
    A.toRealFun (q.1, j) = 0 ∨ A.toRealFun (i, q.2) = 0

/-- The positive entries in the two crossing arms of a corner. -/
private def arms (A : TransportMatrix μ ν) (q : ι × κ) : Finset (ι × κ) :=
  Finset.univ.filter fun p ↦
    (p.1 = q.1 ∧ q.2 < p.2 ∨ q.1 < p.1 ∧ p.2 = q.2) ∧ 0 < A.toRealFun p

private theorem exists_pivot_step (A : TransportMatrix μ ν) (q : ι × κ)
    (h : ¬ Settled A q) :
    ∃ B : TransportMatrix μ ν, A.UncrossStep B ∧
      (arms B q).card < (arms A q).card ∧
      ∀ p, toLex p < toLex q → Settled A p → Settled B p := by
  classical
  rcases q with ⟨a, b⟩
  obtain ⟨i, j, hi, hj, hrow, hcol⟩ :
      ∃ i j, a < i ∧ b < j ∧
        0 < A.toRealFun (a, j) ∧ 0 < A.toRealFun (i, b) := by
    obtain ⟨i, j, hi, hj, hr, hc⟩ := by
      simpa only [Settled, not_forall, not_imp, not_or] using h
    exact ⟨i, j, hi, hj, lt_of_le_of_ne (A.toRealFun_nonneg _) (Ne.symm hr),
      lt_of_le_of_ne (A.toRealFun_nonneg _) (Ne.symm hc)⟩
  obtain ⟨B, δ, _, hδ, hB, -, -, hz, -⟩ :=
    A.exists_uncross_cost_le (fun _ ↦ 0) hi.ne hj.ne (by simp)
  have hδpos : 0 < δ := hδ ▸ lt_min hrow hcol
  have hstep : A.UncrossStep B := by
    rw [uncrossStep_iff]
    exact ⟨a, i, b, j, δ, hi, hj, hδpos, hδ, hB⟩
  -- The two arms acquire no new positive entries, and at least one source is emptied.
  have harm (p : ι × κ)
      (hp : p.1 = a ∧ b < p.2 ∨ a < p.1 ∧ p.2 = b) :
      B.toRealFun p ≤ A.toRealFun p := by
    rw [hB]
    rcases p with ⟨r, s⟩
    dsimp only at hp
    rcases hp with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · subst r
      by_cases hsj : s = j
      · subst s
        simp [Prod.mk.injEq, hi.ne, hj.ne.symm]
        linarith
      · simp [Prod.mk.injEq, hi.ne, hs.ne.symm, hsj]
    · subst s
      by_cases hri : r = i
      · subst r
        simp [Prod.mk.injEq, hi.ne.symm, hj.ne]
        linarith
      · simp [Prod.mk.injEq, hr.ne.symm, hri, hj.ne]
  have hsub : arms B (a, b) ⊆ arms A (a, b) := by
    intro p hp
    obtain ⟨hp, hpos⟩ := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hpos.trans_le (harm p hp)⟩
  have hcard : (arms B (a, b)).card < (arms A (a, b)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    rcases hz with hz | hz
    · have hmem : (a, j) ∈ arms A (a, b) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨rfl, hj⟩, hrow⟩
      rw [← heq] at hmem
      have := (Finset.mem_filter.mp hmem).2.2
      rw [hz] at this
      exact lt_irrefl _ this
    · have hmem : (i, b) ∈ arms A (a, b) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hi, rfl⟩, hcol⟩
      rw [← heq] at hmem
      have := (Finset.mem_filter.mp hmem).2.2
      rw [hz] at this
      exact lt_irrefl _ this
  refine ⟨B, hstep, hcard, ?_⟩
  -- Earlier rows retain their lower-column zeros; earlier columns of this row stay fixed.
  intro p hp hsettled r s hpr hps
  rcases Prod.Lex.toLex_lt_toLex.mp hp with hp | ⟨hp, hpj⟩
  · have hunchanged : B.toRealFun (p.1, s) = A.toRealFun (p.1, s) := by
      rw [hB]
      simp [Prod.mk.injEq, hp.ne, (hp.trans hi).ne]
    rw [hunchanged]
    by_cases ha : A.toRealFun (p.1, s) = 0
    · exact Or.inl ha
    · right
      have hzero (k : ι) (hk : p.1 < k) : A.toRealFun (k, p.2) = 0 :=
        (hsettled k s hk hps).resolve_left ha
      have hpj₁ : p.2 ≠ b := by
        intro heq
        have := hzero i (hp.trans hi)
        rw [heq] at this
        linarith
      have hpj₂ : p.2 ≠ j := by
        intro heq
        have := hzero a hp
        rw [heq] at this
        linarith
      rw [hB, hzero r hpr]
      simp [Prod.mk.injEq, hpj₁, hpj₂]
  · have hzero : A.toRealFun (r, p.2) = 0 := by
      have := hsettled r j hpr (hpj.trans hj)
      have hrow' : A.toRealFun (p.1, j) ≠ 0 := by rw [hp]; exact hrow.ne'
      exact this.resolve_left hrow'
    right
    rw [hB, hzero]
    simp [Prod.mk.injEq, hpj.ne, (hpj.trans hj).ne]

private theorem exists_settled (A : TransportMatrix μ ν) (q : ι × κ) :
    ∃ B : TransportMatrix μ ν, Relation.ReflTransGen UncrossStep A B ∧ Settled B q ∧
      ∀ p, toLex p < toLex q → Settled A p → Settled B p := by
  classical
  generalize hn : (arms A q).card = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases h : Settled A q
    · exact ⟨A, .refl, h, fun _ _ hp ↦ hp⟩
    · obtain ⟨B, hstep, hcard, hpres⟩ := exists_pivot_step A q h
      obtain ⟨C, hchain, hC, hpresC⟩ := ih (arms B q).card (by omega) B rfl
      exact ⟨C, hchain.head hstep, hC, fun p hp hA ↦ hpresC p hp (hpres p hp hA)⟩

/-- The row-major prefixes containing an unsettled corner. -/
private def unsettledPrefix (A : TransportMatrix μ ν) : Finset (ι ×ₗ κ) := by
  classical
  exact Finset.univ.filter fun q ↦ ∃ p ≤ q, ¬ Settled A (ofLex p)

private theorem exists_uncrossSteps_settled (A : TransportMatrix μ ν) :
    ∃ B : TransportMatrix μ ν, Relation.ReflTransGen UncrossStep A B ∧ ∀ q, Settled B q := by
  classical
  generalize hn : (unsettledPrefix A).card = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases h : ∀ q, Settled A q
    · exact ⟨A, .refl, h⟩
    · let s : Finset (ι ×ₗ κ) := Finset.univ.filter fun p ↦ ¬ Settled A (ofLex p)
      have hs : s.Nonempty := by
        obtain ⟨q, hq⟩ := not_forall.mp h
        exact ⟨toLex q, by simp [s, hq]⟩
      let q := s.min' hs
      have hq : ¬ Settled A (ofLex q) := (Finset.mem_filter.mp (s.min'_mem hs)).2
      have hbefore (p : ι ×ₗ κ) (hp : p < q) : Settled A (ofLex p) := by
        by_contra hbad
        have hmem : p ∈ s := by simp [s, hbad]
        exact (not_le_of_gt hp) (s.min'_le p hmem)
      obtain ⟨B, hchain, hB, hpres⟩ := exists_settled A (ofLex q)
      have hthrough (p : ι ×ₗ κ) (hp : p ≤ q) : Settled B (ofLex p) := by
        rcases hp.eq_or_lt with rfl | hp
        · exact hB
        · exact hpres (ofLex p) hp (hbefore p hp)
      have hsub : unsettledPrefix B ⊆ unsettledPrefix A := by
        intro p hp
        obtain ⟨r, hrp, hr⟩ := (Finset.mem_filter.mp hp).2
        have hqr : q < r := lt_of_not_ge fun h ↦ hr (hthrough r h)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hqr.le.trans hrp, hq⟩
      have hcard : (unsettledPrefix B).card < (unsettledPrefix A).card := by
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hsub, ?_⟩
        intro heq
        have hmem : q ∈ unsettledPrefix A := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, le_rfl, hq⟩
        rw [← heq] at hmem
        obtain ⟨r, hr, hbad⟩ := (Finset.mem_filter.mp hmem).2
        exact hbad (hthrough r hr)
      obtain ⟨C, hBC, hC⟩ := ih (unsettledPrefix B).card (by omega) B rfl
      exact ⟨C, hchain.trans hBC, hC⟩

/-- Every finite transportation matrix reaches the monotone matrix by a finite sequence of
minimum-mass uncrossing steps. This asserts existence of a terminating pivot strategy;
arbitrary choices of crossing pairs are not asserted to terminate. -/
theorem exists_uncrossSteps_isMonotone (A : TransportMatrix μ ν) :
    ∃ B : TransportMatrix μ ν, Relation.ReflTransGen UncrossStep A B ∧ B.IsMonotone := by
  obtain ⟨B, hchain, hB⟩ := exists_uncrossSteps_settled A
  refine ⟨B, hchain, ?_⟩
  rw [isMonotone_iff]
  intro i₁ i₂ j₂ j₁ hi h₁ h₂
  by_contra hj
  have hj : j₁ < j₂ := lt_of_not_ge hj
  have hrow : B.toRealFun (i₁, j₂) ≠ 0 := by
    simpa only [toRealFun_apply] using (ENNReal.toReal_pos h₁ (B.apply_ne_top i₁ j₂)).ne'
  have hcol : B.toRealFun (i₂, j₁) ≠ 0 := by
    simpa only [toRealFun_apply] using (ENNReal.toReal_pos h₂ (B.apply_ne_top i₂ j₁)).ne'
  exact (hB (i₁, j₁) i₂ j₂ hi hj).elim hrow hcol

end TauCeti.TransportMatrix
