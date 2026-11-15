/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain
public import TauCeti.KnotTheory.Grid.SmallGrid.Gradings

/-!
# The bigrading of `GC⁻` on the `2 × 2` unknot grid diagram

The standard `2 × 2` unknot grid diagram `OddComponentGridDiagram.twoByTwo` has two grid states:
`GridState.twoByTwoSwap` (`= twoByTwo.1.X`) in bidegree `(0, 0)` and `GridState.twoByTwoId` in
bidegree `(-1, -1)` (`SmallGrid/Gradings.lean`). Since each polynomial variable has bidegree
`(-2, -1)`, a monomial basis element `V^e · x` has bidegree `(-2 |e|, -|e|)` when
`x = twoByTwoSwap` and `(-1 - 2 |e|, -1 - |e|)` when `x = twoByTwoId`.

Consequently, every bidegree outside the monomial cone
`{(2a, a) | a ≤ 0} ∪ {(2a + 1, a) | a < 0}` has trivial chain piece
(`bigradedChainMinusPiece_twoByTwo_eq_bot`), and every chain in bidegree `(0, 0)` is a ground-ring
multiple of the `X`-marking generator `twoByTwoSwap`
(`eq_smul_single_twoByTwoSwap_of_mem_bigradedChainMinusPiece_zero`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

/-- In the `2 × 2` unknot diagram, `V^e · twoByTwoId` has bidegree `(-1 - 2 |e|, -1 - |e|)`. -/
@[simp]
theorem monomialBidegree_twoByTwo_twoByTwoId (e : Fin 2 →₀ ℕ) :
    twoByTwo.monomialBidegree GridState.twoByTwoId e =
      (-1 - 2 * (e.degree : ℤ), -1 - (e.degree : ℤ)) := by
  have hM := congrArg Prod.fst bidegree_twoByTwo_twoByTwoId
  have hA := congrArg Prod.snd bidegree_twoByTwo_twoByTwoId
  rw [bidegree_fst] at hM
  rw [bidegree_snd] at hA
  exact Prod.ext (by simp only [monomialBidegree_fst, hM])
    (by simp only [monomialBidegree_snd, hA])

/-- In the `2 × 2` unknot diagram, `V^e · twoByTwoSwap` has bidegree `(-2 |e|, -|e|)`. -/
@[simp]
theorem monomialBidegree_twoByTwo_twoByTwoSwap (e : Fin 2 →₀ ℕ) :
    twoByTwo.monomialBidegree GridState.twoByTwoSwap e =
      (-2 * (e.degree : ℤ), -(e.degree : ℤ)) := by
  have hM := congrArg Prod.fst bidegree_twoByTwo_twoByTwoSwap
  have hA := congrArg Prod.snd bidegree_twoByTwo_twoByTwoSwap
  rw [bidegree_fst] at hM
  rw [bidegree_snd] at hA
  refine Prod.ext ?_ ?_
  · simp only [monomialBidegree_fst, hM]
    omega
  · simp only [monomialBidegree_snd, hA]
    omega

variable (R : Type*) [CommSemiring R]

/-- On the `2 × 2` unknot diagram, every bidegree outside the monomial cone of the two states
`(0, 0)` and `(-1, -1)` has trivial chain piece. -/
theorem bigradedChainMinusPiece_twoByTwo_eq_bot {g : ℤ × ℤ}
    (hg : ¬ ((g.2 ≤ 0 ∧ g.1 = 2 * g.2) ∨ (g.2 < 0 ∧ g.1 = 2 * g.2 + 1))) :
    twoByTwo.bigradedChainMinusPiece R g = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro c hc
  by_contra hc0
  obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hc0
  obtain ⟨e, he⟩ := (support_nonempty (p := c x)).mpr (by simpa using hx)
  have hdeg := (twoByTwo.mem_bigradedChainMinusPiece.mp hc) x e he
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · rw [monomialBidegree_twoByTwo_twoByTwoId] at hdeg
    rw [← hdeg] at hg
    exact hg (Or.inr ⟨by omega, by omega⟩)
  · rw [monomialBidegree_twoByTwo_twoByTwoSwap] at hdeg
    rw [← hdeg] at hg
    exact hg (Or.inl ⟨by omega, by omega⟩)

/-- Every chain in bidegree `(0, 0)` on the `2 × 2` unknot diagram is a scalar multiple of the
`X`-marking state generator `twoByTwoSwap`. -/
theorem eq_smul_single_twoByTwoSwap_of_mem_bigradedChainMinusPiece_zero
    {c : GridChainMinus R 2} (hc : c ∈ twoByTwo.bigradedChainMinusPiece R (0, 0)) :
    c = ((c GridState.twoByTwoSwap).coeff 0) • Finsupp.single GridState.twoByTwoSwap 1 := by
  ext x : 1
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · rw [Finsupp.smul_single, Finsupp.single_eq_of_ne GridState.twoByTwoId_ne_twoByTwoSwap]
    by_contra hx
    obtain ⟨e, he⟩ := (support_nonempty (p := c GridState.twoByTwoId)).mpr hx
    have hdeg := (twoByTwo.mem_bigradedChainMinusPiece.mp hc) GridState.twoByTwoId e he
    rw [monomialBidegree_twoByTwo_twoByTwoId, Prod.mk.injEq] at hdeg
    omega
  · simp only [Finsupp.smul_single, Finsupp.single_eq_same, Algebra.smul_def, mul_one]
    ext e
    rcases eq_or_ne e 0 with rfl | he0
    · simp [algebraMap_eq, coeff_C]
    · rw [algebraMap_eq, coeff_C, ite_eq_right_iff.mpr fun h ↦ absurd h.symm he0]
      by_contra hne
      have hdeg := (twoByTwo.mem_bigradedChainMinusPiece.mp hc) GridState.twoByTwoSwap e
        (mem_support_iff.mpr hne)
      rw [monomialBidegree_twoByTwo_twoByTwoSwap, Prod.mk.injEq] at hdeg
      exact he0 ((Finsupp.degree_eq_zero_iff e).mp (by omega))

end TauCeti.OddComponentGridDiagram
