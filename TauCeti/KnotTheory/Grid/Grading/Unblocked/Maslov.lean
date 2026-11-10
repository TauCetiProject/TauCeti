/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain

/-!
# Maslov-homogeneous polynomial grid chains

The `O`-Maslov degree of `V^e · x` is `M_O(x) - 2|e|`. The corresponding
homogeneous pieces of the polynomial grid chain module are submodules over the
coefficient ring, not over the polynomial ring. Unlike the integral Alexander
grading, this grading is defined for every grid diagram. It grades both the
unblocked differential and the differential that allows rectangles through
`X`-markings, so it can be used before taking the Alexander associated graded.

The convention is that of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Sections 4.3, 4.6 and Chapter 13.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- Polynomial grid chains homogeneous of `O`-Maslov degree `m`. Each variable
has degree `-2`; the coefficient at a state `x` therefore has weighted degree
`m - M_O(x)`. -/
noncomputable def maslovChainMinusPiece (m : ℤ) : Submodule R (GridChainMinus R n) :=
  ⨅ x : GridState n, (weightedHomogeneousSubmodule R (fun _ : Fin n => (-2 : ℤ))
    (m - G.maslovOℤ x)).comap (Finsupp.lapply x)

variable {G R} in
/-- Maslov homogeneity is weighted homogeneity of the coefficient at each state. -/
@[simp]
theorem mem_maslovChainMinusPiece {m : ℤ} {c : GridChainMinus R n} :
    c ∈ G.maslovChainMinusPiece R m ↔ ∀ x : GridState n,
      IsWeightedHomogeneous (fun _ : Fin n => (-2 : ℤ)) (c x) (m - G.maslovOℤ x) := by
  simp [maslovChainMinusPiece]

variable {G R} in
/-- Equivalently, every monomial of a Maslov-homogeneous chain has the specified
Maslov degree. -/
theorem mem_maslovChainMinusPiece_iff_forall_mem_support {m : ℤ} {c : GridChainMinus R n} :
    c ∈ G.maslovChainMinusPiece R m ↔ ∀ x : GridState n, ∀ e ∈ (c x).support,
      G.maslovOℤ x - 2 * (e.degree : ℤ) = m := by
  have hw (e : Fin n →₀ ℕ) :
      Finsupp.weight (fun _ : Fin n => (-2 : ℤ)) e = -2 * (e.degree : ℤ) := by
    simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
      Finset.mul_sum, Nat.cast_sum, mul_comm]
  simp only [mem_maslovChainMinusPiece, IsWeightedHomogeneous, ← mem_support_iff, hw]
  constructor
  · intro h x e he
    have := h x he
    omega
  · intro h x e he
    have := h x e he
    omega

/-- A monomial multiple of a state has the expected Maslov degree. -/
theorem single_monomial_mem_maslovChainMinusPiece (x : GridState n) (e : Fin n →₀ ℕ) (r : R) :
    (Finsupp.single x (monomial e r) : GridChainMinus R n) ∈
      G.maslovChainMinusPiece R (G.maslovOℤ x - 2 * (e.degree : ℤ)) := by
  classical
  rw [mem_maslovChainMinusPiece_iff_forall_mem_support]
  intro y d hd
  rcases eq_or_ne y x with rfl | hy
  · rw [Finsupp.single_eq_same] at hd
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)]
  · simp [Finsupp.single_eq_of_ne hy] at hd

variable {R} in
/-- Multiplication by a polynomial variable lowers Maslov degree by two. -/
theorem X_smul_mem_maslovChainMinusPiece (i : Fin n) {m : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.maslovChainMinusPiece R m) :
    (MvPolynomial.X i : MvPolynomial (Fin n) R) • c ∈
      G.maslovChainMinusPiece R (m - 2) := by
  rw [mem_maslovChainMinusPiece] at hc ⊢
  intro x
  simp only [Finsupp.smul_apply, smul_eq_mul]
  convert (isWeightedHomogeneous_X R (fun _ : Fin n => (-2 : ℤ)) i).mul (hc x) using 1
  ring

variable {R} in
/-- Multiplication by a variable reflects Maslov homogeneity as well as lowering degree
by two, over any commutative coefficient semiring. -/
theorem X_smul_mem_maslovChainMinusPiece_iff (i : Fin n) {m : ℤ} {c : GridChainMinus R n} :
    (MvPolynomial.X i : MvPolynomial (Fin n) R) • c ∈ G.maslovChainMinusPiece R (m - 2) ↔
      c ∈ G.maslovChainMinusPiece R m := by
  refine ⟨fun hc => ?_, G.X_smul_mem_maslovChainMinusPiece i⟩
  rw [mem_maslovChainMinusPiece_iff_forall_mem_support] at hc ⊢
  intro x e he
  have hmem : Finsupp.single i 1 + e ∈
      (((MvPolynomial.X i : MvPolynomial (Fin n) R) • c) x).support := by
    simpa only [Finsupp.smul_apply, smul_eq_mul, MvPolynomial.mem_support_iff,
      coeff_X_mul] using MvPolynomial.mem_support_iff.mp he
  have h := hc x _ hmem
  have hdeg : ((Finsupp.single i 1 + e).degree : ℤ) = 1 + (e.degree : ℤ) := by simp
  rw [hdeg] at h
  omega

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]

/-- A bigraded homogeneous chain is Maslov homogeneous in its first degree. -/
theorem bigradedChainMinusPiece_le_maslovChainMinusPiece (g : ℤ × ℤ) :
    G.bigradedChainMinusPiece R g ≤ G.1.maslovChainMinusPiece R g.1 := by
  intro c hc
  rw [GridDiagram.mem_maslovChainMinusPiece_iff_forall_mem_support]
  intro x e he
  simpa only [monomialBidegree_fst] using congrArg Prod.fst
    (G.mem_bigradedChainMinusPiece.mp hc x e he)

end TauCeti.OddComponentGridDiagram
