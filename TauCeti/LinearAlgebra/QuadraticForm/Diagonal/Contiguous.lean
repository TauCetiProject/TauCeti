/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.WittChain

/-!
# Contiguous orthogonal bases and diagonal chains

Two orthogonal bases are contiguous in Serre's sense when they have a vector in common. Moving
that vector to the first position gives a common diagonal coefficient. Cancelling its line
leaves isometric diagonal forms on the complements, so Witt's chain theorem connects their
coefficients when the original rank is at least three. Adjoining the common coefficient lifts
this to a diagonal chain that keeps the common line fixed throughout.

`Module.Basis.diagonalChain_tail_of_isOrtho_of_apply_eq` gives this comparison with the common
vector specified by its two indices. The coefficient families are supplied as units with their
evaluation equations, so the statement needs no separate nondegeneracy hypothesis. The theorem
compares a contiguous step with diagonal chains; it does not assert Serre's theorem that any two
orthogonal bases of a regular form of rank at least three are connected by contiguous steps.

The rank bound matters even for contiguous bases: rescaling the other vector of a rank-two
basis changes its coefficient by a square, whereas a rank-one diagonal chain requires equality.

## References

* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer (1973),
  Chapter IV, §1.3, Definition 6 and Theorem 2; §2.1, Theorem 5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Theorem 5.2.
-/

public section

namespace Module.Basis

open QuadraticMap TauCeti

variable {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- If two orthogonal bases have a vector in common, their unit coefficient families are joined
by a diagonal chain on its complement after swapping that vector to the head of each basis.
Thus the common coefficient may be kept fixed when lifting this chain with `DiagonalChain.cons`.
The rank is at least three because the complement must have rank at least two. -/
theorem diagonalChain_tail_of_isOrtho_of_apply_eq {n : ℕ}
    (b b' : Basis (Fin (n + 3)) K V)
    (hb : Q.associated.IsOrthoᵢ b) (hb' : Q.associated.IsOrthoᵢ b')
    (w w' : Fin (n + 3) → Kˣ)
    (hw : ∀ k, (w k : K) = Q (b k)) (hw' : ∀ k, (w' k : K) = Q (b' k))
    {i j : Fin (n + 3)} (hshared : b i = b' j) :
    DiagonalChain (fun k : Fin (n + 2) ↦ w (Equiv.swap i 0 k.succ))
      (fun k : Fin (n + 2) ↦ w' (Equiv.swap j 0 k.succ)) := by
  have hdiag : (weightedSumSquares K fun k ↦ (w k : K)).Equivalent
      (weightedSumSquares K fun k ↦ (w' k : K)) := by
    have h : (Q.basisRepr b).Equivalent (Q.basisRepr b') :=
      ⟨(Q.isometryEquivBasisRepr b).symm.trans (Q.isometryEquivBasisRepr b')⟩
    simpa only [basisRepr_eq_of_iIsOrtho Q b hb,
      basisRepr_eq_of_iIsOrtho Q b' hb', ← hw, ← hw'] using
      h
  have hpermuted :
      (weightedSumSquares K fun k ↦ (w (Equiv.swap i 0 k) : K)).Equivalent
        (weightedSumSquares K fun k ↦ (w' (Equiv.swap j 0 k) : K)) :=
    (equivalent_weightedSumSquares_comp (fun k ↦ (w k : K)) (Equiv.swap i 0)).symm.trans
      (hdiag.trans
        (equivalent_weightedSumSquares_comp (fun k ↦ (w' k : K)) (Equiv.swap j 0)))
  have hhead : (w ∘ Equiv.swap i 0) 0 = (w' ∘ Equiv.swap j 0) 0 := by
    simp only [Function.comp_apply, Equiv.swap_apply_right]
    apply Units.ext
    rw [hw, hw', hshared]
  exact diagonalChain_iff_equivalent.mpr
    (equivalent_weightedSumSquares_tail_of_head_eq hhead hpermuted)

end Module.Basis
