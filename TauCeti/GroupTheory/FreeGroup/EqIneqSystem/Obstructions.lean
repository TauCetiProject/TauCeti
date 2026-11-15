/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Centralizer
public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem.Basic

/-!
# Obstructions to solvability over a free group

Two small systems of equations and inequations over a free group `F(A)` have no solution, for
reasons that come from the structure of `F(A)` rather than from the shape of the system. An
element of `F(A)` commuting with two distinct basis letters is trivial, because the centralizer
of a nontrivial element of a free group is cyclic; so the system `[x, a] = 1`, `[x, b] = 1`,
`x ≠ 1` is unsolvable. A basis letter is neither trivial nor a proper power; so the equation
`x ^ n = a` with a natural-number exponent `n ≠ 1` is unsolvable.

## Main results

* `TauCeti.EqIneqSystem.not_isSolution_commutator_commutator_ineq_of`: over a free group, the
  system `[x, a] = 1`, `[x, b] = 1`, `x ≠ 1` has no solution for distinct basis letters `a`, `b`.
* `TauCeti.EqIneqSystem.not_isSolution_pow_eq_of`: over a free group, the equation `x ^ n = a`
  with a natural-number exponent `n ≠ 1` has no solution for a basis letter `a`.

## References

* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually
  free groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, proof of Lemma 21
  (centralizers of nontrivial elements of a free group are cyclic).
-/

public section

namespace TauCeti

namespace EqIneqSystem

open FreeGroup (of)
open scoped commutatorElement

variable {X A : Type*}

/-- Over a free group, the system `[x, a] = 1`, `[x, b] = 1`, `x ≠ 1` has no solution when `a`
and `b` are distinct basis letters: an element commuting with both is trivial. -/
theorem not_isSolution_commutator_commutator_ineq_of {a b : A} (hab : a ≠ b) (x : X)
    (v : X → FreeGroup A) :
    ¬ (⟨[⁅(of (Sum.inl x) : FreeGroup (X ⊕ A)), of (Sum.inr a)⁆,
        ⁅(of (Sum.inl x) : FreeGroup (X ⊕ A)), of (Sum.inr b)⁆],
      [of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution v of := by
  simp only [isSolution_iff, List.forall_mem_cons, map_commutatorElement, eval_of, Sum.elim_inl,
    Sum.elim_inr, commutatorElement_eq_one_iff_commute]
  rintro ⟨⟨ha, hb, -⟩, hx, -⟩
  exact hx (FreeGroup.eq_one_of_commute_of_of_commute_of hab ha hb)

/-- Over a free group, the equation `x ^ n = a` with a natural-number exponent `n ≠ 1` has no
solution when `a` is a basis letter: a basis letter is neither trivial nor a proper power. -/
theorem not_isSolution_pow_eq_of {n : ℕ} (hn : n ≠ 1) (x : X) (a : A) (v : X → FreeGroup A) :
    ¬ (⟨[of (Sum.inl x) ^ n * (of (Sum.inr a))⁻¹], []⟩ : EqIneqSystem X A).IsSolution v of := by
  intro h
  have hx : v x ^ n = of a := by simpa [isSolution_iff, mul_inv_eq_one] using h
  obtain rfl | hn0 := Nat.eq_zero_or_pos n
  · exact FreeGroup.of_ne_one a (by simpa using hx.symm)
  · exact FreeGroup.not_isProperPower_of a (Group.isProperPower_iff.2 ⟨v x, n, by omega, hx.symm⟩)

end EqIneqSystem

end TauCeti
