/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Between.Append
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup

/-!
# Conjugating Moore loops by a Moore path

For a Moore path `δ` from `a` to `b` and a Moore loop `λ` at `b`, the loop `δ ⋆ λ ⋆ δ⁻¹` at `a`
is obtained by letting `λ` act on `δ` from the right and then appending the reversal of `δ`:
it is `(MoorePathBetween.loopAppendHomotopyEquiv δ).symm (op λ • δ)`. This is the conjugation
by `δ` that carries loops at `b` to loops at `a`, the change of basepoint of the fundamental
group along `δ`.

When `δ` is itself a loop at `a`, read as a Moore path from `a` to itself, its class in the
fundamental group is that of `(MoorePathBetween.loopHomeomorph a).symm δ`, and the class of
`δ ⋆ λ ⋆ δ⁻¹` is the conjugate of the class of `λ` by the class of `δ`
(`TauCeti.MoorePathBetween.fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul`), in the
multiplicative convention of `TauCeti.MooreLoopSpace.fundamentalGroupHom`. So when that class is
central, for instance when the fundamental group is commutative, conjugating by `δ` does not
change the class of a loop.

## Main results

* `TauCeti.MoorePathBetween.fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul`: the class
  of `δ ⋆ λ ⋆ δ⁻¹` is the conjugate of the class of `λ` by the class of `δ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.1, Proposition 1.5
  (the change-of-basepoint isomorphism `β_h`).
-/

public section

open MulOpposite

namespace TauCeti.MoorePathBetween

variable {X : Type*} [TopologicalSpace X] {a : X}

/-- **The class of `δ ⋆ λ ⋆ δ⁻¹` is the conjugate of the class of `λ`** by the class of `δ`, for
Moore loops `δ` and `λ` at `a`, with `δ` read as a Moore path from `a` to itself. -/
theorem fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul (δ : MoorePathBetween X a a)
    (l : MooreLoopSpace X a) :
    MooreLoopSpace.fundamentalGroupHom a ((loopAppendHomotopyEquiv δ).symm (op l • δ)) =
      MooreLoopSpace.fundamentalGroupHom a ((loopHomeomorph a).symm δ) *
        MooreLoopSpace.fundamentalGroupHom a l *
          (MooreLoopSpace.fundamentalGroupHom a ((loopHomeomorph a).symm δ))⁻¹ := by
  set g := MooreLoopSpace.fundamentalGroupHom a
  set D := (loopHomeomorph a).symm δ
  -- The loop `δ⁻¹`, obtained by appending the reversal of `δ` to the unit.
  set E := (loopAppendHomotopyEquiv δ).symm (loopHomeomorph a 1)
  have hDE : g D * g E = 1 := by
    -- `δ ⋆ δ⁻¹` is joined to the unit by retracting the suffix `δ⁻¹`.
    obtain ⟨H⟩ := (loopAppendHomotopyEquiv δ).left_inv
    have h : D * E = (loopAppendHomotopyEquiv δ).symm (loopAppendHomotopyEquiv δ 1) :=
      MooreLoopSpace.ext (by simp [D, E])
    rw [← map_mul, h, ← MooreLoopSpace.zerothHomotopyEquivFundamentalGroup_mk,
      ← map_one g, ← MooreLoopSpace.zerothHomotopyEquivFundamentalGroup_mk]
    exact congrArg _ (Quotient.sound ⟨H.evalAt 1⟩)
  have h : (loopAppendHomotopyEquiv δ).symm (op l • δ) = D * l * E :=
    MooreLoopSpace.ext (by simp [D, E, MoorePath.trans_assoc])
  rw [h, map_mul, map_mul, eq_inv_of_mul_eq_one_right hDE]

end TauCeti.MoorePathBetween
