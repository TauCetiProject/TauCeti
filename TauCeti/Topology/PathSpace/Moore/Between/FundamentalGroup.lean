/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Between.Append
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup
public import TauCeti.Topology.PathSpace.Moore.Comparison.Homotopic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# Conjugating Moore loops by a Moore path

For a Moore path `δ` from `a` to `b` and a Moore loop `λ` at `b`, the loop `δ ⋆ λ ⋆ δ⁻¹` at `a`
is obtained by letting `λ` act on `δ` from the right and then appending the reversal of `δ`:
it is `(MoorePathBetween.loopAppendHomotopyEquiv δ).symm (op λ • δ)`. This is the conjugation
by `δ` that carries loops at `b` to loops at `a`, the change of basepoint of the fundamental
group along `δ`. On classes it is the inverse of Mathlib's change of basepoint
`FundamentalGroup.fundamentalGroupMulEquivOfPath` along the reparametrization `δ.toPath` of `δ`
to the unit interval: changing the basepoint of the class of `δ ⋆ λ ⋆ δ⁻¹` along `δ.toPath` gives
the class of `λ`
(`fundamentalGroupMulEquivOfPath_fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul` in the
namespace `TauCeti.MoorePathBetween`).

When `δ` is itself a loop at `a`, read as a Moore path from `a` to itself, its class in the
fundamental group is that of `(MoorePathBetween.loopHomeomorph a).symm δ`, and the class of
`δ ⋆ λ ⋆ δ⁻¹` is the conjugate of the class of `λ` by the class of `δ`
(`TauCeti.MoorePathBetween.fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul`), in the
multiplicative convention of `TauCeti.MooreLoopSpace.fundamentalGroupHom`. So when that class is
central, for instance when the fundamental group is commutative, conjugating by `δ` does not
change the class of a loop.

## Main results

* `fundamentalGroupMulEquivOfPath_fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul`: for a
  Moore path `δ` from `a` to `b`, changing the basepoint of the class of `δ ⋆ λ ⋆ δ⁻¹` along
  `δ.toPath` gives the class of `λ`.
* `TauCeti.MoorePathBetween.fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul`: the class
  of `δ ⋆ λ ⋆ δ⁻¹` is the conjugate of the class of `λ` by the class of `δ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.1, Proposition 1.5
  (the change-of-basepoint isomorphism `β_h`).
-/

public section

open MulOpposite

namespace TauCeti.MoorePathBetween

variable {X : Type*} [TopologicalSpace X] {a b : X}

/-- **Conjugating by a Moore path is Mathlib's change of basepoint.** For a Moore path `δ` from
`a` to `b` and a Moore loop `λ` at `b`, changing the basepoint of the class of the loop
`δ ⋆ λ ⋆ δ⁻¹` at `a` along the reparametrization `δ.toPath` of `δ`, by
`FundamentalGroup.fundamentalGroupMulEquivOfPath`, gives the class of `λ`. -/
theorem fundamentalGroupMulEquivOfPath_fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul
    (δ : MoorePathBetween X a b) (l : MooreLoopSpace X b) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath δ.toPath
        (MooreLoopSpace.fundamentalGroupHom a ((loopAppendHomotopyEquiv δ).symm (op l • δ))) =
      MooreLoopSpace.fundamentalGroupHom b l := by
  set L := (loopAppendHomotopyEquiv δ).symm (op l • δ)
  have hL : loopHomeomorph a L = (rightAct δ l).trans δ.symm := ext (by simp [L])
  -- Reparametrization commutes with concatenation and reversal up to homotopy.
  have h : L.toPath.Homotopic ((δ.toPath.trans l.toPath).trans δ.toPath.symm) := by
    rw [← toPath_loopHomeomorph, hL, ← toPath_symm]
    exact (homotopic_toPath_trans _ _).trans
      ((homotopic_toPath_rightAct δ l).hcomp (Path.Homotopic.refl _))
  rw [← MulEquiv.eq_symm_apply, MooreLoopSpace.fundamentalGroupHom_apply,
    MooreLoopSpace.fundamentalGroupHom_apply, map_inv, inv_inj,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply, Path.Homotopic.Quotient.eq.2 h]
  simp [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]

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
    rw [← map_mul, h, ← map_one g]
    exact MooreLoopSpace.fundamentalGroupHom_eq_iff_joined.mpr ⟨H.evalAt 1⟩
  have h : (loopAppendHomotopyEquiv δ).symm (op l • δ) = D * l * E :=
    MooreLoopSpace.ext (by simp [D, E, MoorePath.trans_assoc])
  rw [h, map_mul, map_mul, eq_inv_of_mul_eq_one_right hDE]

end TauCeti.MoorePathBetween
