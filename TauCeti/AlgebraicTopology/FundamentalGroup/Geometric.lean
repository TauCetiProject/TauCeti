/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The geometric fundamental group

Mathlib's `FundamentalGroup X x₀` multiplies loop classes by `p * q = q.trans p`
(`FundamentalGroup.mul_def`): the right factor is traversed first. The **geometric fundamental
group** `TauCeti.GeometricFundamentalGroup X x₀ = (FundamentalGroup X x₀)ᵐᵒᵖ` reverses this, so
that the class of `p.trans q` is the product of the class of `p` and the class of `q`
(`TauCeti.GeometricFundamentalGroup.mk_trans`): multiplication is first-traverse concatenation.
Inversion `(MulEquiv.inv' (FundamentalGroup X x₀)).symm`, `op g ↦ g⁻¹`, identifies it with
`FundamentalGroup X x₀`. Through it the two groups have the same automorphisms
(`MulAut.congr_inv'`: `φ` corresponds to `MulEquiv.op φ`), inner automorphisms
(`MulAut.map_congr_range_conj`) and outer automorphisms (`TauCeti.OuterAut.congr` and
`TauCeti.OuterAut.congr_symm_inv'_mk_op`).

The deck dictionary for the universal cover, in this convention, is in
`TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.UniversalCover` (the endpoint
formula and path lifting) and `TauCeti.AlgebraicTopology.UniversalCover.Classification.DeckGroup`
(quotients by normal subgroups).

## Main definitions

* `TauCeti.GeometricFundamentalGroup X x₀`: the opposite of the fundamental group.
* `TauCeti.GeometricFundamentalGroup.mk`: the class of a loop.

## Main results

* `TauCeti.GeometricFundamentalGroup.mk_trans`: concatenation is multiplication.
* `TauCeti.GeometricFundamentalGroup.mk_symm`: the reverse loop represents the inverse.
* `TauCeti.GeometricFundamentalGroup.mk_eq_mk_iff`: two loops have the same class iff they are
  homotopic.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Chapter 8.
-/

public section
noncomputable section

open MulOpposite

namespace TauCeti

/-- The **geometric fundamental group** `(π₁(X, x₀))ᵐᵒᵖ`, whose multiplication is
first-traverse concatenation of loops: the class of `p.trans q` is the class of `p` times the
class of `q`. -/
abbrev GeometricFundamentalGroup (X : Type*) [TopologicalSpace X] (x₀ : X) : Type _ :=
  (FundamentalGroup X x₀)ᵐᵒᵖ

namespace GeometricFundamentalGroup

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- The class of a loop in the geometric fundamental group. -/
abbrev mk (p : Path x₀ x₀) : GeometricFundamentalGroup X x₀ :=
  op (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))

/-- Multiplication in the geometric fundamental group is first-traverse concatenation. -/
@[simp]
theorem mk_trans (p q : Path x₀ x₀) : mk (p.trans q) = mk p * mk q :=
  unop_injective <| by simp [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans]

/-- The constant loop represents the identity. -/
@[simp]
theorem mk_refl : mk (Path.refl x₀) = 1 :=
  unop_injective <| by simp [FundamentalGroup.one_def, Path.Homotopic.Quotient.mk_refl]

/-- The reverse loop represents the inverse. -/
@[simp]
theorem mk_symm (p : Path x₀ x₀) : mk p.symm = (mk p)⁻¹ :=
  unop_injective <| by simp [FundamentalGroup.inv_def, Path.Homotopic.Quotient.mk_symm]

/-- Two loops have the same class iff they are homotopic. -/
theorem mk_eq_mk_iff {p q : Path x₀ x₀} : mk p = mk q ↔ p.Homotopic q := by
  rw [op_inj, CategoryTheory.End.of.injEq, Path.Homotopic.Quotient.eq]

/-- Every element of the geometric fundamental group is the class of a loop. -/
theorem mk_surjective :
    Function.Surjective (mk : Path x₀ x₀ → GeometricFundamentalGroup X x₀) := by
  intro a
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective a.unop.asHom
  exact ⟨p, unop_injective <| CategoryTheory.End.ext hp⟩

end GeometricFundamentalGroup

end TauCeti
