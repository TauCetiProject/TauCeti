/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Algebra.Group.Equiv.Opposite
public import TauCeti.AlgebraicTopology.UniversalCover.AddCircle
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular

/-!
# The fundamental group of the circle is `ℤ`

The covering `(↑) : ℝ → AddCircle p` is the universal cover of the circle: its total space
`ℝ` is contractible, hence simply connected, and the cover is regular with deck group
`Multiplicative ℤ` (the translations by the period subgroup, computed in
`TauCeti.Deck.addCircleMulEquivInt`). The regular-cover comparison
`TauCeti.Deck.IsRegular.fundamentalGroupEquiv` then identifies the fundamental group of the
base with the opposite of the deck group, and since `Multiplicative ℤ` is commutative the
opposite drops out, giving

  `FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ`

for any nonzero real period `p`. Specialising to the unit circle `UnitAddCircle = ℝ ⧸ ℤ`
yields the classical `π₁(S¹) ≅ ℤ`.

The regularity input is elementary and holds for an arbitrary topological additive group:
two points of `𝕜` with the same image under `(↑) : 𝕜 → AddCircle p` differ by an element of
the period subgroup `zmultiples p`, and translation by that element is a deck
transformation, so `Deck ((↑) : 𝕜 → AddCircle p)` acts transitively on every fibre.

## Main declarations

* `TauCeti.Deck.isRegular_addCircleCoe`: the quotient cover `(↑) : 𝕜 → AddCircle p` has
  regular deck action.
* `TauCeti.AddCircle.fundamentalGroupMulEquiv`: for a nonzero real period, the fundamental
  group of `AddCircle p` (based at any point with a chosen lift) is `Multiplicative ℤ`.
* `TauCeti.AddCircle.zeroFundamentalGroupMulEquiv`: the basepoint-`0` specialisation, using
  the lift `0 : ℝ`.
* `TauCeti.UnitAddCircle.fundamentalGroupMulEquiv`: `π₁(S¹) ≅ ℤ` for the unit circle.

## References

This advances the Tau Ceti universal-covers roadmap, Stage 4 target 12 (`π₁(S¹) ≅ ℤ`,
"built from `AddCircle.isCoveringMap_coe` (`ℝ → S¹`) and deck transformations";
`TauCetiRoadmap/UniversalCovers/README.md`). It consumes Mathlib's `AddCircle` covering map
(`AddCircle.isCoveringMap_coe`, Junyan Xu) and the contractibility of a real topological
vector space, together with the Tau Ceti deck-transformation theory of Stages 0.4 and 1.
-/

public section

namespace TauCeti

open AddSubgroup

namespace Deck

variable {𝕜 : Type*} [AddCommGroup 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] {p : 𝕜}

/-- The quotient cover `(↑) : 𝕜 → AddCircle p` has regular deck action: it is surjective and
its deck transformation group acts transitively on every fibre. Transitivity is witnessed by
translation: two points with the same image differ by an element of the period subgroup
`zmultiples p`, and translating by that element is a deck transformation. -/
theorem isRegular_addCircleCoe : IsRegular ((↑) : 𝕜 → AddCircle p) := by
  rw [isRegular_iff_exists_apply_eq]
  refine ⟨QuotientAddGroup.mk_surjective, ?_⟩
  intro e e' he
  have hmem : e' - e ∈ zmultiples p := by
    have hsub : e - e' ∈ zmultiples p := (QuotientAddGroup.eq_iff_sub_mem ..).1 he
    simpa using neg_mem hsub
  exact ⟨addRightZMultiples ⟨e' - e, hmem⟩, by simp [addRightZMultiples_apply]⟩

end Deck

namespace AddCircle

variable (p : ℝ)

/-- For a nonzero real period `p`, the fundamental group of the circle `AddCircle p`, based at
any point `x` with a chosen lift `e : (↑) ⁻¹' {x}`, is infinite cyclic:
`FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ`.

The cover `(↑) : ℝ → AddCircle p` is regular (`TauCeti.Deck.isRegular_addCircleCoe`) with
contractible (hence simply connected) total space `ℝ`, so the regular-cover comparison
`TauCeti.Deck.IsRegular.fundamentalGroupEquiv` identifies `π₁` with the opposite deck group;
the deck group is `Multiplicative ℤ` by `TauCeti.Deck.addCircleMulEquivInt`, and the opposite
of a commutative group is itself. -/
noncomputable def fundamentalGroupMulEquiv (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  (Deck.isRegular_addCircleCoe.fundamentalGroupEquiv (AddCircle.isCoveringMap_coe p) e).trans
    ((MulEquiv.op
      (Deck.addCircleMulEquivInt (not_isOfFinAddOrder_of_isAddTorsionFree hp)).symm).trans
        (MulOpposite.opMulEquiv (M := Multiplicative ℤ)).symm)

/-- The fundamental group of the circle `AddCircle p` based at `0`, with the lift `0 : ℝ`, is
`Multiplicative ℤ`. -/
noncomputable def zeroFundamentalGroupMulEquiv (hp : p ≠ 0) :
    FundamentalGroup (AddCircle p) 0 ≃* Multiplicative ℤ :=
  fundamentalGroupMulEquiv p hp ⟨0, by simp⟩

end AddCircle

namespace UnitAddCircle

/-- The fundamental group of the unit circle `S¹ = ℝ ⧸ ℤ` is `ℤ`:
`FundamentalGroup UnitAddCircle 0 ≃* Multiplicative ℤ`. This is the classical `π₁(S¹) ≅ ℤ`. -/
noncomputable def fundamentalGroupMulEquiv :
    FundamentalGroup UnitAddCircle 0 ≃* Multiplicative ℤ :=
  AddCircle.zeroFundamentalGroupMulEquiv 1 one_ne_zero

end UnitAddCircle

end TauCeti
