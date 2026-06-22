/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Instances.AddCircle.Defs
import TauCeti.Algebra.Group.ZMultiples
import TauCeti.AlgebraicTopology.UniversalCover.Deck.QuotientAddGroup

/-!
# The deck transformation group of the quotient map `𝕜 → AddCircle p`

For a topological additive commutative group `𝕜`, this file specializes the quotient-map deck
computation from `TauCeti.AlgebraicTopology.UniversalCover.Deck.QuotientAddGroup` to
`H = zmultiples p`. Since `AddCircle p = 𝕜 ⧸ zmultiples p`, it gives

  `Deck ((↑) : 𝕜 → AddCircle p) ≃* Multiplicative (zmultiples p)`.

The forward inclusion is elementary. For the converse, a deck transformation `φ` keeps
`φ e - e` inside the totally disconnected subgroup while varying continuously in `e`, so on a
preconnected `𝕜` it is constant; that constant is `φ 0`, and `φ` is translation by it.

When the period subgroup is totally disconnected and `p` is not a torsion element
(`¬ IsOfFinAddOrder p`), the translation subgroup is infinite cyclic, giving
`Deck ((↑) : 𝕜 → AddCircle p) ≃* Multiplicative ℤ`. In the standard real case, where
`AddCircle.isCoveringMap_coe` supplies the covering hypothesis, this is the deck group of the
universal cover `ℝ → S¹` and the algebraic input to the universal-covers roadmap target
`π₁(S¹) ≅ ℤ` (Stage 4).

## Main declarations

* `TauCeti.Deck.addRightZMultiples`: translation by an element of `zmultiples p` as a deck
  transformation of `(↑) : 𝕜 → AddCircle p`.
* `TauCeti.Deck.addCircleMulEquiv`: the deck group of `(↑) : 𝕜 → AddCircle p` is
  `Multiplicative (zmultiples p)`.
* `TauCeti.Deck.addCircleMulEquivInt`: for a totally disconnected period subgroup and a
  non-torsion period, the deck group is `Multiplicative ℤ`.

## References

This advances the Tau Ceti universal-covers roadmap, Stage 4 (`π₁(S¹) ≅ ℤ`, "built from
`AddCircle.isCoveringMap_coe` (`ℝ → S¹`) and deck transformations"), consuming Mathlib's
`AddCircle` covering and the deck-transformation group of Stage 0.4.
-/

namespace TauCeti

open AddSubgroup

namespace Deck

variable {𝕜 : Type*} [AddCommGroup 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  {p : 𝕜}

omit [IsTopologicalAddGroup 𝕜] in
/-- A homeomorphism of `𝕜` is a deck transformation of `(↑) : 𝕜 → AddCircle p` exactly when it
moves every point within the period subgroup `zmultiples p`. -/
@[simp]
theorem mem_addCircleCoe {φ : 𝕜 ≃ₜ 𝕜} :
    φ ∈ Deck ((↑) : 𝕜 → AddCircle p) ↔ ∀ e, φ e - e ∈ zmultiples p :=
  mem_quotientMk

/-- Right translation by an element of `zmultiples p`, as a deck transformation of
`(↑) : 𝕜 → AddCircle p`. -/
def addRightZMultiples (a : zmultiples p) : Deck ((↑) : 𝕜 → AddCircle p) :=
  addRightQuotient a

@[simp]
theorem addRightZMultiples_apply (a : zmultiples p) (e : 𝕜) :
    (addRightZMultiples a).1 e = e + (a : 𝕜) :=
  rfl

@[simp]
theorem addRightZMultiples_zero : addRightZMultiples (0 : zmultiples p) = 1 := by
  exact addRightQuotient_zero

@[simp]
theorem addRightZMultiples_add (a b : zmultiples p) :
    addRightZMultiples (a + b) = addRightZMultiples a * addRightZMultiples b := by
  exact addRightQuotient_add a b

theorem addRightZMultiples_injective :
    Function.Injective (addRightZMultiples : zmultiples p → Deck ((↑) : 𝕜 → AddCircle p)) := by
  exact addRightQuotient_injective

/-- On a preconnected domain with totally disconnected period subgroup, a deck transformation of
`(↑) : 𝕜 → AddCircle p` is right translation by `φ 0`. -/
theorem addCircleCoe_eq_add_apply_zero [PreconnectedSpace 𝕜]
    [TotallyDisconnectedSpace (zmultiples p)] (φ : Deck ((↑) : 𝕜 → AddCircle p)) (e : 𝕜) :
    φ.1 e = e + φ.1 0 := by
  exact quotientMk_eq_add_apply_zero φ e

/-- The deck transformation group of `(↑) : 𝕜 → AddCircle p` on a preconnected domain with
totally disconnected period subgroup is the group of translations by the period subgroup. -/
noncomputable def addCircleMulEquiv [PreconnectedSpace 𝕜]
    [TotallyDisconnectedSpace (zmultiples p)] :
    Multiplicative (zmultiples p) ≃* Deck ((↑) : 𝕜 → AddCircle p) :=
  quotientMulEquiv

@[simp]
theorem addCircleMulEquiv_apply [PreconnectedSpace 𝕜] [TotallyDisconnectedSpace (zmultiples p)]
    (a : Multiplicative (zmultiples p)) :
    addCircleMulEquiv a = addRightZMultiples a.toAdd :=
  rfl

@[simp]
theorem addCircleMulEquiv_symm_apply_coe [PreconnectedSpace 𝕜]
    [TotallyDisconnectedSpace (zmultiples p)] (φ : Deck ((↑) : 𝕜 → AddCircle p)) :
    ((addCircleMulEquiv.symm φ).toAdd : 𝕜) = φ.1 0 := by
  exact quotientMulEquiv_symm_apply_coe φ

/-- For a non-torsion period, the deck transformation group of the quotient map
`(↑) : 𝕜 → AddCircle p` on a preconnected domain with totally disconnected period subgroup is
infinite cyclic: `Multiplicative ℤ`. In the standard real covering case this is the deck group
of the universal cover `ℝ → S¹`. -/
noncomputable def addCircleMulEquivInt [PreconnectedSpace 𝕜]
    [TotallyDisconnectedSpace (zmultiples p)] (hp : ¬ IsOfFinAddOrder p) :
    Multiplicative ℤ ≃* Deck ((↑) : 𝕜 → AddCircle p) :=
  (intEquivZMultiples hp).toMultiplicative.trans addCircleMulEquiv

@[simp]
theorem addCircleMulEquivInt_apply [PreconnectedSpace 𝕜]
    [TotallyDisconnectedSpace (zmultiples p)] (hp : ¬ IsOfFinAddOrder p) (a : Multiplicative ℤ)
    (e : 𝕜) :
    (addCircleMulEquivInt hp a).1 e = e + a.toAdd • p := by
  simp [addCircleMulEquivInt]

theorem addCircleMulEquivInt_symm_zsmul_apply_zero [PreconnectedSpace 𝕜]
    [TotallyDisconnectedSpace (zmultiples p)] (hp : ¬ IsOfFinAddOrder p)
    (φ : Deck ((↑) : 𝕜 → AddCircle p)) :
    ((addCircleMulEquivInt hp).symm φ).toAdd • p = φ.1 0 := by
  have happly :=
    addCircleMulEquivInt_apply hp ((addCircleMulEquivInt hp).symm φ) (0 : 𝕜)
  have hzero := congrArg (fun ψ : Deck ((↑) : 𝕜 → AddCircle p) => ψ.1 0)
    (MulEquiv.apply_symm_apply (addCircleMulEquivInt hp) φ)
  exact (by simpa using happly.symm.trans hzero)

end Deck

end TauCeti
