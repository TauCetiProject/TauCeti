/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import TauCeti.AlgebraicTopology.UniversalCover.Deck

/-!
# The deck transformation group of the covering `𝕜 → AddCircle p`

For a topological additive commutative group `𝕜` with `zmultiples p` discrete, the quotient
map `(↑) : 𝕜 → AddCircle p = 𝕜 ⧸ zmultiples p` is a covering map
(`AddCircle.isCoveringMap_coe`). This file identifies its deck transformation group: when `𝕜`
is preconnected, every deck transformation is right translation by an element of `zmultiples p`,
and conversely each such translation is a deck transformation, so

  `Deck ((↑) : 𝕜 → AddCircle p) ≃* Multiplicative (zmultiples p)`.

The forward inclusion is elementary. For the converse, a deck transformation `φ` keeps
`φ e - e` inside the *discrete* subgroup `zmultiples p` while varying continuously in `e`, so on
a preconnected `𝕜` it is constant; that constant is `φ 0`, and `φ` is translation by it.

When `p` is not a torsion element (`NoZeroSMulDivisors ℤ 𝕜` and `p ≠ 0`), the translation
subgroup is infinite cyclic, giving `Deck ((↑) : 𝕜 → AddCircle p) ≃* Multiplicative ℤ`. For
`𝕜 = ℝ` this is the deck group of the universal cover `ℝ → S¹` and the algebraic input to the
universal-covers roadmap target `π₁(S¹) ≅ ℤ` (Stage 4).

## Main declarations

* `TauCeti.Deck.addRightZMultiples`: translation by an element of `zmultiples p` as a deck
  transformation of `(↑) : 𝕜 → AddCircle p`.
* `TauCeti.Deck.addCircleMulEquiv`: the deck group of `(↑) : 𝕜 → AddCircle p` is
  `Multiplicative (zmultiples p)`.
* `TauCeti.Deck.addCircleMulEquivMultInt`: for a non-torsion period, the deck group is
  `Multiplicative ℤ`.

## References

This advances the Tau Ceti universal-covers roadmap, Stage 4 (`π₁(S¹) ≅ ℤ`, "built from
`AddCircle.isCoveringMap_coe` (`ℝ → S¹`) and deck transformations"), consuming Mathlib's
`AddCircle` covering and the deck-transformation group of Stage 0.4.
-/

namespace TauCeti

open AddSubgroup

namespace Deck

variable {𝕜 : Type*} [AddCommGroup 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] {p : 𝕜}

omit [IsTopologicalAddGroup 𝕜] in
/-- A homeomorphism of `𝕜` is a deck transformation of `(↑) : 𝕜 → AddCircle p` exactly when it
moves every point within the period subgroup `zmultiples p`. -/
theorem mem_addCircleCoe {φ : 𝕜 ≃ₜ 𝕜} :
    φ ∈ Deck ((↑) : 𝕜 → AddCircle p) ↔ ∀ e, φ e - e ∈ zmultiples p := by
  rw [mem_iff]
  exact forall_congr' fun e => QuotientAddGroup.eq_iff_sub_mem

/-- Right translation by an element of `zmultiples p`, as a deck transformation of
`(↑) : 𝕜 → AddCircle p`. -/
def addRightZMultiples (a : zmultiples p) : Deck ((↑) : 𝕜 → AddCircle p) :=
  ⟨Homeomorph.addRight (a : 𝕜), mem_addCircleCoe.2 fun e => by
    simpa only [Homeomorph.coe_addRight, add_sub_cancel_left] using a.2⟩

@[simp]
theorem addRightZMultiples_apply (a : zmultiples p) (e : 𝕜) :
    (addRightZMultiples a).1 e = e + (a : 𝕜) :=
  rfl

theorem addRightZMultiples_zero : addRightZMultiples (0 : zmultiples p) = 1 := by
  apply Subtype.ext
  ext e
  simp

theorem addRightZMultiples_add (a b : zmultiples p) :
    addRightZMultiples (a + b) = addRightZMultiples a * addRightZMultiples b := by
  apply Subtype.ext
  ext e
  simp only [Subgroup.coe_mul, Homeomorph.mul_apply, addRightZMultiples_apply]
  change e + ((a : 𝕜) + b) = e + (b : 𝕜) + a
  abel

theorem addRightZMultiples_injective :
    Function.Injective (addRightZMultiples : zmultiples p → Deck ((↑) : 𝕜 → AddCircle p)) := by
  intro _ _ h
  have := congrArg (fun φ : Deck ((↑) : 𝕜 → AddCircle p) => φ.1 0) h
  simpa using this

/-- On a preconnected base with discrete period subgroup, a deck transformation of
`(↑) : 𝕜 → AddCircle p` is right translation by `φ 0`. -/
theorem eq_add_apply_zero [PreconnectedSpace 𝕜] [DiscreteTopology (zmultiples p)]
    (φ : Deck ((↑) : 𝕜 → AddCircle p)) (e : 𝕜) : φ.1 e = e + φ.1 0 := by
  have hmem : ∀ x, φ.1 x - x ∈ zmultiples p := mem_addCircleCoe.1 φ.2
  have hcont : Continuous fun x => φ.1 x - x := φ.1.continuous.sub continuous_id
  have key : (⟨φ.1 e - e, hmem e⟩ : zmultiples p) = ⟨φ.1 0 - 0, hmem 0⟩ :=
    PreconnectedSpace.constant ‹PreconnectedSpace 𝕜› (hcont.subtype_mk hmem)
  have h : φ.1 e - e = φ.1 0 - 0 := congrArg Subtype.val key
  rw [sub_zero, sub_eq_iff_eq_add] at h
  rw [h, add_comm]

variable (p) in
/-- The deck transformation group of `(↑) : 𝕜 → AddCircle p` contains the translations by the
period subgroup as a subgroup, packaged as a homomorphism from `Multiplicative (zmultiples p)`. -/
def addRightZMultiplesHom :
    Multiplicative (zmultiples p) →* Deck ((↑) : 𝕜 → AddCircle p) where
  toFun a := addRightZMultiples a.toAdd
  map_one' := addRightZMultiples_zero
  map_mul' _ _ := addRightZMultiples_add _ _

@[simp]
theorem addRightZMultiplesHom_apply (a : Multiplicative (zmultiples p)) :
    addRightZMultiplesHom p a = addRightZMultiples a.toAdd :=
  rfl

/-- The deck transformation group of the covering `(↑) : 𝕜 → AddCircle p` of a preconnected
base with discrete period subgroup is the group of translations by the period subgroup. -/
noncomputable def addCircleMulEquiv [PreconnectedSpace 𝕜] [DiscreteTopology (zmultiples p)] :
    Multiplicative (zmultiples p) ≃* Deck ((↑) : 𝕜 → AddCircle p) :=
  MulEquiv.ofBijective (addRightZMultiplesHom p) <| by
    refine ⟨fun a b h => ?_, fun φ => ?_⟩
    · exact Multiplicative.toAdd.injective (addRightZMultiples_injective h)
    · refine ⟨Multiplicative.ofAdd ⟨φ.1 0, by simpa using mem_addCircleCoe.1 φ.2 0⟩, ?_⟩
      apply Subtype.ext
      ext e
      simpa using (eq_add_apply_zero φ e).symm

@[simp]
theorem addCircleMulEquiv_apply [PreconnectedSpace 𝕜] [DiscreteTopology (zmultiples p)]
    (a : Multiplicative (zmultiples p)) :
    addCircleMulEquiv a = addRightZMultiples a.toAdd :=
  rfl

variable [NoZeroSMulDivisors ℤ 𝕜]

/-- For a non-torsion period (`p ≠ 0` with `NoZeroSMulDivisors ℤ 𝕜`), the period subgroup
`zmultiples p` is infinite cyclic, identified with `ℤ` by `n ↦ n • p`. -/
noncomputable def intEquivZMultiples (hp : p ≠ 0) : ℤ ≃+ zmultiples p :=
  AddEquiv.ofBijective
    ({ toFun := fun n => ⟨n • p, mem_zmultiples_iff.2 ⟨n, rfl⟩⟩
       map_zero' := by ext; simp
       map_add' := fun n m => by ext; simp [add_zsmul] } : ℤ →+ zmultiples p)
    (by
      refine ⟨fun n m h => ?_, fun a => ?_⟩
      · have h' : n • p = m • p := congrArg Subtype.val h
        have hsub : (n - m) • p = 0 := by rw [sub_zsmul, h']; abel
        rcases smul_eq_zero.1 hsub with hnm | hp'
        · exact sub_eq_zero.1 hnm
        · exact absurd hp' hp
      · obtain ⟨n, hn⟩ := mem_zmultiples_iff.1 a.2
        exact ⟨n, by ext; exact hn⟩)

/-- For a non-torsion period, the deck transformation group of the covering
`(↑) : 𝕜 → AddCircle p` of a preconnected base is infinite cyclic: `Multiplicative ℤ`. For
`𝕜 = ℝ` this is the deck group of the universal cover `ℝ → S¹`. -/
noncomputable def addCircleMulEquivMultInt [PreconnectedSpace 𝕜]
    [DiscreteTopology (zmultiples p)] (hp : p ≠ 0) :
    Multiplicative ℤ ≃* Deck ((↑) : 𝕜 → AddCircle p) :=
  (intEquivZMultiples hp).toMultiplicative.trans addCircleMulEquiv

end Deck

end TauCeti
