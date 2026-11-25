/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import TauCeti.GroupTheory.Automorphism.Outer
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Discrete

/-!
# The outer automorphism group of the quaternion group

Checks for `TauCeti.OuterAut` and `TauCeti.ContinuousOut` on the quaternion group
`Q₈ = QuaternionGroup 2`: `MulAut Q₈` has order `24`, the inner automorphisms form `Q₈/{±1}`, of
order `4`, so `OuterAut Q₈` has order `6`; with the discrete topology `ContinuousOut Q₈` has
order `6` too.

An automorphism `φ` of `Q₈` is determined by the pair `(φ(a 1), φ(xa 0))`, since
`a i = (a 1) ^ i` and `xa i = xa 0 * (a 1) ^ i`. Conversely a pair `(u, v)` comes from an
automorphism exactly when `a i ↦ u ^ i`, `xa i ↦ v * u ^ i` is an injective homomorphism, which
is decidable; there are `24` such pairs.
-/

public section

open QuaternionGroup

namespace TauCeti.QuaternionOuterAut

/-- The quaternion group `Q₈`. -/
local notation "Q₈" => QuaternionGroup 2

/-- The map `a i ↦ u ^ i`, `xa i ↦ v * u ^ i` attached to a pair `p = (u, v)`. -/
private def ofGens (p : Q₈ × Q₈) : Q₈ → Q₈
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val

/-- The pairs `(u, v)` for which `ofGens (u, v)` is an injective homomorphism. -/
private def IsGenPair (p : Q₈ × Q₈) : Prop :=
  (∀ x y, ofGens p (x * y) = ofGens p x * ofGens p y) ∧ Function.Injective (ofGens p)

private instance : DecidablePred IsGenPair := fun _ => by unfold IsGenPair; infer_instance

/-- Exactly `24` pairs satisfy `IsGenPair`. -/
private theorem card_isGenPair : Fintype.card {p : Q₈ × Q₈ // IsGenPair p} = 24 := by
  decide +kernel

/-- An automorphism `φ` of `Q₈` agrees with `ofGens` of its values on `a 1` and `xa 0`. -/
private theorem ofGens_apply_eq (φ : MulAut Q₈) (x : Q₈) : ofGens (φ (a 1), φ (xa 0)) x = φ x := by
  cases x with
  | a i => simp [ofGens, ← map_pow, a_one_pow]
  | xa i => simp [ofGens, ← map_pow, ← map_mul, a_one_pow, xa_mul_a]

/-- The images of `a 1` and `xa 0` under an automorphism form a pair satisfying `IsGenPair`. -/
private theorem isGenPair_mulAut (φ : MulAut Q₈) : IsGenPair (φ (a 1), φ (xa 0)) := by
  have h : ofGens (φ (a 1), φ (xa 0)) = φ := funext (ofGens_apply_eq φ)
  refine ⟨fun x y => ?_, ?_⟩ <;> rw [h]
  · exact map_mul φ x y
  · exact φ.injective

/-- The automorphism of `Q₈` attached to a pair satisfying `IsGenPair`. -/
private noncomputable def mulAutOfIsGenPair (p : {p : Q₈ × Q₈ // IsGenPair p}) : MulAut Q₈ :=
  MulEquiv.ofBijective (MulHom.mk (ofGens p.val) p.property.1)
    (Finite.injective_iff_bijective.1 p.property.2)

private theorem mulAutOfIsGenPair_apply (p : {p : Q₈ × Q₈ // IsGenPair p}) (x : Q₈) :
    mulAutOfIsGenPair p x = ofGens p.val x :=
  rfl

/-- `MulAut Q₈` is in bijection with the pairs satisfying `IsGenPair`, by
`φ ↦ (φ(a 1), φ(xa 0))`. -/
private noncomputable def mulAutEquiv : MulAut Q₈ ≃ {p : Q₈ × Q₈ // IsGenPair p} where
  toFun φ := ⟨(φ (a 1), φ (xa 0)), isGenPair_mulAut φ⟩
  invFun := mulAutOfIsGenPair
  left_inv φ := MulEquiv.ext fun x => by
    rw [mulAutOfIsGenPair_apply, ofGens_apply_eq]
  right_inv p := by
    obtain ⟨⟨u, v⟩, hp⟩ := p
    have h1 : (1 : ZMod (2 * 2)).val = 1 := rfl
    ext <;> simp [mulAutOfIsGenPair_apply, ofGens, h1]

/-- `MulAut Q₈` has order `24`. -/
theorem card_mulAut : Nat.card (MulAut Q₈) = 24 := by
  rw [Nat.card_congr mulAutEquiv, Nat.card_eq_fintype_card, card_isGenPair]

/-- The centre of `Q₈` is `{±1}`, of order `2`. -/
theorem card_center : Nat.card (Subgroup.center Q₈) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The inner automorphisms of `Q₈` form `Q₈/{±1}`, of order `4`. -/
theorem card_range_conj : Nat.card (MulAut.conj : Q₈ →* MulAut Q₈).range = 4 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q₈)
  rw [card_center, Nat.card_eq_fintype_card, QuaternionGroup.card] at h
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, MulAut.ker_conj]
  omega

/-- `OuterAut Q₈` has order `24 / 4 = 6`. -/
theorem card_outerAut : Nat.card (OuterAut Q₈) = 6 := by
  have h : Nat.card (MulAut Q₈) =
      Nat.card (OuterAut Q₈) * Nat.card (MulAut.conj : Q₈ →* MulAut Q₈).range :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [card_mulAut, card_range_conj] at h
  omega

section Discrete

/-- The discrete topology on `Q₈`. -/
local instance instTopologicalSpace : TopologicalSpace Q₈ := ⊥

local instance instDiscreteTopology : DiscreteTopology Q₈ := ⟨rfl⟩

/-- With the discrete topology, `ContinuousOut Q₈` has order `6`, agreeing with `OuterAut Q₈`. -/
theorem card_continuousOut : Nat.card (ContinuousOut Q₈) = 6 := by
  rw [Nat.card_congr ContinuousOut.mulEquivOuterAutOfDiscrete.toEquiv, card_outerAut]

end Discrete

end TauCeti.QuaternionOuterAut
