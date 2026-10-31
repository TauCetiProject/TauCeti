/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Linear equivariant actions on families of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a period family and let a monoid `Γ` act on the parameter space
`Y`. The period translation action of `Λ` on `Y × E` (`TauCeti.periodAddAction`) has orbit space
the family of tori `(Y × E)/Λ → Y`. This file lifts the action of `Γ` to that family by fibrewise
additive maps.

The input is a family `R g y : E →+ E` satisfying the cocycle laws `R 1 y = id` and
`R (g * h) y = R g (h • y) ∘ R h y`, together with a representation `ρ : Representation ℤ Γ Λ`
for which the periods are equivariant: `P (g • y) (ρ g l) = R g y (P y l)`. For holomorphic
families of complex tori, `R g y` is a complex linear automorphism of `E` depending
holomorphically on `y`; only additivity is used here, and for a group `Γ` invertibility of
`R g y` follows from the cocycle laws (`TauCeti.linearCocycle_apply_inv_apply`).

* `TauCeti.linearCocycleMulAction` is the action `g • (y, v) = (g • y, R g y v)` of `Γ` on
  `Y × E`. It normalizes the period translation action:
  `g • (l +ᵥ p) = ρ g l +ᵥ g • p` (`TauCeti.linearCocycleMulAction_smul_vadd`).
* `TauCeti.torusFamilyLinearMulAction` is the action of `Γ` descended to the orbit space
  `(Y × E)/Λ`. The projection of the family to `Y` is equivariant
  (`TauCeti.torusFamilyProjection_smul`), so `g` carries the fibre over `y` to the fibre over
  `g • y`.

The descended action fixes the zero section over each fixed point of the base: the stabilizer of
the class of `(y, 0)` is the stabilizer of `y`
(`TauCeti.torusFamilyLinearMulAction_stabilizer_mk_zero`). Consequently the action on the total
space of the family is free exactly when the action on the base is
(`TauCeti.isCancelSMul_torusFamilyLinearMulAction_iff`); in particular this action never removes
a base stabilizer. Topologically, both actions act by continuous maps when the base action does
and `(y, v) ↦ R g y v` is continuous, and both are properly discontinuous whenever the base
action is, with no further hypothesis.

## Main definitions

* `TauCeti.linearCocycleMulAction`: the action `g • (y, v) = (g • y, R g y v)` on `Y × E`.
* `TauCeti.torusFamilyLinearMulAction`: its descent to the family of tori `(Y × E)/Λ`.

## Main results

* `TauCeti.linearCocycleMulAction_smul_vadd`: the lifted action normalizes the period
  translations, twisting them by `ρ`.
* `TauCeti.torusFamilyProjection_smul`: the projection of the family of tori is equivariant.
* `TauCeti.torusFamilyLinearMulAction_stabilizer_mk_zero`: the stabilizer of a point of the zero
  section is the stabilizer of its base point.
* `TauCeti.isCancelSMul_torusFamilyLinearMulAction_iff`: the action on the family of tori is free
  if and only if the action on the base is free.
* `TauCeti.continuousConstSMul_torusFamilyLinearMulAction`,
  `TauCeti.properlyDiscontinuousSMul_torusFamilyLinearMulAction`: continuity and proper
  discontinuity of the descended action.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices, and the actions of discrete groups on them).
-/

public section

open Function

namespace TauCeti

variable {Y Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]

section Monoid

variable {Γ : Type*} [Monoid Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))

/-! ### The lifted action on `Y × E` -/

/-- The action of `Γ` on `Y × E` lifted from the action on `Y` by the cocycle `R`:
`g • (y, v) = (g • y, R g y v)`. The cocycle laws `R 1 y = id` and
`R (g * h) y = R g (h • y) ∘ R h y` are exactly the action laws. -/
@[instance_reducible]
def linearCocycleMulAction : MulAction Γ (Y × E) where
  smul g p := (g • p.1, R g p.1 p.2)
  one_smul p := by
    -- Unfold the action field to expose the concrete formula.
    change (1 • p.1, R 1 p.1 p.2) = p
    rw [one_smul, hone]
  mul_smul g h p := by
    -- Unfold the action field to expose the concrete formula.
    change ((g * h) • p.1, R (g * h) p.1 p.2) = (g • h • p.1, R g (h • p.1) (R h p.1 p.2))
    rw [mul_smul, hmul]

/-- The lifted action acts on the parameter by the base action and on the vector by `R`. -/
@[simp] theorem linearCocycleMulAction_smul (g : Γ) (p : Y × E) :
    letI := linearCocycleMulAction R hone hmul
    g • p = (g • p.1, R g p.1 p.2) := (rfl)

variable (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))

include hP in
/-- **The lifted action normalizes the period translations.** When the periods are equivariant,
`P (g • y) (ρ g l) = R g y (P y l)`, acting by `g` after translating by the period of `l` is
translating by the period of `ρ g l` after acting by `g`. -/
theorem linearCocycleMulAction_smul_vadd (g : Γ) (l : Λ) (p : Y × E) :
    letI := linearCocycleMulAction R hone hmul
    letI := periodAddAction P
    g • (l +ᵥ p) = ρ g l +ᵥ g • p := by
  simp [hP]

/-! ### The descended action on the family of tori -/

include hP in
/-- The lifted action carries period orbits to period orbits. -/
private theorem orbitRel_smul (g : Γ) (p q : Y × E) :
    letI := periodAddAction P
    letI := linearCocycleMulAction R hone hmul
    AddAction.orbitRel Λ (Y × E) p q → AddAction.orbitRel Λ (Y × E) (g • p) (g • q) := by
  let _ := periodAddAction P
  let _ := linearCocycleMulAction R hone hmul
  intro hpq
  obtain ⟨l, rfl⟩ := AddAction.mem_orbit_iff.1 (AddAction.orbitRel_apply.1 hpq)
  rw [AddAction.orbitRel_apply, linearCocycleMulAction_smul_vadd R hone hmul P ρ hP]
  exact AddAction.mem_orbit _ _

include hP in
/-- The action of `Γ` on the family of tori `(Y × E)/Λ` descended from
`TauCeti.linearCocycleMulAction`: `g • [y, v] = [g • y, R g y v]`. It is well defined because
the lifted action carries period orbits to period orbits
(`TauCeti.linearCocycleMulAction_smul_vadd`). -/
@[instance_reducible]
def torusFamilyLinearMulAction :
    letI := periodAddAction P
    MulAction Γ (AddAction.orbitRel.Quotient Λ (Y × E)) :=
  letI := periodAddAction P
  letI := linearCocycleMulAction R hone hmul
  { smul g := Quotient.map (g • ·) (orbitRel_smul R hone hmul P ρ hP g)
    one_smul x := by
      induction x using Quotient.inductionOn with
      | h p => exact congrArg (Quotient.mk _) (one_smul Γ p)
    mul_smul g h x := by
      induction x using Quotient.inductionOn with
      | h p => exact congrArg (Quotient.mk _) (mul_smul g h p) }

/-- The descended action sends the class of `(y, v)` to the class of `(g • y, R g y v)`. -/
@[simp] theorem torusFamilyLinearMulAction_smul_mk (g : Γ) (p : Y × E) :
    letI := periodAddAction P
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    g • (Quotient.mk _ p : AddAction.orbitRel.Quotient Λ (Y × E)) =
      Quotient.mk _ (g • p.1, R g p.1 p.2) := (rfl)

/-- **The projection of the family of tori is equivariant**: `g` carries the fibre over `y` to
the fibre over `g • y`. -/
@[simp] theorem torusFamilyProjection_smul (g : Γ) (x : letI := periodAddAction P
      AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    torusFamilyProjection P (g • x) = g • torusFamilyProjection P x := by
  induction x using Quotient.inductionOn with
  | h p => simp

/-! ### Topology of the lifted and descended actions -/

section Topology

variable [TopologicalSpace Y] [TopologicalSpace E]

/-- The lifted action on `Y × E` acts by continuous maps when the base action does and each
`(y, v) ↦ R g y v` is continuous. -/
theorem continuousConstSMul_linearCocycleMulAction [ContinuousConstSMul Γ Y]
    (hR : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2) :
    letI := linearCocycleMulAction R hone hmul
    ContinuousConstSMul Γ (Y × E) := by
  let _ := linearCocycleMulAction R hone hmul
  refine ⟨fun g ↦ ?_⟩
  simp only [linearCocycleMulAction_smul]
  exact ((continuous_const_smul g).comp continuous_fst).prodMk (hR g)

/-- The descended action on the family of tori acts by continuous maps when the base action
does and each `(y, v) ↦ R g y v` is continuous. -/
theorem continuousConstSMul_torusFamilyLinearMulAction [ContinuousConstSMul Γ Y]
    (hR : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2) :
    letI := periodAddAction P
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    ContinuousConstSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := linearCocycleMulAction R hone hmul
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  have := continuousConstSMul_linearCocycleMulAction R hone hmul hR
  exact ⟨fun g ↦ (continuous_const_smul g).quotient_map' (orbitRel_smul R hone hmul P ρ hP g)⟩

/-- The lifted action on `Y × E` is properly discontinuous whenever the base action is, since the
first projection is continuous and equivariant. -/
theorem properlyDiscontinuousSMul_linearCocycleMulAction [ProperlyDiscontinuousSMul Γ Y] :
    letI := linearCocycleMulAction R hone hmul
    ProperlyDiscontinuousSMul Γ (Y × E) :=
  let _ := linearCocycleMulAction R hone hmul
  continuous_fst.properlyDiscontinuousSMul fun g p ↦
    congrArg Prod.fst (linearCocycleMulAction_smul R hone hmul g p)

/-- **Proper discontinuity of the descended action.** The action on the family of tori is
properly discontinuous whenever the base action is, since the projection of the family is
continuous and equivariant. -/
theorem properlyDiscontinuousSMul_torusFamilyLinearMulAction [ProperlyDiscontinuousSMul Γ Y] :
    letI := periodAddAction P
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    ProperlyDiscontinuousSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)) :=
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  (continuous_torusFamilyProjection P).properlyDiscontinuousSMul
    (torusFamilyProjection_smul R hone hmul P ρ hP)

end Topology

end Monoid

section Group

variable {Γ : Type*} [Group Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))

include hone hmul in
/-- **A cocycle over a group action is invertible**: `R g⁻¹ (g • y)` is a right inverse of
`R g y`, since their composite is `R (g * g⁻¹) (g • y) = R 1 (g • y)`. -/
theorem linearCocycle_apply_inv_apply (g : Γ) (y : Y) (v : E) : R g y (R g⁻¹ (g • y) v) = v := by
  simpa [hone] using (hmul g g⁻¹ (g • y) v).symm

/-- An element fixing a point of the family of tori fixes its base point. -/
theorem torusFamilyLinearMulAction_stabilizer_le (x : letI := periodAddAction P
      AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    MulAction.stabilizer Γ x ≤ MulAction.stabilizer Γ (torusFamilyProjection P x) := by
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← torusFamilyProjection_smul R hone hmul P ρ hP, hg]

/-- **The descended action fixes the zero section over fixed base points**: the stabilizer of the
class of `(y, 0)` is the stabilizer of `y`. -/
theorem torusFamilyLinearMulAction_stabilizer_mk_zero (y : Y) :
    letI := periodAddAction P
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    MulAction.stabilizer Γ (Quotient.mk _ (y, 0) : AddAction.orbitRel.Quotient Λ (Y × E)) =
      MulAction.stabilizer Γ y := by
  let _ := periodAddAction P
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  have hle := torusFamilyLinearMulAction_stabilizer_le R hone hmul P ρ hP (Quotient.mk _ (y, 0))
  rw [torusFamilyProjection_mk] at hle
  refine le_antisymm hle ?_
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [torusFamilyLinearMulAction_smul_mk, map_zero, hg]

/-- **Freeness of the linear action.** The action of a group `Γ` on the family of tori is free
exactly when its action on the base is free: a base stabilizer fixes the corresponding point of
the zero section. -/
theorem isCancelSMul_torusFamilyLinearMulAction_iff :
    letI := periodAddAction P
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)) ↔ IsCancelSMul Γ Y := by
  let _ := periodAddAction P
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  simp only [isCancelSMul_iff_eq_one_of_smul_eq, ← MulAction.mem_stabilizer_iff]
  constructor
  · intro h g y hg
    exact h g _ ((torusFamilyLinearMulAction_stabilizer_mk_zero R hone hmul P ρ hP y).ge hg)
  · intro h g x hg
    exact h g _ (torusFamilyLinearMulAction_stabilizer_le R hone hmul P ρ hP x hg)

end Group

end TauCeti
