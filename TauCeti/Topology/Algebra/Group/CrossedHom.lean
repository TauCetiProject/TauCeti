/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Separation.Basic

import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle.Topology

/-!
# Crossed homomorphisms twisted by a unit-valued function

Let `H` be a group, `R` a semiring and `χ : H → Rˣ` a unit-valued function. A function
`F : H → R` is a **crossed homomorphism** for `χ` when

  `F (x * y) = χ x * F y + F x`

for all `x y : H` (`TauCeti.IsCrossedHom`). The predicate itself only reads the values of `χ`, so
it is stated for any `χ` with a `FunLike` coercion to `H → Rˣ`; when `χ : H →* Rˣ` is a character
(a monoid homomorphism), `H` acts on `R` through `χ` and the crossed homomorphisms for `χ` are
exactly the `1`-cocycles of `H` with values in this action, written without a module structure on
`R`. For `R = ℤ_p` and a continuous character `χ : G →ₜ* ℤ_pˣ` of a pro-`p` group, the continuous
crossed homomorphisms `G → ℤ_p` for `χ` are the compatible systems of continuous `1`-cocycles with
values in the twisted coefficients `I(χ)/pⁱ`, and their values on a minimal generating tuple are
what Labute's prescription property of `χ` prescribes.

This file records the elementary calculus of crossed homomorphisms. The definition, the cocycle
identity and the composite with a homomorphism need only a semiring and an arbitrary unit-valued
`χ`; the values at `1`, at an inverse and at a power, the value on a product of elements on which
`χ` is trivial, and the fact that two continuous crossed homomorphisms for the same `χ` into a
`T1` topological ring agreeing on a topological generating set of `H` are equal (the analogue for
crossed homomorphisms of the uniqueness of continuous `1`-cocycles on a topological generating
set) use additive inverses and the multiplicativity of `χ`, and are stated for a ring and a
character `χ`.

## Main definitions

* `TauCeti.IsCrossedHom`: `F : H → R` is a crossed homomorphism for the unit-valued `χ`.

## Main results

* `TauCeti.IsCrossedHom.ringHom_comp`: composing with a semiring homomorphism `φ` gives a crossed
  homomorphism for `Units.map φ ∘ χ`.
* `TauCeti.IsCrossedHom.map_pow`: `F (x ^ k) = (1 + χ x + ⋯ + χ x ^ (k - 1)) * F x`.
* `TauCeti.IsCrossedHom.map_list_prod_of_forall_eq_one`: on a product of elements on which `χ` is
  trivial, `F` is additive.
* `TauCeti.IsCrossedHom.map_commutatorElement`: for a commutative `R`,
  `F ⁅x, y⁆ = (χ x - 1) * F y - (χ y - 1) * F x`.
* `TauCeti.IsCrossedHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top`: two continuous crossed
  homomorphisms agreeing on a topological generating set are equal.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.3.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2.
-/

public section

namespace TauCeti

variable {H : Type*} [Group H] {R : Type*}

section Semiring

variable [Semiring R] {F' : Type*} [FunLike F' H Rˣ]

/-- A function `F : H → R` is a **crossed homomorphism** for the unit-valued function `χ` when
`F (x * y) = χ x * F y + F x` for all `x y : H`. Here `χ` is any function `H → Rˣ` (via a `FunLike`
coercion); when `χ : H →* Rˣ` is a character, this is the `1`-cocycle condition for the action of
`H` on `R` through `χ`. -/
def IsCrossedHom (χ : F') (F : H → R) : Prop :=
  ∀ x y, F (x * y) = (χ x : R) * F y + F x

variable {χ : F'} {F : H → R}

/-- The defining property of `IsCrossedHom`. -/
theorem isCrossedHom_iff : IsCrossedHom χ F ↔ ∀ x y, F (x * y) = (χ x : R) * F y + F x :=
  Iff.rfl

namespace IsCrossedHom

variable (hF : IsCrossedHom χ F)
include hF

/-- The cocycle identity of a crossed homomorphism. -/
theorem map_mul (x y : H) : F (x * y) = (χ x : R) * F y + F x :=
  hF x y

/-- The composite of a crossed homomorphism for `χ` with a homomorphism `φ` is a crossed
homomorphism for the unit-valued function `χ ∘ φ`. -/
theorem comp {H' : Type*} [Group H'] {F'' : Type*} [FunLike F'' H' H] [MonoidHomClass F'' H' H]
    (φ : F'') {F''' : Type*} [FunLike F''' H' Rˣ] {χ' : F'''} (hχ' : ∀ x, χ' x = χ (φ x)) :
    IsCrossedHom χ' (F ∘ φ) := fun x y ↦ by
  rw [Function.comp_apply, _root_.map_mul, hF.map_mul, hχ', Function.comp_apply,
    Function.comp_apply]

end IsCrossedHom

/-- The composite of a crossed homomorphism for a character `χ : H →* Rˣ` with a semiring
homomorphism `φ : R →+* S` is a crossed homomorphism for the character `Units.map φ ∘ χ`. -/
theorem IsCrossedHom.ringHom_comp {S : Type*} [Semiring S] {χ : H →* Rˣ} {F : H → R}
    (hF : IsCrossedHom χ F) (φ : R →+* S) :
    IsCrossedHom ((Units.map (φ : R →* S)).comp χ) (φ ∘ F) := fun x y ↦ by
  rw [Function.comp_apply, hF.map_mul x y, map_add, _root_.map_mul, MonoidHom.comp_apply,
    Units.coe_map, MonoidHom.coe_ofClass, Function.comp_apply, Function.comp_apply]

end Semiring

section Ring

variable [Ring R] {F' : Type*} [FunLike F' H Rˣ] [MonoidHomClass F' H Rˣ] {χ : F'} {F : H → R}

namespace IsCrossedHom

variable (hF : IsCrossedHom χ F)
include hF

/-- A crossed homomorphism vanishes at `1`. -/
theorem map_one : F 1 = 0 := by
  have h := hF.map_mul 1 1
  rw [one_mul, _root_.map_one, Units.val_one, one_mul] at h
  simpa using h

/-- The value of a crossed homomorphism at an inverse, multiplied through by the character. -/
theorem mul_map_inv (x : H) : (χ x : R) * F x⁻¹ = -F x := by
  have h := hF.map_mul x x⁻¹
  rw [mul_inv_cancel, hF.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The value of a crossed homomorphism at an inverse. -/
theorem map_inv (x : H) : F x⁻¹ = -(((χ x)⁻¹ : Rˣ) : R) * F x := by
  calc F x⁻¹ = (((χ x)⁻¹ : Rˣ) : R) * ((χ x : R) * F x⁻¹) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = -(((χ x)⁻¹ : Rˣ) : R) * F x := by rw [hF.mul_map_inv, mul_neg, neg_mul]

/-- The value of a crossed homomorphism at a power is a geometric sum in the character times the
value at the base. -/
theorem map_pow (x : H) (k : ℕ) :
    F (x ^ k) = (∑ j ∈ Finset.range k, (χ x : R) ^ j) * F x := by
  induction k with
  | zero => simp [hF.map_one]
  | succ k ih =>
    rw [pow_succ, hF.map_mul, ih, _root_.map_pow, Units.val_pow_eq_pow_val,
      Finset.sum_range_succ, add_mul, add_comm]

/-- On an element on which the character is trivial, a crossed homomorphism is additive along
powers: `F (x ^ k) = k * F x`. -/
theorem map_pow_of_eq_one {x : H} (hx : χ x = 1) (k : ℕ) : F (x ^ k) = k * F x := by
  rw [hF.map_pow, hx, Units.val_one]
  simp

/-- On a product of elements on which the character is trivial, a crossed homomorphism is
additive. -/
theorem map_list_prod_of_forall_eq_one {l : List H} (hl : ∀ a ∈ l, χ a = 1) :
    F l.prod = (l.map F).sum := by
  induction l with
  | nil => simp [hF.map_one]
  | cons a l ih =>
    rw [List.prod_cons, hF.map_mul, hl a (by simp), Units.val_one, one_mul,
      ih fun b hb ↦ hl b (by simp [hb]), List.map_cons, List.sum_cons, add_comm]

section Topology

variable [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace R] [IsTopologicalAddGroup R]
  [T1Space R]

omit hF in
/-- **Two continuous crossed homomorphisms for the same character agreeing on a topological
generating set are equal.** Their difference is a continuous crossed homomorphism whose zero locus
is a closed subgroup containing the generating set, hence all of `H`. -/
theorem eq_of_eqOn_of_topologicalClosure_closure_eq_top {F₁ F₂ : H → R} (h₁ : IsCrossedHom χ F₁)
    (h₂ : IsCrossedHom χ F₂) (hc₁ : Continuous F₁) (hc₂ : Continuous F₂) {s : Set H}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) (h : Set.EqOn F₁ F₂ s) : F₁ = F₂ := by
  have hsub : IsCrossedHom χ (F₁ - F₂) := fun x y ↦ by
    simp only [Pi.sub_apply, h₁ x y, h₂ x y, mul_sub, add_sub_add_comm]
  -- `H` acts on `R` through `χ`, and for this action a crossed homomorphism is a `1`-cocycle.
  let : MulAction H R := MulAction.compHom R ((Units.coeHom R).comp (χ : H →* Rˣ))
  have hcoc : groupCohomology.IsCocycle₁ (F₁ - F₂) := fun x y ↦ by
    rw [hsub.map_mul, MulAction.compHom_smul_def, MonoidHom.comp_apply, Units.coeHom_apply,
      smul_eq_mul, MonoidHom.coe_ofClass]
  exact sub_eq_zero.1 (groupCohomology.eq_zero_of_eqOn_zero_of_topologicalClosure_closure_eq_top
    hcoc (hc₁.sub hc₂) hs fun g hg ↦ sub_eq_zero.2 (h hg))

end Topology

end IsCrossedHom

end Ring

section CommRing

open scoped commutatorElement

variable [CommRing R] {F' : Type*} [FunLike F' H Rˣ] [MonoidHomClass F' H Rˣ] {χ : F'} {F : H → R}

/-- The value of a crossed homomorphism on the commutator `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`, read off
`F (⁅x, y⁆ * (y * x)) = F (x * y)`; the character kills the commutator because `Rˣ` is
commutative. -/
theorem IsCrossedHom.map_commutatorElement (hF : IsCrossedHom χ F) (x y : H) :
    F ⁅x, y⁆ = ((χ x : R) - 1) * F y - ((χ y : R) - 1) * F x := by
  have h : ⁅x, y⁆ * (y * x) = x * y := by
    rw [commutatorElement_def]
    group
  have h1 := hF.map_mul ⁅x, y⁆ (y * x)
  rw [h, hF.map_mul x y, hF.map_mul y x, _root_.map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (χ x) (χ y)), Units.val_one, one_mul] at h1
  linear_combination -h1

end CommRing

end TauCeti
