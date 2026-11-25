/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Diagonal

import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Kernel

/-!
# The idele group of an algebraic function field

The **idele group** of an algebraic function field `F / k` is the restricted product

`J_F = ∏'_P F_Pˣ`

of the unit groups of the completions `F_P` at all places `P` of `F / k`, restricted with respect
to the unit groups `𝒪_Pˣ` of their valuation rings: an idele is a family of local units, all but
finitely many of which are integral units. Unlike the repartitions of
`TauCeti.FieldTheory.FunctionField.Repartition.Basic`, its components live in the completions.
The idele group is the domain of the local–global pairings of class field theory, which pair a
function with an idele through local symbols at every place.

This file constructs `J_F`, the diagonal embedding `Fˣ → J_F` of principal ideles, the subgroup
`U_F = ∏_P 𝒪_Pˣ` of unit ideles, and the divisor map

`div : J_F → Div(F),  x ↦ ∑_P ord_P(x_P) · P`.

The divisor map is surjective with kernel `U_F`, and it carries the principal idele of `z` to the
principal divisor of `z`. Consequently `J_F / U_F` is the divisor group of `F / k`, and the
quotient of `J_F` by `U_F Fˣ` is its divisor class group.

## Main definitions

* `TauCeti.IdeleGroup k F`: the idele group of `F / k`.
* `TauCeti.IdeleGroup.unitEmbedding`: the diagonal embedding `Fˣ →* J_F`.
* `TauCeti.IdeleGroup.unitIdeles k F`: the subgroup of ideles that are units everywhere.
* `TauCeti.IdeleGroup.orderSystem k F`: the places of `F / k` with the orders of idele
  components, as an order system on `Additive J_F`.
* `TauCeti.IdeleGroup.divisor` and `TauCeti.IdeleGroup.divisorHom`: the divisor of an idele, and
  its packaging as a group homomorphism `Additive J_F →+ Divisor k F`, the principal-divisor
  homomorphism of that order system.
* `TauCeti.IdeleGroup.quotientUnitIdelesEquiv`: `J_F / U_F ≃* Div(F)`.
* `TauCeti.IdeleGroup.quotientClassGroupEquiv`: `J_F / (U_F Fˣ) ≃* Cl(F)`.

## Main results

* `TauCeti.IdeleGroup.unitEmbedding_injective`: the diagonal embedding is injective.
* `TauCeti.IdeleGroup.divisor_unitEmbedding`: the divisor of a principal idele is the principal
  divisor of the function.
* `TauCeti.IdeleGroup.divisor_eq_zero_iff` and `TauCeti.IdeleGroup.divisor_surjective`: the
  kernel and the image of the divisor map.
* `TauCeti.IdeleGroup.exists_principal_eq_divisor_iff`: an idele has principal divisor exactly
  when it is a unit idele times a principal idele.

## Implementation notes

The places are Tau Ceti's normalized places `TauCeti.Place k F`, so only places trivial on `k`
occur; for a function field over a finite field these are all places. The completion is
`TauCeti.Place.Completion`, and its valuation ring is that of the extended place
`TauCeti.Place.completionPlace`. No topology is put on `J_F` here.

## References

* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich, eds.,
  *Algebraic Number Theory*, Chapter VII, §2 and §4.
* A. Weil, *Basic Number Theory*, Chapter IV, §3, and Chapter VI, §1.
-/

public section
noncomputable section

namespace TauCeti

open AlgebraicGeometry Filter
open scoped RestrictedProduct

variable (k F : Type*) [Field k] [Field F] [Algebra k F]

/-- **The idele group** `J_F = ∏'_P F_Pˣ` of `F / k`: families of units of the completions at
the places of `F / k` that are units of the completed valuation ring at all but finitely many
places. -/
abbrev IdeleGroup : Type _ :=
  Πʳ (P : Place k F), [P.Completionˣ, P.completionPlace.integers.unitGroup]

namespace IdeleGroup

/-- The idele group is commutative. Instance search does not derive this from the
restricted-product `CommGroup` instance, because the multiplication it carries is not identified
with the directly synthesized one at instance transparency; without this instance, subgroups of
`J_F` are not recognized as normal and the quotients below do not elaborate. -/
instance : IsMulCommutative (IdeleGroup k F) :=
  ⟨⟨fun _ _ ↦ RestrictedProduct.ext _ _ fun _ ↦ mul_comm _ _⟩⟩

variable {k F}

/-- An idele has order zero at all but finitely many places. -/
theorem eventually_ord_eq_zero (x : IdeleGroup k F) :
    ∀ᶠ (P : Place k F) in cofinite, P.completionPlace.ord (x P : P.Completion) = 0 :=
  (RestrictedProduct.eventually _ _ x).mono fun P hP ↦
    (P.completionPlace.mem_unitGroup_iff_ord_eq_zero (x P)).1 hP

/-- An idele has nonzero order at only finitely many places. -/
theorem finite_setOf_ord_ne_zero (x : IdeleGroup k F) :
    {P : Place k F | P.completionPlace.ord (x P : P.Completion) ≠ 0}.Finite :=
  Filter.eventually_cofinite.1 (eventually_ord_eq_zero x)

/-! ### Principal ideles -/

/-- A nonzero function is a unit of the completed valuation ring at all but finitely many
places. -/
private theorem eventually_units_map_mem_unitGroup (hF : IsFunctionField k F) (z : Fˣ) :
    ∀ᶠ (P : Place k F) in cofinite, Units.map (P.completionEmbedding : F →* P.Completion) z ∈
      P.completionPlace.integers.unitGroup := by
  filter_upwards [(Place.finite_setOf_ord_ne_zero hF (z : F)).compl_mem_cofinite] with P hP
  rw [Place.mem_unitGroup_iff_ord_eq_zero]
  simpa using hP

/-- **The diagonal embedding** `Fˣ →* J_F`, sending a function to its *principal idele*, the
family of its images in all completions. -/
def unitEmbedding (hF : IsFunctionField k F) : Fˣ →* IdeleGroup k F :=
  rationalDiagonal (fun P : Place k F ↦ Units.map (P.completionEmbedding : F →* P.Completion))
    (fun P ↦ P.completionPlace.integers.unitGroup) (eventually_units_map_mem_unitGroup hF)

@[simp]
theorem unitEmbedding_apply (hF : IsFunctionField k F) (z : Fˣ) (P : Place k F) :
    unitEmbedding hF z P = Units.map (P.completionEmbedding : F →* P.Completion) z :=
  rationalDiagonal_apply _ _ _ z P

/-- The component of a principal idele at `P` is the image of the function in the completion. -/
theorem coe_unitEmbedding_apply (hF : IsFunctionField k F) (z : Fˣ) (P : Place k F) :
    (unitEmbedding hF z P : P.Completion) = P.completionEmbedding (z : F) := by
  simp

/-- The diagonal embedding is injective. -/
theorem unitEmbedding_injective (hF : IsFunctionField k F) :
    Function.Injective (unitEmbedding hF) := by
  obtain ⟨P⟩ := Place.nonempty hF
  exact injective_rationalDiagonal _ _ _
    ⟨P, Units.map_injective P.completionEmbedding.toRingHom.injective⟩

/-! ### Unit ideles -/

variable (k F) in
/-- **The unit ideles** `U_F = ∏_P 𝒪_Pˣ`: the ideles whose every component is a unit of the
completed valuation ring. -/
def unitIdeles : Subgroup (IdeleGroup k F) :=
  integralSubgroup fun P : Place k F ↦ P.completionPlace.integers.unitGroup

@[simp]
theorem mem_unitIdeles_iff {x : IdeleGroup k F} :
    x ∈ unitIdeles k F ↔ ∀ P, x P ∈ P.completionPlace.integers.unitGroup :=
  mem_integralSubgroup _ x

/-- An idele is a unit idele exactly when it has order zero at every place. -/
theorem mem_unitIdeles_iff_ord_eq_zero {x : IdeleGroup k F} :
    x ∈ unitIdeles k F ↔ ∀ P : Place k F, P.completionPlace.ord (x P : P.Completion) = 0 := by
  simp only [mem_unitIdeles_iff, Place.mem_unitGroup_iff_ord_eq_zero]

/-! ### The divisor of an idele -/

variable (k F) in
/-- **The places of `F / k` as an order system on the idele group**: the order of an idele at `P`
is the order of its component at `P` in the completion. Its principal divisors are the divisors
of ideles. -/
def orderSystem : WeilDivisor.OrderSystem (Place k F) (Additive (IdeleGroup k F)) where
  ord P := P.completionPlace.ordAddMonoidHom.comp
    (RestrictedProduct.evalMonoidHom (fun Q : Place k F ↦ Q.Completionˣ) P).toAdditive
  finite_support x := (finite_setOf_ord_ne_zero x.toMul).subset fun P hP ↦ by
    simpa using hP

@[simp]
theorem orderSystem_ord (P : Place k F) (x : IdeleGroup k F) :
    (orderSystem k F).ord P (Additive.ofMul x) = P.completionPlace.ord (x P : P.Completion) := by
  simp [orderSystem]

/-- **The divisor homomorphism** `J_F → Div(F)`, `x ↦ ∑_P ord_P(x_P) · P`, in its additivized
form: the principal-divisor homomorphism of `TauCeti.IdeleGroup.orderSystem`. -/
def divisorHom : Additive (IdeleGroup k F) →+ Divisor k F :=
  (orderSystem k F).principalHom

/-- **The divisor** `div x = ∑_P ord_P(x_P) · P` of an idele. -/
def divisor (x : IdeleGroup k F) : Divisor k F :=
  divisorHom (Additive.ofMul x)

@[simp]
theorem divisorHom_ofMul (x : IdeleGroup k F) : divisorHom (Additive.ofMul x) = divisor x :=
  (rfl)

theorem divisorHom_apply (x : Additive (IdeleGroup k F)) :
    divisorHom x = divisor x.toMul :=
  (rfl)

/-- The coefficient of a place in the divisor of an idele is the order of its component there. -/
@[simp]
theorem coeff_divisor (x : IdeleGroup k F) (P : Place k F) :
    (divisor x).coeff P = P.completionPlace.ord (x P : P.Completion) := by
  simp [divisor, divisorHom]

theorem mem_support_divisor_iff {x : IdeleGroup k F} {P : Place k F} :
    P ∈ (divisor x).support ↔ P.completionPlace.ord (x P : P.Completion) ≠ 0 := by
  rw [WeilDivisor.mem_support_iff, coeff_divisor]

@[simp]
theorem divisor_one : divisor (1 : IdeleGroup k F) = 0 :=
  map_zero divisorHom

theorem divisor_mul (x y : IdeleGroup k F) : divisor (x * y) = divisor x + divisor y :=
  map_add divisorHom (Additive.ofMul x) (Additive.ofMul y)

@[simp]
theorem divisor_inv (x : IdeleGroup k F) : divisor x⁻¹ = -divisor x :=
  map_neg divisorHom (Additive.ofMul x)

theorem divisor_div (x y : IdeleGroup k F) : divisor (x / y) = divisor x - divisor y :=
  map_sub divisorHom (Additive.ofMul x) (Additive.ofMul y)

/-- **The divisor of a principal idele is the principal divisor** of the function. -/
@[simp]
theorem divisor_unitEmbedding (hF : IsFunctionField k F) (z : Fˣ) :
    divisor (unitEmbedding hF z) = Divisor.principal hF z :=
  WeilDivisor.ext fun P ↦ by
    rw [coeff_divisor, coe_unitEmbedding_apply, Place.ord_completionEmbedding,
      Divisor.coeff_principal]

/-- The idele concentrated at a single place `P` has divisor `ord_P(u) · P`. -/
@[simp]
theorem divisor_mulSingle [DecidableEq (Place k F)] (P : Place k F) (u : P.Completionˣ) :
    divisor (RestrictedProduct.mulSingle (fun Q : Place k F ↦ Q.completionPlace.integers.unitGroup)
      P u) = P.completionPlace.ord (u : P.Completion) • WeilDivisor.ofPoint P := by
  refine WeilDivisor.ext fun Q ↦ ?_
  rw [coeff_divisor, RestrictedProduct.coe_mulSingle_apply, WeilDivisor.coeff_zsmul]
  by_cases hQ : Q = P
  · subst hQ
    simp [WeilDivisor.coeff_ofPoint_self]
  · simp [WeilDivisor.coeff_ofPoint_of_ne hQ, Pi.mulSingle_eq_of_ne hQ]

/-- **The kernel of the divisor map** is the group of unit ideles. -/
theorem divisor_eq_zero_iff {x : IdeleGroup k F} : divisor x = 0 ↔ x ∈ unitIdeles k F := by
  rw [mem_unitIdeles_iff_ord_eq_zero, ← divisorHom_ofMul, divisorHom, ← AddMonoidHom.mem_ker]
  simpa only [orderSystem_ord] using
    (orderSystem k F).mem_principalKernel_iff_forall_ord_eq_zero (g := Additive.ofMul x)

/-- **The divisor map is surjective**: every divisor is the divisor of an idele, built from local
elements of prescribed order at finitely many places. -/
theorem divisor_surjective : Function.Surjective (divisor : IdeleGroup k F → Divisor k F) := by
  classical
  intro D
  induction D using Finsupp.induction with
  | zero => exact ⟨1, divisor_one⟩
  | single_add P n D _ _ ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨t, ht0, ht⟩ := P.completionPlace.exists_ne_zero_ord_eq n
    refine ⟨RestrictedProduct.mulSingle
      (fun Q : Place k F ↦ Q.completionPlace.integers.unitGroup) P (Units.mk0 t ht0) * x, ?_⟩
    rw [divisor_mul, divisor_mulSingle, Units.val_mk0, ht, hx,
      WeilDivisor.single_eq_zsmul_ofPoint]

/-- **An idele has principal divisor exactly when it is a unit idele times a principal idele.** -/
theorem exists_principal_eq_divisor_iff (hF : IsFunctionField k F) {x : IdeleGroup k F} :
    (∃ z : Fˣ, Divisor.principal hF z = divisor x) ↔
      ∃ u ∈ unitIdeles k F, ∃ z : Fˣ, u * unitEmbedding hF z = x := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨x * unitEmbedding hF z⁻¹, divisor_eq_zero_iff.1 ?_, z, ?_⟩
    · rw [divisor_mul, divisor_unitEmbedding, Divisor.principal_inv, hz, add_neg_cancel]
    · rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  · rintro ⟨u, hu, z, rfl⟩
    exact ⟨z, by rw [divisor_mul, divisor_eq_zero_iff.2 hu, zero_add, divisor_unitEmbedding]⟩

/-! ### The divisor group and the divisor class group as quotients of the idele group -/

/-- The divisor map, as a homomorphism to the multiplicative divisor group. -/
private def divisorMonoidHom : IdeleGroup k F →* Multiplicative (Divisor k F) :=
  AddMonoidHom.toMultiplicativeRight divisorHom

private theorem ker_divisorMonoidHom :
    (divisorMonoidHom : IdeleGroup k F →* _).ker = unitIdeles k F :=
  Subgroup.ext fun _ ↦ MonoidHom.mem_ker.trans divisor_eq_zero_iff

variable (k F) in
/-- **The idele group modulo the unit ideles is the divisor group**: `J_F / U_F ≃* Div(F)`,
induced by the divisor map. -/
def quotientUnitIdelesEquiv : IdeleGroup k F ⧸ unitIdeles k F ≃* Multiplicative (Divisor k F) :=
  (QuotientGroup.quotientMulEquivOfEq ker_divisorMonoidHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective divisorMonoidHom divisor_surjective)

@[simp]
theorem quotientUnitIdelesEquiv_mk (x : IdeleGroup k F) :
    quotientUnitIdelesEquiv k F x = Multiplicative.ofAdd (divisor x) :=
  (rfl)

/-- The divisor class of an idele, as a homomorphism to the multiplicative divisor class
group. -/
private def divisorClassMonoidHom (hF : IsFunctionField k F) :
    IdeleGroup k F →* Multiplicative (Place.orderSystem hF).ClassGroup :=
  AddMonoidHom.toMultiplicativeRight ((Place.orderSystem hF).divisorClass.comp divisorHom)

private theorem ker_divisorClassMonoidHom (hF : IsFunctionField k F) :
    (divisorClassMonoidHom hF).ker = unitIdeles k F ⊔ (unitEmbedding hF).range := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le (fun u hu ↦ ?_) ?_)
  · obtain ⟨u, hu, z, rfl⟩ := (exists_principal_eq_divisor_iff hF).1
      ((Divisor.divisorClass_eq_zero_iff hF).1 (MonoidHom.mem_ker.1 hx))
    exact Subgroup.mul_mem_sup hu ⟨z, rfl⟩
  · exact MonoidHom.mem_ker.2 <| (Divisor.divisorClass_eq_zero_iff hF).2
      ((exists_principal_eq_divisor_iff hF).2 ⟨u, hu, 1, by rw [map_one, mul_one]⟩)
  · rintro _ ⟨z, rfl⟩
    exact MonoidHom.mem_ker.2 <| (Divisor.divisorClass_eq_zero_iff hF).2
      ((exists_principal_eq_divisor_iff hF).2 ⟨1, one_mem _, z, one_mul _⟩)

private theorem divisorClassMonoidHom_surjective (hF : IsFunctionField k F) :
    Function.Surjective (divisorClassMonoidHom hF) := fun c ↦ by
  obtain ⟨D, hD⟩ := (Place.orderSystem hF).divisorClass_surjective c.toAdd
  obtain ⟨x, rfl⟩ := divisor_surjective D
  exact ⟨x, congrArg Multiplicative.ofAdd hD⟩

/-- **The idele group modulo the unit and principal ideles is the divisor class group**:
`J_F / (U_F Fˣ) ≃* Cl(F)`, sending the class of an idele to the class of its divisor. -/
def quotientClassGroupEquiv (hF : IsFunctionField k F) :
    IdeleGroup k F ⧸ (unitIdeles k F ⊔ (unitEmbedding hF).range) ≃*
      Multiplicative (Place.orderSystem hF).ClassGroup :=
  (QuotientGroup.quotientMulEquivOfEq (ker_divisorClassMonoidHom hF).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (divisorClassMonoidHom_surjective hF))

@[simp]
theorem quotientClassGroupEquiv_mk (hF : IsFunctionField k F) (x : IdeleGroup k F) :
    quotientClassGroupEquiv hF x =
      Multiplicative.ofAdd ((Place.orderSystem hF).divisorClass (divisor x)) :=
  (rfl)

end IdeleGroup

end TauCeti
