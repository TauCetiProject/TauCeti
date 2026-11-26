/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.NumberTheory.Quaternion.Order.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Unit groups of quaternion orders

Let `R` be an integrally closed domain with fraction field `F`, and let `Λ` be an `R`-order in a
quaternion algebra `B = ℍ[F,c₁,c₂,c₃]`. Its unit group `Λˣ` is realised as Mathlib's unit subgroup
`Λ.toSubmonoid.units` of `Bˣ`, whose members are the units `γ` of `B` with `γ ∈ Λ` and
`γ⁻¹ ∈ Λ`. This file adds the norm-one group `Λ¹ = {γ ∈ Λˣ : nrd γ = 1}` and relates the two
through the reduced norm `nrd = normForm c₁ c₂ c₃`.

Elements of an order have reduced norm in `R`, so `nrd` restricts to a monoid homomorphism
`Λ →* R`. An element `γ ∈ Λ` is a unit of `Λ` exactly when `nrd γ` is a unit of `R`: its inverse is
then `nrd(γ)⁻¹ star γ`, which lies in `Λ` because orders are stable under conjugation. On unit
groups the reduced norm is a homomorphism `Λˣ →* Rˣ` with kernel `Λ¹`, so `Λ¹` is normal in `Λˣ`
and `Λˣ / Λ¹` embeds in `Rˣ`. For `R = ℤ` the quotient therefore has order `1` or `2`, according
as `Λ` has no unit of reduced norm `-1` or has one; in a definite algebra, where the reduced norm
takes no negative values, every unit has reduced norm `1`.

The group `Λ¹` is the norm-one group `Λ ∩ B¹`, where `B¹` is Mathlib's `unitary B`: these are the
groups whose images in `SL₂(ℝ)` are the arithmetic Fuchsian groups of an indefinite algebra.

## Main definitions

* `TauCeti.QuaternionAlgebra.normOne Λ`: the norm-one group `Λ¹`, a subgroup of `Bˣ`.
* `TauCeti.IntegralOrder.IsOrder.reducedNorm`: the reduced norm `Λ →* R` of an order.
* `TauCeti.IntegralOrder.IsOrder.unitsReducedNorm`: the reduced norm `Λˣ →* Rˣ` on units.
* `TauCeti.IntegralOrder.IsOrder.unitsQuotientNormOneHom`: the induced map `Λˣ / Λ¹ →* Rˣ`.

## Main results

* `TauCeti.IntegralOrder.IsOrder.isUnit_iff_reducedNorm_isUnit` and
  `TauCeti.IntegralOrder.IsOrder.mem_units_iff`: an element of an order is a unit of the order
  exactly when its reduced norm is a unit of `R`.
* `TauCeti.IntegralOrder.IsOrder.mem_normOne_iff` and
  `TauCeti.IntegralOrder.IsOrder.mem_normOne_iff_mem_unitary`: `Λ¹` consists of the elements of
  `Λ` of reduced norm `1`, that is, it is `Λ ∩ B¹`.
* `TauCeti.IntegralOrder.IsOrder.ker_unitsReducedNorm`: the kernel of `Λˣ →* Rˣ` is `Λ¹`.
* `TauCeti.IntegralOrder.IsOrder.unitsQuotientNormOneHom_injective`: `Λˣ / Λ¹` embeds in `Rˣ`.
* `TauCeti.IntegralOrder.IsOrder.relIndex_normOne_units_eq_two_iff` and
  `TauCeti.IntegralOrder.IsOrder.relIndex_normOne_units_eq_one_iff`: over `ℤ`, `[Λˣ : Λ¹]` is `2`
  when `Λ` has a unit of reduced norm `-1`, and `1` otherwise.
* `TauCeti.IntegralOrder.IsOrder.normOne_eq_units_of_nonneg`: over `ℤ`, if the reduced norm takes
  no negative values then `Λ¹ = Λˣ`.

## References

* J. Voight, *Quaternion algebras*, Exercise 10.15.
-/

public section

open TauCeti.IntegralOrder QuaternionAlgebra

open scoped Quaternion

namespace TauCeti.QuaternionAlgebra

variable {R F : Type*} [CommRing R] [CommRing F] [Algebra R F] {c₁ c₂ c₃ : F}

/-- The **norm-one group** `Λ¹ = {γ ∈ Λˣ : nrd γ = 1}` of an `R`-subalgebra `Λ` of
`ℍ[F,c₁,c₂,c₃]`: the units `γ` of the quaternion algebra with `γ, γ⁻¹ ∈ Λ` and reduced norm
`normForm c₁ c₂ c₃ γ = 1`. When `Λ` is an order, `γ ∈ Λ` and `nrd γ = 1` already force `γ⁻¹ ∈ Λ`
(`TauCeti.IntegralOrder.IsOrder.mem_normOne_iff`). -/
def normOne (Λ : Subalgebra R ℍ[F,c₁,c₂,c₃]) : Subgroup ℍ[F,c₁,c₂,c₃]ˣ where
  carrier := {γ | γ ∈ Λ.toSubmonoid.units ∧ normForm c₁ c₂ c₃ (γ : ℍ[F,c₁,c₂,c₃]) = 1}
  one_mem' := ⟨one_mem _, by rw [Units.val_one, normForm_one]⟩
  mul_mem' := fun ⟨hγ, hγ₁⟩ ⟨hδ, hδ₁⟩ => ⟨mul_mem hγ hδ, by rw [Units.val_mul, normForm_mul, hγ₁,
    hδ₁, one_mul]⟩
  inv_mem' {γ} := fun ⟨hγ, hγ₁⟩ => ⟨inv_mem hγ, by
    simpa [hγ₁] using normForm_units_inv_mul c₁ c₂ c₃ γ⟩

variable {Λ : Subalgebra R ℍ[F,c₁,c₂,c₃]} {γ : ℍ[F,c₁,c₂,c₃]ˣ}

/-- A unit `γ` of `ℍ[F,c₁,c₂,c₃]` lies in `Λ¹` exactly when it lies in `Λˣ` and has reduced norm
`1`. -/
theorem mem_normOne_iff_mem_units_and_normForm_eq_one :
    γ ∈ normOne Λ ↔ γ ∈ Λ.toSubmonoid.units ∧ normForm c₁ c₂ c₃ (γ : ℍ[F,c₁,c₂,c₃]) = 1 :=
  Iff.rfl

/-- The norm-one group `Λ¹` is a subgroup of the unit group `Λˣ`. -/
theorem normOne_le_units : normOne Λ ≤ Λ.toSubmonoid.units := fun _ hγ => hγ.1

/-- The norm-one group `Λ¹` is normal in the unit group `Λˣ`: conjugation by a unit preserves the
reduced norm. -/
instance normal_normOne_subgroupOf_units :
    ((normOne Λ).subgroupOf Λ.toSubmonoid.units).Normal where
  conj_mem δ hδ γ := by
    rw [Subgroup.mem_subgroupOf] at hδ ⊢
    refine ⟨mul_mem (mul_mem γ.property hδ.1) (inv_mem γ.property), ?_⟩
    simpa [hδ.2, mul_comm] using normForm_units_inv_mul c₁ c₂ c₃ (γ : ℍ[F,c₁,c₂,c₃]ˣ)

end TauCeti.QuaternionAlgebra

namespace TauCeti.IntegralOrder.IsOrder

open TauCeti.QuaternionAlgebra

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] {c₁ c₂ c₃ : F}
  [IsFractionRing R F] [IsIntegrallyClosed R] {Λ : Subalgebra R ℍ[F,c₁,c₂,c₃]}

/-- The **reduced norm of an order** `Λ` in `ℍ[F,c₁,c₂,c₃]`, as a monoid homomorphism `Λ →* R`:
the element of `R` whose image in `F` is `normForm c₁ c₂ c₃ x`
(`TauCeti.IntegralOrder.IsOrder.algebraMap_reducedNorm`). -/
noncomputable def reducedNorm (h : IsOrder F Λ) : Λ →* R where
  toFun x := (h.normForm_mem_range x.property).choose
  map_one' := IsFractionRing.injective R F <| by
    rw [(h.normForm_mem_range (1 : Λ).property).choose_spec, map_one, Subalgebra.coe_one,
      normForm_one]
  map_mul' x y := IsFractionRing.injective R F <| by
    rw [(h.normForm_mem_range (x * y).property).choose_spec, map_mul,
      (h.normForm_mem_range x.property).choose_spec, (h.normForm_mem_range y.property).choose_spec,
      Subalgebra.coe_mul, normForm_mul]

/-- The reduced norm of an element of an order, seen in `F`, is its norm form. -/
@[simp]
theorem algebraMap_reducedNorm (h : IsOrder F Λ) (x : Λ) :
    algebraMap R F (h.reducedNorm x) = normForm c₁ c₂ c₃ (x : ℍ[F,c₁,c₂,c₃]) :=
  (h.normForm_mem_range x.property).choose_spec

/-- **Units of an order are detected by the reduced norm.** An element of an `R`-order in
`ℍ[F,c₁,c₂,c₃]` is a unit of the order exactly when its reduced norm is a unit of `R`; the inverse
is then `nrd(x)⁻¹ star x`. -/
theorem isUnit_iff_reducedNorm_isUnit (h : IsOrder F Λ) {x : Λ} :
    IsUnit x ↔ IsUnit (h.reducedNorm x) := by
  refine ⟨fun hx => hx.map h.reducedNorm, fun ⟨u, hu⟩ => ?_⟩
  -- the inverse `star x * u⁻¹` lies in `Λ`, as orders are stable under conjugation
  let y : Λ := ⟨star (x : ℍ[F,c₁,c₂,c₃]) * algebraMap R _ (u⁻¹ : Rˣ),
    mul_mem (h.star_mem x.property) (Λ.algebraMap_mem _)⟩
  have hF : normForm c₁ c₂ c₃ (x : ℍ[F,c₁,c₂,c₃]) * algebraMap R F (u⁻¹ : Rˣ) = 1 := by
    rw [← h.algebraMap_reducedNorm, ← hu, ← map_mul, Units.mul_inv, map_one]
  have hnrd : (normForm c₁ c₂ c₃ (x : ℍ[F,c₁,c₂,c₃]) : ℍ[F,c₁,c₂,c₃]) *
      algebraMap R _ (u⁻¹ : Rˣ) = 1 := by
    simpa [IsScalarTower.algebraMap_apply R F ℍ[F,c₁,c₂,c₃]] using
      congrArg (algebraMap F ℍ[F,c₁,c₂,c₃]) hF
  refine ⟨⟨x, y, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · rw [Subalgebra.coe_mul, ← mul_assoc, self_mul_star, hnrd, Subalgebra.coe_one]
  · rw [Subalgebra.coe_mul, mul_assoc, Algebra.commutes, ← mul_assoc, star_mul_self, hnrd,
      Subalgebra.coe_one]

/-- **The unit criterion in `Bˣ`.** A unit `γ` of `ℍ[F,c₁,c₂,c₃]` lies in the unit group of an
`R`-order `Λ` exactly when `γ ∈ Λ` and its reduced norm is the image of a unit of `R`. -/
theorem mem_units_iff (h : IsOrder F Λ) {γ : ℍ[F,c₁,c₂,c₃]ˣ} :
    γ ∈ Λ.toSubmonoid.units ↔ (γ : ℍ[F,c₁,c₂,c₃]) ∈ Λ ∧
      ∃ u : Rˣ, algebraMap R F u = normForm c₁ c₂ c₃ (γ : ℍ[F,c₁,c₂,c₃]) := by
  refine ⟨fun hγ => ?_, fun ⟨hγ, u, hu⟩ => ?_⟩
  · obtain ⟨u, hu⟩ := h.isUnit_iff_reducedNorm_isUnit.1
      (Λ.toSubmonoid.unitsEquivUnitsType ⟨γ, hγ⟩).isUnit
    exact ⟨hγ.1, u, by rw [hu]; exact h.algebraMap_reducedNorm _⟩
  · have hx : IsUnit (⟨γ, hγ⟩ : Λ) := h.isUnit_iff_reducedNorm_isUnit.2
      ⟨u, IsFractionRing.injective R F (by rw [hu, h.algebraMap_reducedNorm])⟩
    obtain ⟨v, hv⟩ := hx
    -- the inverse of `γ` in `B` is its inverse in `Λ`
    have hvγ : ((v : Λ) : ℍ[F,c₁,c₂,c₃]) = γ := congrArg Subtype.val hv
    have hinv : ((γ⁻¹ : ℍ[F,c₁,c₂,c₃]ˣ) : ℍ[F,c₁,c₂,c₃]) = ((v⁻¹ : Λˣ) : Λ) :=
      Units.inv_eq_of_mul_eq_one_right <| by
        rw [← hvγ, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    exact Λ.toSubmonoid.mem_units_of_val_mem_inv_val_mem hγ <| by
      rw [hinv]; exact (v⁻¹ : Λˣ).val.property

/-- In an order, an element of reduced norm `1` is automatically invertible in the order: the
norm-one group `Λ¹` consists of the units `γ ∈ Λ` with `nrd γ = 1`. -/
theorem mem_normOne_iff (h : IsOrder F Λ) {γ : ℍ[F,c₁,c₂,c₃]ˣ} :
    γ ∈ normOne Λ ↔ (γ : ℍ[F,c₁,c₂,c₃]) ∈ Λ ∧ normForm c₁ c₂ c₃ (γ : ℍ[F,c₁,c₂,c₃]) = 1 := by
  refine ⟨fun hγ => ⟨hγ.1.1, hγ.2⟩, fun ⟨hγ, hγ₁⟩ => ⟨(h.mem_units_iff).2 ⟨hγ, 1, ?_⟩, hγ₁⟩⟩
  rw [Units.val_one, map_one, hγ₁]

/-- The norm-one group `Λ¹` of an order is `Λ ∩ B¹`, where `B¹ = unitary B` consists of the
quaternions `x` with `star x * x = x * star x = 1`. -/
theorem mem_normOne_iff_mem_unitary (h : IsOrder F Λ) {γ : ℍ[F,c₁,c₂,c₃]ˣ} :
    γ ∈ normOne Λ ↔
      (γ : ℍ[F,c₁,c₂,c₃]) ∈ Λ ∧ (γ : ℍ[F,c₁,c₂,c₃]) ∈ unitary ℍ[F,c₁,c₂,c₃] := by
  rw [h.mem_normOne_iff, mem_unitary_iff_normForm_eq_one]

/-- The **reduced norm on units** `Λˣ →* Rˣ` of an order `Λ`, where `Λˣ` is the unit subgroup
`Λ.toSubmonoid.units` of `ℍ[F,c₁,c₂,c₃]ˣ`. Its kernel is the norm-one group `Λ¹`
(`TauCeti.IntegralOrder.IsOrder.ker_unitsReducedNorm`). -/
noncomputable def unitsReducedNorm (h : IsOrder F Λ) : Λ.toSubmonoid.units →* Rˣ :=
  (Units.map h.reducedNorm).comp Λ.toSubmonoid.unitsEquivUnitsType.toMonoidHom

/-- The reduced norm of a unit of an order, seen in `F`, is its norm form. -/
@[simp]
theorem algebraMap_unitsReducedNorm (h : IsOrder F Λ) (γ : Λ.toSubmonoid.units) :
    algebraMap R F (h.unitsReducedNorm γ) =
      normForm c₁ c₂ c₃ ((γ : ℍ[F,c₁,c₂,c₃]ˣ) : ℍ[F,c₁,c₂,c₃]) :=
  h.algebraMap_reducedNorm _

/-- **The kernel of the reduced norm on units is the norm-one group:**
`ker(Λˣ → Rˣ) = Λ¹`. -/
theorem ker_unitsReducedNorm (h : IsOrder F Λ) :
    h.unitsReducedNorm.ker = (normOne Λ).subgroupOf Λ.toSubmonoid.units := by
  ext γ
  simp [Subgroup.mem_subgroupOf, mem_normOne_iff_mem_units_and_normForm_eq_one, γ.property,
    ← Units.val_inj, ← (IsFractionRing.injective R F).eq_iff]

/-- The map `Λˣ / Λ¹ →* Rˣ` induced by the reduced norm of an order `Λ`; it is injective
(`TauCeti.IntegralOrder.IsOrder.unitsQuotientNormOneHom_injective`). -/
noncomputable def unitsQuotientNormOneHom (h : IsOrder F Λ) :
    Λ.toSubmonoid.units ⧸ (normOne Λ).subgroupOf Λ.toSubmonoid.units →* Rˣ :=
  (QuotientGroup.kerLift h.unitsReducedNorm).comp
    (QuotientGroup.quotientMulEquivOfEq h.ker_unitsReducedNorm.symm).toMonoidHom

/-- The map `Λˣ / Λ¹ →* Rˣ` sends the class of a unit to its reduced norm. -/
@[simp]
theorem unitsQuotientNormOneHom_mk (h : IsOrder F Λ) (γ : Λ.toSubmonoid.units) :
    h.unitsQuotientNormOneHom γ = h.unitsReducedNorm γ := by
  simp [unitsQuotientNormOneHom]

/-- **`Λˣ / Λ¹` embeds in `Rˣ`** by the reduced norm. -/
theorem unitsQuotientNormOneHom_injective (h : IsOrder F Λ) :
    Function.Injective h.unitsQuotientNormOneHom := by
  rw [unitsQuotientNormOneHom, MonoidHom.coe_comp]
  exact (QuotientGroup.kerLift_injective _).comp (MulEquiv.injective _)

/-- The index `[Λˣ : Λ¹]` is the order of the group of reduced norms of the units of `Λ`. -/
theorem relIndex_normOne_units (h : IsOrder F Λ) :
    (normOne Λ).relIndex Λ.toSubmonoid.units = Nat.card h.unitsReducedNorm.range := by
  rw [Subgroup.relIndex, ← h.ker_unitsReducedNorm, Subgroup.index_ker]

section Int

variable [IsFractionRing ℤ F] {Λ : Subalgebra ℤ ℍ[F,c₁,c₂,c₃]}

/-- Over `ℤ`, the reduced norms of the units of an order form all of `ℤˣ = {±1}` exactly when
some unit has reduced norm `-1`. -/
theorem range_unitsReducedNorm_eq_top_iff (h : IsOrder F Λ) :
    h.unitsReducedNorm.range = ⊤ ↔
      ∃ γ ∈ Λ.toSubmonoid.units, normForm c₁ c₂ c₃ (γ : ℍ[F,c₁,c₂,c₃]) = -1 := by
  have hneg {γ : Λ.toSubmonoid.units} :
      h.unitsReducedNorm γ = -1 ↔
        normForm c₁ c₂ c₃ ((γ : ℍ[F,c₁,c₂,c₃]ˣ) : ℍ[F,c₁,c₂,c₃]) = -1 := by
    rw [← Units.val_inj, ← (IsFractionRing.injective ℤ F).eq_iff, algebraMap_unitsReducedNorm]
    simp
  refine ⟨fun htop => ?_, fun ⟨γ, hγ, hγ₁⟩ => eq_top_iff.2 fun u _ => ?_⟩
  · obtain ⟨γ, hγ⟩ := htop ▸ Subgroup.mem_top (-1 : ℤˣ)
    exact ⟨γ, γ.property, hneg.1 hγ⟩
  · rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · exact ⟨⟨γ, hγ⟩, hneg.2 hγ₁⟩

/-- **`[Λˣ : Λ¹] = 2` over `ℤ` with a unit of norm `-1`.** For a `ℤ`-order `Λ`, the norm-one group
has index `2` in the unit group exactly when `Λ` contains a unit of reduced norm `-1`. -/
theorem relIndex_normOne_units_eq_two_iff (h : IsOrder F Λ) :
    (normOne Λ).relIndex Λ.toSubmonoid.units = 2 ↔
      ∃ γ ∈ Λ.toSubmonoid.units, normForm c₁ c₂ c₃ (γ : ℍ[F,c₁,c₂,c₃]) = -1 := by
  rw [← h.range_unitsReducedNorm_eq_top_iff, h.relIndex_normOne_units, ← Fintype.card_units_int,
    ← Nat.card_eq_fintype_card, ← Subgroup.card_top (G := ℤˣ)]
  exact ⟨fun hc => Subgroup.eq_of_le_of_card_ge le_top hc.ge, fun ht => by rw [ht]⟩

/-- **`[Λˣ : Λ¹] = 1` over `ℤ` without a unit of norm `-1`.** For a `ℤ`-order `Λ`, every unit has
reduced norm `1` exactly when no unit has reduced norm `-1`. -/
theorem relIndex_normOne_units_eq_one_iff (h : IsOrder F Λ) :
    (normOne Λ).relIndex Λ.toSubmonoid.units = 1 ↔
      ¬ ∃ γ ∈ Λ.toSubmonoid.units, normForm c₁ c₂ c₃ (γ : ℍ[F,c₁,c₂,c₃]) = -1 := by
  rw [← h.range_unitsReducedNorm_eq_top_iff, h.relIndex_normOne_units, Subgroup.card_eq_one]
  -- `ℤˣ` has prime order `2`, so its subgroups are `⊥` and `⊤`, and `⊥ ≠ ⊤`
  have : Fact (Nat.card ℤˣ).Prime := ⟨by simp [Nat.card_eq_fintype_card, Nat.prime_two]⟩
  have : Nontrivial ℤˣ := ⟨⟨-1, 1, by decide⟩⟩
  rcases h.unitsReducedNorm.range.eq_bot_or_eq_top_of_prime_card with hr | hr <;> simp [hr]

/-- **Definite orders over `ℤ`.** If the reduced norm of `ℍ[F,c₁,c₂,c₃]` takes no negative values,
as for a definite algebra, then every unit of a `ℤ`-order `Λ` has reduced norm `1`: `Λ¹ = Λˣ`. -/
theorem normOne_eq_units_of_nonneg [LinearOrder F] [IsStrictOrderedRing F] (h : IsOrder F Λ)
    (hnn : ∀ x ∈ Λ, 0 ≤ normForm c₁ c₂ c₃ x) : normOne Λ = Λ.toSubmonoid.units := by
  refine le_antisymm normOne_le_units fun γ hγ => ?_
  have hr := (h.mem_units_iff.1 hγ)
  obtain ⟨u, hu⟩ := hr.2
  refine ⟨hγ, ?_⟩
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [← hu, Units.val_one, map_one]
  · exact absurd (hnn _ hr.1) (by norm_num [← hu])

end Int

end TauCeti.IntegralOrder.IsOrder

/-! ### Examples -/

namespace TauCeti.QuaternionAlgebra

section Examples

/-- In the Lipschitz order `ℤ⟨i, j⟩` of the definite algebra `ℍ[ℚ,-1,-1]` every unit has reduced
norm `1`. -/
example : normOne (standardOrder ℤ (-1 : ℚ) 0 (-1)) =
    (standardOrder ℤ (-1 : ℚ) 0 (-1)).toSubmonoid.units :=
  (isOrder_standardOrder ⟨-1, by simp⟩ ⟨0, by simp⟩ ⟨-1, by simp⟩).normOne_eq_units_of_nonneg
    fun x _ => (posDef_normForm_of_neg (by norm_num) (by norm_num)).nonneg x

/-- The scalar `2` is a unit of `ℍ[ℚ,-1,-1]` lying in the Lipschitz order, but its inverse `1/2`
does not: `2` has reduced norm `4`, which is not a unit of `ℤ`. -/
example : Units.map (algebraMap ℚ ℍ[ℚ,-1,-1]).toMonoidHom (Units.mk0 2 two_ne_zero) ∉
    (standardOrder ℤ (-1 : ℚ) 0 (-1)).toSubmonoid.units := by
  rw [(isOrder_standardOrder ⟨-1, by simp⟩ ⟨0, by simp⟩ ⟨-1, by simp⟩).mem_units_iff]
  rintro ⟨-, u, hu⟩
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num [normForm_apply_coordinates] at hu

/-- In the order `ℤ⟨i, j⟩` of the indefinite algebra `ℍ[ℚ,3,-1]` the unit `1 + i + j` has reduced
norm `1 - 3 + 1 = -1`, so the norm-one group has index `2` in the unit group. -/
example : (normOne (standardOrder ℤ (3 : ℚ) 0 (-1))).relIndex
    (standardOrder ℤ (3 : ℚ) 0 (-1)).toSubmonoid.units = 2 := by
  have h := isOrder_standardOrder (R := ℤ) (c₁ := (3 : ℚ)) (c₂ := 0) (c₃ := -1) ⟨3, by simp⟩
    ⟨0, by simp⟩ ⟨-1, by simp⟩
  have hnrd : normForm (3 : ℚ) 0 (-1) (⟨1, 1, 1, 0⟩ : ℍ[ℚ,3,-1]) = -1 := by
    rw [normForm_apply_coordinates]; norm_num
  let γ : ℍ[ℚ,3,-1]ˣ :=
    ((isUnit_iff_normForm_isUnit _ _ _ _).2 (by rw [hnrd]; exact isUnit_one.neg)).unit
  refine h.relIndex_normOne_units_eq_two_iff.2 ⟨γ, h.mem_units_iff.2 ⟨?_, -1, ?_⟩, hnrd⟩
  · exact (mem_standardOrder_iff ⟨3, by simp⟩ ⟨0, by simp⟩ ⟨-1, by simp⟩).2
      ⟨⟨1, by simp [γ]⟩, ⟨1, by simp [γ]⟩, ⟨1, by simp [γ]⟩, ⟨0, by simp [γ]⟩⟩
  · simp [γ, hnrd]

end Examples

end TauCeti.QuaternionAlgebra
