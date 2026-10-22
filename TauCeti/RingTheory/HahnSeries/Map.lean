/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.PowerSeries

/-!
# Coefficientwise maps of Hahn series

A ring homomorphism `f : R →+* S` induces the ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` applying `f` to
every coefficient. Mathlib provides the underlying map `HahnSeries.map` and its compatibility with
addition, multiplication and monomials; this file bundles it as a ring homomorphism, records that
it commutes with exponent embeddings and with the inclusion of power series, and shows that an
injective coefficient map preserves supports and orders.

For Laurent series `R⸨X⸩ = R⟦ℤ⟧` this is the base change of the coefficients, for instance
along a field embedding `K → L`, under which formal substitution and the other coefficient-level
constructions on Laurent series are natural.

## Main definitions

* `HahnSeries.mapRingHom f`: the coefficientwise ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧`.

## Main results

* `HahnSeries.map_embDomain`: coefficientwise maps commute with exponent embeddings.
* `HahnSeries.map_ofPowerSeries`: coefficientwise maps commute with the inclusion of power
  series, `PowerSeries.map` on the source side.
* `HahnSeries.support_map_of_injective`, `HahnSeries.orderTop_map_of_injective`,
  `HahnSeries.order_map_of_injective`: an injective coefficient map preserves the support and
  the order.
-/

public section

open scoped PowerSeries

namespace HahnSeries

variable {Γ Γ' R S T : Type*}

section Zero

variable [Zero R] [Zero S] {F : Type*} [FunLike F R S] [ZeroHomClass F R S]

section PartialOrder

variable [PartialOrder Γ]

/-- Coefficientwise maps commute with exponent embeddings. -/
theorem map_embDomain [PartialOrder Γ'] (f : Γ ↪o Γ') (x : R⟦Γ⟧) (g : F) :
    (embDomain f x).map g = embDomain f (x.map g) := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    simp
  · simp [embDomain_of_notMem_range hb]

/-- An injective coefficient map preserves the support. -/
@[simp]
theorem support_map_of_injective (x : R⟦Γ⟧) {g : F} (hg : Function.Injective g) :
    (x.map g).support = x.support := by
  ext a
  simp only [mem_support, map_coeff, ne_eq]
  rw [← map_zero g, hg.eq_iff]

end PartialOrder

/-- An injective coefficient map preserves `orderTop`. -/
@[simp]
theorem orderTop_map_of_injective [LinearOrder Γ] (x : R⟦Γ⟧) {g : F} (hg : Function.Injective g) :
    (x.map g).orderTop = x.orderTop := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [orderTop_zero, orderTop_eq_top, ← support_eq_empty_iff, support_map_of_injective _ hg,
      support_zero]
  rw [orderTop_of_ne_zero hx]
  refine orderTop_eq_of_le ?_ fun b hb ↦ ?_
  · rw [support_map_of_injective x hg]
    exact x.isWF_support.min_mem _
  · rw [support_map_of_injective x hg] at hb
    exact x.isWF_support.min_le _ hb

/-- An injective coefficient map preserves the order of a nonzero series, and the junk value `0`
of the order of `0`. -/
@[simp]
theorem order_map_of_injective [LinearOrder Γ] [Zero Γ] (x : R⟦Γ⟧) {g : F}
    (hg : Function.Injective g) : (x.map g).order = x.order := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [support_eq_empty_iff.mp ((support_map_of_injective _ hg).trans support_zero), order_zero,
      order_zero]
  have hx' : x.map g ≠ 0 := by
    rw [← support_nonempty_iff, support_map_of_injective x hg]
    exact support_nonempty_iff.mpr hx
  exact WithTop.coe_injective <| by
    rw [order_eq_orderTop_of_ne_zero hx', order_eq_orderTop_of_ne_zero hx,
      orderTop_map_of_injective x hg]

end Zero

section Semiring

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring R] [Semiring S] [Semiring T]

/-- The ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` applying a ring homomorphism `f : R →+* S` to every
coefficient. -/
def mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧ where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero (f : ZeroHom R S)
  map_one' := HahnSeries.map_one (f : R →*₀ S)
  map_add' _ _ := HahnSeries.map_add (f : R →+ S)
  map_mul' _ _ := HahnSeries.map_mul (f : R →ₙ+* S)

theorem mapRingHom_apply (f : R →+* S) (x : R⟦Γ⟧) : mapRingHom f x = x.map f :=
  (rfl)

@[simp]
theorem coeff_mapRingHom (f : R →+* S) (x : R⟦Γ⟧) (g : Γ) :
    (mapRingHom f x).coeff g = f (x.coeff g) :=
  (rfl)

@[simp]
theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R⟦Γ⟧ :=
  RingHom.ext fun _ ↦ HahnSeries.ext rfl

theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f : R⟦Γ⟧ →+* S⟦Γ⟧) :=
  RingHom.ext fun _ ↦ HahnSeries.ext rfl

theorem mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom f : R⟦Γ⟧ →+* S⟦Γ⟧) := fun _ _ h ↦
  HahnSeries.ext <| funext fun g ↦ hf congr(($h).coeff g)

end Semiring

section PowerSeries

variable [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ] [Semiring R] [Semiring S]

/-- Coefficientwise maps commute with the inclusion of power series into Hahn series. -/
@[simp]
theorem map_ofPowerSeries (f : R →+* S) (p : R⟦X⟧) :
    (ofPowerSeries Γ R p).map f = ofPowerSeries Γ S (PowerSeries.map f p) := by
  rw [ofPowerSeries_apply, ofPowerSeries_apply, map_embDomain]
  refine congrArg _ (HahnSeries.ext <| funext fun n ↦ ?_)
  simp

end PowerSeries

end HahnSeries
