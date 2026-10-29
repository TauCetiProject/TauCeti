/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
public import Mathlib.Data.ZMod.QuotientRing
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm

/-!
# The order `ℤ + f 𝓞 K`

For a positive integer `f`, the set `ℤ + f 𝓞 K` of algebraic integers congruent to a rational
integer modulo `f` is an order of the number field `K`. In a quadratic field it is the order of
conductor `f`, and every order arises this way for exactly one `f`; that comparison lives in
`TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.OrderOfConductor`. This file collects
what holds in every degree `n = [K : ℚ]`.

Modulo `f 𝓞 K`, the order `ℤ + f 𝓞 K` is the image of `ℤ`. Since a rational integer divisible
by `f` in `𝓞 K` is divisible by `f` in `ℤ`, this image is `ℤ / f`, of size `f` inside a ring of
size `f ^ n`. Hence `[𝓞 K : ℤ + f 𝓞 K] = f ^ (n - 1)`, the discriminant is
`f ^ (2 (n - 1)) disc K`, and the residue ring of the order modulo `f 𝓞 K` is `ℤ / f`.

## Main definitions

* `TauCeti.GlobalNumberFields.orderOfConductor K f`: the order `ℤ + f 𝓞 K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.quotientOrderOfConductorEquiv`: the residue ring
  of `ℤ + f 𝓞 K` modulo `f 𝓞 K` is `ZMod f`; it sends the class of `a + f y` to `a`
  (`TauCeti.GlobalNumberFields.NumberFieldOrder.quotientOrderOfConductorEquiv_mk`).

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.index_orderOfConductor`:
  `[𝓞 K : ℤ + f 𝓞 K] = f ^ (n - 1)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.discr_orderOfConductor`: the discriminant of
  `ℤ + f 𝓞 K` is `f ^ (2 (n - 1)) disc K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.orderOfConductor_le_orderOfConductor_iff`: for
  `n ≥ 2`, `ℤ + f 𝓞 K ⊆ ℤ + g 𝓞 K` exactly when `g ∣ f`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.orderOfConductor_inj`: for `n ≥ 2`, the orders
  `ℤ + f 𝓞 K` are pairwise distinct.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.card_units_quotientOrderOfConductor`: the residue
  ring of `ℤ + f 𝓞 K` modulo `f 𝓞 K` has `φ(f)` units.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Lemma 7.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K] (f : ℕ) [NeZero f]

/-- The `ℤ`-subalgebra `ℤ + f 𝓞 K` of `K`. -/
private def intAddMulSubalgebra : Subalgebra ℤ K where
  carrier := {x | ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * (y : K)}
  mul_mem' := by
    rintro _ _ ⟨a, y, rfl⟩ ⟨b, z, rfl⟩
    refine ⟨a * b, a * z + b * y + f * y * z, ?_⟩
    simp only [map_add, map_mul, map_intCast, map_natCast]
    push_cast
    ring
  add_mem' := by
    rintro _ _ ⟨a, y, rfl⟩ ⟨b, z, rfl⟩
    exact ⟨a + b, y + z, by simp only [map_add]; push_cast; ring⟩
  algebraMap_mem' a := ⟨a, 0, by simp⟩

/-- **The order `ℤ + f 𝓞 K`**: the algebraic integers congruent to a rational integer modulo `f`.
In a quadratic field this is the unique order of conductor `f`. -/
def orderOfConductor : NumberFieldOrder K where
  toSubalgebra := intAddMulSubalgebra K f
  finite := by
    have h : intAddMulSubalgebra K f ≤ integralClosure ℤ K := by
      rintro _ ⟨a, y, rfl⟩
      exact add_mem (Subalgebra.algebraMap_mem _ a)
        (mul_mem (Subalgebra.natCast_mem _ f) y.2)
    have : Module.Finite ℤ (integralClosure ℤ K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))
    exact Module.Finite.of_injective (Subalgebra.inclusion h).toLinearMap
      (Subalgebra.inclusion_injective h)
  spans := by
    refine top_unique ((maximalNumberFieldOrder K).spans.symm.trans_le (Submodule.span_le.mpr ?_))
    intro y hy
    rw [SetLike.mem_coe, maximalNumberFieldOrder_toSubalgebra] at hy
    have hf : (f : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne f)
    have hy' : y = (f : ℚ)⁻¹ • ((f : K) * y) := by
      rw [Rat.smul_def]
      push_cast
      field_simp
    rw [hy']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, ⟨y, hy⟩, by simp⟩)

namespace NumberFieldOrder

variable {K f}

/-- An element of `K` lies in `ℤ + f 𝓞 K` exactly when it is a rational integer plus `f` times an
algebraic integer. -/
theorem mem_orderOfConductor {x : K} :
    x ∈ (orderOfConductor K f).toSubalgebra ↔ ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * (y : K) :=
  Iff.rfl

/-- An algebraic integer lies in `ℤ + f 𝓞 K` exactly when it is a rational integer plus `f` times an
algebraic integer. -/
theorem mem_toRingOfIntegers_orderOfConductor {x : 𝓞 K} :
    x ∈ (orderOfConductor K f).toRingOfIntegers ↔ ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * y := by
  rw [mem_toRingOfIntegers, mem_orderOfConductor]
  refine exists_congr fun a ↦ exists_congr fun y ↦ ?_
  rw [← RingOfIntegers.coe_injective.eq_iff]
  simp

/-- An algebraic integer lies in `ℤ + f 𝓞 K` exactly when its residue modulo `f` is the residue
of a rational integer. -/
private theorem mem_toRingOfIntegers_orderOfConductor_iff_mk {x : 𝓞 K} :
    x ∈ (orderOfConductor K f).toRingOfIntegers ↔
      ∃ a : ℤ, (a : 𝓞 K ⧸ Ideal.span {(f : 𝓞 K)}) = Ideal.Quotient.mk _ x := by
  rw [mem_toRingOfIntegers_orderOfConductor]
  refine exists_congr fun a ↦ ?_
  rw [← map_intCast (Ideal.Quotient.mk (Ideal.span {(f : 𝓞 K)})) a, eq_comm, Ideal.Quotient.eq,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by ring⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [mul_comm, hy]; ring⟩

variable (K f)

/-- **The index of `ℤ + f 𝓞 K`.** For a number field of degree `n`,
`[𝓞 K : ℤ + f 𝓞 K] = f ^ (n - 1)`. -/
@[simp]
theorem index_orderOfConductor :
    (orderOfConductor K f).index = f ^ (Module.finrank ℚ K - 1) := by
  set I := Ideal.span {(f : 𝓞 K)}
  set π := Ideal.Quotient.mk I
  -- The order is the preimage of the additive subgroup `ℤ · 1` of `𝓞 K / f`.
  have hS : (Subalgebra.toSubmodule (orderOfConductor K f).toRingOfIntegers).toAddSubgroup =
      (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ I)).comap π.toAddMonoidHom := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Subalgebra.mem_toSubmodule, AddSubgroup.mem_comap,
      AddSubgroup.mem_zmultiples_iff, zsmul_one, mem_toRingOfIntegers_orderOfConductor_iff_mk]
    rfl
  have hcard : Nat.card (𝓞 K ⧸ I) = f ^ Module.finrank ℚ K := by
    have : Infinite (𝓞 K) := Infinite.of_injective _ Nat.cast_injective
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
      ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  have hmul := (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ I)).index_mul_card
  rw [Nat.card_zmultiples, CharP.eq _ (CharP.addOrderOf_one _)
    (RingOfIntegers.charP_quotient_span_natCast K f),
    hcard, ← AddSubgroup.index_comap_of_surjective (f := π.toAddMonoidHom) _
      Ideal.Quotient.mk_surjective, ← hS,
    ← pow_sub_one_mul Module.finrank_pos.ne'] at hmul
  rw [index_def, ← Submodule.cardQuot_apply]
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_neZero f) hmul

/-- **The discriminant of `ℤ + f 𝓞 K`.** For a number field of degree `n`, the order
`ℤ + f 𝓞 K` has discriminant `f ^ (2 (n - 1)) disc K`. -/
theorem discr_orderOfConductor :
    (orderOfConductor K f).discr =
      (f : ℤ) ^ (2 * (Module.finrank ℚ K - 1)) * NumberField.discr K := by
  rw [discr_eq_index_sq_mul, index_orderOfConductor, pow_mul']
  push_cast
  rfl

/-- `ℤ + 1 𝓞 K` is the maximal order. -/
@[simp]
theorem orderOfConductor_one : orderOfConductor K 1 = maximalNumberFieldOrder K :=
  (index_eq_one_iff _).mp (by simp [index_orderOfConductor])

variable {K}

/-- **Inclusions between the orders `ℤ + f 𝓞 K`.** In degree at least two,
`ℤ + f 𝓞 K ⊆ ℤ + g 𝓞 K` exactly when `g ∣ f`. -/
theorem orderOfConductor_le_orderOfConductor_iff (hK : 1 < Module.finrank ℚ K) {f g : ℕ}
    [NeZero f] [NeZero g] :
    (orderOfConductor K f).toSubalgebra ≤ (orderOfConductor K g).toSubalgebra ↔ g ∣ f := by
  constructor
  · intro h
    have hdvd := index_dvd_index_of_le h
    rwa [index_orderOfConductor, index_orderOfConductor, Nat.pow_dvd_pow_iff (by omega)] at hdvd
  · rintro ⟨k, rfl⟩ _ ⟨a, y, rfl⟩
    exact ⟨a, k * y, by push_cast; ring⟩

/-- **The orders `ℤ + f 𝓞 K` are pairwise distinct** in degree at least two. -/
theorem orderOfConductor_inj (hK : 1 < Module.finrank ℚ K) {f g : ℕ} [NeZero f] [NeZero g] :
    orderOfConductor K f = orderOfConductor K g ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  have hindex := congrArg index h
  rwa [index_orderOfConductor, index_orderOfConductor,
    Nat.pow_left_inj (by omega)] at hindex

variable {f} in
/-- An element `a + f y` of `ℤ + f 𝓞 K` is congruent to `a` modulo `f 𝓞 K`. -/
private theorem mk_eq_intCast {x : (orderOfConductor K f).toRingOfIntegers} {a : ℤ} {y : 𝓞 K}
    (hxy : (x : 𝓞 K) = a + f * y) :
    Ideal.Quotient.mk ((Ideal.span {(f : 𝓞 K)}).comap
      ((orderOfConductor K f).toRingOfIntegers.val :
        (orderOfConductor K f).toRingOfIntegers →+* 𝓞 K)) x = a := by
  rw [← map_intCast (Ideal.Quotient.mk ((Ideal.span {(f : 𝓞 K)}).comap
      ((orderOfConductor K f).toRingOfIntegers.val :
        (orderOfConductor K f).toRingOfIntegers →+* 𝓞 K))), Ideal.Quotient.eq, Ideal.mem_comap,
    map_sub, map_intCast, AlgHom.coe_toRingHom, Subalgebra.coe_val, hxy, add_sub_cancel_left]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable (K)

/-- **The residue ring of `ℤ + f 𝓞 K` modulo `f 𝓞 K` is `ℤ / f`.** Every element of the order is
congruent to a rational integer modulo `f 𝓞 K`, and a rational integer lies in `f 𝓞 K` exactly when
`f` divides it. -/
def quotientOrderOfConductorEquiv :
    (orderOfConductor K f).toRingOfIntegers ⧸ (Ideal.span {(f : 𝓞 K)}).comap
      ((orderOfConductor K f).toRingOfIntegers.val :
        (orderOfConductor K f).toRingOfIntegers →+* 𝓞 K) ≃+* ZMod f :=
  let O := (orderOfConductor K f).toRingOfIntegers
  let J := (Ideal.span {(f : 𝓞 K)}).comap (O.val : O →+* 𝓞 K)
  let ψ := Int.castRingHom (O ⧸ J)
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, y, hxy⟩ := mem_toRingOfIntegers_orderOfConductor.mp x.2
    exact ⟨a, by rw [eq_intCast, mk_eq_intCast hxy]⟩
  have hker : RingHom.ker ψ = Ideal.span {(f : ℤ)} := by
    ext a
    rw [RingHom.mem_ker, eq_intCast, ← map_intCast (Ideal.Quotient.mk J),
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap, map_intCast,
      ← Ideal.Quotient.eq_zero_iff_mem, map_intCast, CharP.intCast_eq_zero_iff _ f,
      Ideal.mem_span_singleton]
  ((RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hker)).trans
    (Int.quotientSpanNatEquivZMod f)

variable {f} in
/-- The residue of `a + f y` in `ℤ / f` is the residue of `a`. -/
theorem quotientOrderOfConductorEquiv_mk {x : (orderOfConductor K f).toRingOfIntegers} {a : ℤ}
    {y : 𝓞 K} (hxy : (x : 𝓞 K) = a + f * y) :
    quotientOrderOfConductorEquiv K f (Ideal.Quotient.mk _ x) = a := by
  rw [mk_eq_intCast hxy, map_intCast]

/-- **The residue ring of `ℤ + f 𝓞 K` modulo `f 𝓞 K` has `φ(f)` units.** -/
theorem card_units_quotientOrderOfConductor :
    Nat.card ((orderOfConductor K f).toRingOfIntegers ⧸ (Ideal.span {(f : 𝓞 K)}).comap
      ((orderOfConductor K f).toRingOfIntegers.val :
        (orderOfConductor K f).toRingOfIntegers →+* 𝓞 K))ˣ = f.totient := by
  rw [Nat.card_congr (Units.mapEquiv (quotientOrderOfConductorEquiv K f).toMulEquiv).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

end NumberFieldOrder

end TauCeti.GlobalNumberFields
