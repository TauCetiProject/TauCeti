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

* `TauCeti.GlobalNumberFields.intAddMulOrder K f`: the order `ℤ + f 𝓞 K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.quotientIntAddMulOrderEquiv`: the residue ring
  of `ℤ + f 𝓞 K` modulo `f 𝓞 K` is `ZMod f`; it sends the class of `a + f y` to `a`
  (`TauCeti.GlobalNumberFields.NumberFieldOrder.quotientIntAddMulOrderEquiv_mk`).

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.index_intAddMulOrder`:
  `[𝓞 K : ℤ + f 𝓞 K] = f ^ (n - 1)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.discr_intAddMulOrder`: the discriminant of
  `ℤ + f 𝓞 K` is `f ^ (2 (n - 1)) disc K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.intAddMulOrder_le_intAddMulOrder_iff`: for
  `n ≥ 2`, `ℤ + f 𝓞 K ⊆ ℤ + g 𝓞 K` exactly when `g ∣ f`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.intAddMulOrder_inj`: for `n ≥ 2`, the orders
  `ℤ + f 𝓞 K` are pairwise distinct.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.index_range_unitsMap_intAddMulOrder_one`: the
  units of `ℤ + 1 𝓞 K` have index `1` in the units of `𝓞 K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.card_units_quotientIntAddMulOrder`: the residue
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
-/
def intAddMulOrder : NumberFieldOrder K where
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
@[simp]
theorem mem_intAddMulOrder {x : K} :
    x ∈ (intAddMulOrder K f).toSubalgebra ↔ ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * (y : K) :=
  Iff.rfl

/-- An algebraic integer lies in `ℤ + f 𝓞 K` exactly when it is a rational integer plus `f` times an
algebraic integer. -/
theorem mem_toRingOfIntegers_intAddMulOrder {x : 𝓞 K} :
    x ∈ (intAddMulOrder K f).toRingOfIntegers ↔ ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * y := by
  rw [mem_toRingOfIntegers, mem_intAddMulOrder]
  refine exists_congr fun a ↦ exists_congr fun y ↦ ?_
  rw [← RingOfIntegers.coe_injective.eq_iff]
  simp

/-- An algebraic integer lies in `ℤ + f 𝓞 K` exactly when its residue modulo `f` is the residue
of a rational integer. -/
private theorem mem_toRingOfIntegers_intAddMulOrder_iff_mk {x : 𝓞 K} :
    x ∈ (intAddMulOrder K f).toRingOfIntegers ↔
      ∃ a : ℤ, (a : 𝓞 K ⧸ Ideal.span {(f : 𝓞 K)}) = Ideal.Quotient.mk _ x := by
  rw [mem_toRingOfIntegers_intAddMulOrder]
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
theorem index_intAddMulOrder :
    (intAddMulOrder K f).index = f ^ (Module.finrank ℚ K - 1) := by
  set I := Ideal.span {(f : 𝓞 K)}
  set π := Ideal.Quotient.mk I
  -- The order is the preimage of the additive subgroup `ℤ · 1` of `𝓞 K / f`.
  have hS : (Subalgebra.toSubmodule (intAddMulOrder K f).toRingOfIntegers).toAddSubgroup =
      (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ I)).comap π.toAddMonoidHom := by
    ext x
    rw [Submodule.mem_toAddSubgroup, Subalgebra.mem_toSubmodule,
      mem_toRingOfIntegers_intAddMulOrder_iff_mk]
    simp [AddSubgroup.mem_zmultiples_iff, π, I]
  have hindex : (intAddMulOrder K f).index = (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ I)).index := by
    rw [index_eq_addSubgroup_index, hS,
      AddSubgroup.index_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  -- `𝓞 K / f` has `f ^ n` elements, and its subgroup `ℤ · 1` has `f`.
  have hcard : Nat.card (𝓞 K ⧸ I) = f ^ Module.finrank ℚ K := by
    have : Infinite (𝓞 K) := Infinite.of_injective _ Nat.cast_injective
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast,
      RingOfIntegers.rank]
  have hone : Nat.card (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ I)) = f := by
    rw [Nat.card_zmultiples, CharP.eq _ (CharP.addOrderOf_one _)
      (RingOfIntegers.charP_quotient_span_natCast K f)]
  have hmul := (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ I)).index_mul_card
  rw [hone, hcard, ← pow_sub_one_mul Module.finrank_pos.ne'] at hmul
  exact hindex.trans (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_neZero f) hmul)

/-- **The discriminant of `ℤ + f 𝓞 K`.** For a number field of degree `n`, the order
`ℤ + f 𝓞 K` has discriminant `f ^ (2 (n - 1)) disc K`. -/
theorem discr_intAddMulOrder :
    (intAddMulOrder K f).discr =
      (f : ℤ) ^ (2 * (Module.finrank ℚ K - 1)) * NumberField.discr K := by
  rw [discr_eq_index_sq_mul, index_intAddMulOrder]
  push_cast
  ring

/-- `ℤ + 1 𝓞 K` is the maximal order. -/
@[simp]
theorem intAddMulOrder_one : intAddMulOrder K 1 = maximalNumberFieldOrder K :=
  (index_eq_one_iff _).mp (by simp [index_intAddMulOrder])

/-- **The unit index of the maximal order.** Every unit of `𝓞 K` is a unit of `ℤ + 1 𝓞 K`, so
`[(𝓞 K)ˣ : O_1ˣ] = 1`. -/
@[simp]
theorem index_range_unitsMap_intAddMulOrder_one :
    (Units.map ((intAddMulOrder K 1).toRingOfIntegers.val :
      (intAddMulOrder K 1).toRingOfIntegers →* 𝓞 K)).range.index = 1 := by
  rw [Subgroup.index_eq_one, MonoidHom.range_eq_top]
  intro ε
  have hmem (x : 𝓞 K) : x ∈ (intAddMulOrder K 1).toRingOfIntegers :=
    mem_toRingOfIntegers_intAddMulOrder.mpr ⟨0, x, by simp⟩
  exact ⟨⟨⟨ε, hmem _⟩, ⟨_, hmem _⟩, Subtype.ext ε.mul_inv, Subtype.ext ε.inv_mul⟩,
    Units.ext rfl⟩

variable {K}

/-- **Inclusions between the orders `ℤ + f 𝓞 K`.** In degree at least two,
`ℤ + f 𝓞 K ⊆ ℤ + g 𝓞 K` exactly when `g ∣ f`. -/
theorem intAddMulOrder_le_intAddMulOrder_iff (hK : 1 < Module.finrank ℚ K) {f g : ℕ}
    [NeZero f] [NeZero g] :
    (intAddMulOrder K f).toSubalgebra ≤ (intAddMulOrder K g).toSubalgebra ↔ g ∣ f := by
  constructor
  · intro h
    have hdvd := index_dvd_index_of_le h
    rwa [index_intAddMulOrder, index_intAddMulOrder, Nat.pow_dvd_pow_iff (by omega)] at hdvd
  · rintro ⟨k, rfl⟩ _ ⟨a, y, rfl⟩
    exact ⟨a, k * y, by push_cast; ring⟩

/-- **The orders `ℤ + f 𝓞 K` are pairwise distinct** in degree at least two. -/
theorem intAddMulOrder_inj (hK : 1 < Module.finrank ℚ K) {f g : ℕ} [NeZero f] [NeZero g] :
    intAddMulOrder K f = intAddMulOrder K g ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  have hindex := congrArg index h
  rwa [index_intAddMulOrder, index_intAddMulOrder,
    Nat.pow_left_inj (by omega)] at hindex

variable {f} in
/-- An element `a + f y` of `ℤ + f 𝓞 K` is congruent to `a` modulo `f 𝓞 K`. -/
private theorem mk_eq_intCast {x : (intAddMulOrder K f).toRingOfIntegers} {a : ℤ} {y : 𝓞 K}
    (hxy : (x : 𝓞 K) = a + f * y) :
    Ideal.Quotient.mk ((Ideal.span {(f : 𝓞 K)}).comap
      ((intAddMulOrder K f).toRingOfIntegers.val :
        (intAddMulOrder K f).toRingOfIntegers →+* 𝓞 K)) x = a := by
  exact (Ideal.Quotient.eq.mpr (by simp [hxy, Ideal.mem_span_singleton])).trans (map_intCast _ a)

variable (K)

/-- **The residue ring of `ℤ + f 𝓞 K` modulo `f 𝓞 K` is `ℤ / f`.** Every element of the order is
congruent to a rational integer modulo `f 𝓞 K`, and a rational integer lies in `f 𝓞 K` exactly when
`f` divides it. -/
def quotientIntAddMulOrderEquiv :
    (intAddMulOrder K f).toRingOfIntegers ⧸ (Ideal.span {(f : 𝓞 K)}).comap
      ((intAddMulOrder K f).toRingOfIntegers.val :
        (intAddMulOrder K f).toRingOfIntegers →+* 𝓞 K) ≃+* ZMod f :=
  let O := (intAddMulOrder K f).toRingOfIntegers
  let J := (Ideal.span {(f : 𝓞 K)}).comap (O.val : O →+* 𝓞 K)
  let ψ := Int.castRingHom (O ⧸ J)
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, y, hxy⟩ := mem_toRingOfIntegers_intAddMulOrder.mp x.2
    exact ⟨a, by rw [eq_intCast, mk_eq_intCast hxy]⟩
  have hker : RingHom.ker ψ = Ideal.span {(f : ℤ)} := by
    ext a
    rw [RingHom.mem_ker, eq_intCast, ← map_intCast (Ideal.Quotient.mk J),
      Ideal.Quotient.eq_zero_iff_mem]
    simp only [J, Ideal.mem_comap, map_intCast, Ideal.mem_span_singleton]
    norm_cast
  ((RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hker)).trans
    (Int.quotientSpanNatEquivZMod f)

variable {f} in
/-- The residue of `a + f y` in `ℤ / f` is the residue of `a`. -/
theorem quotientIntAddMulOrderEquiv_mk {x : (intAddMulOrder K f).toRingOfIntegers} {a : ℤ}
    {y : 𝓞 K} (hxy : (x : 𝓞 K) = a + f * y) :
    quotientIntAddMulOrderEquiv K f (Ideal.Quotient.mk _ x) = a := by
  rw [mk_eq_intCast hxy, map_intCast]

/-- **The residue ring of `ℤ + f 𝓞 K` modulo `f 𝓞 K` has `φ(f)` units.** -/
theorem card_units_quotientIntAddMulOrder :
    Nat.card ((intAddMulOrder K f).toRingOfIntegers ⧸ (Ideal.span {(f : 𝓞 K)}).comap
      ((intAddMulOrder K f).toRingOfIntegers.val :
        (intAddMulOrder K f).toRingOfIntegers →+* 𝓞 K))ˣ = f.totient := by
  rw [Nat.card_congr (Units.mapEquiv (quotientIntAddMulOrderEquiv K f).toMulEquiv).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

end NumberFieldOrder

end TauCeti.GlobalNumberFields
