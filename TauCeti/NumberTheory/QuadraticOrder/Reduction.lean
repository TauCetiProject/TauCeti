/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.ZMod
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Algebra.QuadraticAlgebra.Ideal

/-!
# Reduction of an integral quadratic algebra modulo `m`

Let `ℤ[ω] = QuadraticAlgebra ℤ a b`, so `ω² = a + b ω`. Reduction modulo a natural number `m` is
the coefficientwise map `mapRingHom (Int.castRingHom (ZMod m)) a b : ℤ[ω] → (ℤ/m)[ω]`. This file
identifies its kernel with the principal ideal `(m)`, through the kernel of a general change of
coefficients (`QuadraticAlgebra.ker_mapRingHom`), and deduces that `ℤ[ω]/(m)` is the quadratic
algebra over `ℤ/m` with the reduced parameters, of cardinality `m²`. Every `m` is allowed: at
`m = 0` the reduction is the identity on coordinates and the quotient is `ℤ[ω]` itself, which is
infinite, and at `m = 1` the quotient is the zero ring.

## Main results

* `QuadraticAlgebra.mem_span_natCast_iff`, `QuadraticAlgebra.sub_mem_span_natCast_iff`:
  `z ∈ (m)` exactly when `m` divides both coordinates of `z`, and `z ≡ w` modulo `(m)` exactly
  when the coordinates are congruent modulo `m`.
* `QuadraticAlgebra.ker_mapRingHom_intCastRingHom`: the kernel of reduction modulo `m` is `(m)`.
* `QuadraticAlgebra.quotientSpanNatCastEquiv`: the ring isomorphism
  `ℤ[ω]/(m) ≃+* (ℤ/m)[ω]` induced by reduction modulo `m`.
* `QuadraticAlgebra.card_quotient_span_natCast`: `ℤ[ω]/(m)` has `m²` elements, read as `0`
  for the infinite quotient at `m = 0`; `QuadraticAlgebra.finite_quotient_span_natCast_iff`:
  the quotient is finite exactly when `m ≠ 0`.

## References

* J. S. Milne, *Algebraic Number Theory*, proof of Theorem 3.41, which identifies `A/pA` with
  `𝔽_p[X]/(X² - bX - a)`, the coefficients read modulo `p`. This is the prime case of
  `quotientSpanNatCastEquiv`.
-/

public section

namespace QuadraticAlgebra

variable {a b : ℤ} {m n : ℕ}

/-- **Membership in `(m)`.** An element of `ℤ[ω]` lies in the principal ideal `(m)` exactly when
`m` divides both of its coordinates. -/
theorem mem_span_natCast_iff {z : QuadraticAlgebra ℤ a b} :
    z ∈ Ideal.span {(m : QuadraticAlgebra ℤ a b)} ↔ (m : ℤ) ∣ z.re ∧ (m : ℤ) ∣ z.im := by
  rw [Ideal.mem_span_singleton, ← map_natCast (algebraMap ℤ (QuadraticAlgebra ℤ a b)) m,
    algebraMap_dvd_iff]

/-- **Congruence modulo `(m)`.** Two elements of `ℤ[ω]` are congruent modulo `(m)` exactly when
their coordinates are congruent modulo `m`. -/
theorem sub_mem_span_natCast_iff {z w : QuadraticAlgebra ℤ a b} :
    z - w ∈ Ideal.span {(m : QuadraticAlgebra ℤ a b)} ↔
      z.re ≡ w.re [ZMOD m] ∧ z.im ≡ w.im [ZMOD m] := by
  rw [mem_span_natCast_iff, re_sub, im_sub]
  exact and_congr (by rw [Int.modEq_iff_dvd, dvd_sub_comm])
    (by rw [Int.modEq_iff_dvd, dvd_sub_comm])

/-- **Equality in `ℤ[ω]/(m)`.** Two elements of `ℤ[ω]` have the same class modulo `(m)` exactly
when their coordinates are congruent modulo `m`. -/
theorem mk_eq_mk_span_natCast_iff {z w : QuadraticAlgebra ℤ a b} :
    Ideal.Quotient.mk (Ideal.span {(m : QuadraticAlgebra ℤ a b)}) z =
        Ideal.Quotient.mk (Ideal.span {(m : QuadraticAlgebra ℤ a b)}) w ↔
      z.re ≡ w.re [ZMOD m] ∧ z.im ≡ w.im [ZMOD m] := by
  rw [Ideal.Quotient.eq, sub_mem_span_natCast_iff]

/-- Reduction modulo `m` is surjective. -/
theorem mapRingHom_intCastRingHom_surjective (a b : ℤ) (m : ℕ) :
    Function.Surjective (mapRingHom (Int.castRingHom (ZMod m)) a b) :=
  mapRingHom_surjective _ a b ZMod.intCast_surjective

/-- **The kernel of reduction modulo `m`.** Coefficientwise reduction
`ℤ[ω] → (ℤ/m)[ω]` has kernel the principal ideal `(m)`, for every `m`, including `m = 0`. -/
theorem ker_mapRingHom_intCastRingHom (a b : ℤ) (m : ℕ) :
    RingHom.ker (mapRingHom (Int.castRingHom (ZMod m)) a b) =
      Ideal.span {(m : QuadraticAlgebra ℤ a b)} := by
  rw [ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, map_natCast]

/-- An element of `ℤ[ω]` reduces to zero modulo `m` exactly when `m` divides both of its
coordinates. -/
theorem mapRingHom_intCastRingHom_eq_zero_iff {z : QuadraticAlgebra ℤ a b} :
    mapRingHom (Int.castRingHom (ZMod m)) a b z = 0 ↔ (m : ℤ) ∣ z.re ∧ (m : ℤ) ∣ z.im := by
  rw [← RingHom.mem_ker, ker_mapRingHom_intCastRingHom, mem_span_natCast_iff]

/-- Two elements of `ℤ[ω]` have the same reduction modulo `m` exactly when their coordinates are
congruent modulo `m`. -/
theorem mapRingHom_intCastRingHom_eq_iff {z w : QuadraticAlgebra ℤ a b} :
    mapRingHom (Int.castRingHom (ZMod m)) a b z = mapRingHom (Int.castRingHom (ZMod m)) a b w ↔
      z.re ≡ w.re [ZMOD m] ∧ z.im ≡ w.im [ZMOD m] := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_mapRingHom_intCastRingHom,
    sub_mem_span_natCast_iff]

/-- The first coordinate of the reduction modulo `m` is the reduction of the first coordinate.

Mathlib's `re_mapRingHom_apply` does not fire under `simp` at `f = Int.castRingHom (ZMod m)`,
since `Int.coe_castRingHom` first rewrites the reduced parameters `Int.castRingHom (ZMod m) a`
in the type of the coercion to `(a : ZMod m)`. This lemma is stated in that rewritten form. -/
@[simp]
theorem re_mapRingHom_intCastRingHom (z : QuadraticAlgebra ℤ a b) :
    (DFunLike.coe (F := QuadraticAlgebra ℤ a b →+* QuadraticAlgebra (ZMod m) a b)
      (mapRingHom (Int.castRingHom (ZMod m)) a b) z).re = z.re := by
  rw [re_mapRingHom_apply, eq_intCast]

/-- The second coordinate of the reduction modulo `m` is the reduction of the second coordinate;
see `re_mapRingHom_intCastRingHom` for the form of the statement. -/
@[simp]
theorem im_mapRingHom_intCastRingHom (z : QuadraticAlgebra ℤ a b) :
    (DFunLike.coe (F := QuadraticAlgebra ℤ a b →+* QuadraticAlgebra (ZMod m) a b)
      (mapRingHom (Int.castRingHom (ZMod m)) a b) z).im = z.im := by
  rw [im_mapRingHom_apply, eq_intCast]

/-- The reduction modulo `m` of the generator is the generator; see
`re_mapRingHom_intCastRingHom` for the form of the statement. -/
@[simp]
theorem mapRingHom_intCastRingHom_omega :
    DFunLike.coe (F := QuadraticAlgebra ℤ a b →+* QuadraticAlgebra (ZMod m) a b)
      (mapRingHom (Int.castRingHom (ZMod m)) a b) ω = ω :=
  mapRingHom_omega _ a b

variable (a b m) in
/-- **The quotient `ℤ[ω]/(m)`.** Reduction modulo `m` induces a ring isomorphism between
`ℤ[ω]/(m)` and the quadratic algebra over `ℤ/m` with the reduced parameters. -/
noncomputable def quotientSpanNatCastEquiv :
    QuadraticAlgebra ℤ a b ⧸ Ideal.span {(m : QuadraticAlgebra ℤ a b)} ≃+*
      QuadraticAlgebra (ZMod m) (a : ZMod m) (b : ZMod m) :=
  (Ideal.quotEquivOfEq (ker_mapRingHom_intCastRingHom a b m).symm).trans
    (RingHom.quotientKerEquivOfSurjective (mapRingHom_intCastRingHom_surjective a b m))

/-- `quotientSpanNatCastEquiv` sends the class of `z` to its reduction modulo `m`. -/
@[simp]
theorem quotientSpanNatCastEquiv_mk (z : QuadraticAlgebra ℤ a b) :
    quotientSpanNatCastEquiv a b m (Ideal.Quotient.mk _ z) =
      mapRingHom (Int.castRingHom (ZMod m)) a b z := by
  rw [quotientSpanNatCastEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- **Change of modulus.** For `m ∣ n`, the quotient map `ℤ[ω]/(n) → ℤ[ω]/(m)` corresponds under
`quotientSpanNatCastEquiv` to reducing both coordinates from `ℤ/n` to `ℤ/m`. -/
theorem quotientSpanNatCastEquiv_factor (h : m ∣ n)
    (x : QuadraticAlgebra ℤ a b ⧸ Ideal.span {(n : QuadraticAlgebra ℤ a b)}) :
    quotientSpanNatCastEquiv a b m (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (Nat.cast_dvd_cast h)) x) =
      ⟨ZMod.castHom h (ZMod m) (quotientSpanNatCastEquiv a b n x).re,
        ZMod.castHom h (ZMod m) (quotientSpanNatCastEquiv a b n x).im⟩ := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  ext <;> simp

/-- **The cardinality of `ℤ[ω]/(m)`.** The quotient has `m²` elements. At `m = 0` both sides
vanish: the quotient is `ℤ[ω]`, which is infinite. -/
theorem card_quotient_span_natCast (a b : ℤ) (m : ℕ) :
    Nat.card (QuadraticAlgebra ℤ a b ⧸ Ideal.span {(m : QuadraticAlgebra ℤ a b)}) = m ^ 2 := by
  rw [Nat.card_congr (quotientSpanNatCastEquiv a b m).toEquiv,
    Nat.card_congr (equivProd _ _), Nat.card_prod, Nat.card_zmod, sq]

/-- The quotient `ℤ[ω]/(m)` is finite exactly when `m ≠ 0`. -/
theorem finite_quotient_span_natCast_iff :
    Finite (QuadraticAlgebra ℤ a b ⧸ Ideal.span {(m : QuadraticAlgebra ℤ a b)}) ↔ m ≠ 0 := by
  rw [← pow_ne_zero_iff two_ne_zero, ← card_quotient_span_natCast a b m, Nat.card_ne_zero]
  exact ⟨fun h => ⟨inferInstance, h⟩, And.right⟩

instance [NeZero m] :
    Finite (QuadraticAlgebra ℤ a b ⧸ Ideal.span {(m : QuadraticAlgebra ℤ a b)}) :=
  finite_quotient_span_natCast_iff.mpr (NeZero.ne m)

end QuadraticAlgebra
