/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotients of products of rings by an idempotent

Let `(V i)_{i : I}` be a family of commutative rings without zero divisors, and let `e : ∀ i, V i`
be an idempotent element (`IsIdempotentElem e`). At each coordinate `i`, either `e i = 1` or
`e i = 0`, so restricting a tuple to the coordinates `{i // e i ≠ 1}` defines a surjective ring
homomorphism `TauCeti.piIdempotentRestrict e` whose kernel is `Ideal.span {e}`
(`TauCeti.ker_piIdempotentRestrict`). Consequently, the quotient `(∀ i, V i) ⧸ Ideal.span {e}` is
isomorphic to `∀ i : {i // e i ≠ 1}, V i.val` (`TauCeti.piQuotientSpanIdempotentEquiv`), and
every ring homomorphism out of `∀ i, V i` killing `e` factors uniquely through this projection
(`TauCeti.existsUnique_comp_piIdempotentRestrict`).

## Main results

* `TauCeti.piIdempotentRestrict`: the coordinate projection
  `(∀ i, V i) →+* ∀ i : {i // e i ≠ 1}, V i.val`.
* `TauCeti.surjective_piIdempotentRestrict`: `piIdempotentRestrict e` is surjective.
* `TauCeti.ker_piIdempotentRestrict`: for an idempotent `e` in a product of rings with
  `NoZeroDivisors`, the kernel of `piIdempotentRestrict e` is `Ideal.span {e}`.
* `TauCeti.piQuotientSpanIdempotentEquiv`: the induced ring isomorphism
  `((∀ i, V i) ⧸ Ideal.span {e}) ≃+* ∀ i : {i // e i ≠ 1}, V i.val`.
* `TauCeti.existsUnique_comp_piIdempotentRestrict`: universal property among ring homomorphisms
  killing `e`.

## Provenance

Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/PadicComparison/Descent/TestCovers.lean`, declaration
`New.Variety.PadicTest.exists_isQuotientByElem`, generalized from products of `p`-adic cells to
arbitrary products of commutative rings without zero divisors.
-/

public section

namespace TauCeti

variable {I : Type*} {V : I → Type*} [∀ i, CommRing (V i)]

/-- Projection from a product of rings `∀ i, V i` onto the coordinates where `e i ≠ 1`. -/
def piIdempotentRestrict (e : ∀ i, V i) : (∀ i, V i) →+* ∀ i : {i // e i ≠ 1}, V i.val :=
  RingHom.pi fun i ↦ Pi.evalRingHom V i.val

/-- The projection `piIdempotentRestrict e` is surjective. -/
theorem surjective_piIdempotentRestrict (e : ∀ i, V i) :
    Function.Surjective (piIdempotentRestrict e) :=
  Subtype.surjective_restrict fun i ↦ e i ≠ 1

/-- For an idempotent `e` in a product of rings without zero divisors, the kernel of
`piIdempotentRestrict e` is the principal ideal `Ideal.span {e}`. -/
theorem ker_piIdempotentRestrict [∀ i, NoZeroDivisors (V i)] {e : ∀ i, V i}
    (he : IsIdempotentElem e) :
    RingHom.ker (piIdempotentRestrict e) = Ideal.span {e} := by
  refine le_antisymm (fun x hx ↦ Ideal.mem_span_singleton'.mpr ⟨x, ?_⟩) ?_
  · ext i
    by_cases hi : e i = 1
    · simp [hi]
    · have hxi : x i = 0 := congrFun hx ⟨i, hi⟩
      have hei : e i = 0 := mul_left_eq_self₀.mp (congrFun he i) |>.resolve_left hi
      simp [hxi, hei]
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    ext i
    exact (mul_left_eq_self₀.mp (congrFun he i.val)).resolve_left i.property

/-- For an idempotent `e` in a product of rings without zero divisors, the quotient by
`Ideal.span {e}` is isomorphic to the sub-product over `{i // e i ≠ 1}`. -/
noncomputable def piQuotientSpanIdempotentEquiv [∀ i, NoZeroDivisors (V i)] {e : ∀ i, V i}
    (he : IsIdempotentElem e) :
    ((∀ i, V i) ⧸ Ideal.span {e}) ≃+* ∀ i : {i // e i ≠ 1}, V i.val :=
  (Ideal.quotEquivOfEq (ker_piIdempotentRestrict he).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_piIdempotentRestrict e))

/-- Every ring homomorphism `g : (∀ i, V i) →+* S` killing an idempotent `e` factors uniquely
through `piIdempotentRestrict e`. -/
theorem existsUnique_comp_piIdempotentRestrict [∀ i, NoZeroDivisors (V i)] {S : Type*}
    [CommRing S] {e : ∀ i, V i} (he : IsIdempotentElem e) {g : (∀ i, V i) →+* S}
    (hg : g e = 0) :
    ∃! g₀ : (∀ i : {i // e i ≠ 1}, V i.val) →+* S, g₀.comp (piIdempotentRestrict e) = g := by
  let f := piIdempotentRestrict e
  let eqv := RingHom.quotientKerEquivOfSurjective (surjective_piIdempotentRestrict e)
  have hker : RingHom.ker f ≤ RingHom.ker g := by
    rw [ker_piIdempotentRestrict he, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact hg
  let g₀ := (Ideal.Quotient.lift (RingHom.ker f) g fun a ha ↦ hker ha).comp eqv.symm.toRingHom
  have hcomp : g₀.comp f = g := by
    ext x
    have h1 : eqv (Ideal.Quotient.mk (RingHom.ker f) x) = f x := rfl
    simp [g₀, ← h1]
    rfl
  refine ⟨g₀, hcomp, fun g' hg' ↦ ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := surjective_piIdempotentRestrict e y
  exact (RingHom.congr_fun hg' x).trans (RingHom.congr_fun hcomp x).symm

end TauCeti
