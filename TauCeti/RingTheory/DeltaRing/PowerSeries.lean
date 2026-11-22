/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.RingTheory.DeltaRing.Basic

/-!
# Frobenius lifts on power series rings

Let `σ` be a Frobenius lift on a commutative ring `A`, that is `σ a ≡ a ^ p` modulo `p`. Then the
ring endomorphism of `A⟦X⟧` that applies `σ` to the coefficients and substitutes `X ^ p` for `X`,

```text
∑ aₙ Xⁿ ↦ ∑ σ(aₙ) X ^ (p n),
```

is again a Frobenius lift (`TauCeti.DeltaRing.IsFrobeniusLift.powerSeries`). For `A = W(k)` with
`k` perfect of characteristic `p` and `σ` the Witt-vector Frobenius, this is the Frobenius of the
Breuil–Kisin ring `𝔖 = W(k)⟦u⟧`, with `φ(u) = u ^ p`.

Modulo `p` the claim is the identity `(∑ bₙ Xⁿ) ^ p = ∑ bₙ ^ p X ^ (p n)` in characteristic `p`
(Mathlib's `PowerSeries.map_frobenius_expand`).
-/

public section

open scoped PowerSeries

namespace TauCeti.DeltaRing

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A]

/-- If `σ` is a Frobenius lift on `A`, then `∑ aₙ Xⁿ ↦ ∑ σ(aₙ) X ^ (p n)` is a Frobenius lift on
`A⟦X⟧`. -/
theorem IsFrobeniusLift.powerSeries {σ : A →+* A} (hσ : IsFrobeniusLift p σ) :
    IsFrobeniusLift p
      ((PowerSeries.map σ).comp (PowerSeries.expand p hp.out.ne_zero : A⟦X⟧ →ₐ[A] A⟦X⟧)) := by
  refine ⟨fun f ↦ ?_⟩
  by_cases hu : IsUnit (p : A)
  · exact (map_natCast (PowerSeries.C (R := A)) p ▸ hu.map PowerSeries.C).dvd
  have := CharP.quotient A p hu
  set q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hq : q.comp σ = (_root_.frobenius _ p).comp q :=
    RingHom.ext fun a ↦ by simpa [q, frobenius_def] using hσ.mk_eq a
  have hmap : PowerSeries.map q
      ((PowerSeries.map σ).comp (PowerSeries.expand p hp.out.ne_zero : A⟦X⟧ →ₐ[A] A⟦X⟧) f -
        f ^ p) = 0 := by
    rw [map_sub, map_pow, RingHom.comp_apply, ← RingHom.comp_apply (PowerSeries.map q),
      ← PowerSeries.map_comp, hq, PowerSeries.map_comp, RingHom.comp_apply, RingHom.coe_coe,
      PowerSeries.map_expand, PowerSeries.map_frobenius_expand, sub_self]
  have hcoeff (n : ℕ) : (p : A) ∣ PowerSeries.coeff n
      ((PowerSeries.map σ).comp (PowerSeries.expand p hp.out.ne_zero : A⟦X⟧ →ₐ[A] A⟦X⟧) f -
        f ^ p) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← PowerSeries.coeff_map,
      hmap, map_zero]
  choose c hc using hcoeff
  refine ⟨PowerSeries.mk c, PowerSeries.ext fun n ↦ ?_⟩
  rw [hc, ← map_natCast (PowerSeries.C (R := A)), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

end TauCeti.DeltaRing
