/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Frobenius
import TauCeti.FieldTheory.Finite.Frobenius
import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# The involution of a quadratic extension is a Frobenius at the primes it fixes

Let `S` be an `R`-algebra and `σ` an `R`-algebra involution of `S` whose fixed elements all come
from `R`, as for the nontrivial automorphism of a quadratic extension. Every `x ∈ S` is then a
root of the polynomial `X ^ 2 - (x + σ x) X + x σ x`, whose coefficients come from `R`. Let `Q` be
a prime of `S` with `σ Q ⊆ Q` and finite residue ring `R ⧸ Q ∩ R` of cardinality `q`. The
`q`-power map of `S ⧸ Q` fixes the coefficients of the reduction of that polynomial, so it sends
its root `x` to a root, `x` or `σ x`; and it fixes `x` only when `x` comes from `R ⧸ Q ∩ R`, where
`σ` fixes it too.
So `σ x ≡ x ^ q` modulo `Q`: `σ` is an arithmetic Frobenius at `Q`
(`AlgHom.IsArithFrobAt.of_involutive`). No hypothesis on the ramification of `Q` is needed: at a
ramified prime both sides are `x` modulo `Q`.

When an involution is a Frobenius at `Q` and does not act trivially on `S ⧸ Q`, the `q`-power map
is an automorphism of order two of the finite field `S ⧸ Q` over `R ⧸ Q ∩ R`, so `S ⧸ Q` has `q ^ 2`
elements (`AlgHom.IsArithFrobAt.natCard_quotient_eq_sq`). For the complex conjugation of a CM
field this says that the residue field of a prime fixed by conjugation, at which conjugation acts
nontrivially, has square cardinality, and that conjugation acts on it as the `q`-power Frobenius.

## Main results

* `AlgHom.IsArithFrobAt.of_involutive`: an `R`-algebra involution of `S` whose fixed elements come
  from `R` is an arithmetic Frobenius at every prime `Q` with `σ Q ⊆ Q` and `R ⧸ Q ∩ R` finite.
* `AlgHom.IsArithFrobAt.natCard_quotient_eq_sq`: if an involution is an arithmetic Frobenius at a
  prime `Q` and acts nontrivially modulo `Q`, then `#(S ⧸ Q) = #(R ⧸ Q ∩ R) ^ 2`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 (decomposition and inertia groups, the
  Frobenius automorphism).
-/

public section

namespace AlgHom.IsArithFrobAt

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ : S →ₐ[R] S} {Q : Ideal S}

/-- **The involution of a quadratic extension is a Frobenius at the primes it fixes.** Let `σ` be
an `R`-algebra involution of `S` whose fixed elements all come from `R`, and `Q` a prime of `S`
with `σ Q ⊆ Q` and `R ⧸ Q ∩ R` finite. Then `σ x ≡ x ^ #(R ⧸ Q ∩ R)` modulo `Q` for every
`x ∈ S`. -/
theorem of_involutive [Q.IsPrime] [_root_.Finite (R ⧸ Q.under R)] (hσ : Function.Involutive σ)
    (hfix : ∀ x, σ x = x → x ∈ Set.range (algebraMap R S)) (hQ : Q ≤ Q.comap σ) :
    σ.IsArithFrobAt Q := by
  set P := Q.under R
  have : P.IsMaximal := Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain (R ⧸ P))
  let := Ideal.Quotient.field P
  let := Fintype.ofFinite (R ⧸ P)
  let f := FiniteField.frobeniusAlgHom (R ⧸ P) (S ⧸ Q)
  intro x
  rw [← Ideal.Quotient.eq, map_pow, Nat.card_eq_fintype_card]
  set θ := Ideal.Quotient.mk Q x
  set θ' := Ideal.Quotient.mk Q (σ x)
  -- the coefficients `x + σ x` and `x * σ x` of the quadratic polynomial come from `R`
  obtain ⟨a, ha⟩ := hfix (x + σ x) (by rw [map_add, hσ x, add_comm])
  obtain ⟨b, hb⟩ := hfix (x * σ x) (by rw [map_mul, hσ x, mul_comm])
  have hroot : θ ^ 2 - algebraMap (R ⧸ P) (S ⧸ Q) (Ideal.Quotient.mk P a) * θ +
      algebraMap (R ⧸ P) (S ⧸ Q) (Ideal.Quotient.mk P b) = 0 := by
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver, ha, hb, map_add, map_mul, θ]
    ring
  -- so `θ ^ q` is a root as well, that is, `θ` or `θ'`
  have hfroot := congrArg f hroot
  simp only [map_add, map_sub, map_mul, map_pow, AlgHom.commutes, map_zero] at hfroot
  have hprod : (f θ - θ) * (f θ - θ') = 0 := by
    rw [← hfroot]
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver, ha, hb, map_add, map_mul, θ, θ']
    ring
  rw [FiniteField.frobeniusAlgHom_apply] at hprod
  rcases mul_eq_zero.mp hprod with h | h
  · -- if `θ ^ q = θ`, then `θ` comes from `R`, where `σ` acts trivially
    rw [sub_eq_zero] at h
    obtain ⟨c, hc⟩ := (TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap θ).mp h
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq] at hc
    rw [h, Ideal.Quotient.eq]
    have := hQ hc
    rw [Ideal.mem_comap, map_sub, AlgHom.commutes] at this
    simpa only [sub_sub_sub_cancel_left] using Q.sub_mem hc this
  · exact (sub_eq_zero.mp h).symm

/-- **The residue field at which an involutive Frobenius acts nontrivially has square order.** If
an involution `σ` of `S` is an arithmetic Frobenius at a prime `Q` and `σ x ≢ x` modulo `Q` for
some `x`, then `S ⧸ Q` is a quadratic extension of the finite field `R ⧸ Q ∩ R`, so
`#(S ⧸ Q) = #(R ⧸ Q ∩ R) ^ 2`. -/
theorem natCard_quotient_eq_sq [Q.IsPrime] (H : σ.IsArithFrobAt Q) (hσ : Function.Involutive σ)
    (hne : ∃ x, σ x - x ∉ Q) : Nat.card (S ⧸ Q) = Nat.card (R ⧸ Q.under R) ^ 2 := by
  set P := Q.under R
  have := H.finite_quotient
  have : P.IsMaximal := Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain (R ⧸ P))
  let := Ideal.Quotient.field P
  let := Fintype.ofFinite (R ⧸ P)
  -- the `q ^ 2`-power map is the identity of `S ⧸ Q`, since it is induced by `σ ^ 2 = 1`
  have hq2 (θ : S ⧸ Q) : θ ^ Fintype.card (R ⧸ P) ^ 2 = θ := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective θ
    rw [sq, pow_mul, ← Nat.card_eq_fintype_card, ← H.mk_apply, ← H.mk_apply, hσ x]
  -- so `S ⧸ Q` is finite, hence a field
  have : _root_.Finite (S ⧸ Q) := by
    have := TauCeti.FiniteField.finite_frobeniusFixedSubalgebra (K := R ⧸ P) (A := S ⧸ Q)
      two_ne_zero
    refine .of_injective (β := TauCeti.FiniteField.frobeniusFixedSubalgebra (R ⧸ P) (S ⧸ Q) 2)
      (fun θ ↦ ⟨θ, TauCeti.FiniteField.mem_frobeniusFixedSubalgebra.mpr ?_⟩)
      fun _ _ ↦ congrArg Subtype.val
    rw [Nat.card_eq_fintype_card, hq2]
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField Q (Finite.isField_of_domain (S ⧸ Q))
  let := Ideal.Quotient.field Q
  -- the `q`-power Frobenius of `S ⧸ Q` over `R ⧸ P` has order two
  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ P) (S ⧸ Q)
  have h2 : frob ^ 2 = 1 := by
    ext θ
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, AlgEquiv.one_apply]
    exact hq2 θ
  have h1 : frob ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    refine fun h ↦ hx (Ideal.Quotient.eq.mp ?_)
    rw [H.mk_apply, Nat.card_eq_fintype_card]
    exact DFunLike.congr_fun h (Ideal.Quotient.mk Q x)
  have hrank := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (R ⧸ P) (S ⧸ Q)
  rw [orderOf_eq_prime h2 h1] at hrank
  rw [Module.natCard_eq_pow_finrank (K := R ⧸ P), ← hrank]

end AlgHom.IsArithFrobAt
