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
a prime of `S` with `σ Q ⊆ Q` and finite residue ring `R ⧸ Q ∩ R` of cardinality `q`. If `x`
comes from `R ⧸ Q ∩ R` modulo `Q`, then `x ^ q ≡ x` and `σ` fixes `x` modulo `Q` too. Otherwise
the `q`-power map of `S ⧸ Q`, which fixes the coefficients of the reduction of that polynomial,
sends its root `x` to the other root `σ x`
(`TauCeti.FiniteField.pow_card_eq_neg_sub_of_notMem_range_algebraMap`).
So `σ x ≡ x ^ q` modulo `Q`: `σ` is an arithmetic Frobenius at `Q`
(`AlgHom.IsArithFrobAt.of_involutive`). No hypothesis on the ramification of `Q` is needed: at a
ramified prime both sides are `x` modulo `Q`.

When an involution is a Frobenius at `Q` and does not act trivially on `S ⧸ Q`, the map it induces
on `S ⧸ Q` (`AlgHom.IsArithFrobAt.restrict`), which is the `q`-power map, is an automorphism of
order two of the finite field `S ⧸ Q` over `R ⧸ Q ∩ R`, so `S ⧸ Q` has `q ^ 2`
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
  intro x
  rw [← Ideal.Quotient.eq, map_pow, Nat.card_eq_fintype_card]
  set θ := Ideal.Quotient.mk Q x
  by_cases hθ : θ ∈ Set.range (algebraMap (R ⧸ P) (S ⧸ Q))
  · -- if `θ` comes from `R`, then `θ ^ q = θ`, and `σ` acts trivially on `θ`
    rw [(TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap θ).mpr hθ,
      Ideal.Quotient.eq]
    obtain ⟨c, hc⟩ := hθ
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq] at hc
    have := hQ hc
    rw [Ideal.mem_comap, map_sub, AlgHom.commutes] at this
    simpa only [sub_sub_sub_cancel_left] using Q.sub_mem hc this
  · -- otherwise `θ ^ q` is the other root of `X ^ 2 - (x + σ x) X + x σ x`, whose coefficients
    -- come from `R`, namely `σ x`
    obtain ⟨a, ha⟩ := hfix (x + σ x) (by rw [map_add, hσ x, add_comm])
    obtain ⟨b, hb⟩ := hfix (x * σ x) (by rw [map_mul, hσ x, mul_comm])
    rw [TauCeti.FiniteField.pow_card_eq_neg_sub_of_notMem_range_algebraMap
      (b := -Ideal.Quotient.mk P a) (c := Ideal.Quotient.mk P b) hθ]
    · simp only [map_neg, neg_neg, Ideal.Quotient.algebraMap_mk_of_liesOver, ha, map_add, θ,
        add_sub_cancel_left]
    · simp only [map_neg, Ideal.Quotient.algebraMap_mk_of_liesOver, ha, hb, map_add, map_mul, θ]
      ring

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
  -- the map `H.restrict` that `σ` induces on `S ⧸ Q` squares to the identity, as `σ ^ 2 = 1`, and
  -- is not the identity
  have h2 : H.restrict ^ 2 = 1 := by
    ext θ
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective θ
    rw [pow_two, AlgHom.mul_apply, H.restrict_mk, H.restrict_mk, hσ x, AlgHom.one_apply]
  have h1 : H.restrict ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    refine fun h ↦ hx (Ideal.Quotient.eq.mp ?_)
    rw [← H.restrict_mk, h, AlgHom.one_apply]
  -- so the `q ^ 2`-power map is the identity of `S ⧸ Q`, which is therefore finite, hence a field
  have hq2 (θ : S ⧸ Q) : θ ^ Fintype.card (R ⧸ P) ^ 2 = θ := by
    rw [← Nat.card_eq_fintype_card, sq, pow_mul, ← H.restrict_apply, ← H.restrict_apply,
      ← AlgHom.mul_apply, ← sq, h2, AlgHom.one_apply]
  have : _root_.Finite (S ⧸ Q) := by
    have := TauCeti.FiniteField.finite_frobeniusFixedSubalgebra (K := R ⧸ P) (A := S ⧸ Q)
      two_ne_zero
    refine .of_injective (β := TauCeti.FiniteField.frobeniusFixedSubalgebra (R ⧸ P) (S ⧸ Q) 2)
      (fun θ ↦ ⟨θ, TauCeti.FiniteField.mem_frobeniusFixedSubalgebra.mpr ?_⟩)
      fun _ _ ↦ congrArg Subtype.val
    rw [Nat.card_eq_fintype_card, hq2]
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField Q (Finite.isField_of_domain (S ⧸ Q))
  let := Ideal.Quotient.field Q
  -- `H.restrict` is the `q`-power Frobenius of `S ⧸ Q` over `R ⧸ P`, which has order the degree
  have hfrob : H.restrict = FiniteField.frobeniusAlgHom (R ⧸ P) (S ⧸ Q) := by
    ext θ
    rw [H.restrict_apply, FiniteField.frobeniusAlgHom_apply, Nat.card_eq_fintype_card]
  have hrank := FiniteField.orderOf_frobeniusAlgHom (R ⧸ P) (S ⧸ Q)
  rw [← hfrob, orderOf_eq_prime h2 h1] at hrank
  rw [Module.natCard_eq_pow_finrank (K := R ⧸ P), ← hrank]

end AlgHom.IsArithFrobAt
