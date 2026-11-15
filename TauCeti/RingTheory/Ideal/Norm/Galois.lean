/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# Product of Galois conjugates of an ideal and the relative norm

Let `R → S` be a finite torsion-free extension of Dedekind domains with Galois group `G`, in the
sense of `IsGaloisGroup G R S`. For every ideal `I` of `S`, the product of its Galois translates
`∏ g : G, g • I` is the extension `(I.relNorm R).map (algebraMap R S)` of its relative norm. Over
`R = ℤ`, when `S` is free of finite rank over `ℤ`, this reads
`∏ g : G, g • I = Ideal.span {(I.absNorm : S)}`.

For a maximal ideal `P` above a nonzero maximal ideal `p = P.under R`, the Galois group acts
transitively on the primes `Q` of `S` above `p`, with decomposition groups of order `e(Q/p) f(Q/p)`
(`Ideal.card_stabilizer_eq_ramificationIdx_mul_inertiaDeg`). Partitioning `G` by the fibres of
`g ↦ g • P` therefore collects `∏ g, g • P` into `∏ Q ∣ p, Q ^ (e f)`, which equals
`(p S) ^ f(P/p) = (P.relNorm R) S` by Dedekind factorisation
(`Ideal.map_algebraMap_eq_finsetProd_pow`) and `Ideal.relNorm_eq_pow_of_isPrime_isGalois`. Prime
factorisation of ideals extends the identity to arbitrary ideals of `S`.

## Main results

* `Ideal.prod_smul_eq_map_relNorm`: `∏ g : G, g • I = (I.relNorm R).map (algebraMap R S)`.
* `Ideal.prod_smul_eq_span_absNorm`: over `ℤ`, `∏ g : G, g • I = Ideal.span {(I.absNorm : S)}`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 8.2 and §6.
* N. Xu, *Reciprocity Laws*, §6, proof of Corollary 6.13.
-/

public section

namespace Ideal

open scoped Pointwise

section RelNorm

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S] [IsGaloisGroup G R S]

open Classical in
/-- For a prime ideal `P ≠ ⊥` of `S` above `p = P.under R`, the fibre of `g ↦ g • P` in `G` over any
prime `Q` above `p` has cardinality `Q.ramificationIdx R * Q.inertiaDeg R`. -/
private theorem card_filter_smul_eq_of_mem_primesOver {P Q : Ideal S} [P.IsPrime]
    (hQ : Q ∈ (P.under R).primesOver S) (hp0 : P.under R ≠ ⊥) :
    (Finset.univ.filter fun g : G ↦ g • P = Q).card = Q.ramificationIdx R * Q.inertiaDeg R := by
  have : (P.under R).IsMaximal := (IsPrime.under R P).isMaximal hp0
  have : Q.IsPrime := hQ.1
  have : Q.LiesOver (P.under R) := hQ.2
  obtain ⟨τ, rfl⟩ := exists_smul_eq_of_isGaloisGroup (P.under R) P Q G
  have hbij : (Finset.univ.filter fun g : G ↦ g • P = τ • P).card =
      Fintype.card (MulAction.stabilizer G P) := by
    refine Finset.card_bij (fun g hg ↦ ⟨τ⁻¹ * g, ?_⟩) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_
    · rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, (Finset.mem_filter.mp hg).2]
    · intro g₁ _ g₂ _ h
      exact mul_left_cancel (congrArg Subtype.val h)
    · rintro ⟨s, hs⟩ _
      refine ⟨τ * s, ?_, Subtype.ext (inv_mul_cancel_left τ s)⟩
      rw [Finset.mem_filter, mul_smul, MulAction.mem_stabilizer_iff.mp hs]
      exact ⟨Finset.mem_univ _, rfl⟩
  rw [hbij, ← Nat.card_eq_fintype_card, card_stabilizer_eq_ramificationIdx_mul_inertiaDeg (R := R),
    ramificationIdx_smul, inertiaDeg_smul]

/-- **Galois product of a prime ideal.** For a prime element `P` of `Ideal S`, the product of its
Galois translates is the extension of `P.relNorm R`. -/
private theorem prod_smul_eq_map_relNorm_of_prime {P : Ideal S} (hP : Prime P) :
    ∏ g : G, g • P = (P.relNorm R).map (algebraMap R S) := by
  classical
  let := FractionRing.liftAlgebra R (FractionRing S)
  let := IsFractionRing.mulSemiringAction G S (FractionRing S)
  have := IsGaloisGroup.isGalois G (FractionRing R) (FractionRing S)
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have : P.IsPrime := isPrime_of_prime hP
  have hp0 : P.under R ≠ ⊥ := fun h ↦ hP0 <| by
    have : P.LiesOver ⊥ := ⟨h.symm⟩
    exact eq_bot_of_liesOver_bot R P
  have : (P.under R).IsMaximal := (IsPrime.under R P).isMaximal hp0
  have hmaps : ∀ g ∈ (Finset.univ : Finset G), g • P ∈ ((P.under R).primesOver S).toFinset :=
    fun g _ ↦ Set.mem_toFinset.mpr ⟨inferInstance, inferInstance⟩
  rw [← Finset.prod_fiberwise_of_maps_to hmaps, relNorm_eq_pow_of_isPrime_isGalois P (P.under R),
    Ideal.map_pow, map_algebraMap_eq_finsetProd_pow hp0, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun Q hQ ↦ ?_
  have hQ' := Set.mem_toFinset.mp hQ
  have : Q.IsPrime := hQ'.1
  have : Q.LiesOver (P.under R) := hQ'.2
  rw [Finset.prod_congr rfl fun g hg ↦ (Finset.mem_filter.mp hg).2, Finset.prod_const,
    card_filter_smul_eq_of_mem_primesOver G hQ' hp0, ← pow_mul,
    inertiaDeg_eq_of_isGaloisGroup (P.under R) P Q G]

/-- **Product of Galois conjugates of an ideal.** In a finite torsion-free extension `R → S` of
Dedekind domains with Galois group `G`, the product `∏ g : G, g • I` of the Galois translates of any
ideal `I` of `S` equals the extension `(I.relNorm R).map (algebraMap R S)` of its relative norm. -/
theorem prod_smul_eq_map_relNorm (I : Ideal S) :
    ∏ g : G, g • I = (I.relNorm R).map (algebraMap R S) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, relNorm_bot, Ideal.map_bot]
    simp_rw [smul_bot, ← zero_eq_bot]
    rw [Finset.prod_const, zero_pow Finset.univ_nonempty.card_ne_zero]
  | h₂ I hI =>
    rw [isUnit_iff.mp hI, relNorm_top, Ideal.map_top, ← one_eq_top]
    simp only [smul_one, Finset.prod_const_one]
  | h₃ J P _ hP ih =>
    simp_rw [smul_mul']
    rw [Finset.prod_mul_distrib, prod_smul_eq_map_relNorm_of_prime (R := R) G hP, ih, map_mul,
      Ideal.map_mul]

end RelNorm

/-- **Product of Galois conjugates over `ℤ`.** In a Dedekind domain `S` that is free of finite rank
over `ℤ` with Galois group `G` over `ℤ` (for instance `S = 𝓞 K` and `G = Gal(K/ℚ)` for a Galois
number field `K`), the product of the Galois translates of an ideal `I` is the principal ideal
generated by `I.absNorm`. -/
theorem prod_smul_eq_span_absNorm {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S] [IsGaloisGroup G ℤ S]
    (I : Ideal S) :
    ∏ g : G, g • I = span {(I.absNorm : S)} := by
  rw [prod_smul_eq_map_relNorm (R := ℤ) G I, relNorm_int, map_span, Set.image_singleton,
    map_natCast]

end Ideal
