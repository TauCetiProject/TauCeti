/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Frobenius
public import TauCeti.NumberTheory.NumberField.IntegralClosure

import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# Frobenius elements at finite places of algebraic extensions of number fields

Let `K` be a number field and `L` an algebraic, possibly infinite, extension of `K`, and let a
compact totally disconnected group `G` act continuously on `L` with the discrete topology, by
`K`-algebra automorphisms, with fixed field `K` (`Algebra.IsInvariant K L G`). The main example is
`L = K^alg` and `G = Gal(K^alg/K)`; another is a Galois extension `L/K` and `G = Gal(L/K)`, and
the group may also be an abstract profinite group acting through a quotient.

For a nonarchimedean absolute value `w` on `L` lying above a nonzero prime `p` of `𝓞 K` (that is,
`p = {r ∈ 𝓞 K | w r < 1}`), this file proves that some `σ : G` stabilizes the valuation subring
`A_w = {x | w x ≤ 1}` of `w` and acts on it by `x ↦ x ^ N(p)` modulo `w < 1`:
`w (σ • x - x ^ #(𝓞 K ⧸ p)) < 1` whenever `w x ≤ 1`. It also proves that any such `σ`, together
with the inertia group, topologically generates the stabilizer of `A_w`.

No completion of `L` is used. The proofs apply
`AbsoluteValue.exists_mem_stabilizer_forall_apply_smul_sub_pow_lt_one` to the integral closure
`B` of `𝓞 K` in `L`, whose elements fixed by `G` are those of `𝓞 K`
(`NumberField.isInvariant_integralClosure`) and whose localizations at primes are valuation rings
(`NumberField.preValuationRing_atPrime_integralClosure`), with the centre `Q = {b ∈ B | w b < 1}`
of `w` on `B`, on which `w ≤ 1` (`AbsoluteValue.apply_algebraMap_integralClosure_le_one`).

## Main results

* `AbsoluteValue.apply_algebraMap_integralClosure_le_one`: a nonarchimedean absolute value on `L`
  is at most `1` on the integral closure of `𝓞 K`.
* `AbsoluteValue.exists_mem_stabilizer_forall_apply_smul_sub_pow_lt_one_of_numberField`:
  existence of a Frobenius element at `w`.
* `AbsoluteValue.topologicalClosure_zpowers_sup_inertia_eq_stabilizer_of_numberField`: a
  Frobenius element at `w` and the inertia group of the centre of `w` generate the stabilizer
  of `A_w`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9 and Chapter II, §9.
* This replaces the completion argument of `New.IsPlaceOver.exists_isFrob` in the
  riemann-hypothesis project (https://github.com/leanprover-community/riemann-hypothesis, file
  `src/Lib/ClassField/Places/DecompositionCompletion.lean` at commit
  e38782a68eb5f6ee793739847c703aa16080ef6c), which embeds `L` in an algebraic closure of `ℚ_p`.
-/

public section

open MulAction NumberField Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {G : Type*} [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

namespace AbsoluteValue

variable {S : Type*} [Semifield S] [LinearOrder S] [IsStrictOrderedRing S] {w : AbsoluteValue L S}

/-- A nonarchimedean absolute value on an extension `L` of a number field `K` is at most `1` on
`𝓞 K`. -/
theorem apply_algebraMap_ringOfIntegers_le_one (hw : IsNonarchimedean w) (r : 𝓞 K) :
    w (algebraMap (𝓞 K) L r) ≤ 1 :=
  hw.apply_le_one_of_isIntegral_int (RingOfIntegers.isIntegral r).algebraMap

/-- A nonarchimedean absolute value on an extension `L` of a number field `K` is at most `1` on
the integral closure of `𝓞 K` in `L`. -/
theorem apply_algebraMap_integralClosure_le_one (hw : IsNonarchimedean w)
    (b : integralClosure (𝓞 K) L) : w (algebraMap (integralClosure (𝓞 K) L) L b) ≤ 1 :=
  hw.apply_le_one_of_isIntegral_int (isIntegral_trans (R := ℤ) (A := 𝓞 K) _ b.property)

variable (K w) in
/-- The centre `{b | w b < 1}` of a nonarchimedean absolute value `w` on the integral closure of
`𝓞 K` in `L`. -/
private noncomputable def centre (hw : IsNonarchimedean w) : Ideal (integralClosure (𝓞 K) L) :=
  (w.valuationSubring hw).valuation.centerIdeal (integralClosure (𝓞 K) L) fun b ↦
    ((w.valuationSubring hw).valuation_le_one_iff _).mpr <| (mem_valuationSubring_iff hw).mpr <|
      apply_algebraMap_integralClosure_le_one hw b

private theorem mem_centre_iff (hw : IsNonarchimedean w) (b : integralClosure (𝓞 K) L) :
    b ∈ centre K w hw ↔ w (algebraMap (integralClosure (𝓞 K) L) L b) < 1 := by
  rw [centre, Valuation.mem_centerIdeal, ← ValuationSubring.mem_nonunits_iff,
    mem_nonunits_valuationSubring_iff]

private instance (hw : IsNonarchimedean w) : (centre K w hw).IsPrime :=
  Valuation.isPrime_centerIdeal _

private theorem under_centre (hw : IsNonarchimedean w) {p : Ideal (𝓞 K)}
    (hp : ∀ r : 𝓞 K, r ∈ p ↔ w (algebraMap (𝓞 K) L r) < 1) : (centre K w hw).under (𝓞 K) = p := by
  ext r
  rw [Ideal.mem_comap, mem_centre_iff, hp, ← IsScalarTower.algebraMap_apply]

variable [NumberField K] [Algebra.IsAlgebraic K L] [Algebra.IsInvariant K L G]
  [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
  [TopologicalSpace L] [DiscreteTopology L] [ContinuousSMul G L]

/-- **Frobenius elements exist at finite places of algebraic extensions of number fields.** Let
`L/K` be algebraic, `K` a number field, and let a profinite group `G` act continuously on `L`
(discrete) by `K`-automorphisms with fixed field `K`. If `w` is a nonarchimedean absolute value on
`L` above the nonzero prime `p = {r ∈ 𝓞 K | w r < 1}`, some `σ : G` stabilizes the valuation
subring of `w` and satisfies `w (σ • x - x ^ #(𝓞 K ⧸ p)) < 1` whenever `w x ≤ 1`. -/
theorem exists_mem_stabilizer_forall_apply_smul_sub_pow_lt_one_of_numberField
    (hw : IsNonarchimedean w) {p : Ideal (𝓞 K)}
    (hp : ∀ r : 𝓞 K, r ∈ p ↔ w (algebraMap (𝓞 K) L r) < 1) (hp0 : p ≠ ⊥) :
    ∃ σ : G, σ ∈ stabilizer G (w.valuationSubring hw) ∧
      ∀ x, w x ≤ 1 → w (σ • x - x ^ Nat.card (𝓞 K ⧸ p)) < 1 := by
  have := Ideal.finiteQuotientOfFreeOfNeBot p hp0
  rw [← under_centre hw hp] at this ⊢
  exact exists_mem_stabilizer_forall_apply_smul_sub_pow_lt_one hw
    (apply_algebraMap_ringOfIntegers_le_one hw) (mem_centre_iff hw)

omit [Algebra.IsInvariant K L G] in
/-- **A Frobenius element and inertia generate the stabilizer of a finite place.** In the setting
of `AbsoluteValue.exists_mem_stabilizer_forall_apply_smul_sub_pow_lt_one_of_numberField`, let `Q`
be the centre `{b | w b < 1}` of `w` on the integral closure of `𝓞 K` in `L`. If `σ` satisfies
`w (σ • x - x ^ #(𝓞 K ⧸ p)) < 1` whenever `w x ≤ 1`, the stabilizer of the valuation subring of
`w` is generated by the closure of `⟨σ⟩` and the inertia group of `Q`, which consists of the `g`
with `w (g • x - x) < 1` whenever `w x ≤ 1`
(`AbsoluteValue.mem_inertia_iff_forall_apply_smul_sub_lt_one`). The fixed field of `G` plays no
role here. -/
theorem topologicalClosure_zpowers_sup_inertia_eq_stabilizer_of_numberField
    (hw : IsNonarchimedean w) {p : Ideal (𝓞 K)}
    (hp : ∀ r : 𝓞 K, r ∈ p ↔ w (algebraMap (𝓞 K) L r) < 1)
    {Q : Ideal (integralClosure (𝓞 K) L)}
    (hQ : ∀ b, b ∈ Q ↔ w (algebraMap (integralClosure (𝓞 K) L) L b) < 1) {σ : G}
    (hσ : ∀ x, w x ≤ 1 → w (σ • x - x ^ Nat.card (𝓞 K ⧸ p)) < 1) :
    (Subgroup.zpowers σ).topologicalClosure ⊔ Q.inertia G =
      stabilizer G (w.valuationSubring hw) := by
  obtain rfl : Q = centre K w hw := Ideal.ext fun b ↦ (hQ b).trans (mem_centre_iff hw b).symm
  rw [← under_centre hw hp] at hσ
  exact topologicalClosure_zpowers_sup_inertia_eq_stabilizer_valuationSubring hw
    (apply_algebraMap_integralClosure_le_one hw) (mem_centre_iff hw) hσ

end AbsoluteValue
