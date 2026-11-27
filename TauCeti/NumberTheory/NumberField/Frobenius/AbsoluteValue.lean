/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.Analysis.AbsoluteValue.Frobenius

import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import TauCeti.RingTheory.DedekindDomain.Prufer

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
`B` of `𝓞 K` in `L`, whose elements fixed by `G` are those of `𝓞 K` and whose localizations at
primes are valuation rings (Tau Ceti's `IsIntegralClosure.preValuationRing_atPrime`), with the
centre `Q = {b ∈ B | w b < 1}` of `w` on `B`.

## Main results

* `NumberField.isInvariant_integralClosure`: the elements of the integral closure of `𝓞 K` in `L`
  fixed by `G` are those of `𝓞 K`.
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

namespace NumberField

/-- A group acting on `L` by `K`-algebra automorphisms acts by `𝓞 K`-algebra automorphisms. -/
instance smulCommClass_ringOfIntegers : SMulCommClass G (𝓞 K) L where
  smul_comm g r x := by
    rw [← algebraMap_smul K r x, ← algebraMap_smul K r (g • x), smul_comm]

/-- If `G` fixes exactly `K` in `L`, then the elements of the integral closure of `𝓞 K` in `L`
fixed by `G` are those of `𝓞 K`. -/
instance isInvariant_integralClosure [Algebra.IsInvariant K L G] :
    Algebra.IsInvariant (𝓞 K) (integralClosure (𝓞 K) L) G where
  isInvariant b hb := by
    obtain ⟨k, hk⟩ := Algebra.IsInvariant.isInvariant (A := K) (G := G) (b : L)
      fun g ↦ congr_arg Subtype.val (hb g)
    have hint : IsIntegral ℤ (algebraMap K L k) := by
      rw [hk]
      exact isIntegral_trans (R := ℤ) (A := 𝓞 K) _ b.property
    exact ⟨⟨k, (isIntegral_algHom_iff ((Algebra.ofId K L).restrictScalars ℤ)
      (algebraMap K L).injective).mp hint⟩, Subtype.ext hk⟩

end NumberField

namespace AbsoluteValue

variable {S : Type*} [Semifield S] [LinearOrder S] [IsStrictOrderedRing S] {w : AbsoluteValue L S}

/-- A nonarchimedean absolute value on an extension `L` of a number field `K` is at most `1` on
`𝓞 K`. -/
theorem apply_algebraMap_ringOfIntegers_le_one (hw : IsNonarchimedean w) (r : 𝓞 K) :
    w (algebraMap (𝓞 K) L r) ≤ 1 := by
  refine apply_le_one_of_isIntegral hw (R := ℤ) (fun n ↦ ?_) ?_
  · rw [eq_intCast]
    exact (mem_valuationSubring_iff hw).mp (intCast_mem _ n)
  · rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact (RingOfIntegers.isIntegral_coe r).algebraMap

variable (K w) in
/-- The centre `{b | w b < 1}` of a nonarchimedean absolute value `w` on the integral closure of
`𝓞 K` in `L`. -/
private noncomputable def centre (hw : IsNonarchimedean w) : Ideal (integralClosure (𝓞 K) L) :=
  (w.valuationSubring hw).valuation.centerIdeal (integralClosure (𝓞 K) L) fun b ↦
    ((w.valuationSubring hw).valuation_le_one_iff _).mpr <| (mem_valuationSubring_iff hw).mpr <|
      apply_le_one_of_isIntegral hw (apply_algebraMap_ringOfIntegers_le_one hw) b.property

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

variable [NumberField K] [Algebra.IsAlgebraic K L]

private instance : IsFractionRing (integralClosure (𝓞 K) L) L :=
  have : Algebra.IsAlgebraic (𝓞 K) L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  integralClosure.isFractionRing_of_algebraic fun _ hx ↦
    IsFractionRing.to_map_eq_zero_iff.mp ((map_eq_zero (algebraMap K L)).mp
      ((IsScalarTower.algebraMap_apply (𝓞 K) K L _).symm.trans hx))

private instance (Q : Ideal (integralClosure (𝓞 K) L)) [Q.IsPrime] :
    PreValuationRing (Localization.AtPrime Q) :=
  IsIntegralClosure.preValuationRing_atPrime (𝓞 K) K L Q

variable [Algebra.IsInvariant K L G] [TopologicalSpace G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [IsTopologicalGroup G] [TopologicalSpace L] [DiscreteTopology L]
  [ContinuousSMul G L]

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
    (fun b ↦ apply_le_one_of_isIntegral hw (apply_algebraMap_ringOfIntegers_le_one hw) b.property)
    (mem_centre_iff hw) hσ

end AbsoluteValue
