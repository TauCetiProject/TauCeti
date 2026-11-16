/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Dvr
import TauCeti.RingTheory.RamificationInertia.Unramified

/-!
# The ramification index over a discrete valuation ring

Let `S → T` be a local homomorphism from a local ring to a discrete valuation ring such that the
maximal ideal `𝔪_S` of `S` does not map to zero. Then `𝔪_S T` is a nonzero ideal of `T`, hence a
power `𝔪_T ^ e` of the maximal ideal of `T`, and `e` is Mathlib's ramification index
`(maximalIdeal T).ramificationIdx S`, the length of `T ⧸ 𝔪_S T`. For an extension of discrete
valuation rings this is the ramification index of Stacks, Definition 15.113.1 (09E4): the
exponent `e` with `π_S = u π_T ^ e` for uniformizers `π_S`, `π_T` and a unit `u`.

Globalizing along a torsion-free extension `A → B` from a discrete valuation ring `A` to a Dedekind
domain `B`, the localization `Localization.AtPrime P` at any prime `P` over `maximalIdeal A` is a
discrete valuation ring in which a uniformizer `π` of `A` factors as `u * ϖ ^ P.ramificationIdx A`
for a uniformizer `ϖ` and unit `u`. Conversely, in a tower `A → A₁ → B₁` with `A` local and `A₁` a
discrete valuation ring, if a uniformizer of `A₁` remains irreducible in a discrete valuation ring
localization `Localization.AtPrime Q` at a maximal ideal `Q` over `maximalIdeal A₁` whose residue
field is separable over `ResidueField A`, then `Q.ramificationIdx A₁ = 1` and `(B₁ ⧸ Q)` is
separable over `(A₁ ⧸ maximalIdeal A₁)`.

## Main results

* `TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx`: `𝔪_S T = 𝔪_T ^ e` with
  `e` the ramification index of `𝔪_T` over `S`.
* `TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow`: the index equals
  any exponent satisfying this maximal-ideal identity.
* `Ideal.isDiscreteValuationRing_localizationAtPrime_of_liesOver` and
  `Ideal.exists_eq_unit_mul_pow_ramificationIdx`: for a prime `P` of a Dedekind domain `B` over a
  nonzero ideal (in particular `maximalIdeal A` of a discrete valuation ring `A`), `B_P` is a
  discrete valuation ring in which a uniformizer of `A` writes as `u * ϖ ^ P.ramificationIdx A`.
* `Ideal.ramificationIdx_eq_one_and_isSeparable_of_irreducible_localizationAtPrime`: ramification
  index one and quotient-field separability over a discrete valuation ring `A₁` when a uniformizer
  of `A₁` stays irreducible in `Localization.AtPrime Q` and `ResidueField (Localization.AtPrime Q)`
  is separable over `ResidueField A`.

## References

* [Stacks Project, Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/Divisors.lean`:
  `map_maximalIdeal_eq_pow_ramificationIdx` is the local form of its
  `Pcf.heightOneRamificationIdx_eq_dvrExponent` with `Pcf.heightOneDvrExponent_spec`, stated
  there at a height-one prime of a finite extension of normal Noetherian domains.
-/

public section

open IsLocalRing IsDiscreteValuationRing

namespace TauCeti.IsDiscreteValuationRing

variable {S T : Type*} [CommRing S] [CommRing T] [IsLocalRing S] [IsDomain T]
  [IsDiscreteValuationRing T] [Algebra S T] [IsLocalHom (algebraMap S T)]

/-- For a local homomorphism from a local ring `S` to a discrete valuation ring `T` under which
the maximal ideal of `S` does not vanish, `𝔪_S T = 𝔪_T ^ e` with `e` the ramification index of the
maximal ideal of `T` over `S`. -/
theorem map_maximalIdeal_eq_pow_ramificationIdx
    (h : (maximalIdeal S).map (algebraMap S T) ≠ ⊥) :
    (maximalIdeal S).map (algebraMap S T) =
      maximalIdeal T ^ (maximalIdeal T).ramificationIdx S := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible T
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible h hϖ
  have hpow : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  -- The length-based ramification index agrees with the exponent-based one over the Dedekind
  -- domain `T` (`Ideal.ramificationIdx'_eq_ramificationIdx'`), and the latter is `n`.
  have : (maximalIdeal T).LiesOver (maximalIdeal S) :=
    ⟨(maximalIdeal_comap (algebraMap S T)).symm⟩
  have hidx : (maximalIdeal T).ramificationIdx S = n := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx' (maximalIdeal S) (maximalIdeal T) h]
    refine Ideal.ramificationIdx'_spec hpow.le ?_
    rw [hpow]
    exact (Ideal.pow_succ_lt_pow (not_a_field T) n).not_ge
  rw [hidx, hpow]

/-- For a local homomorphism to a DVR, the exponent in a maximal-ideal power identity is the
ramification index. This is the exponent characterization of Stacks, Definition 15.113.1 (09E4),
with no DVR assumption on the base ring. -/
@[stacks 09E4 "exponent characterization with arbitrary local base ring"]
theorem ramificationIdx_eq_of_map_maximalIdeal_eq_pow {exponent : ℕ}
    (hexponent : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ^ exponent) :
    (maximalIdeal T).ramificationIdx S = exponent := by
  have hpowers : StrictAnti (fun power : ℕ ↦ maximalIdeal T ^ power) :=
    Ideal.pow_right_strictAnti (maximalIdeal T) (not_a_field T) (maximalIdeal.isMaximal T).ne_top
  have hmap : (maximalIdeal S).map (algebraMap S T) ≠ ⊥ := by
    rw [hexponent]
    exact ne_of_gt (lt_of_le_of_lt bot_le (hpowers (Nat.lt_succ_self exponent)))
  exact hpowers.injective ((map_maximalIdeal_eq_pow_ramificationIdx hmap).symm.trans hexponent)

end TauCeti.IsDiscreteValuationRing

namespace Ideal

/-- If `P` is a prime ideal of a Dedekind domain `B` lying over a nonzero ideal `p` along an
injective algebra map `A → B`, then `Localization.AtPrime P` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_localizationAtPrime_of_liesOver
    {A B : Type*} [CommSemiring A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [FaithfulSMul A B] (P : Ideal B) [P.IsPrime] {p : Ideal A} (hp : p ≠ ⊥) [P.LiesOver p] :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  refine IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
    (fun hP : P = ⊥ ↦ hp ?_) (Localization.AtPrime P)
  refine eq_bot_iff.mpr fun a ha ↦ ?_
  have haP : algebraMap A B a ∈ (⊥ : Ideal B) := hP ▸ (P.mem_of_liesOver p a).mp ha
  exact Ideal.mem_bot.mpr ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mp
    (Ideal.mem_bot.mp haP))

/-- At a prime ideal `P` of a Dedekind domain `B` lying over the maximal ideal of a discrete
valuation ring `A` with `[FaithfulSMul A B]`, a uniformizer `π` of `A` factors in
`Localization.AtPrime P` as `u * ϖ ^ P.ramificationIdx A` for a uniformizer `ϖ` and unit `u`. -/
theorem exists_eq_unit_mul_pow_ramificationIdx
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [FaithfulSMul A B]
    (P : Ideal B) [P.IsPrime] [P.LiesOver (maximalIdeal A)] {π : A} (hπ : Irreducible π) :
    ∃ (ϖ u : Localization.AtPrime P), Irreducible ϖ ∧ IsUnit u ∧
      algebraMap A (Localization.AtPrime P) π = u * ϖ ^ P.ramificationIdx A := by
  have := P.isDiscreteValuationRing_localizationAtPrime_of_liesOver (not_a_field A)
  have := Localization.AtPrime.isLocalHom_algebraMap_of_liesOver (R := A) P
  have : FaithfulSMul A (Localization.AtPrime P) := .trans A B _
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible (Localization.AtPrime P)
  have hmap_ne : (maximalIdeal A).map (algebraMap A (Localization.AtPrime P)) ≠ ⊥ := fun hbot ↦
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A (Localization.AtPrime P))).mpr
      hπ.ne_zero (Ideal.mem_bot.mp
        (hbot ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal π).mpr hπ.not_isUnit)))
  have hpow := TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx hmap_ne
  have he_eq : P.ramificationIdx A = (maximalIdeal (Localization.AtPrime P)).ramificationIdx A :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A) P _ hpow
  rw [← he_eq, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hϖ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hpow
  obtain ⟨u, hu⟩ := hpow.symm
  exact ⟨ϖ, u, hϖ, u.isUnit, by rw [← hu, mul_comm]⟩

/-- In a tower `A → A₁ → B₁` with `A` local and `A₁` a discrete valuation ring, if `Q` is a maximal
ideal of `B₁` over `maximalIdeal A₁` whose localization `Localization.AtPrime Q` is a discrete
valuation ring dominating `A` in which a uniformizer `ϖ₁` of `A₁` stays irreducible, and
`IsLocalRing.ResidueField (Localization.AtPrime Q)` is separable over `IsLocalRing.ResidueField A`,
then `Q.ramificationIdx A₁ = 1` and `B₁ ⧸ Q` is separable over `A₁ ⧸ maximalIdeal A₁`. -/
theorem ramificationIdx_eq_one_and_isSeparable_of_irreducible_localizationAtPrime
    {A A₁ B₁ : Type*} [CommRing A] [IsLocalRing A]
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A A₁]
    [CommRing B₁] [Algebra A B₁] [Algebra A₁ B₁] [IsScalarTower A A₁ B₁]
    (Q : Ideal B₁) [Q.IsMaximal] [Q.LiesOver (maximalIdeal A₁)]
    [IsDomain (Localization.AtPrime Q)] [IsDiscreteValuationRing (Localization.AtPrime Q)]
    [IsLocalHom (algebraMap A (Localization.AtPrime Q))]
    {ϖ₁ : A₁} (hϖ₁ : Irreducible ϖ₁)
    (hirr : Irreducible (algebraMap B₁ (Localization.AtPrime Q) (algebraMap A₁ B₁ ϖ₁)))
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Localization.AtPrime Q))) :
    Q.ramificationIdx A₁ = 1 ∧
      Algebra.IsSeparable (A₁ ⧸ maximalIdeal A₁) (B₁ ⧸ Q) := by
  have hmap1 : (maximalIdeal A₁).map (algebraMap A₁ (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) ^ 1 := by
    rw [pow_one, hϖ₁.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      IsScalarTower.algebraMap_apply A₁ B₁ (Localization.AtPrime Q), hirr.maximalIdeal_eq]
  refine ⟨Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A₁) Q 1 hmap1, ?_⟩
  have := Localization.AtPrime.isLocalHom_algebraMap_of_liesOver (R := A₁) Q
  have : IsScalarTower A A₁ (Localization.AtPrime Q) := .to₁₂₄ A A₁ B₁ (Localization.AtPrime Q)
  have : IsLocalHom ((algebraMap A₁ (Localization.AtPrime Q)).comp (algebraMap A A₁)) := by
    rw [← IsScalarTower.algebraMap_eq A A₁ (Localization.AtPrime Q)]
    infer_instance
  have : IsLocalHom (algebraMap A A₁) :=
    isLocalHom_of_comp (algebraMap A A₁) (algebraMap A₁ (Localization.AtPrime Q))
  have hsepA₁ : Algebra.IsSeparable (IsLocalRing.ResidueField A₁)
      (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
    Algebra.isSeparable_tower_top_of_isSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A₁) (IsLocalRing.ResidueField (Localization.AtPrime Q))
  let := Ideal.Quotient.field (maximalIdeal A₁)
  let := Ideal.Quotient.field Q
  exact (Q.isSeparable_quotient_iff_residueField (R := A₁)).mpr hsepA₁

end Ideal
