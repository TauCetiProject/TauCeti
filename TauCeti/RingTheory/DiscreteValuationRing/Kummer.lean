/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Integral
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.RingTheory.DiscreteValuationRing.Eisenstein
import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly

/-!
# Adjoining a root of a uniformizer to a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, let `n ≠ 0`, and
let `L = K(α)` be a field generated over `K` by an `n`-th root `α` of `π`. Then

1. `[L : K] = n`, and the minimal polynomial of `α` over `A` is `X ^ n - π`;
2. the integral closure `A₁` of `A` in `L` is `A[α]`, so that `A₁ ≅ A[X] ⧸ (X ^ n - π)` by
   Mathlib's `minpoly.equivAdjoin`;
3. `A₁` is a discrete valuation ring with uniformizer `α`;
4. the maximal ideal of `A₁` has ramification index `n` over `A`;
5. `L` is totally ramified with respect to `A`.

These are parts (1)–(5) of Stacks, Lemma 15.116.2. They hold for every `n ≠ 0`, also when the
residue characteristic divides `n` and `L / K` is inseparable. The ring-theoretic input is that
`X ^ n - π` is Eisenstein, so that `A[α]` is a discrete valuation ring with uniformizer `α`
(`Polynomial.IsEisensteinAt.isDiscreteValuationRing_of_adjoin_eq_top`). Being integrally closed
and having fraction field `L`, it is then the integral closure of `A` in `L`.

## Main results

* `TauCeti.IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible`: `[L : K] = n`.
* `TauCeti.IsDiscreteValuationRing.minpoly_eq_of_pow_eq_of_irreducible`: the minimal polynomial of
  `α` over `A` is `X ^ n - π`.
* `TauCeti.IsDiscreteValuationRing.integralClosure_eq_adjoin_of_pow_eq_of_irreducible`: the
  integral closure of `A` in `L` is `A[α]`.
* `TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible`
  and `TauCeti.IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible`: it is a discrete
  valuation ring with uniformizer `α`.
* `TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_pow_eq_of_irreducible`: its maximal ideal
  has ramification index `n` over `A`.
* `TauCeti.IsDiscreteValuationRing.isTotallyRamifiedWRT_of_pow_eq_of_irreducible`: `L` is totally
  ramified with respect to `A`.

## References

* [Stacks Project, Lemma 15.116.2](https://stacks.math.columbia.edu/tag/09EV).
-/

public section

open IntermediateField IsLocalRing Polynomial

namespace TauCeti.IsDiscreteValuationRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A} {n : ℕ}

/-- The minimal polynomial over a discrete valuation ring `A` of an `n`-th root of a uniformizer
`π` of `A`, in a torsion-free domain `A`-algebra, is `X ^ n - π`. -/
theorem minpoly_eq_of_pow_eq_of_irreducible {L : Type*} [CommRing L] [IsDomain L] [Algebra A L]
    [Module.IsTorsionFree A L] {α : L} (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) : minpoly A α = X ^ n - C π := by
  refine eq_of_monic_of_associated
    (minpoly.monic (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap)))
    (monic_X_pow_sub_C π hn) ?_
  refine associated_minpoly_of_eisenstein_isRoot α _
    (isEisensteinAt_X_pow_sub_C_of_irreducible hπ (Nat.pos_of_ne_zero hn)) ?_
  simp [hα]

variable {K L : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] {α : L}

include K in
/-- **The degree of a Kummer extension of a discrete valuation ring.** If `L` is generated over
the fraction field `K` of a discrete valuation ring `A` by an `n`-th root of a uniformizer of `A`,
then `[L : K] = n`. -/
@[stacks 09EV "(1)"]
theorem finrank_eq_of_pow_eq_of_irreducible (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) : Module.finrank K L = n := by
  have hroot : aeval α (X ^ n - C (algebraMap A K π)) = 0 := by
    simp [hα, ← IsScalarTower.algebraMap_apply]
  have hmin : X ^ n - C (algebraMap A K π) = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_irreducible hπ hn) hroot
      (monic_X_pow_sub_C _ hn)
  have hint : IsIntegral A α :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap)
  rw [← IntermediateField.finrank_top', ← hgen, IntermediateField.adjoin.finrank hint.tower_top,
    ← hmin, natDegree_X_pow_sub_C]

include K in
/-- If `S = A[α]` for an `n`-th root `α` of a uniformizer `π`, then `α` is a root in `S` of the
Eisenstein polynomial `X ^ n - π` generating `S`, so the results of
`TauCeti.RingTheory.DiscreteValuationRing.Eisenstein` apply to it. -/
private theorem isEisensteinAt_and_aeval_eq_zero_and_adjoin_eq_top (hπ : Irreducible π)
    (hn : n ≠ 0) (hα : α ^ n = algebraMap A L π) {S : Subalgebra A L}
    (hS : Algebra.adjoin A {α} = S) (h : α ∈ S) :
    FaithfulSMul A S ∧ (X ^ n - C π).IsEisensteinAt (maximalIdeal A) ∧ (X ^ n - C π).Monic ∧
      aeval (⟨α, h⟩ : S) (X ^ n - C π) = 0 ∧ Algebra.adjoin A {(⟨α, h⟩ : S)} = ⊤ := by
  have := FaithfulSMul.trans A K L
  refine ⟨inferInstance, isEisensteinAt_X_pow_sub_C_of_irreducible hπ (Nat.pos_of_ne_zero hn),
    monic_X_pow_sub_C π hn, Subtype.ext (by simp [hα]), ?_⟩
  -- `S = A[α]` is generated by `α`, viewed as an element of `S`.
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, Subalgebra.range_val]
  exact hS

include K in
/-- **The integral closure in a Kummer extension of a discrete valuation ring.** If `L` is
generated over the fraction field `K` of a discrete valuation ring `A` by an `n`-th root `α` of a
uniformizer `π` of `A`, then the integral closure of `A` in `L` is `A[α]`. Together with
`TauCeti.IsDiscreteValuationRing.minpoly_eq_of_pow_eq_of_irreducible` and
`minpoly.equivAdjoin`, it is `A[X] ⧸ (X ^ n - π)`. -/
@[stacks 09EV "(2)"]
theorem integralClosure_eq_adjoin_of_pow_eq_of_irreducible (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) :
    integralClosure A L = Algebra.adjoin A {α} := by
  have hint : IsIntegral A α :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap)
  set B := Algebra.adjoin A {α}
  have := FaithfulSMul.trans A K L
  obtain ⟨_, hf, hmo, hx, hadj⟩ := isEisensteinAt_and_aeval_eq_zero_and_adjoin_eq_top
    (K := K) hπ hn hα rfl (Algebra.self_mem_adjoin_singleton A α)
  -- `A[α]` is a discrete valuation ring, hence integrally closed.
  have := hf.isDiscreteValuationRing_of_adjoin_eq_top hmo hx hadj
  have : Algebra.IsIntegral A B :=
    have := Algebra.finite_adjoin_simple_of_isIntegral hint
    inferInstance
  -- Every element of `L = K[α]` is `p(α) / b` for some `p ∈ A[X]` and `b ∈ A`, after clearing
  -- the denominators of a polynomial over `K`.
  have : IsFractionRing B L := by
    refine .of_field B L fun z ↦ ?_
    have hz : z ∈ (K⟮α⟯).toSubalgebra := hgen ▸ Algebra.mem_top
    rw [adjoin_simple_toSubalgebra_of_isAlgebraic hint.tower_top.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
    have hb0 : algebraMap A L b ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A L)).mpr
        (nonZeroDivisors.ne_zero hb)
    refine ⟨⟨_, aeval_mem_adjoin_singleton A α
      (p := IsLocalization.integerNormalization (nonZeroDivisors A) p)⟩, algebraMap A B b, ?_⟩
    have hqα : aeval α (IsLocalization.integerNormalization (nonZeroDivisors A) p) =
        algebraMap A L b * aeval α p := by
      rw [← aeval_map_algebraMap K, hq, (aeval α).map_smul_of_tower, Algebra.smul_def]
    rw [eq_div_iff (by simpa using hb0)]
    simp [hqα, mul_comm]
  -- So `A[α]` is the integral closure of `A` in its fraction field `L`.
  refine le_antisymm (fun z hz ↦ ?_) (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hint))
  obtain ⟨y, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp hz
  exact y.2

include K in
/-- If `L` is generated over the fraction field of a discrete valuation ring `A` by an `n`-th root
`α` of a uniformizer of `A`, the results of `TauCeti.RingTheory.DiscreteValuationRing.Eisenstein`
apply to `α` in the integral closure of `A` in `L`. -/
private theorem isEisensteinAt_and_aeval_eq_zero_and_adjoin_eq_top_integralClosure
    (hπ : Irreducible π) (hn : n ≠ 0) (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤)
    (h : α ∈ integralClosure A L) :
    FaithfulSMul A (integralClosure A L) ∧ (X ^ n - C π).IsEisensteinAt (maximalIdeal A) ∧
      (X ^ n - C π).Monic ∧ aeval (⟨α, h⟩ : integralClosure A L) (X ^ n - C π) = 0 ∧
      Algebra.adjoin A {(⟨α, h⟩ : integralClosure A L)} = ⊤ :=
  isEisensteinAt_and_aeval_eq_zero_and_adjoin_eq_top (K := K) hπ hn hα
    (integralClosure_eq_adjoin_of_pow_eq_of_irreducible hπ hn hα hgen).symm h

include K in
/-- **The integral closure in a Kummer extension is a discrete valuation ring.** If `L` is
generated over the fraction field `K` of a discrete valuation ring `A` by an `n`-th root of a
uniformizer of `A`, then the integral closure of `A` in `L` is a discrete valuation ring. -/
@[stacks 09EV "(3)"]
theorem isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible (hπ : Irreducible π)
    (hn : n ≠ 0) (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) :
    IsDiscreteValuationRing (integralClosure A L) :=
  have h := (mem_integralClosure_iff _ _).mpr
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap))
  have ⟨_, hf, hmo, hx, hadj⟩ :=
    isEisensteinAt_and_aeval_eq_zero_and_adjoin_eq_top_integralClosure hπ hn hα hgen h
  hf.isDiscreteValuationRing_of_adjoin_eq_top hmo hx hadj

include K in
/-- **A root of a uniformizer is a uniformizer of the integral closure.** If `L` is generated over
the fraction field `K` of a discrete valuation ring `A` by an `n`-th root `α` of a uniformizer of
`A`, then `α` is a uniformizer of the integral closure of `A` in `L`. -/
@[stacks 09EV "(3)"]
theorem irreducible_mk_of_pow_eq_of_irreducible (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) (h : α ∈ integralClosure A L) :
    Irreducible (⟨α, h⟩ : integralClosure A L) :=
  have ⟨_, hf, hmo, hx, hadj⟩ :=
    isEisensteinAt_and_aeval_eq_zero_and_adjoin_eq_top_integralClosure hπ hn hα hgen h
  hf.irreducible_of_adjoin_eq_top hmo hx hadj

include K in
/-- **The ramification index of a Kummer extension of a discrete valuation ring.** If `L` is
generated over the fraction field `K` of a discrete valuation ring `A` by an `n`-th root of a
uniformizer of `A`, then the maximal ideal of the integral closure of `A` in `L` has ramification
index `n` over `A`. -/
@[stacks 09EV "(4)"]
theorem ramificationIdx_eq_of_pow_eq_of_irreducible (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) (P : Ideal (integralClosure A L))
    [P.IsMaximal] : P.ramificationIdx A = n := by
  have h := (mem_integralClosure_iff _ _).mpr
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap))
  obtain ⟨_, hf, hmo, hx, hadj⟩ :=
    isEisensteinAt_and_aeval_eq_zero_and_adjoin_eq_top_integralClosure hπ hn hα hgen h
  rw [hf.ramificationIdx_eq_natDegree hmo hx hadj P, natDegree_X_pow_sub_C]

include K in
/-- **A Kummer extension of a discrete valuation ring is totally ramified.** If `L` is generated
over the fraction field `K` of a discrete valuation ring `A` by an `n`-th root of a uniformizer of
`A`, then `L` is totally ramified with respect to `A`. -/
@[stacks 09EV "(5)"]
theorem isTotallyRamifiedWRT_of_pow_eq_of_irreducible (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) : Algebra.IsTotallyRamifiedWRT A L := by
  have h := (mem_integralClosure_iff _ _).mpr
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap))
  obtain ⟨_, hf, hmo, hx, hadj⟩ :=
    isEisensteinAt_and_aeval_eq_zero_and_adjoin_eq_top_integralClosure hπ hn hα hgen h
  exact Algebra.isTotallyRamifiedWRT_def.mpr ⟨⟨_, hf.isMaximal_span_singleton hmo hx hadj,
      fun P _ ↦ hf.eq_span_singleton_of_isMaximal hmo hx hadj P⟩,
    fun P _ ↦ hf.inertiaDeg_eq_one hmo hx hadj P⟩

end TauCeti.IsDiscreteValuationRing
