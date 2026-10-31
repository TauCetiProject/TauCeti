/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.RingTheory.DiscreteValuationRing.Eisenstein
import TauCeti.RingTheory.LocalRing.Roots
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
5. `L` is totally ramified with respect to `A`;
6. if `n` is invertible in the residue field `κ_A`, then `L` is tamely ramified with respect to
   `A`, and every intermediate field of `L / K` is `K(α ^ (n / d))` for a divisor `d` of `n`.

These are parts (1)–(6) of Stacks, Lemma 15.116.2. Parts (1)–(5) hold for every `n ≠ 0`, also
when the residue characteristic divides `n` and `L / K` is inseparable. The ring-theoretic input
is that `X ^ n - π` is Eisenstein, so that `A[α]` is a discrete valuation ring with uniformizer
`α` (`Polynomial.IsEisensteinAt.isDiscreteValuationRing_of_adjoin_eq_top`). Being integrally
closed and having fraction field `L`, it is then the integral closure of `A` in `L`.

Kummer extensions are the building blocks of tame ramification (Stacks, Lemma 15.116.7): a finite
separable extension `L / K` is tamely ramified with respect to `A` iff it embeds into an extension
of some `K(π ^ (1 / e))`, with `e` invertible in the residue field of `A`, that is unramified with
respect to the integral closure `A[π ^ (1 / e)]`. This file proves that such an embedding forces
tame ramification.

## Main results

* `TauCeti.IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible`: `[L : K] = n`, and
  `TauCeti.IsDiscreteValuationRing.finrank_adjoin_of_pow_eq_of_irreducible`: `[K(α) : K] = n`.
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
* `TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible`: `L` is
  tamely ramified with respect to `A` iff `n` is invertible in `κ_A`.
* `TauCeti.IsDiscreteValuationRing.mem_range_algebraMap_of_pow_eq_one_of_pow_eq_of_irreducible`:
  the roots of unity in `L` of order invertible in `κ_A` lie in `K`.
* `TauCeti.IsDiscreteValuationRing.eq_adjoin_pow_finrank_of_pow_eq_of_irreducible`: if `n` is
  invertible in `κ_A`, every intermediate field `M` of `L / K` is `K(α ^ [L : M])`.
* `TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible`:
  a finite separable extension of `K` contained in an extension of `K(π ^ (1 / e))` unramified
  with respect to `A[π ^ (1 / e)]`, with `e` invertible in the residue field of `A`, is tamely
  ramified with respect to `A`.

## References

* [Stacks Project, Lemma 15.116.2](https://stacks.math.columbia.edu/tag/09EV).
* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
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
/-- If `α` is an `n`-th root of a uniformizer of a discrete valuation ring `A`, then the field
`K(α)` it generates over the fraction field `K` of `A` has degree `n` over `K`. -/
theorem finrank_adjoin_of_pow_eq_of_irreducible (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) : Module.finrank K K⟮α⟯ = n := by
  have hroot : aeval α (X ^ n - C (algebraMap A K π)) = 0 := by
    simp [hα, ← IsScalarTower.algebraMap_apply]
  have hmin : X ^ n - C (algebraMap A K π) = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_irreducible hπ hn) hroot
      (monic_X_pow_sub_C _ hn)
  have hint : IsIntegral A α :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap)
  rw [IntermediateField.adjoin.finrank hint.tower_top, ← hmin, natDegree_X_pow_sub_C]

include K in
/-- **The degree of a Kummer extension of a discrete valuation ring.** If `L` is generated over
the fraction field `K` of a discrete valuation ring `A` by an `n`-th root of a uniformizer of `A`,
then `[L : K] = n`. -/
@[stacks 09EV "(1)"]
theorem finrank_eq_of_pow_eq_of_irreducible (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) : Module.finrank K L = n := by
  rw [← IntermediateField.finrank_top', ← hgen, finrank_adjoin_of_pow_eq_of_irreducible hπ hn hα]

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
  have : IsFractionRing B L :=
    TauCeti.IntermediateField.isFractionRing_algebra_adjoin_of_adjoin_eq_top hgen
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

include K in
/-- In a Kummer extension `L = K(α)` of a discrete valuation ring `A`, the residue field extension
at every maximal ideal of the integral closure of `A` in `L` is trivial. -/
private theorem surjective_algebraMap_quotient_of_pow_eq_of_irreducible (hπ : Irreducible π)
    (hn : n ≠ 0) (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤)
    (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Function.Surjective (algebraMap (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P)) := by
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field P
  have h := (Algebra.isTotallyRamifiedWRT_def.mp
    (isTotallyRamifiedWRT_of_pow_eq_of_irreducible hπ hn hα hgen)).2 P
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) P] at h
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2

include K in
/-- **A Kummer extension of a discrete valuation ring has no new roots of unity of order prime to
the residue characteristic.** If `L` is generated over the fraction field `K` of a discrete
valuation ring `A` by an `n`-th root of a uniformizer of `A`, and `m` is invertible in the residue
field of `A`, then every `m`-th root of unity in `L` lies in `K`. -/
theorem mem_range_algebraMap_of_pow_eq_one_of_pow_eq_of_irreducible (hπ : Irreducible π)
    (hn : n ≠ 0) (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) {m : ℕ}
    (hm : IsUnit (m : A ⧸ maximalIdeal A)) {ξ : L} (hξ : ξ ^ m = 1) :
    ξ ∈ Set.range (algebraMap K L) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have := isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible hπ hn hα hgen
  have hint : IsIntegral A α :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap)
  have : FaithfulSMul A (integralClosure A L) :=
    have := FaithfulSMul.trans A K L
    inferInstance
  have : Module.Finite A (integralClosure A L) :=
    have := Algebra.finite_adjoin_simple_of_isIntegral hint
    .equiv (Subalgebra.equivOfEq _ _
      (integralClosure_eq_adjoin_of_pow_eq_of_irreducible hπ hn hα hgen)).symm.toLinearEquiv
  have : (maximalIdeal (integralClosure A L)).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  -- The residue field extension is trivial, so roots of units descend from `A[α]` to `A`.
  have hres : Function.Surjective
      (algebraMap (ResidueField A) (ResidueField (integralClosure A L))) :=
    surjective_algebraMap_quotient_of_pow_eq_of_irreducible hπ hn hα hgen _
  have hξB : ξ ∈ integralClosure A L :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) (hξ ▸ isIntegral_one)
  obtain ⟨a, ha⟩ := TauCeti.IsLocalRing.mem_range_algebraMap_of_pow_eq_of_isUnit hres
    ((isUnit_map_iff (IsLocalRing.residue A) _).mp (by rw [map_natCast]; exact hm)) isUnit_one
    (s := ⟨ξ, hξB⟩) (Subtype.ext (by simpa using hξ))
  refine ⟨algebraMap A K a, ?_⟩
  rw [← IsScalarTower.algebraMap_apply A K L]
  simpa using congrArg Subtype.val ha

include K in
/-- **When a Kummer extension of a discrete valuation ring is tamely ramified.** If `L` is
generated over the fraction field `K` of a discrete valuation ring `A` by an `n`-th root of a
uniformizer of `A`, then `L` is tamely ramified with respect to `A` iff `n` is invertible in the
residue field of `A`. -/
@[stacks 09EV "(6), tame ramification"]
theorem isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible (hπ : Irreducible π) (hn : n ≠ 0)
    (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) :
    Algebra.IsTamelyRamifiedWRT A L ↔ IsUnit (n : A ⧸ maximalIdeal A) := by
  have := isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible hπ hn hα hgen
  have he := ramificationIdx_eq_of_pow_eq_of_irreducible hπ hn hα hgen
  rw [Algebra.isTamelyRamifiedWRT_def]
  refine ⟨fun h ↦ ?_, fun hu P _ _ ↦ ⟨⟨fun x ↦ ?_⟩, by rwa [he P]⟩⟩
  · have : (maximalIdeal (integralClosure A L)).LiesOver (maximalIdeal A) :=
      ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
    simpa [he] using (h (maximalIdeal _)).2
  -- The residue field extension is trivial, hence separable.
  let := Ideal.Quotient.field (maximalIdeal A)
  obtain ⟨y, rfl⟩ := surjective_algebraMap_quotient_of_pow_eq_of_irreducible hπ hn hα hgen P x
  exact isSeparable_algebraMap y

include K in
/-- **The intermediate fields of a tamely ramified Kummer extension.** Let `L` be generated over
the fraction field `K` of a discrete valuation ring `A` by an `n`-th root `α` of a uniformizer of
`A`, with `n` invertible in the residue field of `A`. Then every intermediate field `M` of `L / K`
is generated by `α ^ [L : M]`, an `[M : K]`-th root of the uniformizer, where
`[L : M] · [M : K] = n`. -/
@[stacks 09EV "(6), intermediate fields"]
theorem eq_adjoin_pow_finrank_of_pow_eq_of_irreducible (hπ : Irreducible π)
    (hn : IsUnit (n : A ⧸ maximalIdeal A)) (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤)
    (M : IntermediateField K L) : M = K⟮α ^ Module.finrank M L⟯ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hfin := finrank_eq_of_pow_eq_of_irreducible hπ hn0 hα hgen
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hfin ▸ Nat.pos_of_ne_zero hn0)
  set m := Module.finrank M L
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0, IsScalarTower.algebraMap_apply A K L, eq_comm, map_eq_zero,
      IsFractionRing.to_map_eq_zero_iff] at hα
    exact hπ.ne_zero hα
  -- The norm `N_{L/M}(α)` and `α ^ m` have the same `n`-th power `π ^ m`, so they differ by an
  -- `n`-th root of unity, which lies in `K`. Hence `α ^ m ∈ M`.
  set β : M := Algebra.norm M α
  have hβ : algebraMap M L β ^ n = (α ^ m) ^ n :=
    calc algebraMap M L β ^ n = algebraMap M L (Algebra.norm M (α ^ n)) := by
          rw [map_pow, map_pow]
      _ = algebraMap M L (Algebra.norm M (algebraMap M L (algebraMap K M (algebraMap A K π)))) := by
          rw [hα, IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply K M L]
      _ = algebraMap M L (algebraMap K M (algebraMap A K π)) ^ m := by
          rw [Algebra.norm_algebraMap, map_pow]
      _ = (α ^ m) ^ n := by
          rw [← IsScalarTower.algebraMap_apply K M L, ← IsScalarTower.algebraMap_apply A K L, ← hα,
            ← pow_mul, ← pow_mul, mul_comm]
  have hξ : (algebraMap M L β / α ^ m) ^ n = 1 := by
    rw [div_pow, hβ, div_self (pow_ne_zero _ (pow_ne_zero _ hα0))]
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_pow_eq_one_of_pow_eq_of_irreducible hπ hn0 hα hgen
    hn hξ
  have hβ0 : algebraMap M L β ≠ 0 := by
    rintro h
    rw [h, zero_div, zero_pow hn0] at hξ
    exact zero_ne_one hξ
  have hmem : α ^ m ∈ M := by
    have : α ^ m = algebraMap M L (β / algebraMap K M c) := by
      rw [map_div₀, ← IsScalarTower.algebraMap_apply K M L, hc, div_div_cancel₀ hβ0]
    rw [this]
    exact (β / algebraMap K M c).2
  -- `α ^ m` is an `[M : K]`-th root of `π`, so by part (1) both fields have degree `[M : K]`.
  have hmd : m * Module.finrank K M = n := by
    rw [mul_comm, Module.finrank_mul_finrank K M L, hfin]
  have hd : Module.finrank K K⟮α ^ m⟯ = Module.finrank K M :=
    finrank_adjoin_of_pow_eq_of_irreducible hπ Module.finrank_pos.ne'
      (by rw [← pow_mul, hmd, hα])
  exact (IntermediateField.eq_of_le_of_finrank_eq
    (IntermediateField.adjoin_simple_le_iff.mpr hmem) hd).symm

include K in
/-- **Tame ramification from an unramified extension of a Kummer extension.** Let `L` be a finite
separable extension of the fraction field `K` of a discrete valuation ring `A`, and let `E` be an
extension of `L` containing an `n`-th root `β` of a uniformizer `π` of `A`, with `n` invertible in
the residue field of `A`. If `E` is unramified with respect to the integral closure
`A[β]` of `A` in `K(β)`, then `L` is tamely ramified with respect to `A`.

This is the implication (2) ⇒ (1) of Stacks, Lemma 15.116.7. The integral closure of `A` in
`K(β)` is a discrete valuation ring by
`TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible`,
so the local ring hypothesis, needed to state unramifiedness with respect to it, always holds. -/
@[stacks 0EXW "(2) ⇒ (1)"]
theorem isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {E : Type*} [Field E] [Algebra K E] [Algebra A E]
    [IsScalarTower A K E] [Algebra L E] [IsScalarTower K L E] {β : E}
    [IsLocalRing (integralClosure A K⟮β⟯)] (hπ : Irreducible π)
    (hn : IsUnit (n : A ⧸ maximalIdeal A)) (hβ : β ^ n = algebraMap A E π)
    (h : Algebra.IsUnramifiedWRT (integralClosure A K⟮β⟯) E) :
    Algebra.IsTamelyRamifiedWRT A L := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have : IsScalarTower A L E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L E,
      ← IsScalarTower.algebraMap_apply A K E]
  have : IsScalarTower A K⟮β⟯ E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K K⟮β⟯, ← IsScalarTower.algebraMap_apply K K⟮β⟯ E,
      ← IsScalarTower.algebraMap_apply A K E]
  -- Inside `K(β)`, the generator is an `n`-th root of `π` generating everything, so `09EV` applies.
  have hβ' : AdjoinSimple.gen K β ^ n = algebraMap A K⟮β⟯ π := (algebraMap K⟮β⟯ E).injective (by
    rw [map_pow, AdjoinSimple.algebraMap_gen, hβ, ← IsScalarTower.algebraMap_apply])
  have hgen : K⟮AdjoinSimple.gen K β⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top β
  have := isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible hπ hn0 hβ' hgen
  -- `K(β)` is a Kummer extension of degree `n`, invertible in the residue field: it is tame.
  have hK₁ : Algebra.IsTamelyRamifiedWRT A K⟮β⟯ :=
    (isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible hπ hn0 hβ' hgen).mpr hn
  exact (hK₁.trans h.isTamelyRamifiedWRT).tower_bot K

end TauCeti.IsDiscreteValuationRing
