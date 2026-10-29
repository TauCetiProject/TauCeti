/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.RingTheory.DiscreteValuationRing.Eisenstein
import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.RingTheory.RootsOfUnity.LocalRing

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
6. if `n` is invertible in the residue field of `A`, then `L` is tamely ramified with respect to
   `A`, and every intermediate field of `L / K` is `K(α ^ (n / d)) = K[π ^ (1 / d)]` for a divisor
   `d` of `n`.

These are the parts of Stacks, Lemma 15.116.2. Parts (1)–(5) hold for every `n ≠ 0`, also when
the residue characteristic divides `n` and `L / K` is inseparable. The ring-theoretic input is that
`X ^ n - π` is Eisenstein, so that `A[α]` is a discrete valuation ring with uniformizer `α`
(`Polynomial.IsEisensteinAt.isDiscreteValuationRing_of_adjoin_eq_top`). Being integrally closed
and having fraction field `L`, it is then the integral closure of `A` in `L`.

For part (6), the integral closure `A[α]` is a local ring with a power basis over `A` whose
generator `α` lies in its maximal ideal, so its roots of unity of order invertible in the residue
field come from `A` (`PowerBasis.mem_range_algebraMap_of_pow_eq_one`). If `E` is an intermediate
field of degree `d` and `m = [L : E]`, the norm `γ` of `α` to `E` satisfies `γ ^ n = π ^ m`, so
`γ / α ^ m` is such a root of unity; hence `α ^ m ∈ E`, and `K(α ^ m) = E` as both have degree `d`.

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
* `TauCeti.IsDiscreteValuationRing.mem_range_algebraMap_of_pow_eq_one_of_pow_eq_of_irreducible`:
  the roots of unity in `L` of order invertible in the residue field of `A` lie in `K`.
* `TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_of_pow_eq_of_irreducible`: if `n` is
  invertible in the residue field of `A`, then `L` is tamely ramified with respect to `A`.
* `TauCeti.IsDiscreteValuationRing.finrank_dvd_and_eq_adjoin_pow_of_pow_eq_of_irreducible`: if
  `n` is invertible in the residue field of `A`, every intermediate field `E` of `L / K` has degree
  `d` dividing `n` and equals `K(α ^ (n / d))`.

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
/-- **Roots of unity in a Kummer extension of a discrete valuation ring.** If `L` is generated
over the fraction field `K` of a discrete valuation ring `A` by an `n`-th root of a uniformizer of
`A`, then every root of unity in `L` whose order is invertible in the residue field of `A` lies in
`K`. -/
theorem mem_range_algebraMap_of_pow_eq_one_of_pow_eq_of_irreducible (hπ : Irreducible π)
    (hn : n ≠ 0) (hα : α ^ n = algebraMap A L π) (hgen : K⟮α⟯ = ⊤) {m : ℕ}
    (hm : IsUnit ((m : ℕ) : A ⧸ maximalIdeal A)) {ζ : L} (hζ : ζ ^ m = 1) :
    ζ ∈ Set.range (algebraMap K L) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hint : IsIntegral A α :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap)
  have hζB : ζ ∈ integralClosure A L :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) (hζ ▸ isIntegral_one)
  have := isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible hπ hn hα hgen
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  -- The integral closure `A[α]` has a power basis whose generator `α` is a uniformizer.
  let pb : PowerBasis A (integralClosure A L) := (Algebra.adjoin.powerBasis' hint).map
    (Subalgebra.equivOfEq _ _
      (integralClosure_eq_adjoin_of_pow_eq_of_irreducible hπ hn hα hgen).symm)
  have hpb : pb.gen ∈ maximalIdeal (integralClosure A L) := by
    have h : pb.gen = ⟨α, hint⟩ := by simp [pb]
    rw [h, mem_maximalIdeal, mem_nonunits_iff]
    exact (irreducible_mk_of_pow_eq_of_irreducible hπ hn hα hgen hint).not_isUnit
  have hmA : IsUnit (m : A) := (isUnit_map_iff (residue A) _).mp (by rwa [map_natCast])
  have hmB : IsUnit (m : integralClosure A L) := by
    simpa using hmA.map (algebraMap A (integralClosure A L))
  obtain ⟨c, hc⟩ := pb.mem_range_algebraMap_of_pow_eq_one hpb hmB (ζ := ⟨ζ, hζB⟩)
    (Subtype.ext (by simpa using hζ))
  refine ⟨algebraMap A K c, ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A (integralClosure A L) L,
    hc, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply]

include K in
/-- **A tame Kummer extension of a discrete valuation ring.** If `L` is generated over the fraction
field `K` of a discrete valuation ring `A` by an `n`-th root of a uniformizer of `A`, and `n` is
invertible in the residue field of `A`, then `L` is tamely ramified with respect to `A`. The
extension `L / K` is then also separable, by `TauCeti.isSeparable_of_pow_eq_of_adjoin_eq_top`. -/
@[stacks 09EV "(6)"]
theorem isTamelyRamifiedWRT_of_pow_eq_of_irreducible (hπ : Irreducible π)
    (hn : IsUnit ((n : ℕ) : A ⧸ maximalIdeal A)) (hα : α ^ n = algebraMap A L π)
    (hgen : K⟮α⟯ = ⊤) : Algebra.IsTamelyRamifiedWRT A L := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have htot := isTotallyRamifiedWRT_of_pow_eq_of_irreducible hπ hn0 hα hgen
  rw [Algebra.isTamelyRamifiedWRT_def]
  intro P _ _
  refine ⟨?_, by rwa [ramificationIdx_eq_of_pow_eq_of_irreducible hπ hn0 hα hgen P]⟩
  -- The residue field extension has degree one, so it is trivial, hence separable.
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field P
  have : Module.Free (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) :=
    Module.Free.of_divisionRing _ _
  have hbot : (⊥ : Subalgebra (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P)) = ⊤ := by
    rw [Subalgebra.bot_eq_top_iff_finrank_eq_one,
      ← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) P]
    exact (Algebra.isTotallyRamifiedWRT_def.mp htot).2 P
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp (hbot ▸ Algebra.mem_top : x ∈ (⊥ : Subalgebra _ _))
  exact isSeparable_algebraMap a

include K in
/-- **Intermediate fields of a tame Kummer extension.** If `L = K(α)` is generated over the
fraction field `K` of a discrete valuation ring `A` by an `n`-th root `α` of a uniformizer `π` of
`A`, and `n` is invertible in the residue field of `A`, then every intermediate field `E` of
`L / K` is `K(α ^ (n / d))` for its degree `d = [E : K]`, which divides `n`. As
`(α ^ (n / d)) ^ d = π`, this says that `E = K[π ^ (1 / d)]`. -/
@[stacks 09EV "(6)"]
theorem finrank_dvd_and_eq_adjoin_pow_of_pow_eq_of_irreducible (hπ : Irreducible π)
    (hn : IsUnit ((n : ℕ) : A ⧸ maximalIdeal A)) (hα : α ^ n = algebraMap A L π)
    (hgen : K⟮α⟯ = ⊤) (E : IntermediateField K L) :
    Module.finrank K E ∣ n ∧ E = K⟮α ^ (n / Module.finrank K E)⟯ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hfin : Module.finrank K L = n := finrank_eq_of_pow_eq_of_irreducible hπ hn0 hα hgen
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hfin ▸ Nat.pos_of_ne_zero hn0)
  set d := Module.finrank K E
  set m := Module.finrank E L
  have hdm : d * m = n := by rw [Module.finrank_mul_finrank K E L, hfin]
  have hd : 0 < d := Module.finrank_pos
  refine ⟨Dvd.intro m hdm, ?_⟩
  rw [← hdm, Nat.mul_div_cancel_left _ hd]
  have hπL : algebraMap A L π = algebraMap E L (algebraMap K E (algebraMap A K π)) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have := FaithfulSMul.trans A K L
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0, eq_comm, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective A L)] at hα
    exact hπ.ne_zero hα
  -- The norm `γ` of `α` to `E` satisfies `γ ^ n = π ^ m = (α ^ m) ^ n`, so `γ / α ^ m` is an
  -- `n`-th root of unity in `L`, hence lies in `K`. So `α ^ m ∈ E`.
  set γ : E := Algebra.norm E α
  have hγ : (γ : L) ^ n = (α ^ m) ^ n := by
    have h : γ ^ n = algebraMap K E (algebraMap A K π) ^ m := by
      rw [← map_pow, hα, hπL, Algebra.norm_algebraMap]
    rw [← pow_mul, mul_comm m, pow_mul, hα, hπL, ← map_pow, ← h, map_pow,
      IntermediateField.algebraMap_apply]
  have hζ : ((γ : L) / α ^ m) ^ n = 1 := by
    rw [div_pow, hγ, div_self (pow_ne_zero _ (pow_ne_zero _ hα0))]
  obtain ⟨c, hc⟩ :=
    mem_range_algebraMap_of_pow_eq_one_of_pow_eq_of_irreducible hπ hn0 hα hgen hn hζ
  have hc0 : algebraMap K L c ≠ 0 := by
    rw [hc]
    rintro h
    rw [h, zero_pow hn0] at hζ
    exact zero_ne_one hζ
  have hαm : α ^ m ∈ E := by
    have h : α ^ m = γ / algebraMap K L c := by
      rw [eq_div_iff hc0, hc, mul_div_cancel₀ _ (pow_ne_zero _ hα0)]
    rw [h]
    exact E.div_mem γ.2 (E.algebraMap_mem c)
  -- `K(α ^ m) ≤ E`, and both have degree `d` over `K`.
  have hroot : aeval (α ^ m) (X ^ d - C (algebraMap A K π)) = 0 := by
    rw [map_sub, aeval_X_pow, aeval_C, ← pow_mul, mul_comm, hdm, hα,
      IsScalarTower.algebraMap_apply A K L, sub_self]
  have hint : IsIntegral K (α ^ m) := ⟨_, monic_X_pow_sub_C _ hd.ne', by rwa [← aeval_def]⟩
  have hmin : X ^ d - C (algebraMap A K π) = minpoly K (α ^ m) :=
    minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_irreducible hπ hd.ne') hroot
      (monic_X_pow_sub_C _ hd.ne')
  refine (IntermediateField.eq_of_le_of_finrank_eq
    (IntermediateField.adjoin_simple_le_iff.mpr hαm) ?_).symm
  rw [IntermediateField.adjoin.finrank hint, ← hmin, natDegree_X_pow_sub_C]

end TauCeti.IsDiscreteValuationRing
