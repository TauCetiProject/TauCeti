/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.AlgebraicIndependent.DiscreteValuationRing
import TauCeti.RingTheory.AlgebraicIndependent.TranscendenceBasis
import TauCeti.RingTheory.DiscreteValuationRing.FractionRing
import TauCeti.RingTheory.IsTensorProduct.Pushout
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Special-fibre Krull dimension over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, and let `A` be
a torsion-free `R`-algebra of finite type, for instance a flat `R`-algebra of finite type. Then the
special fibre `κ ⊗[R] A` has Krull dimension at most the Krull dimension of the generic fibre
`K ⊗[R] A`; no excellence or universal catenarity hypothesis on `R` is needed. Consequently every
fibre ring `p.Fiber A` of `A` over `Spec R` has Krull dimension at most `ringKrullDim (K ⊗[R] A)`.

Without torsion-freeness over `R` the bound fails: `A = R ⧸ maximalIdeal R` has special fibre of
dimension `0` and empty generic fibre `K ⊗[R] A = 0` of dimension `⊥`. Without finite type over
`R` it also fails: for a uniformizer `π`, the subring `A = R[X] + π R[X]_{(π)}` of `K(X)` is a
torsion-free `R`-algebra whose generic fibre `A[1/π] = K(X)` has dimension `0`, whereas
`(π R[X]_{(π)}) ^ 2 ⊆ π A ⊆ π R[X]_{(π)}` gives `(A ⧸ π A)_red ≃ κ[X]` of dimension `1`.

The proof reduces to a prime `q` of `A` lying over `maximalIdeal R`. Because a uniformizer `π` acts
as a non-zero-divisor on `A`, any minimal prime `p ≤ q` of `A` misses `π`, so `D = A ⧸ p` embeds
into a prime quotient `E` of `K ⊗[R] A`. Noether normalization of the finite-type `κ`-domain
`A ⧸ q` supplies `s = dim (A ⧸ q)` algebraically independent elements modulo `q`; clearing
denominators in `R` and dividing by the highest power of `π` dividing all coefficients shows that
any lifts to `D` remain algebraically independent over `K` in `E`, whence `s ≤ trdeg_K E = dim E`.

## Main results

* `TauCeti.IsDiscreteValuationRing.ringKrullDim_quotient_maximalIdeal_le`: for a pushout `B` of
  `A` along `R → K`, `ringKrullDim (A ⧸ (maximalIdeal R).map (algebraMap R A)) ≤ ringKrullDim B`.
* `TauCeti.IsDiscreteValuationRing.krullDimLE_quotient_maximalIdeal`: `Ring.KrullDimLE n B`
  transfers to `Ring.KrullDimLE n (A ⧸ (maximalIdeal R).map (algebraMap R A))`.
* `TauCeti.IsDiscreteValuationRing.ringKrullDim_residueField_tensorProduct_le`:
  `ringKrullDim (ResidueField R ⊗[R] A) ≤ ringKrullDim (K ⊗[R] A)`.
* `TauCeti.IsDiscreteValuationRing.ringKrullDim_fiber_le`: for every prime `p` of `R`,
  `ringKrullDim (p.Fiber A) ≤ ringKrullDim B`.

## References

* [Stacks Project, Lemma 10.125.9 (0B2J)](https://stacks.math.columbia.edu/tag/0B2J), upper
  bounding special-fibre dimensions over discrete valuation rings.
-/

public section

open scoped TensorProduct nonZeroDivisors

namespace TauCeti.IsDiscreteValuationRing

section Dimension

variable {R K A B : Type*} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra R A] [Module.IsTorsionFree R A] [Algebra.FiniteType R A]
  [CommRing B] [Algebra R B] [Algebra A B] [Algebra K B]
  [IsScalarTower R A B] [IsScalarTower R K B] [Algebra.IsPushout R A K B]

include K in
/-- Every prime quotient `A ⧸ q` lying over the maximal ideal of `R` has Krull dimension at most
that of the generic fibre `B`. -/
private lemma ringKrullDim_quotient_le_of_maximalIdeal_le (q : Ideal A) [q.IsPrime]
    (hq : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ q) :
    ringKrullDim (A ⧸ q) ≤ ringKrullDim B := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away (algebraMap R A π) B := hπ.isLocalizationAway_of_isPushout (K := K)
  have hπ_nzd : algebraMap R A π ∈ A⁰ := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    rw [← Algebra.smul_def] at ha
    exact (smul_eq_zero_iff_right hπ.ne_zero).mp ha
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q)
  have : p.IsPrime := hp.1.1
  have hdisj : Disjoint (Submonoid.powers (algebraMap R A π) : Set A) p :=
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp).symm.mono_left
      (Submonoid.powers_le.mpr hπ_nzd)
  have : (p.map (algebraMap A B)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ B p ‹_› hdisj
  have hp_comap : (p.map (algebraMap A B)).comap (algebraMap A B) = p :=
    IsLocalization.under_map_of_isPrime_disjoint _ B ‹_› hdisj
  have hπp : algebraMap R A π ∉ p :=
    Set.disjoint_left.mp hdisj (Submonoid.mem_powers _)
  let pB := p.map (algebraMap A B)
  let : Algebra (A ⧸ p) (B ⧸ pB) := (Ideal.quotientMap pB (algebraMap A B) hp_comap.ge).toAlgebra
  have : IsScalarTower R (A ⧸ p) (B ⧸ pB) := .of_algebraMap_eq fun r ↦ by
    simpa [RingHom.algebraMap_toAlgebra] using IsScalarTower.algebraMap_apply R A (B ⧸ pB) r
  let qD : Ideal (A ⧸ p) := q.map (Ideal.Quotient.mk p)
  have : qD.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have hqD : (IsLocalRing.maximalIdeal R).map (algebraMap R (A ⧸ p)) ≤ qD := by
    rw [IsScalarTower.algebraMap_eq R A (A ⧸ p), Ideal.Quotient.algebraMap_eq, ← Ideal.map_map]
    exact Ideal.map_mono hq
  let κ := IsLocalRing.ResidueField R
  let : Algebra κ ((A ⧸ p) ⧸ qD) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp hqD)
  have : IsScalarTower R κ ((A ⧸ p) ⧸ qD) := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType κ ((A ⧸ p) ⧸ qD) := .of_restrictScalars_finiteType R κ _
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg κ ((A ⧸ p) ⧸ qD)
  choose y hy using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (I := qD) (g (MvPolynomial.X i))
  have hindep : AlgebraicIndependent K (fun i ↦ algebraMap (A ⧸ p) (B ⧸ pB) (y i)) := by
    refine AlgebraicIndependent.of_quotient_residueField (R := R) (K := K) hπ
      (fun h0 ↦ hπp (Ideal.Quotient.eq_zero_iff_mem.mp h0))
      (Ideal.quotientMap_injective' hp_comap.le) qD y ?_
    rw [algebraicIndependent_iff_injective_aeval]
    convert hginj
    ext i
    simp [hy i]
  have : Algebra.FiniteType K B := .of_isPushout R A K B
  calc ringKrullDim (A ⧸ q)
      = ringKrullDim ((A ⧸ p) ⧸ qD) :=
        (ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)).symm
    _ = (s : WithBot ℕ∞) := by
        simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g.toRingHom hginj hgint
    _ ≤ (Algebra.trdeg K (B ⧸ pB)).toNat := mod_cast by simpa using hindep.natCard_le_toNat_trdeg
    _ = ringKrullDim (B ⧸ pB) := (ringKrullDim_eq_toNat_trdeg K _).symm
    _ ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

include K in
/-- **Special-fibre Krull dimension bound over a discrete valuation ring.** Let `R` be a discrete
valuation ring with fraction field `K`, let `A` be a torsion-free `R`-algebra of finite type, and
let `B` be a pushout of `A` along `R → K` (such as `K ⊗[R] A` or `A[1/π]`). Then the special-fibre
quotient `A ⧸ 𝔪_R A` has Krull dimension at most `ringKrullDim B`. -/
@[stacks 0B2J]
theorem ringKrullDim_quotient_maximalIdeal_le :
    ringKrullDim (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ≤ ringKrullDim B := by
  set J := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ (PrimeSpectrum.coheight_eq_ringKrullDim_quotient x).trans_le ?_
  let q := x.asIdeal.comap (Ideal.Quotient.mk J)
  have : q.IsPrime := x.isPrime.comap _
  have hJq : J ≤ q := by
    rw [← Ideal.mk_ker (I := J)]
    exact Ideal.comap_mono bot_le
  have hmap : q.map (Ideal.Quotient.mk J) = x.asIdeal :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective x.asIdeal
  let eqv : (A ⧸ J) ⧸ x.asIdeal ≃+* A ⧸ q :=
    (Ideal.quotEquivOfEq hmap.symm).trans (DoubleQuot.quotQuotEquivQuotOfLE hJq)
  rw [ringKrullDim_eq_of_ringEquiv eqv]
  exact ringKrullDim_quotient_le_of_maximalIdeal_le (K := K) q hJq

include K B in
/-- If the generic fibre `B` of a torsion-free finite-type `R`-algebra `A` over a discrete valuation
ring `R` has Krull dimension at most `n`, so does the special-fibre quotient `A ⧸ 𝔪_R A`. -/
theorem krullDimLE_quotient_maximalIdeal (n : ℕ) [Ring.KrullDimLE n B] :
    Ring.KrullDimLE n (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
  Ring.krullDimLE_iff.mpr
    ((ringKrullDim_quotient_maximalIdeal_le (K := K)).trans (Ring.krullDimLE_iff.mp ‹_›))

include K in
/-- Every fibre ring `p.Fiber A` of a torsion-free finite-type algebra `A` over a discrete
valuation ring `R` has Krull dimension at most that of the generic fibre `B`. -/
theorem ringKrullDim_fiber_le (p : Ideal R) [hp : p.IsPrime] :
    ringKrullDim (p.Fiber A) ≤ ringKrullDim B := by
  have : Algebra.IsPushout R K A B := Algebra.IsPushout.symm ‹_›
  rcases eq_or_ne p ⊥ with rfl | hp0
  · let eK : (⊥ : Ideal R).ResidueField ≃ₐ[R] K :=
      IsLocalization.algEquiv R⁰ (⊥ : Ideal R).ResidueField K
    let eB : (⊥ : Ideal R).Fiber A ≃ₐ[R] B :=
      (Algebra.TensorProduct.congr eK (.refl : A ≃ₐ[R] A)).trans
        ((Algebra.IsPushout.equiv R K A B).restrictScalars R)
    exact (ringKrullDim_eq_of_ringEquiv eB.toRingEquiv).le
  · have hpmax : p.IsMaximal := IsPrime.to_maximal_ideal hp0
    obtain rfl : p = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hpmax
    let em : (R ⧸ IsLocalRing.maximalIdeal R) ≃ₐ[R] (IsLocalRing.maximalIdeal R).ResidueField :=
      AlgEquiv.ofBijective (IsScalarTower.toAlgHom R _ _)
        (Ideal.bijective_algebraMap_quotient_residueField _)
    let eF : (IsLocalRing.maximalIdeal R).Fiber A ≃ₐ[R]
        A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A) :=
      (Algebra.TensorProduct.congr em.symm (.refl : A ≃ₐ[R] A)).trans
        ((Algebra.TensorProduct.comm R _ A).trans
          ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A
            (IsLocalRing.maximalIdeal R)).symm.restrictScalars R))
    rw [ringKrullDim_eq_of_ringEquiv eF.toRingEquiv]
    exact ringKrullDim_quotient_maximalIdeal_le (R := R) (K := K) (A := A) (B := B)

end Dimension

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- For a torsion-free finite-type algebra `A` over a discrete valuation ring `R` with fraction
field `K`, the special fibre `ResidueField R ⊗[R] A` has Krull dimension at most that of the
generic fibre `K ⊗[R] A`. -/
theorem ringKrullDim_residueField_tensorProduct_le {R : Type*} [CommRing R] [IsDomain R]
    [_root_.IsDiscreteValuationRing R] (K A : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra R A] [Module.IsTorsionFree R A] [Algebra.FiniteType R A] :
    ringKrullDim (IsLocalRing.ResidueField R ⊗[R] A) ≤ ringKrullDim (K ⊗[R] A) := by
  let e := (Algebra.TensorProduct.comm R (IsLocalRing.ResidueField R) A).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A
      (IsLocalRing.maximalIdeal R)).symm.restrictScalars R)
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  have : Algebra.IsPushout R A K (K ⊗[R] A) := Algebra.IsPushout.symm inferInstance
  exact ringKrullDim_quotient_maximalIdeal_le (R := R) (K := K) (A := A) (B := K ⊗[R] A)

end TauCeti.IsDiscreteValuationRing
