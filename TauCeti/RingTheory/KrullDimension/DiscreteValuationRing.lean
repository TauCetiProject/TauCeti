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

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.DiscreteValuationRing.FractionRing
import TauCeti.RingTheory.KrullDimension.FiniteType
import TauCeti.RingTheory.KrullDimension.Quotient

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

section AlgebraicIndependent

/-- A nonzero multivariate polynomial over a discrete valuation ring factors out a power of a
uniformizer so that at least one coefficient is not divisible by the uniformizer. -/
private lemma exists_C_pow_mul_and_not_dvd_coeff {R ι : Type*} [CommRing R] [IsDomain R]
    [_root_.IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
    {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ (n : ℕ) (g : MvPolynomial ι R) (m : ι →₀ ℕ),
      f = MvPolynomial.C (π ^ n) * g ∧ ¬ π ∣ g.coeff m := by
  classical
  obtain ⟨m₀, hm₀, hmin⟩ :=
    f.support.exists_min_image (fun m ↦ (_root_.IsDiscreteValuationRing.addVal R (f.coeff m)).toNat)
      (MvPolynomial.support_nonempty.mpr hf)
  set n := (_root_.IsDiscreteValuationRing.addVal R (f.coeff m₀)).toNat
  have hval_m₀ : _root_.IsDiscreteValuationRing.addVal R (f.coeff m₀) = n :=
    (ENat.natCast_toNat (_root_.IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
      (MvPolynomial.mem_support_iff.mp hm₀))).symm
  have hdvd (m : ι →₀ ℕ) : π ^ n ∣ f.coeff m := by
    by_cases hm : m ∈ f.support
    · rw [← _root_.IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow]
      have hne : _root_.IsDiscreteValuationRing.addVal R (f.coeff m) ≠ ⊤ :=
        _root_.IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
          (MvPolynomial.mem_support_iff.mp hm)
      rw [← ENat.natCast_toNat hne]
      exact mod_cast hmin m hm
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      exact dvd_zero _
  choose c hc using hdvd
  let g : MvPolynomial ι R := ∑ m ∈ f.support, MvPolynomial.monomial m (c m)
  have hg {m : ι →₀ ℕ} (hm : m ∈ f.support) : g.coeff m = c m := by
    simp [g, MvPolynomial.coeff_monomial, hm]
  refine ⟨n, g, m₀, MvPolynomial.ext _ _ fun m ↦ ?_, fun ⟨d, hd⟩ ↦ ?_⟩
  · rw [MvPolynomial.coeff_C_mul]
    by_cases hm : m ∈ f.support
    · rw [hg hm, ← hc]
    · simp [g, MvPolynomial.coeff_monomial, hm, MvPolynomial.notMem_support_iff.mp hm]
  · have hle : ((n + 1 : ℕ) : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal R (f.coeff m₀) := by
      rw [← hπ.addVal_pow, _root_.IsDiscreteValuationRing.addVal_le_iff_dvd]
      exact ⟨d, by rw [hc m₀, ← hg hm₀, hd, pow_succ, mul_assoc]⟩
    rw [hval_m₀] at hle
    exact Nat.not_succ_le_self n (ENat.natCast_le_natCast.mp hle)

/-- Clearing denominators in a nonzero polynomial over the fraction field of `R` produces a
nonzero polynomial over `R` with the same vanishing under an injective algebra map `D → E`. -/
private lemma exists_mvPolynomial_ne_zero_and_aeval_eq_zero {R K D E ι : Type*}
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [Algebra K E] [Algebra D E]
    [IsScalarTower R K E] [IsScalarTower R D E]
    (hinj : Function.Injective (algebraMap D E)) (y : ι → D) {f : MvPolynomial ι K} (hf : f ≠ 0)
    (heval : MvPolynomial.aeval (fun i ↦ algebraMap D E (y i)) f = 0) :
    ∃ f₁ : MvPolynomial ι R, f₁ ≠ 0 ∧ MvPolynomial.aeval y f₁ = 0 := by
  classical
  have : IsDomain R := (IsFractionRing.injective R K).isDomain _
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finset R⁰ (f.support.image f.coeff)
  have hmem (m : ι →₀ ℕ) : (d : R) • f.coeff m ∈ Set.range (algebraMap R K) := by
    by_cases hm : m ∈ f.support
    · exact hd _ (Finset.mem_image_of_mem f.coeff hm)
    · rw [MvPolynomial.notMem_support_iff.mp hm, smul_zero]
      exact ⟨0, map_zero _⟩
  choose c hc using hmem
  let f₁ : MvPolynomial ι R := ∑ m ∈ f.support, MvPolynomial.monomial m (c m)
  have hf₁_map : MvPolynomial.map (algebraMap R K) f₁ = algebraMap R K d • f := by
    ext m
    by_cases hm : m ∈ f.support
    · simp [f₁, MvPolynomial.coeff_monomial, hm, hc m, Algebra.smul_def]
    · simp [f₁, MvPolynomial.coeff_monomial, hm, MvPolynomial.notMem_support_iff.mp hm]
  refine ⟨f₁, fun h0 ↦ hf ?_, hinj ?_⟩
  · have hd0 : algebraMap R K d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have hsmul : algebraMap R K d • f = 0 := by rw [← hf₁_map, h0, map_zero]
    exact (smul_eq_zero.mp hsmul).resolve_left hd0
  · have hmap : (algebraMap D E) (MvPolynomial.aeval y f₁) =
        MvPolynomial.aeval (fun i ↦ algebraMap D E (y i))
          (MvPolynomial.map (algebraMap R K) f₁) := by
      induction f₁ using MvPolynomial.induction_on with
      | C r => simp [← IsScalarTower.algebraMap_apply]
      | add p q hp hq => simp [hp, hq]
      | mul_X p i hp => simp [hp]
    rw [map_zero, hmap, hf₁_map, map_smul, heval, smul_zero]

/-- Elements of a domain `D` over a discrete valuation ring `R` whose residues modulo an ideal `q`
above `maximalIdeal R` are algebraically independent over `ResidueField R` have images in `E`
algebraically independent over `K`, provided `π` maps to a nonzero element of `D` and `D → E` is
injective. -/
private lemma algebraicIndependent_of_injective_quotient {R K D E ι : Type*}
    [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing D] [IsDomain D] [Algebra R D]
    [CommRing E] [Algebra R E] [Algebra K E] [Algebra D E]
    [IsScalarTower R K E] [IsScalarTower R D E]
    {π : R} (hπ : Irreducible π) (hπD : algebraMap R D π ≠ 0)
    (hinj : Function.Injective (algebraMap D E)) (q : Ideal D)
    [Algebra (IsLocalRing.ResidueField R) (D ⧸ q)]
    [IsScalarTower R (IsLocalRing.ResidueField R) (D ⧸ q)] (y : ι → D)
    (hy : Function.Injective
      (MvPolynomial.aeval (R := IsLocalRing.ResidueField R) fun i ↦ Ideal.Quotient.mk q (y i))) :
    AlgebraicIndependent K (fun i ↦ algebraMap D E (y i)) := by
  rw [algebraicIndependent_iff]
  intro f heval
  by_contra hf
  obtain ⟨f₁, hf₁, heval₁⟩ :=
    exists_mvPolynomial_ne_zero_and_aeval_eq_zero (R := R) (K := K) hinj y hf heval
  obtain ⟨n, g, m₀, rfl, hndvd⟩ := exists_C_pow_mul_and_not_dvd_coeff hπ hf₁
  rw [map_mul, MvPolynomial.aeval_C, map_pow, mul_eq_zero] at heval₁
  have hg0 : MvPolynomial.aeval y g = 0 := heval₁.resolve_left (pow_ne_zero n hπD)
  let φ : D →+* D ⧸ q := Ideal.Quotient.mk q
  have hcomm : φ.comp (algebraMap R D) =
      (algebraMap (IsLocalRing.ResidueField R) (D ⧸ q)).comp (IsLocalRing.residue R) := by
    ext r
    exact IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) (D ⧸ q) r
  have hres : MvPolynomial.aeval (R := IsLocalRing.ResidueField R) (fun i ↦ φ (y i))
      (MvPolynomial.map (IsLocalRing.residue R) g) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hcomm, ← MvPolynomial.hom_eval₂,
      ← MvPolynomial.aeval_def, hg0, map_zero]
  have hg_map : MvPolynomial.map (IsLocalRing.residue R) g = 0 :=
    hy (hres.trans (map_zero _).symm)
  have hm₀_zero : IsLocalRing.residue R (g.coeff m₀) = 0 := by
    rw [← MvPolynomial.coeff_map, hg_map]
    rfl
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm₀_zero
  exact hndvd hm₀_zero

/-- An algebraically independent `s`-tuple in a finite-type domain `E` over a field `K` bounds `s`
by `(Algebra.trdeg K E).toNat`. -/
private lemma le_toNat_trdeg_of_algebraicIndependent {K E : Type*} [Field K] [CommRing E]
    [IsDomain E] [Algebra K E] [Algebra.FiniteType K E] {s : ℕ} {x : Fin s → E}
    (hx : AlgebraicIndependent K x) :
    s ≤ (Algebra.trdeg K E).toNat := by
  let ψ := MvPolynomial.aeval (R := K) x
  algebraize [ψ.toRingHom]
  have : FaithfulSMul (MvPolynomial (Fin s) K) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraicIndependent_iff_injective_aeval.mp hx)
  have h := lift_trdeg_add_eq K (MvPolynomial (Fin s) K) E
  have hle : (s : Cardinal) ≤ Cardinal.lift (Algebra.trdeg K E) := by
    rw [← h, MvPolynomial.trdeg_of_isDomain]
    simp
  rw [← Cardinal.toNat_lift, ← Cardinal.toNat_natCast s]
  exact Cardinal.toNat_le_toNat hle (by simpa using trdeg_lt_aleph0_of_finiteType (R := K) (S := E))

end AlgebraicIndependent

section Dimension

/-- A minimal prime `p ≤ q` of a torsion-free `R`-algebra `A` misses a uniformizer `π` of `R` and
extends to a prime of `A[1/π]` contracting back to `p`. -/
private lemma exists_minimalPrime_le_and_map_isPrime {R A B : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Module.IsTorsionFree R A] [CommRing B] [Algebra A B]
    {π : R} (hπ : Irreducible π) [IsLocalization.Away (algebraMap R A π) B]
    (q : Ideal A) [q.IsPrime] :
    ∃ p : Ideal A, p.IsPrime ∧ p ≤ q ∧ algebraMap R A π ∉ p ∧
      (p.map (algebraMap A B)).IsPrime ∧
      (p.map (algebraMap A B)).comap (algebraMap A B) = p := by
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q)
  have hp_prime : p.IsPrime := hp.1.1
  have hπ_nzd : algebraMap R A π ∈ A⁰ := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    rw [← Algebra.smul_def] at ha
    exact (smul_eq_zero_iff_right hπ.ne_zero).mp ha
  have hπp : algebraMap R A π ∉ p :=
    Set.disjoint_right.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) hπ_nzd
  have hdisj : Disjoint (Submonoid.powers (algebraMap R A π) : Set A) p :=
    (Ideal.disjoint_powers_iff_notMem _ hp_prime.isRadical).mpr hπp
  exact ⟨p, hp_prime, hpq, hπp,
    IsLocalization.isPrime_of_isPrime_disjoint _ B p hp_prime hdisj,
    IsLocalization.under_map_of_isPrime_disjoint _ B hp_prime hdisj⟩

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
  have : IsLocalization.Away π K := hπ.isLocalizationAway_fractionRing
  have : IsLocalization.Away (algebraMap R A π) B := by
    rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers,
      Algebra.isLocalization_iff_isPushout (S := Submonoid.powers π) (A := K)]
    infer_instance
  obtain ⟨p, _, hpq, hπp, _, hp_comap⟩ := exists_minimalPrime_le_and_map_isPrime (B := B) hπ q
  let pB := p.map (algebraMap A B)
  let : Algebra (A ⧸ p) (B ⧸ pB) := (Ideal.quotientMap pB (algebraMap A B) hp_comap.ge).toAlgebra
  have : IsScalarTower R (A ⧸ p) (B ⧸ pB) := .of_algebraMap_eq fun r ↦ by
    simpa [RingHom.algebraMap_toAlgebra] using IsScalarTower.algebraMap_apply R A (B ⧸ pB) r
  let qD : Ideal (A ⧸ p) := q.map (Ideal.Quotient.mk p)
  have : qD.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  have hqD : (IsLocalRing.maximalIdeal R).map (algebraMap R (A ⧸ p)) ≤ qD := by
    rw [show algebraMap R (A ⧸ p) = (Ideal.Quotient.mk p).comp (algebraMap R A) from rfl,
      ← Ideal.map_map]
    exact Ideal.map_mono hq
  let κ := IsLocalRing.ResidueField R
  let : Algebra κ ((A ⧸ p) ⧸ qD) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp hqD)
  have : IsScalarTower R κ ((A ⧸ p) ⧸ qD) := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType κ ((A ⧸ p) ⧸ qD) := .of_restrictScalars_finiteType R κ _
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg κ ((A ⧸ p) ⧸ qD)
  choose y hy using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (I := qD) (g (MvPolynomial.X i))
  have hindep : AlgebraicIndependent K (fun i ↦ algebraMap (A ⧸ p) (B ⧸ pB) (y i)) := by
    refine algebraicIndependent_of_injective_quotient (R := R) (K := K) hπ
      (fun h0 ↦ hπp (Ideal.Quotient.eq_zero_iff_mem.mp h0))
      (Ideal.quotientMap_injective' hp_comap.le) qD y ?_
    convert hginj
    ext i
    simp [hy i]
  have : Algebra.IsPushout R K A B := Algebra.IsPushout.symm ‹_›
  have : Algebra.FiniteType K B :=
    .of_surjective (Algebra.IsPushout.equiv R K A B).toAlgHom
      (Algebra.IsPushout.equiv R K A B).surjective
  calc ringKrullDim (A ⧸ q)
      = ringKrullDim ((A ⧸ p) ⧸ qD) :=
        (ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)).symm
    _ = (s : WithBot ℕ∞) := by
        simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g.toRingHom hginj hgint
    _ ≤ (Algebra.trdeg K (B ⧸ pB)).toNat := mod_cast le_toNat_trdeg_of_algebraicIndependent hindep
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
