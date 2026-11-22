/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.ClassGroup.Equiv
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Stickelberger.GaussProduct
public import TauCeti.NumberTheory.Padics.TensorPrimaryComponent

import Mathlib.Algebra.GroupWithZero.Torsion
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Relation
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.RingTheory.ClassGroup.Basic
import TauCeti.RingTheory.ClassGroup.CoprimeRepresentative
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Semilocal

/-!
# Stickelberger's theorem on cyclotomic class groups

Let `m` be a positive integer and let `K` be an `m`-th cyclotomic extension of `ℚ`, with Galois
group `Gal(K/ℚ) ≃* (ZMod m)ˣ` acting covariantly on the ideal class group `ClassGroup (𝓞 K)`
through `ClassGroup.mulEquivHom`. This module proves **Stickelberger's theorem**: every element of
the integral Stickelberger ideal `I_m = ℤ[(ZMod m)ˣ] θ_m ∩ ℤ[(ZMod m)ˣ]`
(`TauCeti.stickelbergerIdeal`) annihilates `ClassGroup (𝓞 K)` (and its `p`-primary components).
It also re-exports `TauCeti.NumberTheory.NumberField.Cyclotomic.Stickelberger.GaussProduct`.

## Proof outline

At `m = 1` the integral Stickelberger ideal is `⊥`, so annihilation holds trivially. For `m ≥ 2`
the argument works directly at every maximal ideal `P` of `𝓞 K` whose norm is prime to `m`
(including primes above `2` when `m` is odd and the conductor `m = 2`), without appealing to
Chebotarev density or Hilbert class fields:

1. **Smoothed Gauss descent (`TauCeti.stickelbergerGaussProduct`).** Constructed and analyzed in
   `TauCeti.NumberTheory.NumberField.Cyclotomic.Stickelberger.GaussProduct`: for `x ∈ J_m`,
   Galois descent yields `u(x) ∈ Kˣ` with `u(x) ^ m = ∏_a (σ_a Φ(P)) ^ (x.coeff a)`.
2. **Prime principalization (`TauCeti.toPrincipalIdeal_stickelbergerGaussProduct`).**
   Expanding `(Φ(P))` via Stickelberger's relation (`Ideal.span_stickelbergerPhi_of_isMaximal`)
   and reindexing gives `(u(x)) ^ m = (∏_c (σ_c • P) ^ (y.coeff c)) ^ m` as invertible fractional
   ideals of `K`, where `y = stickelbergerMul m x`. Torsion-freeness of fractional ideals
   (`HasUniqueRoots`) cancels the `m`-th power, proving `∏_c (σ_c • P) ^ (y.coeff c) = (u(x))`.
3. **Full and `p`-primary class-group annihilation.** Passing to `ClassGroup (𝓞 K)` kills `[P]`,
   hence by prime factorization every ideal class represented by an ideal of norm prime to `m`.
   Since `(m)` lies in only finitely many maximal ideals, `ClassGroup.exists_mk_eq_and_sup_eq_top`
   represents every ideal class by an ideal coprime to `(m)`, closing
   `TauCeti.stickelbergerIdeal_annihilates`. Equivariance of the covariant `ℤ[(ZMod m)ˣ]`-action
   and compatibility with `TauCeti.classGroupPrimaryProj` then yield annihilation on every
   `p`-primary component, matching scalar extension along `primaryComponentEquivPadicIntTensor`.

## Main definitions

* `TauCeti.classGroupPrimaryProj`: the canonical projection `ClassGroup (𝓞 K) →*
  CommGroup.primaryComponent (ClassGroup (𝓞 K)) p` defined via
  `AddCommGroup.primaryComponentEquivPadicIntTensor`.
* `TauCeti.cyclotomicClassAction`: the scalar-extended covariant `(ZMod m)ˣ`-action on
  `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`.

## Main results

* `TauCeti.toPrincipalIdeal_stickelbergerGaussProduct` and
  `TauCeti.exists_toPrincipalIdeal_eq_prod_zpow_of_isMaximal`: principal-ideal factorization for
  `stickelbergerGaussProduct` and existential prime principalization.
* `TauCeti.stickelbergerIdeal_annihilates` and `TauCeti.stickelbergerSmoothing_annihilates`:
  annihilation of `ClassGroup (𝓞 K)` by `stickelbergerIdeal m` and `stickelbergerSmoothing m b`.
* `TauCeti.classGroup_mulEquiv_galEquivZMod_comm`, `TauCeti.classGroup_mulEquiv_prod_zpow`,
  `TauCeti.galEquivZMod_symm_prod_zpow`, and `TauCeti.prod_zpow_prod_zpow`: equivariance and
  associativity of the covariant `ℤ[(ZMod m)ˣ]`-action on `ClassGroup (𝓞 K)`.
* `TauCeti.classGroupPrimaryProj_map`, `TauCeti.classGroupPrimaryProj_galEquivZMod`,
  `TauCeti.one_tmul_classGroupPrimaryProj`, and
  `TauCeti.primaryComponentEquivPadicIntTensor_galEquivZMod_prod_zpow`: equivariance and
  `ℤ_p`-tensor comparison for the `p`-primary projection.
* `TauCeti.cyclotomicClassAction_one`, `TauCeti.cyclotomicClassAction_mul`, and
  `TauCeti.cyclotomicClassAction_tmul`: identity, composition, and pure-tensor evaluation of
  `cyclotomicClassAction`.
* `TauCeti.stickelbergerIdeal_annihilates_baseChange`,
  `TauCeti.stickelbergerIdeal_annihilates_primaryComponent`,
  `TauCeti.stickelbergerIdeal_annihilates_classGroupPrimaryProj`, and
  `TauCeti.stickelbergerIdeal_annihilates_addPrimaryComponent`: scalar-extended and `p`-primary
  annihilation theorems.
* `TauCeti.subsingleton_classGroup_of_one_mem_stickelbergerIdeal` and
  `TauCeti.classNumber_eq_one_of_one_mem_stickelbergerIdeal`: whenever `1 ∈ stickelbergerIdeal m`,
  the class group is trivial and `NumberField.classNumber K = 1`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §6.2, Theorem 6.10.
* S. A. Katre, *Gauss–Jacobi sums and Stickelberger's theorem*, §4, Theorem 1.
* R. Sharifi, *Iwasawa Theory* (lecture notes), §4.5, Theorem 4.5.6.
-/

public section

open NumberField IsCyclotomicExtension.Rat
open scoped nonZeroDivisors Pointwise TensorProduct

namespace TauCeti

/-! ### Prime principalization -/

/-- **Galois-twisted Stickelberger relation.** Applying `σ_a ∈ Gal(K/ℚ)` to `Φ(P)` shifts its
prime factorization to `∏_b (σ_{a b⁻¹} • P) ^ b₀`. -/
private theorem span_smul_stickelbergerPhi_of_isMaximal {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m) (a : (ZMod m)ˣ) :
    Ideal.span {((galEquivZMod m K).symm a) • Ideal.stickelbergerPhi P m} =
      ∏ b : (ZMod m)ˣ,
        (((galEquivZMod m K).symm (a * b⁻¹)) • P) ^ (b : ZMod m).val := by
  let φ : (ZMod m)ˣ → Gal(K/ℚ) := fun c ↦ (galEquivZMod m K).symm c
  have hrel : Ideal.span {Ideal.stickelbergerPhi P m} =
      ∏ b : (ZMod m)ˣ, (φ b⁻¹ • P) ^ (b : ZMod m).val := by
    rw [Ideal.span_stickelbergerPhi_of_isMaximal hm P hP]
    refine Fintype.prod_equiv (galEquivZMod m K) _ _ fun τK ↦ ?_
    have hinv : τK⁻¹ = φ (galEquivZMod m K τK)⁻¹ := by simp [φ, map_inv]
    rw [hinv, MulEquiv.coe_toEquiv]
  rw [← Set.smul_set_singleton, ← Ideal.smul_closure, hrel, Finset.smul_prod']
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  rw [smul_pow', smul_smul, ← map_mul]

/-- Exponent bookkeeping for Stickelberger principalization: reindexing the double product of
twisted prime powers by `c = a b⁻¹` and applying the integral coefficient identity
`m * y.coeff c = ∑ a, x.coeff a * (a c⁻¹)₀` collapses the product to
`(∏ c, Q c ^ y.coeff c) ^ m`. -/
private theorem prod_prod_pow_zpow_eq_pow {m : ℕ} [NeZero m] {G : Type*} [CommGroup G]
    (Q : (ZMod m)ˣ → G) {x y : MonoidAlgebra ℤ (ZMod m)ˣ}
    (hxy : integralGroupRingCast m y = integralGroupRingCast m x * stickelberger m) :
    ∏ a : (ZMod m)ˣ, (∏ b : (ZMod m)ˣ, Q (a * b⁻¹) ^ (b : ZMod m).val) ^ x.coeff a =
      (∏ c : (ZMod m)ˣ, Q c ^ y.coeff c) ^ m := by
  have hreindex (a : (ZMod m)ˣ) :
      ∏ b : (ZMod m)ˣ, Q (a * b⁻¹) ^ (b : ZMod m).val =
        ∏ c : (ZMod m)ˣ, Q c ^ ((a * c⁻¹ : (ZMod m)ˣ).val.val : ℤ) := by
    refine Fintype.prod_equiv ((Equiv.inv (ZMod m)ˣ).trans (Equiv.mulLeft a)) _ _ fun b ↦ ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft, mul_inv_rev, inv_inv,
      mul_comm b a⁻¹, mul_inv_cancel_left, zpow_natCast]
  simp_rw [hreindex]
  rw [Finset.prod_prod_zpow Finset.univ Finset.univ (fun c _ ↦ Group.isUnit (Q c)),
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  rw [← natCast_mul_coeff_of_integralGroupRingCast_eq hxy c, mul_comm (m : ℤ), zpow_mul,
    zpow_natCast]

/-- **Principal-ideal formula for `stickelbergerGaussProduct`.** For `m ≥ 2` and
`x ∈ stickelbergerDenominatorIdeal m`, the principal fractional ideal generated by
`stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x)` is
`∏_c (σ_c • P) ^ ((stickelbergerMul m x).coeff c)`. -/
theorem toPrincipalIdeal_stickelbergerGaussProduct (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    (x : stickelbergerDenominatorIdeal m) :
    toPrincipalIdeal (𝓞 K) K
        (stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x)) =
      ∏ c : (ZMod m)ˣ,
        FractionalIdeal.mk0 K
          ⟨((galEquivZMod m K).symm c) • P, mem_nonZeroDivisors_of_ne_zero (NeZero.ne _)⟩ ^
            (stickelbergerMul m x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff c := by
  let φ : (ZMod m)ˣ → Gal(K/ℚ) := fun a ↦ (galEquivZMod m K).symm a
  have hΦ_ne : Ideal.stickelbergerPhi P m ≠ 0 := Ideal.stickelbergerPhi_ne_zero hP hm
  have hΦ_K_ne (a : (ZMod m)ˣ) : algebraMap (𝓞 K) K (φ a • Ideal.stickelbergerPhi P m) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 K) K) (FaithfulSMul.algebraMap_injective _ _)).mpr fun h0 ↦
      hΦ_ne (by rw [← inv_smul_smul (φ a) (Ideal.stickelbergerPhi P m), h0, smul_zero])
  let uΦ : (ZMod m)ˣ → Kˣ := fun a ↦
    Units.mk0 (algebraMap (𝓞 K) K (φ a • Ideal.stickelbergerPhi P m)) (hΦ_K_ne a)
  let u := stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x)
  have hu_pow : u ^ m = ∏ a : (ZMod m)ˣ, uΦ a ^ (x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff a := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_stickelbergerGaussProduct m K hm P hP x, Units.coe_prod]
    exact Finset.prod_congr rfl fun a _ ↦ by rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  let Q : (ZMod m)ˣ → (FractionalIdeal (𝓞 K)⁰ K)ˣ := fun c ↦
    FractionalIdeal.mk0 K ⟨φ c • P, mem_nonZeroDivisors_of_ne_zero (NeZero.ne _)⟩
  have huΦ_ideal (a : (ZMod m)ˣ) :
      toPrincipalIdeal (𝓞 K) K (uΦ a) = ∏ b : (ZMod m)ˣ, Q (a * b⁻¹) ^ (b : ZMod m).val := by
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_mk0, ← FractionalIdeal.coeIdeal_span_singleton,
      span_smul_stickelbergerPhi_of_isMaximal hm P hP a, ← FractionalIdeal.coeIdealHom_apply,
      map_prod, Units.coe_prod]
    exact Finset.prod_congr rfl fun b _ ↦ by
      rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow,
        Units.val_pow_eq_pow_val, FractionalIdeal.coe_mk0]
  have hpow : toPrincipalIdeal (𝓞 K) K u ^ m =
      (∏ c : (ZMod m)ˣ, Q c ^ (stickelbergerMul m x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff c) ^ m := by
    rw [← map_pow, hu_pow, map_prod]
    simp_rw [map_zpow, huΦ_ideal]
    exact prod_prod_pow_zpow_eq_pow Q (integralGroupRingCast_stickelbergerMul x)
  refine Units.ext (HasUniqueRoots.pow_left_injective (NeZero.ne m) ?_)
  simpa only [← Units.val_pow_eq_pow_val] using congrArg Units.val hpow

/-- **Prime principalization.** Let `m` be a positive integer, let `K` be an `m`-th cyclotomic
extension of `ℚ`, and let `P` be a maximal ideal of `𝓞 K` whose norm is prime to `m`. For every
element `y ∈ stickelbergerIdeal m`, the Galois-weighted fractional ideal
`∏_c (σ_c • P) ^ (y.coeff c)` is principal. -/
theorem exists_toPrincipalIdeal_eq_prod_zpow_of_isMaximal (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    {y : MonoidAlgebra ℤ (ZMod m)ˣ} (hy : y ∈ stickelbergerIdeal m) :
    ∃ u : Kˣ, toPrincipalIdeal (𝓞 K) K u =
      ∏ c : (ZMod m)ˣ,
        FractionalIdeal.mk0 K
          ⟨((galEquivZMod m K).symm c) • P, mem_nonZeroDivisors_of_ne_zero (NeZero.ne _)⟩ ^
            y.coeff c := by
  by_cases hm : 2 ≤ m
  · obtain ⟨x, hx⟩ := stickelbergerMul_surjective m ⟨y, hy⟩
    refine ⟨stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x), ?_⟩
    rw [toPrincipalIdeal_stickelbergerGaussProduct m K hm P hP x, hx]
  · have hm1 : m = 1 := by have := NeZero.ne m; omega
    subst hm1
    rw [stickelbergerIdeal_one, Submodule.mem_bot] at hy
    subst hy
    exact ⟨1, by simp⟩

/-! ### Full annihilation of the cyclotomic class group -/

/-- **Stickelberger's theorem.** For every positive conductor `m` and every `m`-th cyclotomic
extension `K / ℚ`, the integral Stickelberger ideal `stickelbergerIdeal m` annihilates the full
ideal class group `ClassGroup (𝓞 K)` under the covariant Galois action. -/
theorem stickelbergerIdeal_annihilates (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x : MonoidAlgebra ℤ (ZMod m)ˣ) (hx : x ∈ stickelbergerIdeal m)
    (c : ClassGroup (𝓞 K)) :
    (∏ a : (ZMod m)ˣ,
      (ClassGroup.mulEquivHom
        (RingOfIntegers.mapRingEquiv
          (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm a).toRingEquiv)) c) ^
        x.coeff a) = 1 := by
  -- Package the group-ring action of `x` as a `MonoidHom` on `ClassGroup (𝓞 K)`.
  let act : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K) :=
    { toFun := fun d ↦
        ∏ a : (ZMod m)ˣ,
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv
              (((galEquivZMod m K).symm a).toRingEquiv)) d) ^ x.coeff a
      map_one' := by simp
      map_mul' := fun d₁ d₂ ↦ by simp only [map_mul, mul_zpow, Finset.prod_mul_distrib] }
  -- Step 1: `act` kills every maximal ideal `P` with `(absNorm P).Coprime m`.
  have hprime (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m) :
      act (ClassGroup.mk0 ⟨P, mem_nonZeroDivisors_of_ne_zero (NeZero.ne _)⟩) = 1 := by
    obtain ⟨u, hu⟩ := exists_toPrincipalIdeal_eq_prod_zpow_of_isMaximal m K P hP hx
    have hmk := congrArg (ClassGroup.mk K) hu
    rw [ClassGroup.mk_toPrincipalIdeal, map_prod] at hmk
    refine (Finset.prod_congr rfl fun a _ ↦ ?_).trans hmk.symm
    rw [map_zpow, ClassGroup.mk_mk0 K, ClassGroup.mulEquivHom_apply, ClassGroup.mulEquiv_mk0]
    exact congrArg (· ^ x.coeff a)
      (congrArg ClassGroup.mk0 (Subtype.ext (P.map_ringOfIntegers_mapRingEquiv _)))
  -- Step 2: By unique factorization, `act` kills every nonzero ideal `I` with
  -- `(absNorm I).Coprime m`.
  have hideal (I : Ideal (𝓞 K)) (hI : (Ideal.absNorm I).Coprime m) (hI0 : I ≠ ⊥) :
      act (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩) = 1 := by
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact absurd rfl hI0
    | h₂ I hIu =>
      obtain rfl : I = ⊤ := Ideal.isUnit_iff.mp hIu
      rw [show (⟨⊤, mem_nonZeroDivisors_of_ne_zero hI0⟩ : (Ideal (𝓞 K))⁰) = 1 from
        Subtype.ext Ideal.one_eq_top.symm, map_one, map_one]
    | h₃ A P hA0 hP ih =>
      have : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
      rw [map_mul, Nat.coprime_mul_iff_left] at hI
      have hmul : (⟨P * A, mem_nonZeroDivisors_of_ne_zero hI0⟩ : (Ideal (𝓞 K))⁰) =
          ⟨P, mem_nonZeroDivisors_of_ne_zero hP.ne_zero⟩ *
            ⟨A, mem_nonZeroDivisors_of_ne_zero hA0⟩ :=
        (Submonoid.mk_mul_mk (Ideal (𝓞 K))⁰ P A _ _).symm
      rw [hmul, map_mul, map_mul, hprime P hI.1, ih hI.2 hA0, one_mul]
  -- Step 3: Represent `c` by an integral ideal `I` coprime to `(m)` (hence of norm coprime to `m`).
  have h𝔞_ne : (Ideal.span {(m : 𝓞 K)}) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.mpr (NeZero.ne m)
  obtain ⟨I, hIu, hmk, hsup⟩ := ClassGroup.exists_mk_eq_and_sup_eq_top (K := K)
    (Ideal.finite_setOfPred_isMaximal_and_le_of_ne_bot h𝔞_ne) c
  have hI0 : I ≠ ⊥ := fun h0 ↦ by
    rw [h0, FractionalIdeal.coeIdeal_bot] at hIu; exact hIu.ne_zero rfl
  have hIcop : (Ideal.absNorm I).Coprime m :=
    Ideal.absNorm_coprime_of_isCoprime_span_natCast (Ideal.isCoprime_iff_sup_eq.mpr hsup)
  have hc : c = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩ := by
    rw [← hmk, ← ClassGroup.mk_mk0 K]
    exact congrArg (ClassGroup.mk K) (Units.ext (by simp [FractionalIdeal.coe_mk0]))
  exact hc ▸ hideal I hIcop hI0

/-- **Positive-smoothing annihilation.** For every positive conductor `m` and every natural `b`
coprime to `m`, the positive smoothed Stickelberger element `stickelbergerSmoothing m b`
annihilates `ClassGroup (𝓞 K)`. -/
theorem stickelbergerSmoothing_annihilates (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    {b : ℕ} (hb : b.Coprime m) (c : ClassGroup (𝓞 K)) :
    (∏ a : (ZMod m)ˣ,
      (ClassGroup.mulEquivHom
        (RingOfIntegers.mapRingEquiv
          (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm a).toRingEquiv)) c) ^
        (stickelbergerSmoothing m b).coeff a) = 1 :=
  stickelbergerIdeal_annihilates m K _ (stickelbergerSmoothing_mem_stickelbergerIdeal hb) c

/-! ### Equivariance of the integral action, `p`-primary projection, and `p`-primary annihilation -/

/-- Transporting ideal classes along a field isomorphism `e : K ≃+* K'` between `m`-th
cyclotomic extensions of `ℚ` commutes with the native covariant `(ZMod m)ˣ`-action. -/
theorem classGroup_mulEquiv_galEquivZMod_comm {m : ℕ} [NeZero m]
    {K K' : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    [Field K'] [NumberField K'] [IsCyclotomicExtension {m} ℚ K']
    (e : K ≃+* K') (a : (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e)
        (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) =
      ClassGroup.mulEquivHom
        (RingOfIntegers.mapRingEquiv (((galEquivZMod m K').symm a).toRingEquiv))
        (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e) c) := by
  let eAlg : K ≃ₐ[ℚ] K' := AlgEquiv.ofRingEquiv (f := e) fun q ↦ map_ratCast e q
  have hconj :
      (((galEquivZMod m K).symm a).toRingEquiv).trans e =
        e.trans (((galEquivZMod m K').symm a).toRingEquiv) := by
    ext x
    change e (((galEquivZMod m K).symm a) x) = ((galEquivZMod m K').symm a) (e x)
    exact eAlg.map_galEquivZMod_symm a x
  rw [ClassGroup.mulEquivHom_apply, ClassGroup.mulEquivHom_apply,
    ← ClassGroup.mulEquiv_trans_apply, ← ClassGroup.mulEquiv_trans_apply,
    ← RingOfIntegers.mapRingEquiv_trans, ← RingOfIntegers.mapRingEquiv_trans, hconj]

/-- Transporting ideal classes along a field isomorphism `e : K ≃+* K'` is equivariant for the
integral group-ring action of `ℤ[(ZMod m)ˣ]`. -/
theorem classGroup_mulEquiv_prod_zpow {m : ℕ} [NeZero m]
    {K K' : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    [Field K'] [NumberField K'] [IsCyclotomicExtension {m} ℚ K']
    (e : K ≃+* K') (x : MonoidAlgebra ℤ (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e)
        (∏ a : (ZMod m)ˣ,
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) ^
            x.coeff a) =
      ∏ a : (ZMod m)ˣ,
        (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K').symm a).toRingEquiv))
          (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e) c)) ^
          x.coeff a := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [map_zpow, classGroup_mulEquiv_galEquivZMod_comm]

/-- Applying `σ_b ∈ Gal(K/ℚ)` commutes with the integral `ℤ[(ZMod m)ˣ]`-action on
`ClassGroup (𝓞 K)` and shifts `x` by `[b]`. -/
theorem galEquivZMod_symm_prod_zpow {m : ℕ} [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (b : (ZMod m)ˣ) (x : MonoidAlgebra ℤ (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquivHom
        (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm b).toRingEquiv))
        (∏ a : (ZMod m)ˣ,
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) ^
            x.coeff a) =
      ∏ a : (ZMod m)ˣ,
        (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm b).toRingEquiv)) c)) ^
          x.coeff a := by
  rw [ClassGroup.mulEquivHom_apply, classGroup_mulEquiv_prod_zpow]

/-- Associativity of the covariant `ℤ[(ZMod m)ˣ]`-action on `ClassGroup (𝓞 K)`. -/
theorem prod_zpow_prod_zpow {m : ℕ} [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x y : MonoidAlgebra ℤ (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    (∏ a : (ZMod m)ˣ,
      (ClassGroup.mulEquivHom
        (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
        (∏ b : (ZMod m)ˣ,
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm b).toRingEquiv)) c) ^
            y.coeff b)) ^ x.coeff a) =
      ∏ d : (ZMod m)ˣ,
        (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm d).toRingEquiv)) c) ^
          (x * y).coeff d := by
  classical
  let g : (ZMod m)ˣ → ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 K) := fun a ↦
    ClassGroup.mulEquivHom
      (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
  have hg_mul (a b : (ZMod m)ˣ) (d : ClassGroup (𝓞 K)) : g a (g b d) = g (a * b) d := by
    simp only [g, ClassGroup.mulEquivHom_apply, ← ClassGroup.mulEquiv_trans_apply,
      ← RingOfIntegers.mapRingEquiv_trans, map_mul, AlgEquiv.toRingEquiv_mul]
  have hreindex (a : (ZMod m)ˣ) :
      g a (∏ b : (ZMod m)ˣ, (g b c) ^ y.coeff b) =
        ∏ d : (ZMod m)ˣ, (g d c) ^ y.coeff (a⁻¹ * d) := by
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft a) _ _ fun b ↦ ?_
    simp [map_zpow, hg_mul]
  have hcoeff (d : (ZMod m)ˣ) :
      (x * y).coeff d = ∑ a : (ZMod m)ˣ, x.coeff a * y.coeff (a⁻¹ * d) := by
    rw [MonoidAlgebra.coeff_mul, Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
    simp only [← eq_inv_mul_iff_mul_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  calc
    ∏ a : (ZMod m)ˣ, (g a (∏ b : (ZMod m)ˣ, (g b c) ^ y.coeff b)) ^ x.coeff a
        = ∏ a : (ZMod m)ˣ, (∏ d : (ZMod m)ˣ, (g d c) ^ y.coeff (a⁻¹ * d)) ^ x.coeff a :=
          Finset.prod_congr rfl fun a _ ↦ by rw [hreindex a]
    _ = ∏ d : (ZMod m)ˣ, (g d c) ^ ∑ a : (ZMod m)ˣ, x.coeff a * y.coeff (a⁻¹ * d) :=
          Finset.prod_prod_zpow Finset.univ Finset.univ (fun _ _ ↦ Group.isUnit _) _ _
    _ = ∏ d : (ZMod m)ˣ, (g d c) ^ (x * y).coeff d :=
          Finset.prod_congr rfl fun d _ ↦ by rw [hcoeff d]

/-- The native covariant `(ZMod m)ˣ`-action preserves every `p`-primary component of
`ClassGroup (𝓞 K)`. -/
theorem galEquivZMod_mem_primaryComponent {m : ℕ} [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (p : ℕ) (a : (ZMod m)ˣ) {c : ClassGroup (𝓞 K)}
    (hc : c ∈ CommGroup.primaryComponent (ClassGroup (𝓞 K)) p) :
    ClassGroup.mulEquivHom
        (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c ∈
      CommGroup.primaryComponent (ClassGroup (𝓞 K)) p := by
  obtain ⟨k, hk⟩ := hc
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

/-- **The canonical `p`-primary projection on `ClassGroup (𝓞 K)`.** For a prime `p` and a number
field `K`, this homomorphism projects `ClassGroup (𝓞 K)` onto its `p`-primary component via
`AddCommGroup.primaryComponentEquivPadicIntTensor`, sending `c` to the unique `p`-primary class
whose image in `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))` is `1 ⊗ c`. -/
noncomputable def classGroupPrimaryProj (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [NumberField K] :
    ClassGroup (𝓞 K) →* CommGroup.primaryComponent (ClassGroup (𝓞 K)) p :=
  let e : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p ≃+
      ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K)) :=
    AddCommGroup.primaryComponentEquivPadicIntTensor p (Additive (ClassGroup (𝓞 K)))
      AddMonoid.ExponentExists.of_finite
  { toFun := fun c ↦
      ⟨Additive.toMul (e.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c) : Additive (ClassGroup (𝓞 K))),
        (e.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c)).property⟩
    map_one' := Subtype.ext <| by
      change Additive.toMul (e.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] 0) : Additive (ClassGroup (𝓞 K))) = 1
      rw [TensorProduct.tmul_zero, map_zero, AddSubgroup.coe_zero, toMul_zero]
    map_mul' := fun c₁ c₂ ↦ Subtype.ext <| by
      change Additive.toMul (e.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] (Additive.ofMul c₁ + Additive.ofMul c₂)) :
          Additive (ClassGroup (𝓞 K))) = _
      rw [TensorProduct.tmul_add, map_add, AddSubgroup.coe_add, toMul_add]
      rfl }

/-- Comparing `classGroupPrimaryProj` with `AddCommGroup.primaryComponentEquivPadicIntTensor`: the
`p`-primary projection of `c` maps to `(1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c`. -/
theorem primaryComponentEquivPadicIntTensor_classGroupPrimaryProj (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    AddCommGroup.primaryComponentEquivPadicIntTensor p (Additive (ClassGroup (𝓞 K)))
        AddMonoid.ExponentExists.of_finite
        ⟨Additive.ofMul (classGroupPrimaryProj p K c : ClassGroup (𝓞 K)),
          (classGroupPrimaryProj p K c).property⟩ =
      (1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c := by
  let e := AddCommGroup.primaryComponentEquivPadicIntTensor p (Additive (ClassGroup (𝓞 K)))
    AddMonoid.ExponentExists.of_finite
  change e (e.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c)) = (1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c
  exact e.apply_symm_apply _

/-- Canonical `simp`-normal form for the image of `classGroupPrimaryProj` in
`ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`: together with
`AddCommGroup.primaryComponentEquivPadicIntTensor_apply`, this simplifies
`primaryComponentEquivPadicIntTensor ... (classGroupPrimaryProj p K c)` to
`(1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c`. -/
@[simp]
theorem one_tmul_classGroupPrimaryProj (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    (1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul (classGroupPrimaryProj p K c : ClassGroup (𝓞 K)) =
      (1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c := by
  simpa [AddCommGroup.primaryComponentEquivPadicIntTensor_apply] using
    primaryComponentEquivPadicIntTensor_classGroupPrimaryProj p K c

/-- `classGroupPrimaryProj` restricts to the identity on the `p`-primary component. -/
@[simp]
theorem classGroupPrimaryProj_coe (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    (c : CommGroup.primaryComponent (ClassGroup (𝓞 K)) p) :
    classGroupPrimaryProj p K (c : ClassGroup (𝓞 K)) = c := by
  let e := AddCommGroup.primaryComponentEquivPadicIntTensor p (Additive (ClassGroup (𝓞 K)))
    AddMonoid.ExponentExists.of_finite
  apply Subtype.ext
  have h := e.symm_apply_apply ⟨Additive.ofMul (c : ClassGroup (𝓞 K)), c.property⟩
  simpa [AddCommGroup.primaryComponentEquivPadicIntTensor_apply, classGroupPrimaryProj, e] using
    congrArg (fun z : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p ↦
      Additive.toMul (z : Additive (ClassGroup (𝓞 K)))) h

/-- Any group homomorphism between class groups commutes with `classGroupPrimaryProj`. -/
theorem classGroupPrimaryProj_map {p : ℕ} [Fact p.Prime]
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (f : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K')) (c : ClassGroup (𝓞 K)) :
    (classGroupPrimaryProj p K' (f c) : ClassGroup (𝓞 K')) =
      f (classGroupPrimaryProj p K c : ClassGroup (𝓞 K)) := by
  let c_p := classGroupPrimaryProj p K c
  have hfc_mem : f (c_p : ClassGroup (𝓞 K)) ∈ CommGroup.primaryComponent (ClassGroup (𝓞 K')) p := by
    obtain ⟨k, hk⟩ := c_p.property
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  let e' := AddCommGroup.primaryComponentEquivPadicIntTensor p (Additive (ClassGroup (𝓞 K')))
    AddMonoid.ExponentExists.of_finite
  have hten :
      e' ⟨Additive.ofMul (classGroupPrimaryProj p K' (f c) : ClassGroup (𝓞 K')),
          (classGroupPrimaryProj p K' (f c)).property⟩ =
        e' ⟨Additive.ofMul (f (c_p : ClassGroup (𝓞 K))), hfc_mem⟩ := by
    rw [primaryComponentEquivPadicIntTensor_classGroupPrimaryProj,
      AddCommGroup.primaryComponentEquivPadicIntTensor_apply]
    have hbase := congrArg (LinearMap.baseChange ℤ_[p] f.toAdditive.toIntLinearMap)
      (primaryComponentEquivPadicIntTensor_classGroupPrimaryProj p K c)
    rw [AddCommGroup.primaryComponentEquivPadicIntTensor_apply] at hbase
    simpa only [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
      MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul] using hbase.symm
  exact congrArg (fun z : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K'))) p ↦
      Additive.toMul (z : Additive (ClassGroup (𝓞 K')))) (e'.injective hten)

/-- The native covariant `(ZMod m)ˣ`-action commutes with `classGroupPrimaryProj`. -/
theorem classGroupPrimaryProj_galEquivZMod {m : ℕ} [NeZero m] (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (a : (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    (classGroupPrimaryProj p K
        (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) :
        ClassGroup (𝓞 K)) =
      ClassGroup.mulEquivHom
        (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
        (classGroupPrimaryProj p K c : ClassGroup (𝓞 K)) :=
  classGroupPrimaryProj_map
    (ClassGroup.mulEquivHom
      (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))).toMonoidHom c

/-- Transporting ideal classes along `e : K ≃+* K'` commutes with `classGroupPrimaryProj`. -/
theorem classGroupPrimaryProj_mapRingEquiv (p : ℕ) [Fact p.Prime]
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (e : K ≃+* K') (c : ClassGroup (𝓞 K)) :
    (classGroupPrimaryProj p K' (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e) c) :
        ClassGroup (𝓞 K')) =
      ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e)
        (classGroupPrimaryProj p K c : ClassGroup (𝓞 K)) :=
  classGroupPrimaryProj_map (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e)).toMonoidHom c

/-- `classGroupPrimaryProj` is equivariant with respect to the integral `ℤ[(ZMod m)ˣ]`-action. -/
theorem classGroupPrimaryProj_prod_zpow {m : ℕ} [NeZero m] (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x : MonoidAlgebra ℤ (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    classGroupPrimaryProj p K
        (∏ a : (ZMod m)ˣ,
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) ^
            x.coeff a) =
      ∏ a : (ZMod m)ˣ,
        (classGroupPrimaryProj p K
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
            (classGroupPrimaryProj p K c : ClassGroup (𝓞 K)))) ^ x.coeff a := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [map_zpow]
  congr 1
  apply Subtype.ext
  rw [classGroupPrimaryProj_galEquivZMod, ← classGroupPrimaryProj_galEquivZMod]
  exact congrArg Subtype.val (classGroupPrimaryProj_coe p K _).symm

/-- **Scalar-extended covariant `(ZMod m)ˣ`-action on `ClassGroup (𝓞 K)`.** Over any commutative
ring `R`, `cyclotomicClassAction R m K a` is the `R`-linear endomorphism of
`R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` obtained by base-changing the covariant Galois action of
`(galEquivZMod m K).symm a`. -/
noncomputable def cyclotomicClassAction (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (a : (ZMod m)ˣ) : Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.baseChange R
    (ClassGroup.mulEquiv
      (RingOfIntegers.mapRingEquiv
        (((galEquivZMod m K).symm a).toRingEquiv))).toAdditive.toAddMonoidHom.toIntLinearMap

/-- Pure-tensor evaluation of `cyclotomicClassAction`. -/
@[simp]
theorem cyclotomicClassAction_tmul (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (a : (ZMod m)ˣ) (r : R) (c : Additive (ClassGroup (𝓞 K))) :
    cyclotomicClassAction R m K a (r ⊗ₜ[ℤ] c) =
      r ⊗ₜ[ℤ] Additive.ofMul
        (ClassGroup.mulEquiv
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
          (Additive.toMul c)) := by
  simp [cyclotomicClassAction]

/-- `cyclotomicClassAction R m K 1` is the identity endomorphism. -/
@[simp]
theorem cyclotomicClassAction_one (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] :
    cyclotomicClassAction R m K 1 = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r c =>
    simp only [cyclotomicClassAction_tmul, map_one, AlgEquiv.toRingEquiv_one,
      RingOfIntegers.mapRingEquiv_refl, ClassGroup.mulEquiv_refl, MulEquiv.refl_apply,
      ofMul_toMul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Composition of `cyclotomicClassAction`: acting by `a * b` equals the composition of the
actions by `a` and `b`. -/
theorem cyclotomicClassAction_mul (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (a b : (ZMod m)ˣ) :
    cyclotomicClassAction R m K (a * b) =
      (cyclotomicClassAction R m K a).comp (cyclotomicClassAction R m K b) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r c =>
    simp only [cyclotomicClassAction_tmul, LinearMap.comp_apply, toMul_ofMul,
      map_mul, AlgEquiv.toRingEquiv_mul, RingOfIntegers.mapRingEquiv_trans,
      ClassGroup.mulEquiv_trans_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Comparison between the `p`-primary projection of the covariant `ℤ[(ZMod m)ˣ]`-action and the
scalar-extended action `cyclotomicClassAction` on `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))` under
`AddCommGroup.primaryComponentEquivPadicIntTensor`. -/
theorem primaryComponentEquivPadicIntTensor_galEquivZMod_prod_zpow {m : ℕ} [NeZero m]
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x : MonoidAlgebra ℤ (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    AddCommGroup.primaryComponentEquivPadicIntTensor p (Additive (ClassGroup (𝓞 K)))
        AddMonoid.ExponentExists.of_finite
        ⟨Additive.ofMul
            (classGroupPrimaryProj p K
              (∏ a : (ZMod m)ˣ,
                (ClassGroup.mulEquivHom
                  (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) ^
                  x.coeff a) : ClassGroup (𝓞 K)),
          (classGroupPrimaryProj p K _).property⟩ =
      (∑ a : (ZMod m)ˣ, (x.coeff a : ℤ_[p]) • cyclotomicClassAction ℤ_[p] m K a)
        ((1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c) := by
  simp only [AddCommGroup.primaryComponentEquivPadicIntTensor_apply, one_tmul_classGroupPrimaryProj,
    LinearMap.sum_apply, LinearMap.smul_apply, cyclotomicClassAction_tmul, toMul_ofMul,
    ClassGroup.mulEquivHom_apply]
  have hsum :
      Additive.ofMul
          (∏ a : (ZMod m)ˣ,
            (ClassGroup.mulEquiv
              (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) ^
              x.coeff a) =
        ∑ a : (ZMod m)ˣ, x.coeff a • Additive.ofMul
          (ClassGroup.mulEquiv
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) := by
    simp only [ofMul_prod, ofMul_zpow]
  rw [hsum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, ← zsmul_eq_mul, TensorProduct.smul_tmul]

/-- **Scalar-extended Stickelberger annihilation.** Over any commutative ring `R`, every element of
`stickelbergerIdeal m` annihilates `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` through
`cyclotomicClassAction`. -/
theorem stickelbergerIdeal_annihilates_baseChange (R : Type*) [CommRing R]
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x : MonoidAlgebra ℤ (ZMod m)ˣ) (hx : x ∈ stickelbergerIdeal m)
    (z : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    (∑ a : (ZMod m)ˣ, (x.coeff a : R) • cyclotomicClassAction R m K a) z = 0 := by
  let T : Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
    ∑ a : (ZMod m)ˣ, (x.coeff a : R) • cyclotomicClassAction R m K a
  refine TensorProduct.inductionOn (motive := fun w ↦ T w = 0) z (fun r c ↦ ?_)
    (fun u v hu hv ↦ by rw [map_add, hu, hv, add_zero])
  have hsum :
      ∑ a : (ZMod m)ˣ,
        x.coeff a • Additive.ofMul
          (ClassGroup.mulEquiv
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
            (Additive.toMul c)) = 0 := by
    have hann := stickelbergerIdeal_annihilates m K x hx (Additive.toMul c)
    simpa only [ofMul_prod, ofMul_zpow, ofMul_one, ClassGroup.mulEquivHom_apply] using
      congrArg Additive.ofMul hann
  simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, cyclotomicClassAction_tmul]
  simp_rw [TensorProduct.smul_tmul', smul_eq_mul, ← zsmul_eq_mul, TensorProduct.smul_tmul]
  rw [← TensorProduct.tmul_sum, hsum, TensorProduct.tmul_zero]

/-- **`p`-primary Stickelberger annihilation.** Every element of `stickelbergerIdeal m` annihilates
the `p`-primary component `CommGroup.primaryComponent (ClassGroup (𝓞 K)) p` under the
`p`-primary covariant Galois action. -/
theorem stickelbergerIdeal_annihilates_primaryComponent (p : ℕ) [Fact p.Prime]
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x : MonoidAlgebra ℤ (ZMod m)ˣ) (hx : x ∈ stickelbergerIdeal m)
    (c : CommGroup.primaryComponent (ClassGroup (𝓞 K)) p) :
    (∏ a : (ZMod m)ˣ,
      (classGroupPrimaryProj p K
        (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
          (c : ClassGroup (𝓞 K)))) ^ x.coeff a) = 1 := by
  rw [← map_one (classGroupPrimaryProj p K),
    ← stickelbergerIdeal_annihilates m K x hx (c : ClassGroup (𝓞 K)), map_prod]
  exact Finset.prod_congr rfl fun a _ ↦ (map_zpow _ _ _).symm

/-- **`p`-primary projection annihilation.** For any class `c : ClassGroup (𝓞 K)`, every element of
`stickelbergerIdeal m` annihilates its `p`-primary projection `classGroupPrimaryProj p K c`. -/
theorem stickelbergerIdeal_annihilates_classGroupPrimaryProj (p : ℕ) [Fact p.Prime]
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x : MonoidAlgebra ℤ (ZMod m)ˣ) (hx : x ∈ stickelbergerIdeal m)
    (c : ClassGroup (𝓞 K)) :
    (∏ a : (ZMod m)ˣ,
      (classGroupPrimaryProj p K
        (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c)) ^
        x.coeff a) = 1 := by
  have h := stickelbergerIdeal_annihilates_primaryComponent p m K x hx (classGroupPrimaryProj p K c)
  refine (Finset.prod_congr rfl fun a _ ↦ congrArg (· ^ x.coeff a) (Subtype.ext ?_)).trans h
  rw [classGroupPrimaryProj_galEquivZMod, classGroupPrimaryProj_galEquivZMod,
    classGroupPrimaryProj_coe]

/-- **Additive `p`-primary Stickelberger annihilation.** Under the scalar-extension equivalence
`AddCommGroup.primaryComponentEquivPadicIntTensor`, every element of `stickelbergerIdeal m`
annihilates `AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p`. -/
theorem stickelbergerIdeal_annihilates_addPrimaryComponent (p : ℕ) [Fact p.Prime]
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x : MonoidAlgebra ℤ (ZMod m)ˣ) (hx : x ∈ stickelbergerIdeal m)
    (z : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p) :
    (∑ a : (ZMod m)ˣ,
      x.coeff a •
        (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))).toAdditive
          (z : Additive (ClassGroup (𝓞 K)))) = 0 := by
  let e := AddCommGroup.primaryComponentEquivPadicIntTensor p (Additive (ClassGroup (𝓞 K)))
    AddMonoid.ExponentExists.of_finite
  have hann := stickelbergerIdeal_annihilates_baseChange ℤ_[p] m K x hx
    ((1 : ℤ_[p]) ⊗ₜ[ℤ] (z : Additive (ClassGroup (𝓞 K))))
  have hmem :
      (∑ a : (ZMod m)ˣ,
        x.coeff a •
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))).toAdditive
            (z : Additive (ClassGroup (𝓞 K)))) ∈
        AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p :=
    sum_mem fun a _ ↦ zsmul_mem
      (show (ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))).toAdditive
          (z : Additive (ClassGroup (𝓞 K))) ∈
          AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p from
        galEquivZMod_mem_primaryComponent K p a z.property) _
  refine congrArg Subtype.val (e.injective (?_ : e ⟨_, hmem⟩ = e 0))
  rw [AddCommGroup.primaryComponentEquivPadicIntTensor_apply, map_zero]
  dsimp only
  rw [TensorProduct.tmul_sum, ← hann]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, cyclotomicClassAction_tmul,
    MulEquiv.toAdditive_apply_apply, ClassGroup.mulEquivHom_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, ← zsmul_eq_mul, TensorProduct.smul_tmul]

/-! ### Trivial class group when `1 ∈ I_m` -/

/-- Whenever `1 ∈ stickelbergerIdeal m`, the ideal class group of every `m`-th cyclotomic extension
of `ℚ` is trivial. -/
theorem subsingleton_classGroup_of_one_mem_stickelbergerIdeal (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (h1 : (1 : MonoidAlgebra ℤ (ZMod m)ˣ) ∈ stickelbergerIdeal m) :
    Subsingleton (ClassGroup (𝓞 K)) := by
  have htriv (c : ClassGroup (𝓞 K)) : c = 1 := by
    have h := stickelbergerIdeal_annihilates m K 1 h1 c
    classical
    simpa only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      pow_ite, zpow_one, zpow_zero, Finset.prod_ite_eq, Finset.mem_univ, ↓reduceIte, map_one,
      AlgEquiv.toRingEquiv_one, RingOfIntegers.mapRingEquiv_refl, ClassGroup.mulEquivHom_apply,
      ClassGroup.mulEquiv_refl, MulEquiv.refl_apply] using h
  exact ⟨fun c₁ c₂ ↦ (htriv c₁).trans (htriv c₂).symm⟩

/-- Whenever `1 ∈ stickelbergerIdeal m`, every `m`-th cyclotomic extension of `ℚ` has class number
one. -/
theorem classNumber_eq_one_of_one_mem_stickelbergerIdeal (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (h1 : (1 : MonoidAlgebra ℤ (ZMod m)ˣ) ∈ stickelbergerIdeal m) :
    NumberField.classNumber K = 1 := by
  have := subsingleton_classGroup_of_one_mem_stickelbergerIdeal m K h1
  let _ : Unique (ClassGroup (𝓞 K)) := uniqueOfSubsingleton 1
  exact Fintype.card_unique

/- Sanity checks at conductors `m = 2` and `m = 3`: since `1 ∈ I_2` and `1 ∈ I_3`, Stickelberger's
theorem immediately implies `classNumber K = 1`. -/
example (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {2} ℚ K] :
    NumberField.classNumber K = 1 :=
  classNumber_eq_one_of_one_mem_stickelbergerIdeal 2 K one_mem_stickelbergerIdeal_two

example (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    NumberField.classNumber K = 1 :=
  classNumber_eq_one_of_one_mem_stickelbergerIdeal 3 K one_mem_stickelbergerIdeal_three

end TauCeti
