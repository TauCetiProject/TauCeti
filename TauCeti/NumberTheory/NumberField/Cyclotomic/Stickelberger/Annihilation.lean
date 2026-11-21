/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.ClassGroup.Equiv
public import TauCeti.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Stickelberger.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Basic
public import TauCeti.NumberTheory.Padics.TensorPrimaryComponent
public import TauCeti.RingTheory.Ideal.Pointwise

import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.FieldTheory.Galois.Basic
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Relation
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.RingTheory.ClassGroup.Basic
import TauCeti.RingTheory.ClassGroup.CoprimeRepresentative
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Semilocal
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Stickelberger's theorem on cyclotomic class groups

Let `m` be a positive integer and let `K` be an `m`-th cyclotomic extension of `ℚ`, with Galois
group `Gal(K/ℚ) ≃* (ZMod m)ˣ` acting covariantly on the ideal class group `ClassGroup (𝓞 K)`
through `ClassGroup.mulEquivHom`. This module proves **Stickelberger's theorem**: every element of
the integral Stickelberger ideal `I_m = ℤ[(ZMod m)ˣ] θ_m ∩ ℤ[(ZMod m)ˣ]`
(`TauCeti.stickelbergerIdeal`) annihilates `ClassGroup (𝓞 K)` (and its `p`-primary components).

## Proof outline

At `m = 1` the integral Stickelberger ideal is `⊥`, so annihilation holds trivially. For `m ≥ 2`
the argument works directly at every maximal ideal `P` of `𝓞 K` whose norm is prime to `m`
(including primes above `2` when `m` is odd and the conductor `m = 2`), without appealing to
Chebotarev density or Hilbert class fields:

1. **Smoothed Gauss descent (`TauCeti.stickelbergerGaussProduct`).** Let `p` be the rational prime
   below `P`; then `p ∤ m`, so `p` is coprime to `discr K`. In any compositum `L = K(ζ_p)`, the
   joint Galois isomorphism `IsCyclotomicExtension.galEquivProd` splits
   `Gal(L/ℚ) ≃* Gal(K/ℚ) × (ZMod p)ˣ`, yielding commuting lifts `σ_a` (`a ∈ (ZMod m)ˣ`) and
   `τ_b` (`b ∈ (ZMod p)ˣ`, fixing `K` and sending `ζ_p ↦ ζ_p ^ b`). For the Gauss sum
   `g = g(χ_P, ψ) ∈ L` attached to `χ_P = (· / P)_m⁻¹` and `ψ(t) = ζ_p ^ Tr(t)`, one has
   `g ^ m = Φ(P)` and `τ_b(g) = (b / P)_m · g`. Given `x ∈ J_m`, the Galois-weighted product
   `G_x = ∏_a (σ_a g) ^ (x.coeff a)` satisfies `τ_b(G_x) = (b / P)_m ^ (∑_a x_a a₀) · G_x = G_x`
   by the denominator congruence `m ∣ ∑_a x_a a₀`
   (`TauCeti.mem_stickelbergerDenominatorIdeal_iff_dvd`). Galois descent produces a multiplicative
   homomorphism `stickelbergerGaussProduct m K hm P hP : Multiplicative J_m →* Kˣ` independent of
   the auxiliary root `ζ_p` and compositum `L`, compatible with field embeddings `K →+* K'`, and
   satisfying `u(x) ^ m = ∏_a (σ_a Φ(P)) ^ (x.coeff a)`.
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

* `TauCeti.stickelbergerGaussProduct`: the descended Gauss product homomorphism
  `Multiplicative (stickelbergerDenominatorIdeal m) →* Kˣ` attached to a maximal ideal `P` of norm
  coprime to `m`.
* `TauCeti.classGroupPrimaryProj`: the canonical projection `ClassGroup (𝓞 K) →*
  CommGroup.primaryComponent (ClassGroup (𝓞 K)) p` defined via
  `AddCommGroup.primaryComponentEquivPadicIntTensor`.

## Main results

* `TauCeti.algebraMap_stickelbergerGaussProduct` and
  `TauCeti.prod_galEquivProd_gaussSum_eq_of_isPrimitiveRoot`: identification of
  `stickelbergerGaussProduct` in any compositum `L = K(ζ_p)` and independence of the auxiliary
  primitive `p`-th root of unity.
* `TauCeti.map_stickelbergerGaussProduct`, `TauCeti.gal_smul_stickelbergerGaussProduct`, and
  `TauCeti.galEquivZMod_symm_stickelbergerGaussProduct`: compatibility of
  `stickelbergerGaussProduct` with field embeddings `K →+* K'` and Galois automorphisms.
* `TauCeti.pow_stickelbergerGaussProduct` and
  `TauCeti.toPrincipalIdeal_stickelbergerGaussProduct`: the `m`-th power formula and
  principal-ideal factorization for `stickelbergerGaussProduct`.
* `TauCeti.exists_pow_eq_prod_stickelbergerPhi_zpow` and
  `TauCeti.exists_toPrincipalIdeal_eq_prod_zpow_of_isMaximal`: existential forms of Gauss descent
  and prime principalization.
* `TauCeti.stickelbergerIdeal_annihilates` and `TauCeti.stickelbergerSmoothing_annihilates`:
  annihilation of `ClassGroup (𝓞 K)` by `stickelbergerIdeal m` and `stickelbergerSmoothing m b`.
* `TauCeti.classGroup_mulEquiv_galEquivZMod_comm`, `TauCeti.classGroup_mulEquiv_prod_zpow`,
  `TauCeti.galEquivZMod_symm_prod_zpow`, and `TauCeti.prod_zpow_prod_zpow`: equivariance and
  associativity of the covariant `ℤ[(ZMod m)ˣ]`-action on `ClassGroup (𝓞 K)`.
* `TauCeti.classGroupPrimaryProj_map`, `TauCeti.classGroupPrimaryProj_galEquivZMod`, and
  `TauCeti.primaryComponentEquivPadicIntTensor_galEquivZMod_prod_zpow`: equivariance and
  `ℤ_p`-tensor comparison for the `p`-primary projection.
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

/-! ### Galois lifts and Gauss descent -/

/-- If `P` is a maximal ideal of `𝓞 K` lying over `(p)` with `(Ideal.absNorm P).Coprime m`,
then `p` is coprime to `discr K`. -/
theorem coprime_natAbs_discr_of_liesOver {m : ℕ}
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    (p : ℕ) [hp : Fact p.Prime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ((NumberField.discr K).natAbs).Coprime p := by
  have hNP : p ^ Ideal.inertiaDeg P ℤ = Ideal.absNorm P := Ideal.pow_inertiaDeg p P
  have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp.out).1 <|
    hP.coprime_dvd_left (hNP ▸ dvd_pow_self p (Ideal.inertiaDeg_pos P ℤ).ne')
  exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun hdvd ↦
    hpm (prime_dvd_of_dvd_natAbs_discr K m hp.out hdvd)).symm

private theorem charP_quotient_of_liesOver {K : Type*} [Field K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] (p : ℕ) [hp : Fact p.Prime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : CharP (𝓞 K ⧸ P) p := by
  let _ := Ideal.Quotient.field P
  refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
  rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
  simpa using (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).1
    (Ideal.mem_span_singleton_self _)

private theorem galEquivProd_symm_sigma_algebraMap {m : ℕ} [NeZero m]
    {K L : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [NeZero p] [IsCyclotomicExtension {p} K L]
    (hcop : ((NumberField.discr K).natAbs).Coprime p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (a : (ZMod m)ˣ) (z : K) :
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
        ((galEquivZMod m K).symm a, 1) (algebraMap K L z) =
      algebraMap K L (((galEquivZMod m K).symm a) z) := by
  have hcomm := ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
    ((galEquivZMod m K).symm a, 1)).restrictNormal_commutes K z
  simpa [IsCyclotomicExtension.restrictNormal_galEquivProd_symm] using hcomm.symm

private theorem galEquivProd_symm_tau_algebraMap
    {K L : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [NeZero p] [IsCyclotomicExtension {p} K L]
    (hcop : ((NumberField.discr K).natAbs).Coprime p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (b : (ZMod p)ˣ) (z : K) :
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b) (algebraMap K L z) =
      algebraMap K L z := by
  have hcomm := ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
    (1, b)).restrictNormal_commutes K z
  simpa [IsCyclotomicExtension.restrictNormal_galEquivProd_symm] using hcomm.symm

private theorem galEquivProd_symm_tau_zeta
    {K L : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [NeZero p] [IsCyclotomicExtension {p} K L]
    (hcop : ((NumberField.discr K).natAbs).Coprime p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (b : (ZMod p)ˣ) :
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b) ζ =
      ζ ^ (b : ZMod p).val := by
  have hspec := hζ.autToPow_spec ℚ
    ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b))
  simpa [IsCyclotomicExtension.autToPow_galEquivProd_symm] using hspec.symm

private theorem galEquivProd_symm_tau_gaussSum {m : ℕ} [NeZero m]
    {K L : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} K L]
    [Fintype (𝓞 K ⧸ P)] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    (hcop : ((NumberField.discr K).natAbs).Coprime p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (b : (ZMod p)ˣ) :
    ∃ ω : 𝓞 K, ω ^ m = 1 ∧
      (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b)
          (gaussSum
            ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
              ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
            (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one)) =
        algebraMap K L (algebraMap (𝓞 K) K ω) *
          gaussSum
            ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
              ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
            (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let _ := Ideal.Quotient.field P
  let τ := (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b)
  let f : 𝓞 K →+* L := (algebraMap K L).comp (algebraMap (𝓞 K) K)
  let χ : MulChar (𝓞 K ⧸ P) L := (Ideal.powerResidueSymbol P m)⁻¹.ringHomComp f
  let u_b : (𝓞 K ⧸ P)ˣ := Units.map (algebraMap (ZMod p) (𝓞 K ⧸ P)).toMonoidHom b
  refine ⟨Ideal.powerResidueSymbol P m (u_b : 𝓞 K ⧸ P),
    Ideal.powerResidueSymbol_pow_eq_one u_b.ne_zero, ?_⟩
  have hact := map_gaussSum_traceAddChar hζ.pow_eq_one χ τ.toRingHom b
    (fun t ↦ galEquivProd_symm_tau_algebraMap hcop hζ b
      (algebraMap (𝓞 K) K ((Ideal.powerResidueSymbol P m)⁻¹ t)))
    (galEquivProd_symm_tau_zeta hcop hζ b)
  have hχinv : χ⁻¹ = (Ideal.powerResidueSymbol P m).ringHomComp f := by
    simp only [χ, ← MulChar.ringHomComp_inv, inv_inv]
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    hχinv, MulChar.ringHomComp_apply, u_b, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, f, RingHom.comp_apply] using hact

private theorem galEquivProd_symm_tau_prod_gaussSum {m : ℕ} [NeZero m]
    {K L : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} K L]
    [Fintype (𝓞 K ⧸ P)] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    (hcop : ((NumberField.discr K).natAbs).Coprime p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (b : (ZMod p)ˣ) {x : MonoidAlgebra ℤ (ZMod m)ˣ}
    (hx : x ∈ stickelbergerDenominatorIdeal m) :
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b)
        (∏ a : (ZMod m)ˣ,
          ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
            ((galEquivZMod m K).symm a, 1)
              (gaussSum
                ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
                  ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
                (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one))) ^ x.coeff a) =
      ∏ a : (ZMod m)ˣ,
        ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1)
            (gaussSum
              ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
                ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
              (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one))) ^ x.coeff a := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let σ : (ZMod m)ˣ → Gal(L/ℚ) := fun a ↦
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm ((galEquivZMod m K).symm a, 1)
  let τ := (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b)
  let f : 𝓞 K →+* L := (algebraMap K L).comp (algebraMap (𝓞 K) K)
  let g : L := gaussSum ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp f)
    (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one)
  have hστ (a : (ZMod m)ˣ) : τ * σ a = σ a * τ :=
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).injective
      (by simp only [σ, τ, map_mul, MulEquiv.apply_symm_apply, Prod.mk_mul_mk, one_mul, mul_one])
  obtain ⟨ω, hω, hτg⟩ := galEquivProd_symm_tau_gaussSum (m := m) P hcop hζ b
  have hσ_ω (a : (ZMod m)ˣ) :
      σ a (algebraMap K L (algebraMap (𝓞 K) K ω)) =
        (algebraMap K L (algebraMap (𝓞 K) K ω)) ^ (a : ZMod m).val := by
    have hωK : (algebraMap (𝓞 K) K ω) ^ m = 1 := by rw [← map_pow, hω, map_one]
    have hact := galEquivZMod_apply_of_pow_eq m K ((galEquivZMod m K).symm a) hωK
    rw [MulEquiv.apply_symm_apply] at hact
    simp only [σ, galEquivProd_symm_sigma_algebraMap, hact, map_pow]
  have hτ_term (a : (ZMod m)ˣ) :
      τ ((σ a g) ^ x.coeff a) =
        (f ω) ^ (x.coeff a * ((a : ZMod m).val : ℤ)) * (σ a g) ^ x.coeff a := by
    have h1 : τ (σ a g) = (f ω) ^ (a : ZMod m).val * σ a g := by
      rw [← AlgEquiv.mul_apply, hστ a, AlgEquiv.mul_apply, hτg, map_mul, hσ_ω a]
      rfl
    rw [map_zpow₀, h1, mul_zpow, ← zpow_natCast, ← zpow_mul, mul_comm ((a : ZMod m).val : ℤ)]
  obtain ⟨k, hk⟩ := mem_stickelbergerDenominatorIdeal_iff_dvd.mp hx
  have hfω_ne : f ω ≠ 0 := fun h0 ↦
    one_ne_zero (by rw [← map_one f, ← hω, map_pow, h0, zero_pow (NeZero.ne m)])
  have hfω_pow : (f ω) ^ (∑ a : (ZMod m)ˣ, x.coeff a * ((a : ZMod m).val : ℤ)) = 1 := by
    rw [hk, zpow_mul, zpow_natCast, ← map_pow, hω, map_one, one_zpow]
  change τ (∏ a : (ZMod m)ˣ, (σ a g) ^ x.coeff a) = ∏ a : (ZMod m)ˣ, (σ a g) ^ x.coeff a
  rw [map_prod, Finset.prod_congr rfl fun a _ ↦ hτ_term a]
  rw [Finset.prod_mul_distrib, Finset.prod_zpow_eq_zpow_sum_of_isUnit _ hfω_ne.isUnit _,
    hfω_pow, one_mul]

/-- **Independence of the auxiliary `p`-th root of unity.** In any compositum `L = K(ζ_p)`,
replacing `ζ` by another primitive `p`-th root of unity `ζ'` leaves the Galois-weighted Gauss
product `∏_a (σ_a g(χ_P, ψ_ζ)) ^ (x.coeff a)` unchanged whenever
`x ∈ stickelbergerDenominatorIdeal m`. -/
theorem prod_galEquivProd_gaussSum_eq_of_isPrimitiveRoot (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} K L]
    [Fintype (𝓞 K ⧸ P)] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    (hcop : ((NumberField.discr K).natAbs).Coprime p)
    {ζ ζ' : L} (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p)
    {x : MonoidAlgebra ℤ (ZMod m)ˣ} (hx : x ∈ stickelbergerDenominatorIdeal m) :
    ∏ a : (ZMod m)ˣ,
      ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
        ((galEquivZMod m K).symm a, 1)
          (gaussSum
            ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
              ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
            (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one))) ^ x.coeff a =
    ∏ a : (ZMod m)ˣ,
      ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ').symm
        ((galEquivZMod m K).symm a, 1)
          (gaussSum
            ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
              ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
            (traceAddChar p (𝓞 K ⧸ P) hζ'.pow_eq_one))) ^ x.coeff a := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨k, hk_lt, hζk⟩ := hζ.eq_pow_of_pow_eq_one hζ'.pow_eq_one
  have hk_ne : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hζk
    exact hζ'.ne_one hp.out.one_lt hζk.symm
  have hk_cop : k.Coprime p :=
    (hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk_ne.bot_lt hk_lt)).symm
  let b : (ZMod p)ˣ := ZMod.unitOfCoprime k hk_cop
  have hb_val : (b : ZMod p).val = k := by
    simp [b, ZMod.coe_unitOfCoprime, Nat.mod_eq_of_lt hk_lt]
  let τ := (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b)
  have hτζ : τ ζ = ζ' := by rw [galEquivProd_symm_tau_zeta hcop hζ b, hb_val, hζk]
  have hσ_eq (a : (ZMod m)ˣ) :
      (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm ((galEquivZMod m K).symm a, 1) =
        (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ').symm
          ((galEquivZMod m K).symm a, 1) := by
    apply (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ').injective
    rw [MulEquiv.apply_symm_apply, IsCyclotomicExtension.galEquivProd_apply,
      IsCyclotomicExtension.restrictNormal_galEquivProd_symm]
    refine Prod.ext rfl ?_
    rw [hζ'.autToPow_eq_one_iff, ← hζk, map_pow]
    have hfix : (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
        ((galEquivZMod m K).symm a, 1) ζ = ζ := by
      rw [← hζ.autToPow_eq_one_iff, IsCyclotomicExtension.autToPow_galEquivProd_symm]
    rw [hfix]
  have hτg :
      τ (gaussSum
          ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
            ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
          (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one)) =
        gaussSum
          ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
            ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
          (traceAddChar p (𝓞 K ⧸ P) hζ'.pow_eq_one) := by
    simp only [gaussSum, map_sum, map_mul]
    refine Finset.sum_congr rfl fun t _ ↦ congrArg₂ (· * ·) ?_ ?_
    · simpa [MulChar.ringHomComp_apply] using
        galEquivProd_symm_tau_algebraMap hcop hζ b
          (algebraMap (𝓞 K) K ((Ideal.powerResidueSymbol P m)⁻¹ t))
    · rw [traceAddChar_apply, traceAddChar_apply, map_pow, hτζ]
  refine (galEquivProd_symm_tau_prod_gaussSum P hcop hζ b hx).symm.trans ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  have hcomm :
      τ * (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1) =
        (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1) * τ :=
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).injective
      (by simp only [τ, map_mul, MulEquiv.apply_symm_apply, Prod.mk_mul_mk, one_mul, mul_one])
  rw [map_zpow₀, ← AlgEquiv.mul_apply, hcomm, AlgEquiv.mul_apply, hτg, hσ_eq a]

private theorem galEquivZMod_symm_conj {m : ℕ} [NeZero m]
    {K K' : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    [Field K'] [NumberField K'] [IsCyclotomicExtension {m} ℚ K']
    (e : K ≃ₐ[ℚ] K') (a : (ZMod m)ˣ) (z : K') :
    e (((galEquivZMod m K).symm a) (e.symm z)) = ((galEquivZMod m K').symm a) z := by
  let σ' : Gal(K'/ℚ) := AlgEquiv.autCongr e ((galEquivZMod m K).symm a)
  have hσ' : galEquivZMod m K' σ' = a := by
    let ζ' := IsCyclotomicExtension.zeta m ℚ K'
    have hζ' : IsPrimitiveRoot ζ' m := IsCyclotomicExtension.zeta_spec m ℚ K'
    have hact : σ' ζ' = ζ' ^ (a : ZMod m).val := by
      have hpow : (e.symm ζ') ^ m = 1 := by rw [← map_pow, hζ'.pow_eq_one, map_one]
      have h := galEquivZMod_apply_of_pow_eq m K ((galEquivZMod m K).symm a) hpow
      rw [MulEquiv.apply_symm_apply] at h
      calc
        σ' ζ' = e (((galEquivZMod m K).symm a) (e.symm ζ')) := rfl
        _ = e ((e.symm ζ') ^ (a : ZMod m).val) := congrArg e h
        _ = ζ' ^ (a : ZMod m).val := by rw [map_pow, e.apply_symm_apply]
    have hζ'act := galEquivZMod_apply_of_pow_eq m K' σ' hζ'.pow_eq_one
    rw [hact] at hζ'act
    exact Units.ext (ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hζ'act.symm))
  exact congrArg (· z) ((galEquivZMod m K').eq_symm_apply.mpr hσ')

private theorem exists_algEquiv_map_prod_galEquivProd_gaussSum {m : ℕ} [NeZero m]
    {K K' : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    [Field K'] [NumberField K'] [IsCyclotomicExtension {m} ℚ K'] [IsGalois ℚ K']
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    {L L' : Type*} [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [Field L'] [Algebra ℚ L'] [Algebra K' L'] [IsScalarTower ℚ K' L']
    {p : ℕ} [hp : Fact p.Prime]
    [IsCyclotomicExtension {p} K L] [IsCyclotomicExtension {p} K' L']
    [Fintype (𝓞 K ⧸ P)] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    (hcop : ((NumberField.discr K).natAbs).Coprime p)
    {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (e : K ≃ₐ[ℚ] K')
    {P' : Ideal (𝓞 K')} [P'.IsMaximal]
    (hPP' : P' = P.map (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv : 𝓞 K →+* 𝓞 K'))
    [Fintype (𝓞 K' ⧸ P')] [Algebra (ZMod p) (𝓞 K' ⧸ P')]
    (hcop' : ((NumberField.discr K').natAbs).Coprime p)
    {ζ' : L'} (hζ' : IsPrimitiveRoot ζ' p)
    {x : MonoidAlgebra ℤ (ZMod m)ˣ} (hx : x ∈ stickelbergerDenominatorIdeal m) :
    ∃ eL : L ≃ₐ[ℚ] L',
      (∀ k : K, eL (algebraMap K L k) = algebraMap K' L' (e k)) ∧
      eL (∏ a : (ZMod m)ˣ,
          ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
            ((galEquivZMod m K).symm a, 1)
              (gaussSum
                ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
                  ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
                (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one))) ^ x.coeff a) =
        ∏ a : (ZMod m)ˣ,
          ((IsCyclotomicExtension.galEquivProd ℚ K' L' p hcop' hζ').symm
            ((galEquivZMod m K').symm a, 1)
              (gaussSum
                ((Ideal.powerResidueSymbol P' m)⁻¹.ringHomComp
                  ((algebraMap K' L').comp (algebraMap (𝓞 K') K')))
                (traceAddChar p (𝓞 K' ⧸ P') hζ'.pow_eq_one))) ^ x.coeff a := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let _ : Algebra K L' := RingHom.toAlgebra ((algebraMap K' L').comp e.toRingHom)
  have hcyc : IsCyclotomicExtension {p} K L' := by
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨IsCyclotomicExtension.exists_isPrimitiveRoot K' L' (Set.mem_singleton p)
      (NeZero.ne p), fun y ↦ ?_⟩
    have hy : y ∈ Algebra.adjoin K' {b : L' | b ^ p = 1} :=
      ((IsCyclotomicExtension.iff_singleton p K' L').mp ‹IsCyclotomicExtension {p} K' L'›).2 y
    induction hy using Algebra.adjoin_induction with
    | mem z hz => exact Algebra.subset_adjoin hz
    | algebraMap c' =>
      have hce : algebraMap K' L' c' = algebraMap K L' (e.symm c') := by
        change algebraMap K' L' c' = algebraMap K' L' (e (e.symm c'))
        rw [e.apply_symm_apply]
      rw [hce]
      exact Subalgebra.algebraMap_mem _ _
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | mul _ _ _ _ ha hb => exact mul_mem ha hb
  let eL_K : L ≃ₐ[K] L' := IsCyclotomicExtension.algEquiv {p} K L L'
  have heL_K (k : K) : eL_K (algebraMap K L k) = algebraMap K' L' (e k) := eL_K.commutes k
  let eL : L ≃ₐ[ℚ] L' := AlgEquiv.ofRingEquiv (f := eL_K.toRingEquiv) fun q ↦ by
    change eL_K (algebraMap ℚ L q) = algebraMap ℚ L' q
    rw [IsScalarTower.algebraMap_apply ℚ K L, heL_K, e.commutes,
      ← IsScalarTower.algebraMap_apply ℚ K' L']
  refine ⟨eL, heL_K, ?_⟩
  let ζ₀ : L' := eL ζ
  have hζ₀ : IsPrimitiveRoot ζ₀ p := hζ.map_of_injective eL.injective
  have heL_symm_K' (k' : K') : eL.symm (algebraMap K' L' k') = algebraMap K L (e.symm k') := by
    apply eL.injective
    change eL_K (eL.symm (algebraMap K' L' k')) = eL_K (algebraMap K L (e.symm k'))
    rw [show eL_K (eL.symm _) = eL (eL.symm _) from rfl, eL.apply_symm_apply, heL_K,
      e.apply_symm_apply]
  have hσ_conj (a : (ZMod m)ˣ) (y : L) :
      eL ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1) y) =
        (IsCyclotomicExtension.galEquivProd ℚ K' L' p hcop' hζ₀).symm
          ((galEquivZMod m K').symm a, 1) (eL y) := by
    let σ' : Gal(L'/ℚ) := AlgEquiv.autCongr eL
      ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm ((galEquivZMod m K).symm a, 1))
    have hσ' : σ' = (IsCyclotomicExtension.galEquivProd ℚ K' L' p hcop' hζ₀).symm
        ((galEquivZMod m K').symm a, 1) := by
      apply (IsCyclotomicExtension.galEquivProd ℚ K' L' p hcop' hζ₀).injective
      rw [MulEquiv.apply_symm_apply, IsCyclotomicExtension.galEquivProd_apply]
      refine Prod.ext ?_ ?_
      · ext k'
        apply (algebraMap K' L').injective
        rw [AlgEquiv.restrictNormal_commutes]
        change eL ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1) (eL.symm (algebraMap K' L' k'))) =
          algebraMap K' L' (((galEquivZMod m K').symm a) k')
        rw [heL_symm_K', galEquivProd_symm_sigma_algebraMap,
          show eL (algebraMap K L _) = eL_K (algebraMap K L _) from rfl, heL_K,
          galEquivZMod_symm_conj]
      · rw [hζ₀.autToPow_eq_one_iff]
        change eL ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1) (eL.symm (eL ζ))) = eL ζ
        rw [eL.symm_apply_apply]
        have hfix : (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
            ((galEquivZMod m K).symm a, 1) ζ = ζ := by
          rw [← hζ.autToPow_eq_one_iff, IsCyclotomicExtension.autToPow_galEquivProd_symm]
        rw [hfix]
    simpa [σ'] using congrArg (· (eL y)) hσ'
  let eO : 𝓞 K ≃+* 𝓞 K' := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  let eQ : 𝓞 K ⧸ P ≃+* 𝓞 K' ⧸ P' := Ideal.quotientEquiv P P' eO hPP'
  let eQ_alg : (𝓞 K ⧸ P) ≃ₐ[ZMod p] (𝓞 K' ⧸ P') := AlgEquiv.ofRingEquiv (f := eQ) fun r ↦ by
    rw [← ZMod.natCast_zmod_val r, map_natCast, map_natCast, map_natCast]
  have heL_g :
      eL (gaussSum
          ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
            ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
          (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one)) =
        gaussSum
          ((Ideal.powerResidueSymbol P' m)⁻¹.ringHomComp
            ((algebraMap K' L').comp (algebraMap (𝓞 K') K')))
          (traceAddChar p (𝓞 K' ⧸ P') hζ₀.pow_eq_one) := by
    rw [gaussSum, gaussSum, map_sum]
    refine Fintype.sum_equiv eQ.toEquiv _ _ fun t ↦ ?_
    rw [map_mul]
    congr 1
    · obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective t
      have heO_L (z : 𝓞 K) :
          eL (algebraMap K L (algebraMap (𝓞 K) K z)) =
            algebraMap K' L' (algebraMap (𝓞 K') K' (eO z)) := by
        change eL_K (algebraMap K L (algebraMap (𝓞 K) K z)) = _
        rw [heL_K]
        rfl
      have hinv :
          eO ((Ideal.powerResidueSymbol P m)⁻¹ (Ideal.Quotient.mk P α)) =
            (Ideal.powerResidueSymbol P' m)⁻¹ (eQ (Ideal.Quotient.mk P α)) := by
        let _ := Ideal.Quotient.field P; let _ := Ideal.Quotient.field P'
        have : IsLocalHom eQ.toRingHom := eQ.surjective.isLocalHom
        obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (Ring.inverse (Ideal.Quotient.mk P α))
        have heQ_inv :
            Ring.inverse (eQ (Ideal.Quotient.mk P α)) = Ideal.Quotient.mk P' (eO β) := by
          have h1 : eQ (Ring.inverse (Ideal.Quotient.mk P α)) =
              Ring.inverse (eQ (Ideal.Quotient.mk P α)) :=
            map_ringInverse eQ.toRingHom _
          rw [← h1, ← hβ]
          exact Ideal.quotientEquiv_mk P P' eO hPP' β
        have hcongr : ∀ {Q : Ideal (𝓞 K')} [Q.IsMaximal], Ideal.map eO P = Q →
            (Ideal.map eO P).powerResidueSymbol m (Ideal.Quotient.mk (Ideal.map eO P) (eO β)) =
              Q.powerResidueSymbol m (Ideal.Quotient.mk Q (eO β)) := by
          intro Q _ hQ; subst hQ; rfl
        simp only [MulChar.inv_apply]
        rw [← hβ, Ideal.map_powerResidueSymbol (n := m) P eO β, hcongr hPP'.symm, heQ_inv]
      simp only [MulChar.ringHomComp_apply, RingHom.comp_apply]
      rw [heO_L, hinv]
      rfl
    · rw [traceAddChar_apply, traceAddChar_apply, map_pow,
        show eQ.toEquiv t = eQ_alg t from rfl, Algebra.trace_eq_of_algEquiv eQ_alg t]
  rw [map_prod]
  refine (Finset.prod_congr rfl fun a _ ↦ ?_).trans
    (prod_galEquivProd_gaussSum_eq_of_isPrimitiveRoot m K' P' hcop' hζ₀ hζ' hx)
  rw [map_zpow₀, hσ_conj, heL_g]

private theorem gaussSum_ne_zero (m : ℕ) [NeZero m]
    {K L : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] (hm : 2 ≤ m)
    (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [Fintype (𝓞 K ⧸ P)] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    gaussSum
      ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
      (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one) ≠ 0 := by
  let _ := Ideal.Quotient.field P
  let f : 𝓞 K →+* L := (algebraMap K L).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective _ _)
  have hg_pow := (Ideal.stickelbergerPhi_prime P hP hm hf
    (isPrimitive_traceAddChar (𝓞 K ⧸ P) hζ)).symm
  exact fun hg0 ↦ Ideal.stickelbergerPhi_ne_zero hP hm
    (hf (by rw [map_zero, ← hg_pow, hg0, zero_pow (NeZero.ne m)]))

private theorem exists_stickelbergerGaussProduct (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    (x : stickelbergerDenominatorIdeal m) :
    ∃ u : Kˣ,
      let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
      let L := CyclotomicField p K
      have : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
      have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
      let ζp : L := IsCyclotomicExtension.zeta p K L
      have hζp : IsPrimitiveRoot ζp p := IsCyclotomicExtension.zeta_spec p K L
      let _ := Ideal.Quotient.field P; let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
      have : CharP (𝓞 K ⧸ P) p := charP_quotient_of_liesOver P p
      let _ : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
      algebraMap K L (u : K) =
        ∏ a : (ZMod m)ˣ,
          ((IsCyclotomicExtension.galEquivProd ℚ K L p
              (coprime_natAbs_discr_of_liesOver K P hP p) hζp).symm
            ((galEquivZMod m K).symm a, 1)
              (gaussSum
                ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
                  ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
                (traceAddChar p (𝓞 K ⧸ P) hζp.pow_eq_one))) ^
            (x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff a := by
  classical
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  have : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcop : ((NumberField.discr K).natAbs).Coprime p :=
    coprime_natAbs_discr_of_liesOver K P hP p
  let L := CyclotomicField p K
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : IsGalois K L := IsCyclotomicExtension.isGalois {p} K L
  have : FiniteDimensional K L := IsCyclotomicExtension.finiteDimensional {p} K L
  have hζp := IsCyclotomicExtension.zeta_spec p K L
  let _ := Ideal.Quotient.field P; let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have : CharP (𝓞 K ⧸ P) p := charP_quotient_of_liesOver P p
  let _ : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
  let σ : (ZMod m)ˣ → Gal(L/ℚ) := fun a ↦
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζp).symm ((galEquivZMod m K).symm a, 1)
  let gx : L := ∏ a : (ZMod m)ˣ,
    (σ a (gaussSum ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
        ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
      (traceAddChar p (𝓞 K ⧸ P) hζp.pow_eq_one))) ^
      (x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff a
  have hgx_ne : gx ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ ↦ zpow_ne_zero _ <|
    (map_ne_zero_iff (σ a) (σ a).injective).mpr (gaussSum_ne_zero m hm P hP hζp)
  have hfixed (ρ : Gal(L/K)) : ρ gx = gx := by
    rw [← AlgEquiv.restrictScalars_apply ℚ ρ gx,
      IsCyclotomicExtension.restrictScalars_eq_galEquivProd_symm_one ℚ K L p hcop hζp ρ]
    exact galEquivProd_symm_tau_prod_gaussSum P hcop hζp _ x.property
  obtain ⟨α, hαL⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed gx).mpr hfixed)
  exact ⟨Units.mk0 α fun h0 ↦ hgx_ne (by rw [← hαL, h0, map_zero]), hαL⟩

/-- **The descended Gauss product homomorphism.** Given `m ≥ 2`, an `m`-th cyclotomic extension
`K / ℚ`, and a maximal ideal `P` of `𝓞 K` with `(Ideal.absNorm P).Coprime m`, this is the
canonical homomorphism `Multiplicative (stickelbergerDenominatorIdeal m) →* Kˣ` sending `x ∈ J_m`
to the Galois-descended element `∏_a (σ_a g(χ_P, ψ)) ^ (x.coeff a) ∈ Kˣ`. -/
noncomputable def stickelbergerGaussProduct (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m) :
    Multiplicative (stickelbergerDenominatorIdeal m) →* Kˣ := by
  classical
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  have : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let L := CyclotomicField p K
  exact
    { toFun := fun x ↦
        Classical.choose (exists_stickelbergerGaussProduct m K hm P hP (Multiplicative.toAdd x))
      map_one' := Units.ext <| (algebraMap K L).injective <| by
        have h1 := Classical.choose_spec
          (exists_stickelbergerGaussProduct m K hm P hP (Multiplicative.toAdd (1 :
            Multiplicative (stickelbergerDenominatorIdeal m))))
        dsimp only at h1; rw [Units.val_one, (algebraMap K L).map_one, h1]; simp
      map_mul' := fun x₁ x₂ ↦ Units.ext <| (algebraMap K L).injective <| by
        have h12 := Classical.choose_spec
          (exists_stickelbergerGaussProduct m K hm P hP (Multiplicative.toAdd (x₁ * x₂)))
        have h1 := Classical.choose_spec
          (exists_stickelbergerGaussProduct m K hm P hP (Multiplicative.toAdd x₁))
        have h2 := Classical.choose_spec
          (exists_stickelbergerGaussProduct m K hm P hP (Multiplicative.toAdd x₂))
        dsimp only at h12 h1 h2
        rw [Units.val_mul, (algebraMap K L).map_mul, h12, h1, h2]
        simp only [toAdd_mul, Submodule.coe_add, MonoidAlgebra.coeff_add, Finsupp.add_apply,
          ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun a _ ↦ ?_
        let _ := Ideal.Quotient.field P; let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
        have : CharP (𝓞 K ⧸ P) p := charP_quotient_of_liesOver P p
        let _ : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
        exact zpow_add₀ ((map_ne_zero_iff _ (AlgEquiv.injective _)).mpr
          (gaussSum_ne_zero m hm P hP (IsCyclotomicExtension.zeta_spec p K L))) _ _ }

/-- **Image of `stickelbergerGaussProduct` in any compositum.** For any compositum `L = K(ζ_p)`
over `K`, any prime `p` below `P`, and any primitive `p`-th root of unity `ζ : L`,
`stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x)` embeds into `L` as
`∏_a (σ_a g(χ_P, ψ_ζ)) ^ (x.coeff a)`. -/
theorem algebraMap_stickelbergerGaussProduct (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [hp : Fact p.Prime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    [IsCyclotomicExtension {p} K L]
    [Fintype (𝓞 K ⧸ P)] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    (hcop : ((NumberField.discr K).natAbs).Coprime p)
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) (x : stickelbergerDenominatorIdeal m) :
    algebraMap K L
        (stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x) : K) =
      ∏ a : (ZMod m)ˣ,
        ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1)
            (gaussSum
              ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp
                ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
              (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one))) ^
          (x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff a := by
  classical
  have hp_eq : Ideal.absNorm (Ideal.under ℤ P) = p := by
    rw [← Ideal.over_def P (Ideal.span {(p : ℤ)}), Int.absNorm_span_singleton, Int.natAbs_natCast]
  have : Fact (Ideal.absNorm (Ideal.under ℤ P)).Prime := ⟨Nat.absNorm_under_prime P⟩
  have : NeZero (Ideal.absNorm (Ideal.under ℤ P)) := ⟨(Nat.absNorm_under_prime P).ne_zero⟩
  let L₀ := CyclotomicField (Ideal.absNorm (Ideal.under ℤ P)) K
  let ζ₀ : L₀ := IsCyclotomicExtension.zeta (Ideal.absNorm (Ideal.under ℤ P)) K L₀
  have hζ₀ : IsPrimitiveRoot ζ₀ (Ideal.absNorm (Ideal.under ℤ P)) :=
    IsCyclotomicExtension.zeta_spec (Ideal.absNorm (Ideal.under ℤ P)) K L₀
  have hL₀ := Classical.choose_spec (exists_stickelbergerGaussProduct m K hm P hP x)
  dsimp only at hL₀
  subst hp_eq
  have hPP_refl :
      P = P.map (NumberField.RingOfIntegers.mapRingEquiv
        (AlgEquiv.refl (R := ℚ) (A₁ := K)).toRingEquiv : 𝓞 K →+* 𝓞 K) := by
    rw [show (AlgEquiv.refl (R := ℚ) (A₁ := K)).toRingEquiv = RingEquiv.refl K from rfl,
      NumberField.RingOfIntegers.mapRingEquiv_refl, RingEquiv.toRingHom_refl, Ideal.map_id]
  let _ := Ideal.Quotient.field P
  obtain ⟨eL, heL_K, heL_prod⟩ :=
    exists_algEquiv_map_prod_galEquivProd_gaussSum P hcop hζ₀
      (AlgEquiv.refl (R := ℚ) (A₁ := K)) (P' := P) hPP_refl hcop hζ x.property
  simp only [AlgEquiv.coe_refl, id_eq] at heL_K
  rw [← heL_K]
  change eL (algebraMap K L₀ (↑(Classical.choose
    (exists_stickelbergerGaussProduct m K hm P hP x)) : K)) = _
  rw [hL₀]
  convert heL_prod
  exact Subsingleton.elim _ _

private theorem liesOver_map_ringOfIntegers_mapRingEquiv {K K' : Type*}
    [Field K] [Field K']
    (P : Ideal (𝓞 K)) (e : K ≃+* K') (p : ℕ) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (P.map (NumberField.RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 K')).LiesOver
      (Ideal.span {(p : ℤ)}) := by
  rw [Ideal.liesOver_iff, Ideal.under_def]
  ext z
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  let eO := NumberField.RingOfIntegers.mapRingEquiv e
  have hez : algebraMap ℤ (𝓞 K') z = eO (algebraMap ℤ (𝓞 K) z) :=
    NumberField.RingOfIntegers.ext (by simp)
  rw [hez]
  constructor
  · intro hz
    exact Ideal.mem_map_of_mem _
      ((Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) z).1 (Ideal.mem_span_singleton.mpr hz))
  · intro hz
    obtain ⟨w, hw, hew⟩ := (Ideal.mem_map_iff_of_surjective _ eO.surjective).mp hz
    rw [eO.injective hew] at hw
    exact (Ideal.mem_span_singleton).mp ((Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) z).2 hw)

/-- **Compatibility with field embeddings.** Any ring homomorphism `e : K →+* K'` between `m`-th
cyclotomic extensions of `ℚ` sends `stickelbergerGaussProduct m K hm P hP` to
`stickelbergerGaussProduct m K' hm P' hP'`, where `P' = P.map (RingOfIntegers.mapRingHom e)`. -/
theorem map_stickelbergerGaussProduct (m : ℕ) [NeZero m]
    {K K' : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    [Field K'] [NumberField K'] [IsCyclotomicExtension {m} ℚ K']
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    {e : K →+* K'} {P' : Ideal (𝓞 K')} [P'.IsMaximal] (hP' : (Ideal.absNorm P').Coprime m)
    (hPP' : P' = P.map (NumberField.RingOfIntegers.mapRingHom e))
    (x : stickelbergerDenominatorIdeal m) :
    e (stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x) : K) =
      (stickelbergerGaussProduct m K' hm P' hP' (Multiplicative.ofAdd x) : K') := by
  classical
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {m} ℚ K'
  let eAlg : K →ₐ[ℚ] K' := e.toRatAlgHom
  have hsurj : Function.Surjective eAlg := by
    have hfin : Module.finrank ℚ K = Module.finrank ℚ K' := by
      rw [IsCyclotomicExtension.Rat.finrank m K, IsCyclotomicExtension.Rat.finrank m K']
    exact (LinearMap.range_eq_top (f := eAlg.toLinearMap)).mp (Submodule.eq_top_of_finrank_eq
      ((LinearMap.finrank_range_of_inj (f := eAlg.toLinearMap) eAlg.injective).trans hfin))
  let eEquiv : K ≃ₐ[ℚ] K' := AlgEquiv.ofBijective eAlg ⟨eAlg.injective, hsurj⟩
  have hPP'_equiv :
      P' = P.map (NumberField.RingOfIntegers.mapRingEquiv eEquiv.toRingEquiv : 𝓞 K →+* 𝓞 K') :=
    hPP'
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  have : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : P'.LiesOver (Ideal.span {(p : ℤ)}) :=
    hPP'_equiv ▸ liesOver_map_ringOfIntegers_mapRingEquiv P eEquiv.toRingEquiv p
  have hcop : ((NumberField.discr K).natAbs).Coprime p :=
    coprime_natAbs_discr_of_liesOver K P hP p
  have hcop' : ((NumberField.discr K').natAbs).Coprime p :=
    coprime_natAbs_discr_of_liesOver K' P' hP' p
  let L := CyclotomicField p K; let L' := CyclotomicField p K'
  have hζ := IsCyclotomicExtension.zeta_spec p K L
  have hζ' := IsCyclotomicExtension.zeta_spec p K' L'
  let _ := Ideal.Quotient.field P; let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have : CharP (𝓞 K ⧸ P) p := charP_quotient_of_liesOver P p
  let _ : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
  let _ := Ideal.Quotient.field P'; let _ : Fintype (𝓞 K' ⧸ P') := Fintype.ofFinite _
  have : CharP (𝓞 K' ⧸ P') p := charP_quotient_of_liesOver P' p
  let _ : Algebra (ZMod p) (𝓞 K' ⧸ P') := ZMod.algebra _ p
  obtain ⟨eL, heL_K, heL_prod⟩ :=
    exists_algEquiv_map_prod_galEquivProd_gaussSum P hcop hζ eEquiv hPP'_equiv hcop' hζ' x.property
  apply (algebraMap K' L').injective
  rw [show e (stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x) : K) =
      eEquiv _ from rfl, ← heL_K,
    algebraMap_stickelbergerGaussProduct m K hm P hP hcop hζ x,
    algebraMap_stickelbergerGaussProduct m K' hm P' hP' hcop' hζ' x]
  exact heL_prod

/-- **Galois equivariance on the prime ideal.** Applying `τ ∈ Gal(K/ℚ)` to
`stickelbergerGaussProduct m K hm P hP` replaces `P` by `τ • P`. -/
theorem gal_smul_stickelbergerGaussProduct (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    (τ : Gal(K/ℚ)) (x : stickelbergerDenominatorIdeal m) :
    τ (stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x) : K) =
      (stickelbergerGaussProduct m K hm (τ • P)
        (by simpa [← Ideal.map_ringOfIntegers_mapRingEquiv,
          Ideal.absNorm_map_of_ringEquiv] using hP)
        (Multiplicative.ofAdd x) : K) :=
  map_stickelbergerGaussProduct m hm P hP _ (Ideal.map_ringOfIntegers_mapRingEquiv P τ).symm x

/-- **Galois equivariance on the denominator multiplier.** Applying `σ_b ∈ Gal(K/ℚ)` to
`stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x)` acts on the multiplier `x` by
`MonoidAlgebra.single b 1 • x`. -/
theorem galEquivZMod_symm_stickelbergerGaussProduct (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    (b : (ZMod m)ˣ) (x : stickelbergerDenominatorIdeal m) :
    ((galEquivZMod m K).symm b)
        (stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x) : K) =
      (stickelbergerGaussProduct m K hm P hP
        (Multiplicative.ofAdd (MonoidAlgebra.single b (1 : ℤ) • x)) : K) := by
  classical
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  have : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcop : ((NumberField.discr K).natAbs).Coprime p :=
    coprime_natAbs_discr_of_liesOver K P hP p
  let L := CyclotomicField p K
  have hζ := IsCyclotomicExtension.zeta_spec p K L
  let _ := Ideal.Quotient.field P; let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have : CharP (𝓞 K ⧸ P) p := charP_quotient_of_liesOver P p
  let _ : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
  apply (algebraMap K L).injective
  rw [← galEquivProd_symm_sigma_algebraMap hcop hζ b,
    algebraMap_stickelbergerGaussProduct m K hm P hP hcop hζ x,
    algebraMap_stickelbergerGaussProduct m K hm P hP hcop hζ
      (MonoidAlgebra.single b (1 : ℤ) • x),
    map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft b) _ _ fun a ↦ ?_
  simp only [Equiv.coe_mulLeft, SetLike.val_smul, smul_eq_mul, map_zpow₀, ← AlgEquiv.mul_apply,
    ← map_mul, Prod.mk_mul_mk, mul_one, ← map_mul (galEquivZMod m K).symm]
  rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff a (by simp), one_mul]

/-- **`m`-th power formula for `stickelbergerGaussProduct`.** Raising
`stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x)` to the `m`-th power produces the
Galois-weighted product `∏_a (σ_a Φ(P)) ^ (x.coeff a)`. -/
theorem pow_stickelbergerGaussProduct (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    (x : stickelbergerDenominatorIdeal m) :
    (stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x) : K) ^ m =
      ∏ a : (ZMod m)ˣ,
        (algebraMap (𝓞 K) K
          (((galEquivZMod m K).symm a) • Ideal.stickelbergerPhi P m)) ^
            (x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff a := by
  classical
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  have : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcop : ((NumberField.discr K).natAbs).Coprime p :=
    coprime_natAbs_discr_of_liesOver K P hP p
  let L := CyclotomicField p K
  have hζ := IsCyclotomicExtension.zeta_spec p K L
  let _ := Ideal.Quotient.field P; let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have : CharP (𝓞 K ⧸ P) p := charP_quotient_of_liesOver P p
  let _ : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
  let f : 𝓞 K →+* L := (algebraMap K L).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective _ _)
  have hg_pow :
      (gaussSum ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp f)
        (traceAddChar p (𝓞 K ⧸ P) hζ.pow_eq_one)) ^ m = f (Ideal.stickelbergerPhi P m) :=
    (Ideal.stickelbergerPhi_prime P hP hm hf (isPrimitive_traceAddChar (𝓞 K ⧸ P) hζ)).symm
  apply (algebraMap K L).injective
  rw [map_pow, algebraMap_stickelbergerGaussProduct m K hm P hP hcop hζ x, map_prod,
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm _ (m : ℤ), zpow_mul, zpow_natCast, ← map_pow, hg_pow,
    map_zpow₀]
  refine congrArg (· ^ (x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff a) ?_
  rw [RingHom.comp_apply, galEquivProd_symm_sigma_algebraMap,
    ← NumberField.algebraMap_smul_eq_apply]

/-- **Smoothed Gauss descent.** Let `m ≥ 2`, let `K` be an `m`-th cyclotomic extension of `ℚ`, and
let `P` be a maximal ideal of `𝓞 K` whose norm is prime to `m`. For every denominator multiplier
`x ∈ stickelbergerDenominatorIdeal m`, the Galois-weighted product
`∏_a (σ_a Φ(P)) ^ (x.coeff a)` is the `m`-th power of a nonzero element of `K`. -/
theorem exists_pow_eq_prod_stickelbergerPhi_zpow (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    {x : MonoidAlgebra ℤ (ZMod m)ˣ} (hx : x ∈ stickelbergerDenominatorIdeal m) :
    ∃ u : Kˣ, (u : K) ^ m =
      ∏ a : (ZMod m)ˣ,
        (algebraMap (𝓞 K) K
          (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm a) •
            Ideal.stickelbergerPhi P m)) ^ x.coeff a :=
  ⟨stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd ⟨x, hx⟩),
    pow_stickelbergerGaussProduct m K hm P hP ⟨x, hx⟩⟩

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
    simpa [eAlg] using galEquivZMod_symm_conj eAlg a (e x)
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

/-- Comparison between the `p`-primary projection of the covariant `ℤ[(ZMod m)ˣ]`-action and the
scalar-extended action on `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))` under
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
      (∑ a : (ZMod m)ˣ,
        (x.coeff a : ℤ_[p]) •
          LinearMap.baseChange ℤ_[p]
            (ClassGroup.mulEquivHom
              (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
              |>.toAdditive.toAddMonoidHom.toIntLinearMap))
        ((1 : ℤ_[p]) ⊗ₜ[ℤ] Additive.ofMul c) := by
  rw [primaryComponentEquivPadicIntTensor_classGroupPrimaryProj]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
    AddMonoidHom.coe_toIntLinearMap, AddEquiv.coe_toAddMonoidHom, MulEquiv.toAdditive_apply_apply,
    toMul_ofMul]
  have hsum :
      Additive.ofMul
          (∏ a : (ZMod m)ˣ,
            (ClassGroup.mulEquivHom
              (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) ^
              x.coeff a) =
        ∑ a : (ZMod m)ˣ, x.coeff a • Additive.ofMul
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv)) c) := by
    simp only [ofMul_prod, ofMul_zpow]
  rw [hsum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, ← zsmul_eq_mul, TensorProduct.smul_tmul]

/-- **Scalar-extended Stickelberger annihilation.** Over any commutative ring `R`, every element of
`stickelbergerIdeal m` annihilates `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` through the base-changed
covariant Galois action. -/
theorem stickelbergerIdeal_annihilates_baseChange (R : Type*) [CommRing R]
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (x : MonoidAlgebra ℤ (ZMod m)ˣ) (hx : x ∈ stickelbergerIdeal m)
    (z : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    (∑ a : (ZMod m)ˣ,
      (x.coeff a : R) •
        LinearMap.baseChange R
          (ClassGroup.mulEquivHom
            (RingOfIntegers.mapRingEquiv
              (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm a).toRingEquiv))
            |>.toAdditive.toAddMonoidHom.toIntLinearMap)) z = 0 := by
  let g : (ZMod m)ˣ → ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 K) := fun a ↦
    ClassGroup.mulEquivHom
      (RingOfIntegers.mapRingEquiv (((galEquivZMod m K).symm a).toRingEquiv))
  let T : Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
    ∑ a : (ZMod m)ˣ,
      (x.coeff a : R) • LinearMap.baseChange R (g a).toAdditive.toAddMonoidHom.toIntLinearMap
  refine TensorProduct.inductionOn (motive := fun w ↦ T w = 0) z (fun r c ↦ ?_)
    (fun u v hu hv ↦ by rw [map_add, hu, hv, add_zero])
  have hsum : ∑ a : (ZMod m)ˣ, x.coeff a • Additive.ofMul (g a (Additive.toMul c)) = 0 := by
    have hann := stickelbergerIdeal_annihilates m K x hx (Additive.toMul c)
    simpa only [ofMul_prod, ofMul_zpow, ofMul_one] using congrArg Additive.ofMul hann
  simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul]
  simp_rw [TensorProduct.smul_tmul', smul_eq_mul, ← zsmul_eq_mul, TensorProduct.smul_tmul,
    AddMonoidHom.coe_toIntLinearMap, AddEquiv.coe_toAddMonoidHom, MulEquiv.toAdditive_apply_apply]
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
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
    AddMonoidHom.coe_toIntLinearMap, AddEquiv.coe_toAddMonoidHom]
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
