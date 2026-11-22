/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Stickelberger.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Basic
public import TauCeti.RingTheory.Ideal.Pointwise

import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.FieldTheory.Galois.Basic
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank
import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Relation
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Smoothed Gauss descent for cyclotomic Stickelberger products

Let `m ≥ 2` be an integer, let `K` be an `m`-th cyclotomic extension of `ℚ`, and let `P` be a
maximal ideal of `𝓞 K` whose norm is prime to `m`, lying over the rational prime `p`. Because
`p ∤ m`, `p` is coprime to `discr K`. In any compositum `L = K(ζ_p)`, the joint Galois isomorphism
`IsCyclotomicExtension.galEquivProd` splits `Gal(L/ℚ) ≃* Gal(K/ℚ) × (ZMod p)ˣ`, yielding
commuting lifts `σ_a` (`a ∈ (ZMod m)ˣ`) and `τ_b` (`b ∈ (ZMod p)ˣ`, fixing `K` and sending
`ζ_p ↦ ζ_p ^ b`).

For the Gauss sum `g = g(χ_P, ψ) ∈ L` attached to `χ_P = (· / P)_m⁻¹` and `ψ(t) = ζ_p ^ Tr(t)`,
one has `g ^ m = Φ(P)` and `τ_b(g) = (b / P)_m · g`. Given `x ∈ stickelbergerDenominatorIdeal m`,
the Galois-weighted product `G_x = ∏_a (σ_a g) ^ (x.coeff a)` satisfies
`τ_b(G_x) = (b / P)_m ^ (∑_a x_a a₀) · G_x = G_x` by the denominator congruence `m ∣ ∑_a x_a a₀`
(`TauCeti.mem_stickelbergerDenominatorIdeal_iff_dvd`). Galois descent produces a multiplicative
homomorphism `TauCeti.stickelbergerGaussProduct : Multiplicative J_m →* Kˣ` independent of the
auxiliary root `ζ_p` and compositum `L`, compatible with field embeddings `K →+* K'`, equivariant
under `Gal(K/ℚ)`, and satisfying `u(x) ^ m = ∏_a (σ_a Φ(P)) ^ (x.coeff a)`.

## Main definitions

* `TauCeti.stickelbergerGaussProduct`: the descended Gauss product homomorphism
  `Multiplicative (stickelbergerDenominatorIdeal m) →* Kˣ` attached to a maximal ideal `P` of norm
  coprime to `m`.

## Main results

* `TauCeti.coprime_natAbs_discr_of_liesOver`: if `(Ideal.absNorm P).Coprime m` and `P` lies over
  `(p)`, then `p` is coprime to `discr K`.
* `TauCeti.prod_galEquivProd_gaussSum_eq_of_isPrimitiveRoot` and
  `TauCeti.algebraMap_stickelbergerGaussProduct`: identification of `stickelbergerGaussProduct` in
  any compositum `L = K(ζ_p)` and independence of the auxiliary primitive `p`-th root of unity.
* `TauCeti.inv_powerResidueSymbol_algebraMap_eq_of_zpowers`,
  `TauCeti.gaussSum_inv_powerResidueSymbol_eq_of_eq`, and
  `TauCeti.algebraMap_stickelbergerGaussProduct_of_zpowers`: split-prime comparison identifying
  `(Ideal.powerResidueSymbol P m)⁻¹`, its native Gauss sum, and `stickelbergerGaussProduct` with a
  generator-normalized character over `ZMod p`.
* `TauCeti.map_stickelbergerGaussProduct`, `TauCeti.gal_smul_stickelbergerGaussProduct`, and
  `TauCeti.galEquivZMod_symm_stickelbergerGaussProduct`: compatibility of
  `stickelbergerGaussProduct` with field embeddings `K →+* K'` and Galois automorphisms.
* `TauCeti.pow_stickelbergerGaussProduct` and `TauCeti.exists_pow_eq_prod_stickelbergerPhi_zpow`:
  the `m`-th power formula and existential smoothed Gauss descent.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §6.2.
* S. A. Katre, *Gauss–Jacobi sums and Stickelberger's theorem*, §4.
* R. Sharifi, *Iwasawa Theory* (lecture notes), §4.5.
-/

public section

open NumberField IsCyclotomicExtension.Rat
open scoped Pointwise

namespace TauCeti

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

private theorem galEquivProd_symm_sigma_algebraMap {m : ℕ} [NeZero m]
    {K L : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [NeZero p] [IsCyclotomicExtension {p} K L]
    (hcop : ((NumberField.discr K).natAbs).Coprime p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (a : (ZMod m)ˣ) (z : K) :
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
        ((galEquivZMod m K).symm a, 1) (algebraMap K L z) =
      algebraMap K L (((galEquivZMod m K).symm a) z) := by
  simp

private theorem galEquivProd_symm_tau_algebraMap
    {K L : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [NeZero p] [IsCyclotomicExtension {p} K L]
    (hcop : ((NumberField.discr K).natAbs).Coprime p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (b : (ZMod p)ˣ) (z : K) :
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b) (algebraMap K L z) =
      algebraMap K L z := by
  simp

private theorem galEquivProd_symm_tau_zeta
    {K L : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [NeZero p] [IsCyclotomicExtension {p} K L]
    (hcop : ((NumberField.discr K).natAbs).Coprime p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (b : (ZMod p)ˣ) :
    (IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm (1, b) ζ =
      ζ ^ (b : ZMod p).val := by
  simp

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
    · simp only [MulChar.ringHomComp_apply, RingHom.comp_apply, τ,
        IsCyclotomicExtension.galEquivProd_symm_algebraMap, AlgEquiv.one_apply]
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
          e.map_galEquivZMod_symm, e.apply_symm_apply]
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
      have : CharP (𝓞 K ⧸ P) p :=
        Ideal.Quotient.charP_of_liesOver P Ideal.IsPrime.ne_top' p Fact.out
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
  have : CharP (𝓞 K ⧸ P) p := Ideal.Quotient.charP_of_liesOver P Ideal.IsPrime.ne_top' p Fact.out
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
        have : CharP (𝓞 K ⧸ P) p :=
          Ideal.Quotient.charP_of_liesOver P Ideal.IsPrime.ne_top' p Fact.out
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

/-- **Split-prime comparison for the inverse power residue symbol.** Let `P` be a maximal ideal
of `𝓞 K` of prime norm `p` coprime to `m`, and let `g` be a generator of `(ZMod p)ˣ`. A
character `χ : MulChar (ZMod p) (𝓞 K)` with `χ (g : ZMod p) ^ m = 1` and
`Ideal.Quotient.mk P (χ⁻¹ (g : ZMod p)) =`
`algebraMap (ZMod p) (𝓞 K ⧸ P) ((g : ZMod p) ^ ((p - 1) / m))`
agrees with `(Ideal.powerResidueSymbol P m)⁻¹` via `algebraMap (ZMod p) (𝓞 K ⧸ P)`. -/
theorem inv_powerResidueSymbol_algebraMap_eq_of_zpowers {m : ℕ} [NeZero m]
    {K : Type*} [Field K] [NumberField K] [HasEnoughRootsOfUnity (𝓞 K) m]
    (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    {p : ℕ} [hp : Fact p.Prime] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    (hNP : Ideal.absNorm P = p) {χ : MulChar (ZMod p) (𝓞 K)} {g : (ZMod p)ˣ}
    (hg : Subgroup.zpowers g = ⊤) (hχm : χ (g : ZMod p) ^ m = 1)
    (hχP : Ideal.Quotient.mk P (χ⁻¹ (g : ZMod p)) =
      algebraMap (ZMod p) (𝓞 K ⧸ P) ((g : ZMod p) ^ ((p - 1) / m)))
    (t : ZMod p) :
    (Ideal.powerResidueSymbol P m)⁻¹ (algebraMap (ZMod p) (𝓞 K ⧸ P) t) = χ t := by
  let _ := Ideal.Quotient.field P
  obtain ⟨u, hu⟩ := IsUnit.of_pow_eq_one hχm (NeZero.ne m)
  have hu_pow : u ^ m = 1 := Units.ext (by simp [hu, hχm])
  have hχinv_pow : χ⁻¹ (g : ZMod p) ^ m = 1 := by
    rw [MulChar.inv_apply_eq_inv, ← hu, Ring.inverse_unit, ← Units.val_pow_eq_pow_val, inv_pow,
      hu_pow, inv_one, Units.val_one]
  have h_gen :
      Ideal.powerResidueSymbol P m (algebraMap (ZMod p) (𝓞 K ⧸ P) (g : ZMod p)) =
        χ⁻¹ (g : ZMod p) := by
    rw [Ideal.powerResidueSymbol_eq_iff hP hχinv_pow, hNP, ← map_pow]
    exact hχP
  have h_gen_inv :
      (Ideal.powerResidueSymbol P m)⁻¹ (algebraMap (ZMod p) (𝓞 K ⧸ P) (g : ZMod p)) =
        χ (g : ZMod p) := by
    rw [MulChar.inv_apply_eq_inv, h_gen, MulChar.inv_apply_eq_inv, ← hu, Ring.inverse_unit,
      Ring.inverse_unit, inv_inv]
  obtain rfl | ht := eq_or_ne t 0
  · rw [map_zero, MulChar.map_zero, MulChar.map_zero]
  lift t to (ZMod p)ˣ using ht.isUnit
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ▸ Subgroup.mem_top t)
  rw [← hk]
  let φ₁ : (ZMod p)ˣ →* (𝓞 K)ˣ :=
    (Ideal.powerResidueSymbol P m)⁻¹.toUnitHom.comp
      (Units.map (algebraMap (ZMod p) (𝓞 K ⧸ P)).toMonoidHom)
  let φ₂ : (ZMod p)ˣ →* (𝓞 K)ˣ := χ.toUnitHom
  have hφ : φ₁ g = φ₂ g := Units.ext h_gen_inv
  have hφk : (φ₁ (g ^ k) : 𝓞 K) = (φ₂ (g ^ k) : 𝓞 K) := by
    rw [map_zpow, map_zpow, hφ]
  simpa only [φ₁, φ₂, MonoidHom.comp_apply, MulChar.coe_toUnitHom, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using hφk

/-- **Split-prime comparison for the native Gauss sum.** If `(Ideal.powerResidueSymbol P m)⁻¹`
agrees with `χ : MulChar (ZMod p) (𝓞 K)` on `algebraMap (ZMod p) (𝓞 K ⧸ P)` and
`Ideal.absNorm P = p`, then the native Gauss sum over `𝓞 K ⧸ P` against `traceAddChar` equals the
Gauss sum of `χ` over `ZMod p` against `AddChar.zmodChar`. -/
theorem gaussSum_inv_powerResidueSymbol_eq_of_eq {m : ℕ} [NeZero m]
    {K : Type*} [Field K] [NumberField K] [HasEnoughRootsOfUnity (𝓞 K) m]
    (P : Ideal (𝓞 K)) [P.IsMaximal] {p : ℕ} [hp : Fact p.Prime]
    [Fintype (𝓞 K ⧸ P)] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    (hNP : Ideal.absNorm P = p) {χ : MulChar (ZMod p) (𝓞 K)}
    {L : Type*} [CommRing L] (f : 𝓞 K →+* L) {ζ : L} (hζ : ζ ^ p = 1)
    (hχ : ∀ t : ZMod p,
      (Ideal.powerResidueSymbol P m)⁻¹ (algebraMap (ZMod p) (𝓞 K ⧸ P) t) = χ t) :
    gaussSum ((Ideal.powerResidueSymbol P m)⁻¹.ringHomComp f) (traceAddChar p (𝓞 K ⧸ P) hζ) =
      gaussSum (χ.ringHomComp f) (AddChar.zmodChar p hζ) := by
  let _ := Ideal.Quotient.field P
  have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card, ← Ideal.absNorm_eq_natCard, hNP]
  have hbij : Function.Bijective (Algebra.ofId (ZMod p) (𝓞 K ⧸ P)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(Algebra.ofId (ZMod p) (𝓞 K ⧸ P)).toRingHom.injective, by rw [ZMod.card, hcard]⟩
  let eQ : ZMod p ≃ₐ[ZMod p] (𝓞 K ⧸ P) :=
    AlgEquiv.ofBijective (Algebra.ofId (ZMod p) (𝓞 K ⧸ P)) hbij
  have heQ (t : ZMod p) : (eQ t : 𝓞 K ⧸ P) = algebraMap (ZMod p) (𝓞 K ⧸ P) t := rfl
  rw [gaussSum, gaussSum]
  refine (Fintype.sum_equiv eQ.toEquiv _ _ fun t ↦ ?_).symm
  simp only [MulChar.ringHomComp_apply, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    heQ, hχ t, traceAddChar_apply, AddChar.zmodChar_apply]
  rw [← heQ, Algebra.trace_eq_of_algEquiv eQ t, Algebra.trace_self, LinearMap.id_apply]

/-- **Split-prime compositum formula for `stickelbergerGaussProduct`.** Under the hypotheses of
`algebraMap_stickelbergerGaussProduct` and `inv_powerResidueSymbol_algebraMap_eq_of_zpowers`,
`stickelbergerGaussProduct` embeds into `L` as the Galois-weighted product of the `ZMod p` Gauss
sums `gaussSum (χ.ringHomComp _) (AddChar.zmodChar p hζ.pow_eq_one)`. -/
theorem algebraMap_stickelbergerGaussProduct_of_zpowers (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    (hm : 2 ≤ m) (P : Ideal (𝓞 K)) [P.IsMaximal] (hP : (Ideal.absNorm P).Coprime m)
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {p : ℕ} [hp : Fact p.Prime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    [IsCyclotomicExtension {p} K L] [Algebra (ZMod p) (𝓞 K ⧸ P)]
    (hcop : ((NumberField.discr K).natAbs).Coprime p)
    {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (hNP : Ideal.absNorm P = p) {χ : MulChar (ZMod p) (𝓞 K)} {g : (ZMod p)ˣ}
    (hg : Subgroup.zpowers g = ⊤) (hχm : χ (g : ZMod p) ^ m = 1)
    (hχP : Ideal.Quotient.mk P (χ⁻¹ (g : ZMod p)) =
      algebraMap (ZMod p) (𝓞 K ⧸ P) ((g : ZMod p) ^ ((p - 1) / m)))
    (x : stickelbergerDenominatorIdeal m) :
    algebraMap K L
        (stickelbergerGaussProduct m K hm P hP (Multiplicative.ofAdd x) : K) =
      ∏ a : (ZMod m)ˣ,
        ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1)
            (gaussSum
              (χ.ringHomComp ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
              (AddChar.zmodChar p hζ.pow_eq_one))) ^
          (x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff a := by
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  rw [algebraMap_stickelbergerGaussProduct m K hm P hP hcop hζ x]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [gaussSum_inv_powerResidueSymbol_eq_of_eq P hNP _ hζ.pow_eq_one
    (inv_powerResidueSymbol_algebraMap_eq_of_zpowers P hP hNP hg hχm hχP)]

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
    hPP'_equiv ▸ Ideal.liesOver_map_ringOfIntegers_mapRingEquiv P eEquiv.toRingEquiv
      (Ideal.span {(p : ℤ)})
  have hcop : ((NumberField.discr K).natAbs).Coprime p :=
    coprime_natAbs_discr_of_liesOver K P hP p
  have hcop' : ((NumberField.discr K').natAbs).Coprime p :=
    coprime_natAbs_discr_of_liesOver K' P' hP' p
  let L := CyclotomicField p K; let L' := CyclotomicField p K'
  have hζ := IsCyclotomicExtension.zeta_spec p K L
  have hζ' := IsCyclotomicExtension.zeta_spec p K' L'
  let _ := Ideal.Quotient.field P; let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have : CharP (𝓞 K ⧸ P) p := Ideal.Quotient.charP_of_liesOver P Ideal.IsPrime.ne_top' p Fact.out
  let _ : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
  let _ := Ideal.Quotient.field P'; let _ : Fintype (𝓞 K' ⧸ P') := Fintype.ofFinite _
  have : CharP (𝓞 K' ⧸ P') p := Ideal.Quotient.charP_of_liesOver P' Ideal.IsPrime.ne_top' p Fact.out
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
  have : CharP (𝓞 K ⧸ P) p := Ideal.Quotient.charP_of_liesOver P Ideal.IsPrime.ne_top' p Fact.out
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
  have : CharP (𝓞 K ⧸ P) p := Ideal.Quotient.charP_of_liesOver P Ideal.IsPrime.ne_top' p Fact.out
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

end TauCeti
