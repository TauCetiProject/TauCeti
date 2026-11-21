/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.ClassGroup.Equiv
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Stickelberger.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Basic
public import TauCeti.RingTheory.Ideal.Pointwise

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.GaussSum
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.LegendreSymbol.AddCharacter
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
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
(`TauCeti.stickelbergerIdeal`) annihilates `ClassGroup (𝓞 K)`.

## Proof outline

At `m = 1` the integral Stickelberger ideal is `⊥`, so annihilation holds trivially. For `m ≥ 2`
the argument works directly at every maximal ideal `P` of `𝓞 K` whose norm is prime to `m`
(including primes above `2` when `m` is odd and the conductor `m = 2`), without appealing to
Chebotarev density or Hilbert class fields:

1. **Smoothed Gauss descent (`TauCeti.exists_pow_eq_prod_stickelbergerPhi_zpow`).** Let `p` be the
   rational prime below `P`; then `p ∤ m`, so `p` is coprime to `discr K`. In the compositum
   `L = K(ζ_p)`, the joint Galois isomorphism `IsCyclotomicExtension.galEquivProd` splits
   `Gal(L/ℚ) ≃* Gal(K/ℚ) × (ZMod p)ˣ`, yielding commuting lifts `σ_a` (`a ∈ (ZMod m)ˣ`) and
   `τ_b` (`b ∈ (ZMod p)ˣ`, fixing `K` and sending `ζ_p ↦ ζ_p ^ b`). For the Gauss sum
   `g = g(χ_P, ψ) ∈ L` attached to `χ_P = (· / P)_m⁻¹` and `ψ(t) = ζ_p ^ Tr(t)`, one has
   `g ^ m = Φ(P)` and `τ_b(g) = (b / P)_m · g`. Given `x ∈ J_m`, the Galois-weighted product
   `G_x = ∏_a (σ_a g) ^ (x.coeff a)` satisfies `τ_b(G_x) = (b / P)_m ^ (∑_a x_a a₀) · G_x = G_x`
   by the denominator congruence `m ∣ ∑_a x_a a₀`
   (`TauCeti.mem_stickelbergerDenominatorIdeal_iff_dvd`). Galois descent therefore produces
   `u ∈ Kˣ` with `u ^ m = ∏_a (σ_a Φ(P)) ^ (x.coeff a)`.
2. **Prime principalization (`TauCeti.exists_toPrincipalIdeal_eq_prod_zpow_of_isMaximal`).**
   Expanding `(Φ(P))` via Stickelberger's relation (`Ideal.span_stickelbergerPhi_of_isMaximal`)
   and reindexing gives `(u) ^ m = (∏_c (σ_c • P) ^ (y.coeff c)) ^ m` as invertible fractional
   ideals of `K`. Torsion-freeness of fractional ideals (`HasUniqueRoots`) cancels the `m`-th
   power, proving `∏_c (σ_c • P) ^ (y.coeff c) = (u)`.
3. **Full class-group annihilation (`TauCeti.stickelbergerIdeal_annihilates`).** Passing to
   `ClassGroup (𝓞 K)` kills `[P]`, hence by prime factorization every ideal class represented by an
   ideal of norm prime to `m`. Since `(m)` lies in only finitely many maximal ideals,
   `ClassGroup.exists_mk_eq_and_sup_eq_top` represents every ideal class of `𝓞 K` by an ideal
   coprime to `(m)` (hence of norm coprime to `m`), closing the theorem for all classes.

## Main results

* `TauCeti.exists_pow_eq_prod_stickelbergerPhi_zpow`: for `m ≥ 2`, a maximal ideal `P` of `𝓞 K`
  with `(Ideal.absNorm P).Coprime m`, and `x ∈ stickelbergerDenominatorIdeal m`, the Galois-weighted
  product `∏_a (σ_a Φ(P)) ^ (x.coeff a)` is an `m`-th power in `Kˣ`.
* `TauCeti.exists_toPrincipalIdeal_eq_prod_zpow_of_isMaximal`: for every maximal ideal `P` of `𝓞 K`
  with `(Ideal.absNorm P).Coprime m` and every `y ∈ stickelbergerIdeal m`, the fractional ideal
  `∏_c (σ_c • P) ^ (y.coeff c)` is principal.
* `TauCeti.stickelbergerIdeal_annihilates`: every element of `stickelbergerIdeal m` annihilates
  `ClassGroup (𝓞 K)` under the covariant Galois action.
* `TauCeti.stickelbergerSmoothing_annihilates`: specialization to the positive smoothed elements
  `stickelbergerSmoothing m b` for `b.Coprime m`.
* `TauCeti.stickelbergerIdeal_annihilates_baseChange`: scalar-extended annihilation on
  `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` for any commutative ring `R`.
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

/-! ### Smoothed Gauss descent and prime principalization -/

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
            Ideal.stickelbergerPhi P m)) ^ x.coeff a := by
  classical
  -- Step 1: Extract the rational prime `p` below `P`; `p ∤ m`, so `p` is coprime to `discr K`.
  obtain ⟨p, hp, hPp⟩ : ∃ p : ℕ, p.Prime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨Ideal.absNorm (Ideal.under ℤ P), Nat.absNorm_under_prime P, inferInstance⟩
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hNP : p ^ Ideal.inertiaDeg P ℤ = Ideal.absNorm P := Ideal.pow_inertiaDeg p P
  have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp).1 <|
    hP.coprime_dvd_left (hNP ▸ dvd_pow_self p (Ideal.inertiaDeg_pos P ℤ).ne')
  have hcop : ((NumberField.discr K).natAbs).Coprime p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd ↦
      hpm (prime_dvd_of_dvd_natAbs_discr K m hp hdvd)).symm
  -- Step 2: Set up `L = K(ζ_p)` and the commuting lifts `σ_a, τ_b ∈ Gal(L/ℚ)`.
  let L := CyclotomicField p K
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : IsGalois K L := IsCyclotomicExtension.isGalois {p} K L
  have : FiniteDimensional K L := IsCyclotomicExtension.finiteDimensional {p} K L
  let ζp : L := IsCyclotomicExtension.zeta p K L
  have hζp : IsPrimitiveRoot ζp p := IsCyclotomicExtension.zeta_spec p K L
  let e : Gal(L/ℚ) ≃* Gal(K/ℚ) × (ZMod p)ˣ :=
    IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζp
  let σ : (ZMod m)ˣ → Gal(L/ℚ) := fun a ↦ e.symm ((galEquivZMod m K).symm a, 1)
  let τ : (ZMod p)ˣ → Gal(L/ℚ) := fun b ↦ e.symm (1, b)
  have hστ (a : (ZMod m)ˣ) (b : (ZMod p)ˣ) : τ b * σ a = σ a * τ b :=
    e.injective (by simp [σ, τ])
  have hσ_K (a : (ZMod m)ˣ) (z : K) :
      σ a (algebraMap K L z) = algebraMap K L (((galEquivZMod m K).symm a) z) := by
    have hcomm := (σ a).restrictNormal_commutes K z
    rw [IsCyclotomicExtension.restrictNormal_galEquivProd_symm] at hcomm
    exact hcomm.symm
  have hτ_K (b : (ZMod p)ˣ) (z : K) : τ b (algebraMap K L z) = algebraMap K L z := by
    have hcomm := (τ b).restrictNormal_commutes K z
    rw [IsCyclotomicExtension.restrictNormal_galEquivProd_symm, AlgEquiv.one_apply] at hcomm
    exact hcomm.symm
  have hτ_ζp (b : (ZMod p)ˣ) : τ b ζp = ζp ^ (b : ZMod p).val := by
    have hspec := hζp.autToPow_spec ℚ (τ b)
    rw [IsCyclotomicExtension.autToPow_galEquivProd_symm] at hspec
    exact hspec.symm
  -- Step 3: Build the Gauss sum `g = g(χ_P, ψ) ∈ L` on `𝓞 K ⧸ P` with `g ^ m = Φ(P)`.
  let _ := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have : CharP (𝓞 K ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    have hmem := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).1
      (Ideal.mem_span_singleton_self _)
    rwa [map_natCast] at hmem
  let _ : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
  let f : 𝓞 K →+* L := (algebraMap K L).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective _ _)
  let χ : MulChar (𝓞 K ⧸ P) L := (Ideal.powerResidueSymbol P m)⁻¹.ringHomComp f
  let g : L := gaussSum χ (traceAddChar p (𝓞 K ⧸ P) hζp.pow_eq_one)
  have hg_pow : g ^ m = f (Ideal.stickelbergerPhi P m) :=
    (Ideal.stickelbergerPhi_prime P hP hm hf (isPrimitive_traceAddChar (𝓞 K ⧸ P) hζp)).symm
  have hΦ_ne : Ideal.stickelbergerPhi P m ≠ 0 := Ideal.stickelbergerPhi_ne_zero hP hm
  have hg_ne : g ≠ 0 := fun hg0 ↦
    hΦ_ne (hf (by rw [map_zero, ← hg_pow, hg0, zero_pow (NeZero.ne m)]))
  -- Step 4: Compute `τ b g = f (ω_b) * g` with `ω_b ^ m = 1`, and descend `G_x` to `Kˣ`.
  have hτ_g (b : (ZMod p)ˣ) : ∃ ω : 𝓞 K, ω ^ m = 1 ∧ τ b g = f ω * g := by
    let u_b : (𝓞 K ⧸ P)ˣ := Units.map (algebraMap (ZMod p) (𝓞 K ⧸ P)).toMonoidHom b
    refine ⟨Ideal.powerResidueSymbol P m (u_b : 𝓞 K ⧸ P),
      Ideal.powerResidueSymbol_pow_eq_one u_b.ne_zero, ?_⟩
    have hact := map_gaussSum_traceAddChar hζp.pow_eq_one χ (τ b).toRingHom b
      (fun t ↦ hτ_K b (algebraMap (𝓞 K) K ((Ideal.powerResidueSymbol P m)⁻¹ t))) (hτ_ζp b)
    have hχinv : χ⁻¹ = (Ideal.powerResidueSymbol P m).ringHomComp f := by
      simp only [χ, ← MulChar.ringHomComp_inv, inv_inv]
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      hχinv, MulChar.ringHomComp_apply, u_b, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass] using hact
  let Gx : L := ∏ a : (ZMod m)ˣ, (σ a g) ^ x.coeff a
  have hGx_ne : Gx ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ ↦
      zpow_ne_zero _ (map_ne_zero_iff (σ a) (σ a).injective |>.mpr hg_ne)
  have hτ_Gx (b : (ZMod p)ˣ) : τ b Gx = Gx := by
    obtain ⟨ω, hω, hτg⟩ := hτ_g b
    have hσ_ω (a : (ZMod m)ˣ) : σ a (f ω) = (f ω) ^ (a : ZMod m).val := by
      have hωK : (algebraMap (𝓞 K) K ω) ^ m = 1 := by rw [← map_pow, hω, map_one]
      have hact := galEquivZMod_apply_of_pow_eq m K ((galEquivZMod m K).symm a) hωK
      rw [MulEquiv.apply_symm_apply] at hact
      simp only [f, RingHom.comp_apply, hσ_K a, hact, map_pow]
    have hτ_term (a : (ZMod m)ˣ) :
        τ b ((σ a g) ^ x.coeff a) =
          (f ω) ^ (x.coeff a * ((a : ZMod m).val : ℤ)) * (σ a g) ^ x.coeff a := by
      have h1 : τ b (σ a g) = (f ω) ^ (a : ZMod m).val * σ a g := by
        rw [← AlgEquiv.mul_apply, hστ a b, AlgEquiv.mul_apply, hτg, map_mul, hσ_ω a]
      rw [map_zpow₀, h1, mul_zpow, ← zpow_natCast, ← zpow_mul, mul_comm ((a : ZMod m).val : ℤ)]
    obtain ⟨k, hk⟩ := mem_stickelbergerDenominatorIdeal_iff_dvd.mp hx
    have hfω_ne : f ω ≠ 0 := fun h0 ↦
      one_ne_zero (by rw [← map_one f, ← hω, map_pow, h0, zero_pow (NeZero.ne m)])
    have hfω_pow : (f ω) ^ (∑ a : (ZMod m)ˣ, x.coeff a * ((a : ZMod m).val : ℤ)) = 1 := by
      rw [hk, zpow_mul, zpow_natCast, ← map_pow, hω, map_one, one_zpow]
    calc
      τ b Gx = ∏ a : (ZMod m)ˣ, τ b ((σ a g) ^ x.coeff a) := map_prod (τ b) _ _
      _ = ∏ a : (ZMod m)ˣ,
            ((f ω) ^ (x.coeff a * ((a : ZMod m).val : ℤ)) * (σ a g) ^ x.coeff a) :=
          Finset.prod_congr rfl fun a _ ↦ hτ_term a
      _ = (∏ a : (ZMod m)ˣ, (f ω) ^ (x.coeff a * ((a : ZMod m).val : ℤ))) * Gx :=
          Finset.prod_mul_distrib
      _ = (f ω) ^ (∑ a : (ZMod m)ˣ, x.coeff a * ((a : ZMod m).val : ℤ)) * Gx := by
          rw [Finset.prod_zpow_eq_zpow_sum_of_isUnit _ hfω_ne.isUnit]
      _ = Gx := by rw [hfω_pow, one_mul]
  have hGx_fixed (ρ : Gal(L/K)) : ρ Gx = Gx := by
    rw [← AlgEquiv.restrictScalars_apply ℚ ρ Gx,
      IsCyclotomicExtension.restrictScalars_eq_galEquivProd_symm_one ℚ K L p hcop hζp ρ]
    exact hτ_Gx _
  obtain ⟨α, hαL⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed Gx).mpr hGx_fixed)
  have hα_ne : α ≠ 0 := fun h0 ↦ hGx_ne (by rw [← hαL, h0, map_zero])
  refine ⟨Units.mk0 α hα_ne, (algebraMap K L).injective ?_⟩
  rw [Units.val_mk0, map_pow, hαL, map_prod]
  calc
    Gx ^ m = ∏ a : (ZMod m)ˣ, ((σ a g) ^ x.coeff a) ^ m := (Finset.prod_pow _ _ _).symm
    _ = ∏ a : (ZMod m)ˣ, (σ a (g ^ m)) ^ x.coeff a := by
          refine Finset.prod_congr rfl fun a _ ↦ ?_
          rw [map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    _ = ∏ a : (ZMod m)ˣ,
          algebraMap K L ((algebraMap (𝓞 K) K
            (((galEquivZMod m K).symm a) • Ideal.stickelbergerPhi P m)) ^ x.coeff a) := by
          refine Finset.prod_congr rfl fun a _ ↦ ?_
          rw [map_zpow₀, hg_pow]
          refine congrArg (· ^ x.coeff a) ?_
          rw [RingHom.comp_apply, hσ_K a, ← NumberField.algebraMap_smul_eq_apply]

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
  calc
    Ideal.span {φ a • Ideal.stickelbergerPhi P m}
        = φ a • Ideal.span {Ideal.stickelbergerPhi P m} := by
          rw [Ideal.smul_closure, Set.smul_set_singleton]
    _ = φ a • ∏ b : (ZMod m)ˣ, (φ b⁻¹ • P) ^ (b : ZMod m).val := by rw [hrel]
    _ = ∏ b : (ZMod m)ˣ, (φ a • (φ b⁻¹ • P) ^ (b : ZMod m).val) := Finset.smul_prod'
    _ = ∏ b : (ZMod m)ˣ, (φ (a * b⁻¹) • P) ^ (b : ZMod m).val := by
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
  calc
    ∏ a : (ZMod m)ˣ, (∏ b : (ZMod m)ˣ, Q (a * b⁻¹) ^ (b : ZMod m).val) ^ x.coeff a
        = ∏ a : (ZMod m)ˣ,
            (∏ c : (ZMod m)ˣ, Q c ^ ((a * c⁻¹ : (ZMod m)ˣ).val.val : ℤ)) ^ x.coeff a :=
          Finset.prod_congr rfl fun a _ ↦ by rw [hreindex a]
    _ = ∏ c : (ZMod m)ˣ,
          Q c ^ (∑ a : (ZMod m)ˣ, x.coeff a * ((a * c⁻¹ : (ZMod m)ˣ).val.val : ℤ)) :=
          Finset.prod_prod_zpow Finset.univ Finset.univ (fun c _ ↦ Group.isUnit (Q c)) _ _
    _ = ∏ c : (ZMod m)ˣ, Q c ^ ((m : ℤ) * y.coeff c) :=
          Finset.prod_congr rfl fun c _ ↦ by
            rw [← natCast_mul_coeff_of_integralGroupRingCast_eq hxy c]
    _ = (∏ c : (ZMod m)ˣ, Q c ^ y.coeff c) ^ m := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl fun c _ ↦ ?_
          rw [mul_comm (m : ℤ), zpow_mul, zpow_natCast]

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
  · obtain ⟨x, hxy⟩ := mem_stickelbergerIdeal.mp hy
    obtain ⟨u, hu⟩ := exists_pow_eq_prod_stickelbergerPhi_zpow m K hm P hP
      (mem_stickelbergerDenominatorIdeal.mpr ⟨y, hxy⟩)
    refine ⟨u, ?_⟩
    let φ : (ZMod m)ˣ → Gal(K/ℚ) := fun a ↦ (galEquivZMod m K).symm a
    have hΦ_ne : Ideal.stickelbergerPhi P m ≠ 0 := Ideal.stickelbergerPhi_ne_zero hP hm
    have hΦ_K_ne (a : (ZMod m)ˣ) :
        algebraMap (𝓞 K) K (φ a • Ideal.stickelbergerPhi P m) ≠ 0 := by
      have hsmul_ne : φ a • Ideal.stickelbergerPhi P m ≠ 0 := fun h0 ↦
        hΦ_ne (by rw [← inv_smul_smul (φ a) (Ideal.stickelbergerPhi P m), h0, smul_zero])
      exact (map_ne_zero_iff (algebraMap (𝓞 K) K) (FaithfulSMul.algebraMap_injective _ _)).mpr
        hsmul_ne
    let uΦ : (ZMod m)ˣ → Kˣ := fun a ↦
      Units.mk0 (algebraMap (𝓞 K) K (φ a • Ideal.stickelbergerPhi P m)) (hΦ_K_ne a)
    have hu_pow : u ^ m = ∏ a : (ZMod m)ˣ, uΦ a ^ x.coeff a := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hu, Units.coe_prod]
      refine Finset.prod_congr rfl fun a _ ↦ ?_
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
    let Q : (ZMod m)ˣ → (FractionalIdeal (𝓞 K)⁰ K)ˣ := fun c ↦
      FractionalIdeal.mk0 K ⟨φ c • P, mem_nonZeroDivisors_of_ne_zero (NeZero.ne _)⟩
    have huΦ_ideal (a : (ZMod m)ˣ) :
        toPrincipalIdeal (𝓞 K) K (uΦ a) =
          ∏ b : (ZMod m)ˣ, Q (a * b⁻¹) ^ (b : ZMod m).val := by
      apply Units.ext
      rw [coe_toPrincipalIdeal, Units.val_mk0, ← FractionalIdeal.coeIdeal_span_singleton,
        span_smul_stickelbergerPhi_of_isMaximal hm P hP a, ← FractionalIdeal.coeIdealHom_apply,
        map_prod, Units.coe_prod]
      refine Finset.prod_congr rfl fun b _ ↦ ?_
      rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow,
        Units.val_pow_eq_pow_val, FractionalIdeal.coe_mk0]
    have hpow : toPrincipalIdeal (𝓞 K) K u ^ m = (∏ c : (ZMod m)ˣ, Q c ^ y.coeff c) ^ m := by
      calc
        toPrincipalIdeal (𝓞 K) K u ^ m
            = toPrincipalIdeal (𝓞 K) K (u ^ m) := (map_pow _ _ _).symm
        _ = ∏ a : (ZMod m)ˣ, toPrincipalIdeal (𝓞 K) K (uΦ a) ^ x.coeff a := by
              rw [hu_pow, map_prod]
              exact Finset.prod_congr rfl fun a _ ↦ map_zpow _ _ _
        _ = ∏ a : (ZMod m)ˣ,
              (∏ b : (ZMod m)ˣ, Q (a * b⁻¹) ^ (b : ZMod m).val) ^ x.coeff a :=
              Finset.prod_congr rfl fun a _ ↦ by rw [huΦ_ideal a]
        _ = (∏ c : (ZMod m)ˣ, Q c ^ y.coeff c) ^ m := prod_prod_pow_zpow_eq_pow Q hxy
    refine Units.ext (HasUniqueRoots.pow_left_injective (NeZero.ne m) ?_)
    simpa only [← Units.val_pow_eq_pow_val] using congrArg Units.val hpow
  · -- Conductor `m = 1`: `stickelbergerIdeal 1 = ⊥`, so `y = 0`.
    have hm1 : m = 1 := by have := NeZero.ne m; omega
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
      map_mul' := fun d₁ d₂ ↦ by
        simp only [map_mul, mul_zpow, Finset.prod_mul_distrib] }
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
      have htop : I = ⊤ := Ideal.isUnit_iff.mp hIu
      subst htop
      have h1 : (⟨⊤, mem_nonZeroDivisors_of_ne_zero hI0⟩ : (Ideal (𝓞 K))⁰) = 1 :=
        Subtype.ext Ideal.one_eq_top.symm
      rw [h1, map_one, map_one]
    | h₃ A P hA0 hP ih =>
      have : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
      rw [map_mul, Nat.coprime_mul_iff_left] at hI
      have hmul : (⟨P * A, mem_nonZeroDivisors_of_ne_zero hI0⟩ : (Ideal (𝓞 K))⁰) =
          ⟨P, mem_nonZeroDivisors_of_ne_zero hP.ne_zero⟩ *
            ⟨A, mem_nonZeroDivisors_of_ne_zero hA0⟩ :=
        (Submonoid.mk_mul_mk (Ideal (𝓞 K))⁰ P A _ _).symm
      rw [hmul, map_mul, map_mul, hprime P hI.1, ih hI.2 hA0, one_mul]
  -- Step 3: Represent `c` by an integral ideal `I` coprime to `(m)` (hence of norm coprime to `m`).
  have hact : act c = 1 := by
    have h𝔞_ne : (Ideal.span {(m : 𝓞 K)}) ≠ ⊥ := by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr (NeZero.ne m)
    have hfin : {P : Ideal (𝓞 K) | P.IsMaximal ∧ Ideal.span {(m : 𝓞 K)} ≤ P}.Finite :=
      Ideal.finite_setOfPred_isMaximal_and_le_of_ne_bot h𝔞_ne
    obtain ⟨I, hIu, hmk, hsup⟩ := ClassGroup.exists_mk_eq_and_sup_eq_top (K := K) hfin c
    have hI0 : I ≠ ⊥ := fun h0 ↦ by
      rw [h0, FractionalIdeal.coeIdeal_bot] at hIu
      exact hIu.ne_zero rfl
    have hIcop : (Ideal.absNorm I).Coprime m :=
      Ideal.absNorm_coprime_of_isCoprime_span_natCast (Ideal.isCoprime_iff_sup_eq.mpr hsup)
    have hc : c = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩ := by
      rw [← hmk, ← ClassGroup.mk_mk0 K]
      exact congrArg (ClassGroup.mk K) (Units.ext (by simp [FractionalIdeal.coe_mk0]))
    rw [hc]
    exact hideal I hIcop hI0
  exact hact

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
  have hT : T z = 0 := by
    refine TensorProduct.inductionOn (motive := fun w ↦ T w = 0) z (fun r c ↦ ?_)
      (fun u v hu hv ↦ by rw [map_add, hu, hv, add_zero])
    have hsum : ∑ a : (ZMod m)ˣ, x.coeff a • Additive.ofMul (g a (Additive.toMul c)) = 0 := by
      have hann := stickelbergerIdeal_annihilates m K x hx (Additive.toMul c)
      simpa only [ofMul_prod, ofMul_zpow, ofMul_one] using congrArg Additive.ofMul hann
    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul]
    calc
      ∑ a : (ZMod m)ˣ,
          (x.coeff a : R) • (r ⊗ₜ[ℤ] (g a).toAdditive.toAddMonoidHom.toIntLinearMap c)
          = ∑ a : (ZMod m)ˣ,
              r ⊗ₜ[ℤ] (x.coeff a • Additive.ofMul (g a (Additive.toMul c))) := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [TensorProduct.smul_tmul', smul_eq_mul, ← zsmul_eq_mul, TensorProduct.smul_tmul,
              AddMonoidHom.coe_toIntLinearMap, AddEquiv.coe_toAddMonoidHom,
              MulEquiv.toAdditive_apply_apply]
      _ = r ⊗ₜ[ℤ] (∑ a : (ZMod m)ˣ, x.coeff a • Additive.ofMul (g a (Additive.toMul c))) :=
            (TensorProduct.tmul_sum r _ _).symm
      _ = 0 := by rw [hsum, TensorProduct.tmul_zero]
  exact hT

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
    simp only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      pow_ite, zpow_one, zpow_zero, Finset.prod_ite_eq, Finset.mem_univ, ↓reduceIte, map_one,
      AlgEquiv.toRingEquiv_one, RingOfIntegers.mapRingEquiv_refl, ClassGroup.mulEquivHom_apply,
      ClassGroup.mulEquiv_refl, MulEquiv.refl_apply] at h
    exact h
  exact ⟨fun c₁ c₂ ↦ (htriv c₁).trans (htriv c₂).symm⟩

/-- Whenever `1 ∈ stickelbergerIdeal m`, every `m`-th cyclotomic extension of `ℚ` has class number
one. -/
theorem classNumber_eq_one_of_one_mem_stickelbergerIdeal (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (h1 : (1 : MonoidAlgebra ℤ (ZMod m)ˣ) ∈ stickelbergerIdeal m) :
    NumberField.classNumber K = 1 := by
  have : Subsingleton (ClassGroup (𝓞 K)) :=
    subsingleton_classGroup_of_one_mem_stickelbergerIdeal m K h1
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
