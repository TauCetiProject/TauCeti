/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
import TauCeti.NumberTheory.ArithmeticFunction.Convolution
import TauCeti.NumberTheory.DirichletCharacter.ArithmeticFunction
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Meromorphic
import TauCeti.NumberTheory.DirichletCharacter.PolynomialProduct
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.LSeries.Convolution
import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting
import TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# The Dedekind zeta function of a cyclotomic field

Let `F` be an `n`-th cyclotomic field over `ℚ` (`[IsCyclotomicExtension {n} ℚ F]` with
`[NeZero n]`). This file proves the cyclotomic factorization of the Dedekind zeta function `ζ_F` at
the local, coefficient, and convergent-series (`Re s > 1`) levels, and deduces the analytic residue
formula at `s = 1`.

For every rational prime `p`, write `n = p ^ k * m` with `p ∤ m` (canonically
`k = n.factorization p`, `m = ordCompl[p] n`). Every prime ideal `P` of `𝓞 F` above `p` has
residue degree `f = orderOf (p : ZMod m)` and hence absolute norm `p ^ f`
(`absNorm_eq_pow_orderOf`), and there are `g = φ(m) / f` such primes
(`card_primesOverFinset_eq_totient_div_orderOf`). On the character side,
`DirichletCharacter.prod_one_sub_C_primitiveCharacter_mul_X` gives
`∏ χ : DirichletCharacter R n, (1 - C (χ.primitiveCharacter p) * X) = (1 - X ^ f) ^ g`
for every integral domain `R` with enough roots of unity, handling ramified (`k > 0`), unramified
(`k = 0`), and `n % 4 = 2` levels uniformly.

Inverting in `PowerSeries R` identifies the product of geometric series at `p` with
`((mk 1).subst (X ^ f)) ^ g`. Passing through `ArithmeticFunction.ofPowerSeries p` matches the local
Euler factor of `normCoeff F 1` at `p ^ r` with the convolution product of the primitive characters
at `p ^ r`. Multiplicativity on both sides yields the coefficient identity over any domain `R` with
enough roots of unity, specializing over `ℂ` to
`normCoeff F 1 = ∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)`
(and likewise for any choice of primitive representatives).

Summing via `ArithmeticFunction.LSeriesHasSum_finset_prod` gives
`ζ_F(s) = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s` for `Re s > 1`
(canonical and arbitrary-primitive-representative forms), together with the imprimitive level-`n`
factorization carrying the deleted Euler factors
`∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * p ^ (-s))` on the left.
Letting `s → 1⁺` gives `dedekindZeta_residue F = ∏ χ ≠ 1, L(1, χ.primitiveCharacter)`.

## Main results

* `TauCeti.NumberField.absNorm_eq_pow_orderOf`: every prime above `p` in `𝓞 F` has norm `p ^ f`.
* `TauCeti.NumberField.card_primesOverFinset_eq_totient_div_orderOf`: the number of primes above `p`
  is `φ(m) / f`.
* `TauCeti.NumberField.prod_primesOverFinset_one_sub_absNorm_cpow`: local Euler factor identity at
  any rational prime `p`.
* `TauCeti.NumberField.dedekindZetaCoeff_prime_pow`: integer power-series formula for the number of
  ideals of norm `p ^ r`.
* `TauCeti.NumberField.toArithmeticFunction_dedekindZetaCoeff_eq_prod_primitiveCharacter`:
  coefficient-level cyclotomic factorization over any integral domain `R` with enough roots of
  unity.
* `TauCeti.NumberField.normCoeff_one_eq_prod_primitiveCharacter`: specialization to `normCoeff F 1`.
* `TauCeti.NumberField.normCoeff_one_eq_prod_of_isPrimitive`: coefficient factorization for any
  family of primitive characters inducing the level-`n` characters.
* `TauCeti.NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter`: convergent-series
  factorization `ζ_F(s) = ∏ χ, L(s, χ.primitiveCharacter)` on `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter`:
  separating the Riemann zeta factor on `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_eq_prod_LFunction_of_isPrimitive`: convergent-series
  factorization for arbitrary primitive representatives on `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_mul_prod_eq_prod_LFunction`: imprimitive level-`n` factorization
  on `Re s > 1`, together with `dedekindZeta_mul_prod_primesOver_eq_prod_LFunction` (via primes
  above `p ∣ n`) and `dedekindZeta_mul_prod_ite_eq_prod_LFunction` (for arbitrary primitive
  representatives).
* `TauCeti.NumberField.dedekindZeta_residue_eq_prod_LFunction_primitiveCharacter_one`: residue
  formula at `s = 1`.
* Local Euler factor checks for `ℚ(i)` (`n = 4`) at `p = 2` (ramified), `p = 3` (inert), and
  `p = 5` (split).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, Corollary 5.11.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4, Theorem 4.3.
* H. Davenport, *Multiplicative Number Theory*, Chapter 6.
* Built on Mathlib's `DirichletCharacter.LFunction` and `DirichletCharacter.LFunction_changeLevel`
  (by David Loeffler and Michael Stoll).
-/

public section

open Filter Ideal IsDedekindDomain NumberField TauCeti.IdealArithmeticFunction
open scoped ArithmeticFunction NumberField Topology

namespace TauCeti.NumberField

/-! ### Local norms and Euler factors in a cyclotomic field -/

variable {n : ℕ} {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]

/-- Every prime ideal of `𝓞 F` lying over a rational prime `p` has absolute norm
`p ^ orderOf (p : ZMod m)`, where `n = p ^ k * m` with `p ∤ m`. -/
theorem absNorm_eq_pow_orderOf {p k m : ℕ} (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m)
    (P : Ideal (𝓞 F)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    Ideal.absNorm P = p ^ orderOf (p : ZMod m) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {n} ℚ F
  rw [← P.pow_inertiaDeg p, ← inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P Gal(F/ℚ),
    inertiaDegIn_eq_orderOf hn hm]

/-- The number of prime ideals of `𝓞 F` above `p` is `φ(m) / orderOf (p : ZMod m)`, where
`n = p ^ k * m` with `p ∤ m`. -/
theorem card_primesOverFinset_eq_totient_div_orderOf {p k m : ℕ} (hp : p.Prime)
    (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    (primesOverFinset (span {(p : ℤ)}) (𝓞 F)).card = m.totient / orderOf (p : ZMod m) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hm
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hord_pos : 0 < orderOf (p : ZMod m) := by
    rw [← ZMod.coe_unitOfCoprime p hcop, orderOf_units]
    exact orderOf_pos _
  have hcard : (primesOverFinset (span {(p : ℤ)}) (𝓞 F)).card =
      (primesOver (span {(p : ℤ)}) (𝓞 F)).ncard := by
    rw [← coe_primesOverFinset hp0, Set.ncard_coe_finset]
  have hmul := ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul (K := F) hn hm
  rw [hcard, ← hmul, Nat.mul_div_cancel _ hord_pos]

/-- The local ideal-counting coefficient at a prime power `p ^ r` in an `n`-th cyclotomic field is
the `r`-th coefficient of `((mk 1).subst (X ^ f)) ^ (φ(m) / f)` in `PowerSeries ℤ`, where
`n = p ^ k * m` with `p ∤ m` and `f = orderOf (p : ZMod m)`. -/
theorem dedekindZetaCoeff_prime_pow {p k m : ℕ} (hp : p.Prime) (hn : n = p ^ k * m)
    (hm : ¬ p ∣ m) (r : ℕ) :
    (dedekindZetaCoeff F (p ^ r) : ℤ) =
      PowerSeries.coeff r
        (((PowerSeries.mk 1 : PowerSeries ℤ).subst (PowerSeries.X ^ orderOf (p : ZMod m))) ^
          (m.totient / orderOf (p : ZMod m))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hm
  have hord_pos : 0 < orderOf (p : ZMod m) := by
    rw [← ZMod.coe_unitOfCoprime p hcop, orderOf_units]
    exact orderOf_pos _
  let f : ℕ := orderOf (p : ZMod m)
  let g : ℕ := m.totient / f
  have hfactor (Q : HeightOneSpectrum (𝓞 F)) (hQ : Q ∈ primesOverHeightOneFinset F p) :
      localArithmeticFactor (1 : IdealArithmeticFunction F) Q =
        ArithmeticFunction.ofPowerSeries p
          ((PowerSeries.mk 1 : PowerSeries ℂ).subst (PowerSeries.X ^ f)) := by
    have hmem := mem_primesOverHeightOneFinset.mp hQ
    have := hmem.1
    have := hmem.2
    have hnorm : Ideal.absNorm Q.asIdeal = p ^ f := absNorm_eq_pow_orderOf (F := F) hp hn hm _
    have hps : localPowerSeries (1 : IdealArithmeticFunction F) Q =
        (PowerSeries.mk 1 : PowerSeries ℂ) := by
      ext j
      simp [coeff_localPowerSeries]
    rw [localArithmeticFactor_def, hnorm, hps, ArithmeticFunction.ofPowerSeries_pow p hord_pos.ne']
  have hℂ : (dedekindZetaCoeff F (p ^ r) : ℂ) =
      PowerSeries.coeff r
        (((PowerSeries.mk 1 : PowerSeries ℂ).subst (PowerSeries.X ^ f)) ^ g) := by
    have hne : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
    calc (dedekindZetaCoeff F (p ^ r) : ℂ)
        = normCoeff F 1 (p ^ r) := by rw [normCoeff_one_apply, ite_eq_right hne]
      _ = (∏ Q ∈ primesOverHeightOneFinset F p,
            localArithmeticFactor (1 : IdealArithmeticFunction F) Q) (p ^ r) :=
          normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor isMultiplicative_one hp
            (primesOverHeightOneFinset F p) mem_primesOverHeightOneFinset_of_natCast_mem r
      _ = ((ArithmeticFunction.ofPowerSeries p
            ((PowerSeries.mk 1 : PowerSeries ℂ).subst (PowerSeries.X ^ f))) ^ g) (p ^ r) := by
          rw [Finset.prod_congr rfl hfactor, Finset.prod_const, card_primesOverHeightOneFinset,
            card_primesOverFinset_eq_totient_div_orderOf (F := F) hp hn hm]
      _ = (ArithmeticFunction.ofPowerSeries p
            (((PowerSeries.mk 1 : PowerSeries ℂ).subst (PowerSeries.X ^ f)) ^ g)) (p ^ r) :=
          congrArg (fun a : ArithmeticFunction ℂ ↦ a (p ^ r))
            (map_pow (ArithmeticFunction.ofPowerSeries p) _ g).symm
      _ = PowerSeries.coeff r
            (((PowerSeries.mk 1 : PowerSeries ℂ).subst (PowerSeries.X ^ f)) ^ g) :=
          ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt _ r
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_natCast, hℂ]
  have hmap : PowerSeries.map (Int.castRingHom ℂ)
      (((PowerSeries.mk 1 : PowerSeries ℤ).subst (PowerSeries.X ^ f)) ^ g) =
        ((PowerSeries.mk 1 : PowerSeries ℂ).subst (PowerSeries.X ^ f)) ^ g := by
    rw [map_pow, ← PowerSeries.expand_apply f hord_pos.ne',
      ← PowerSeries.expand_apply f hord_pos.ne', PowerSeries.map_expand]
    congr 2; ext j; simp
  rw [← hmap, PowerSeries.coeff_map, Int.coe_castRingHom]

variable [NeZero n]

/-- **Local Euler factor identity at a rational prime `p`.** At every prime `p` (ramified or
unramified), the product of `1 - N(P) ^ (-s)` over the primes `P` of `𝓞 F` above `p` equals the
product of `1 - χ.primitiveCharacter p * p ^ (-s)` over all complex Dirichlet characters modulo
`n`. -/
theorem prod_primesOverFinset_one_sub_absNorm_cpow {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ∏ P ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 F), (1 - (Ideal.absNorm P : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n,
        (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) := by
  have : NeZero ((Monoid.exponent (ZMod n)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have : Fact p.Prime := ⟨hp⟩
  set k := n.factorization p
  set m := ordCompl[p] n
  have hn : n = p ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (NeZero.ne n)
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  rw [DirichletCharacter.prod_one_sub_primitiveCharacter_mul hp hn hm]
  rw [← card_primesOverFinset_eq_totient_div_orderOf (F := F) hp hn hm, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun P hP ↦ ?_
  have hmem : P ∈ primesOver (span {(p : ℤ)}) (𝓞 F) :=
    (mem_primesOverFinset_iff hp0 (𝓞 F)).mp hP
  have := hmem.1
  have := hmem.2
  rw [absNorm_eq_pow_orderOf (F := F) hp hn hm P, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-! ### Coefficient-level cyclotomic factorization -/

/-- **Coefficient-level cyclotomic factorization over a general domain.** For any integral domain
`R` with enough roots of unity for `(ZMod n)ˣ`, the arithmetic function of ideal-norm counts of an
`n`-th cyclotomic field equals the Dirichlet-convolution product of the primitive characters
inducing all `R`-valued Dirichlet characters modulo `n`. -/
theorem toArithmeticFunction_dedekindZetaCoeff_eq_prod_primitiveCharacter
    (R : Type*) [CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)] :
    toArithmeticFunction (fun k ↦ (dedekindZetaCoeff F k : R)) =
      ∏ χ : DirichletCharacter R n, toArithmeticFunction (χ.primitiveCharacter ·) := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_toArithmeticFunction_dedekindZetaCoeff F R) _
    (ArithmeticFunction.IsMultiplicative.finset_prod fun χ _ ↦
      DirichletCharacter.isMultiplicative_toArithmeticFunction χ.primitiveCharacter)).mpr
      fun p r hp ↦ ?_
  set k := n.factorization p
  set m := ordCompl[p] n
  have hn : n = p ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (NeZero.ne n)
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hm
  have hord_pos : 0 < orderOf (p : ZMod m) := by
    rw [← ZMod.coe_unitOfCoprime p hcop, orderOf_units]
    exact orderOf_pos _
  have hne : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  have hmap : PowerSeries.map (Int.castRingHom R)
      (((PowerSeries.mk 1 : PowerSeries ℤ).subst (PowerSeries.X ^ orderOf (p : ZMod m))) ^
        (m.totient / orderOf (p : ZMod m))) =
      ((PowerSeries.mk 1 : PowerSeries R).subst (PowerSeries.X ^ orderOf (p : ZMod m))) ^
        (m.totient / orderOf (p : ZMod m)) := by
    rw [map_pow, ← PowerSeries.expand_apply (orderOf (p : ZMod m)) hord_pos.ne',
      ← PowerSeries.expand_apply (orderOf (p : ZMod m)) hord_pos.ne', PowerSeries.map_expand]
    congr 2; ext j; simp
  have hlhs : toArithmeticFunction (fun j ↦ (dedekindZetaCoeff F j : R)) (p ^ r) =
      PowerSeries.coeff r
        (((PowerSeries.mk 1 : PowerSeries R).subst (PowerSeries.X ^ orderOf (p : ZMod m))) ^
          (m.totient / orderOf (p : ZMod m))) := by
    rw [toArithmeticFunction, ArithmeticFunction.coe_mk, ite_eq_right hne]
    have hZ := congrArg (Int.castRingHom R) (dedekindZetaCoeff_prime_pow (F := F) hp hn hm r)
    rw [map_natCast, ← PowerSeries.coeff_map, hmap] at hZ
    simpa only [Int.coe_castRingHom] using hZ
  rw [hlhs, ← DirichletCharacter.prod_mk_pow_primitiveCharacter (R := R) hp hn hm,
    ← ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt _ r, map_prod]
  refine ArithmeticFunction.finset_prod_apply_prime_pow_congr hp fun χ _ j _ ↦ ?_
  rw [ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt, PowerSeries.coeff_mk,
    DirichletCharacter.toArithmeticFunction_apply_pow _ hp.ne_zero]

/-- **Coefficient-level cyclotomic factorization for `normCoeff F 1`.** Over `ℂ`, the regrouped
trivial ideal function of an `n`-th cyclotomic field equals the Dirichlet-convolution product of
the primitive characters modulo `n`. -/
theorem normCoeff_one_eq_prod_primitiveCharacter :
    normCoeff F 1 =
      ∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·) := by
  have : NeZero ((Monoid.exponent (ZMod n)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have h := toArithmeticFunction_dedekindZetaCoeff_eq_prod_primitiveCharacter (n := n) (F := F) ℂ
  convert h using 1
  ext k
  by_cases hk : k = 0
  · simp [hk, toArithmeticFunction]
  · simp [normCoeff_one_apply, hk, toArithmeticFunction]

/-- **Coefficient-level cyclotomic factorization for arbitrary primitive representatives.** For any
choice of primitive `χ' χ` of level `m χ ∣ n` inducing `χ`, `normCoeff F 1` is their
Dirichlet-convolution product. -/
theorem normCoeff_one_eq_prod_of_isPrimitive
    (m : DirichletCharacter ℂ n → ℕ) (hdvd : ∀ χ, m χ ∣ n)
    (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
    (hprim : ∀ χ, (χ' χ).IsPrimitive)
    (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ) :
    normCoeff F 1 = ∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ' χ ·) := by
  rw [normCoeff_one_eq_prod_primitiveCharacter (n := n) (F := F)]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  ext k
  by_cases hk : k = 0
  · simp [hk, toArithmeticFunction]
  · simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, hk, ↓reduceIte]
    exact ((hprim χ).apply_natCast_eq_primitiveCharacter (hdvd χ) (hind χ) k).symm

/-! ### Convergent-series factorization on `Re s > 1` -/

/-- **Cyclotomic factorization of `dedekindZeta` on `Re s > 1`.** For `1 < s.re`, the Dedekind
zeta function of an `n`-th cyclotomic field equals the product of the L-functions of the primitive
characters inducing all complex Dirichlet characters modulo `n`. -/
theorem dedekindZeta_eq_prod_LFunction_primitiveCharacter {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta F s = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZeta_eq_LSeries_normCoeff_one, normCoeff_one_eq_prod_primitiveCharacter (n := n)]
  have hsum := ArithmeticFunction.LSeriesHasSum_finset_prod
    (s := (Finset.univ : Finset (DirichletCharacter ℂ n)))
    (f := fun χ ↦ toArithmeticFunction (χ.primitiveCharacter ·))
    (a := fun χ ↦ χ.primitiveCharacter.LFunction s) (z := s)
    fun χ _ ↦ DirichletCharacter.LSeriesHasSum_toArithmeticFunction χ.primitiveCharacter hs
  exact hsum.LSeries_eq

/-- **Cyclotomic factorization with `riemannZeta` separated**, on `Re s > 1`. -/
theorem dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter
    [DecidableEq (DirichletCharacter ℂ n)] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta F s = riemannZeta s *
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction s := by
  rw [dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) (F := F) hs,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ n)),
    DirichletCharacter.LFunction_primitiveCharacter_one]

/-- **Cyclotomic factorization on `Re s > 1` for arbitrary primitive representatives.** -/
theorem dedekindZeta_eq_prod_LFunction_of_isPrimitive
    (m : DirichletCharacter ℂ n → ℕ) (hdvd : ∀ χ, m χ ∣ n)
    (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
    (hprim : ∀ χ, (χ' χ).IsPrimitive)
    (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta F s =
      ∏ χ : DirichletCharacter ℂ n,
        haveI : NeZero (m χ) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (hdvd χ)⟩
        (χ' χ).LFunction s := by
  rw [dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) (F := F) hs]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  have : NeZero (m χ) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (hdvd χ)⟩
  exact (congrFun ((hprim χ).LFunction_eq_primitiveCharacter (hdvd χ) (hind χ)) s).symm

/-- **Imprimitive cyclotomic factorization on `Re s > 1` (canonical primitive characters).** -/
theorem dedekindZeta_mul_prod_eq_prod_LFunction {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta F s *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  rw [dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) (F := F) hs,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [← DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (Or.inr hs1), χ.changeLevel_primitiveCharacter]

/-- **Imprimitive cyclotomic factorization on `Re s > 1` (Euler factors at primes above `n`).**
Multiplying `ζ_F(s)` by `1 - N(P) ^ (-s)` over all primes `P` of `𝓞 F` lying over prime divisors
of `n` gives the product of all level-`n` Dirichlet L-functions. -/
theorem dedekindZeta_mul_prod_primesOver_eq_prod_LFunction {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta F s *
        ∏ p ∈ n.primeFactors, ∏ P ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 F),
          (1 - (Ideal.absNorm P : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  rw [← dedekindZeta_mul_prod_eq_prod_LFunction (n := n) (F := F) hs]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun p hp ↦
    prod_primesOverFinset_one_sub_absNorm_cpow (n := n) (F := F)
      (Nat.prime_of_mem_primeFactors hp) s

/-- **Imprimitive cyclotomic factorization on `Re s > 1` (arbitrary primitive representatives).** -/
theorem dedekindZeta_mul_prod_ite_eq_prod_LFunction
    (m : DirichletCharacter ℂ n → ℕ) (hdvd : ∀ χ, m χ ∣ n)
    (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
    (hprim : ∀ χ, (χ' χ).IsPrimitive)
    (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta F s *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (if p ∣ m χ then (1 : ℂ) else 1 - χ' χ (p : ZMod (m χ)) * (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  rw [← dedekindZeta_mul_prod_eq_prod_LFunction (n := n) (F := F) hs]
  congr 1
  refine Finset.prod_congr rfl fun χ _ ↦ Finset.prod_congr rfl fun p hp ↦ ?_
  rw [DirichletCharacter.ite_dvd_one_sub_mul (χ' χ) (Nat.prime_of_mem_primeFactors hp),
    (hprim χ).apply_natCast_eq_primitiveCharacter (hdvd χ) (hind χ) p]

/-! ### The residue formula at `s = 1` -/

/-- **The residue of the Dedekind zeta function of a cyclotomic field.** Mathlib's
`dedekindZeta_residue F`, the limit of `(s - 1) ζ_F(s)` as `s → 1⁺`, equals
`∏ χ ≠ 1, L(1, χ.primitiveCharacter)`. -/
theorem dedekindZeta_residue_eq_prod_LFunction_primitiveCharacter_one
    [DecidableEq (DirichletCharacter ℂ n)] :
    (dedekindZeta_residue F : ℂ) =
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction 1 := by
  have hζ : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 1 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by simpa using (Set.mem_Ioi.mp hs).ne')
  have hcont : Continuous (fun s : ℝ ↦
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction s) := by
    refine continuous_finsetProd _ fun χ hχ ↦ ?_
    have hne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    have hprim_ne : χ.primitiveCharacter ≠ 1 := fun h1 ↦ hne <| by
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    exact (DirichletCharacter.differentiable_LFunction hprim_ne).continuous.comp
      Complex.continuous_ofReal
  have hL : Tendsto (fun s : ℝ ↦
        ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
          χ.primitiveCharacter.LFunction s)
      (𝓝[>] 1)
      (𝓝 (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction 1)) :=
    (hcont.tendsto' 1 _ (by simp)).mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta F s) (𝓝[>] 1)
      (𝓝 (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction 1)) := by
    have hmul := hζ.mul hL
    rw [one_mul] at hmul
    refine hmul.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
    dsimp only
    rw [dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter (n := n) (F := F)
      (s := (s : ℂ)) (by simpa using hs), mul_assoc]
  exact tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT F) hF

/-! ### Worked local Euler factors for `ℚ(i)` (`n = 4`) -/

section WorkedLocalChecks

variable {G : Type*} [Field G] [NumberField G] [IsCyclotomicExtension {4} ℚ G]

/-- **Local Euler factor check for `ℚ(i)` at ramified `p = 2`.** There is a single prime of norm
`2` above `2`, so the local factor is `1 - 2 ^ (-s)`. -/
theorem prod_primesOverFinset_four_two (s : ℂ) :
    ∏ P ∈ primesOverFinset (span {(2 : ℤ)}) (𝓞 G), (1 - (Ideal.absNorm P : ℂ) ^ (-s)) =
      1 - (2 : ℂ) ^ (-s) := by
  have : NeZero ((Monoid.exponent (ZMod 4)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hn : (4 : ℕ) = 2 ^ 2 * 1 := by norm_num
  have h1 : ((2 : ℕ) : ZMod 1) = 1 := Subsingleton.elim _ _
  have := prod_primesOverFinset_one_sub_absNorm_cpow (n := 4) (F := G) Nat.prime_two s
  rw [Nat.cast_ofNat] at this
  rw [this, DirichletCharacter.prod_one_sub_primitiveCharacter_mul Nat.prime_two hn
    Nat.prime_two.not_dvd_one, h1, orderOf_one]
  simp

/-- **Local Euler factor check for `ℚ(i)` at inert `p = 3`.** There is a single prime of norm `9`
above `3`, matching `(1 - 3 ^ (-s))(1 + 3 ^ (-s)) = 1 - 9 ^ (-s)`. -/
theorem prod_primesOverFinset_four_three (s : ℂ) :
    ∏ P ∈ primesOverFinset (span {(3 : ℤ)}) (𝓞 G), (1 - (Ideal.absNorm P : ℂ) ^ (-s)) =
      1 - (9 : ℂ) ^ (-s) := by
  have : NeZero ((Monoid.exponent (ZMod 4)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hn : (4 : ℕ) = 3 ^ 0 * 4 := by norm_num
  have hord : orderOf ((3 : ℕ) : ZMod 4) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have h9 : (9 : ℂ) ^ (-s) = ((3 : ℂ) ^ (-s)) ^ 2 := by
    have h9eq : (9 : ℂ) = ((3 ^ 2 : ℕ) : ℂ) := by norm_num
    rw [h9eq, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
    simp
  have ht4 : (4 : ℕ).totient = 2 := by decide
  have hres := prod_primesOverFinset_one_sub_absNorm_cpow (n := 4) (F := G) Nat.prime_three s
  rw [Nat.cast_ofNat] at hres
  rw [hres, DirichletCharacter.prod_one_sub_primitiveCharacter_mul Nat.prime_three hn (by decide),
    hord, ht4]
  simp only [Nat.cast_ofNat]
  norm_num [h9]

/-- **Local Euler factor check for `ℚ(i)` at split `p = 5`.** There are two primes of norm `5`
above `5`, so the local factor is `(1 - 5 ^ (-s)) ^ 2`. -/
theorem prod_primesOverFinset_four_five (s : ℂ) :
    ∏ P ∈ primesOverFinset (span {(5 : ℤ)}) (𝓞 G), (1 - (Ideal.absNorm P : ℂ) ^ (-s)) =
      (1 - (5 : ℂ) ^ (-s)) ^ 2 := by
  have : NeZero ((Monoid.exponent (ZMod 4)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hp5 : Nat.Prime 5 := by decide
  have hn : (4 : ℕ) = 5 ^ 0 * 4 := by norm_num
  have h5 : ((5 : ℕ) : ZMod 4) = 1 := by decide
  have ht4 : (4 : ℕ).totient = 2 := by decide
  have hres := prod_primesOverFinset_one_sub_absNorm_cpow (n := 4) (F := G) hp5 s
  rw [Nat.cast_ofNat] at hres
  rw [hres, DirichletCharacter.prod_one_sub_primitiveCharacter_mul hp5 hn (by decide),
    h5, orderOf_one, ht4]
  simp only [Nat.cast_ofNat]
  norm_num

end WorkedLocalChecks

end TauCeti.NumberField
