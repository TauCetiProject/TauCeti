/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
public import TauCeti.RingTheory.FormalGroup.LazardRing.NSMul
public import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial
-- Proof-only: quotient-ring equivalences, tensor products of polynomial rings and quotients,
-- flat base change of regular sequences, prime ideals in localizations, and triangular polynomial
-- automorphisms.
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.Algebra.MvPolynomial.Variables
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Landweber's generators, quotient presentations, and regularity of the height ideals

In chromatic homotopy theory and the algebraic geometry of formal groups, the invariant ideals of
the Lazard ring `L ≅ MU_*` at a prime `p` are governed by the height ideals
`I_n = (p, v₁, …, v_(n-1))` of the universal formal group law. Their primality and the regularity
of the generating sequence `p, v₁, …, v_(n-1)` form the core algebraic input to Landweber's
invariant prime ideal and filtration theorems for `(MU_*, MU_* MU)`-comodules, as well as to
Landweber's exact functor theorem, where regularity of `p, v₁, …, v_(n-1)` is the exactness
condition and shows in particular that `L`, flat `L`-algebras (such as `L[b₁, b₂, …]`), and the
`p`-localization `L_(p) = MU_(p)*` are Landweber exact.

First, for every `p : ℕ`, homogeneity of the coefficients of `[p]_F(X)` immediately implies that
all height ideals `I_n` and their union `I_∞ = ⨆ n, I_n` are homogeneous ideals of `L`
(`TauCeti.LazardRing.isHomogeneous_heightIdeal`,
`TauCeti.LazardRing.isHomogeneous_iSup_heightIdeal`).

Now let `p` be prime. By Lazard's theorem `L ≃ ℤ[x₁, x₂, …]` with `xₙ` in degree `2n`
(`TauCeti.LazardRing.mvPolynomialEquiv`), and by the first-order computation of the `p`-series
(`TauCeti.LazardRing.coeff_prime_pow_nsmulSeries_sub_smul_generator_mem_sq`), for `n + 1 = pʲ` with
`j ≥ 1` the coefficient `vⱼ = [X^(pʲ)] [p]_F(X)` satisfies

  `vⱼ ≡ (p^n - 1) • xₙ  (mod I²)`,

where `I` is the augmentation ideal of `L`. Setting `x'ₙ = vⱼ` when `n + 1 = pʲ` and `x'ₙ = xₙ`
otherwise (`TauCeti.LazardRing.landweberGenerator`), each `x'ₙ` is homogeneous of degree `2n` and
differs from `cₙ • X n` in `ℤ[x₁, x₂, …]` by a polynomial involving only variables `X k` with
`k < n` (`TauCeti.LazardRing.lt_of_mem_vars_mvPolynomialEquiv_symm_sub_smul_X`), where
`cₙ = p^n - 1` for `n + 1 = pʲ` and `cₙ = 1` otherwise.

Over any commutative ring `R` in which `p^(pʲ - 1) - 1` is a unit for every `j ≥ 1` — in particular
over any local ring in which `p` is not a unit (such as `ℤ_(p)`) and over any ring in which
`(p : R) = 0` — this triangular substitution is an automorphism of `R[x₁, x₂, …]`
(`MvPolynomial.bijective_aeval_of_vars_sub_smul_X_lt`), so `R ⊗[ℤ] L` is the polynomial algebra
`R[x'₁, x'₂, …]` (`TauCeti.LazardRing.landweberMvPolynomialEquivTensor`).

Specializing to `R = ZMod p` identifies `L ⧸ I₁ = L ⧸ (p)` with `(ZMod p)[x'₁, x'₂, …]` sending
`x'ₖ` to `X k` (`TauCeti.LazardRing.quotientHeightIdealOneEquiv`). Since `I_n = (p, v₁, …, v_(n-1))`
for `n ≥ 1`, passing to the quotient kills precisely the variables `X k` with `k + 1 = pʲ` for
`1 ≤ j < n`, giving polynomial ring presentations of `L ⧸ I_n` for all `n ≥ 1` and of `L ⧸ I_∞`
(`TauCeti.LazardRing.quotientHeightIdealEquiv`,
`TauCeti.LazardRing.quotientISupHeightIdealEquiv`).

Since `I₀ = 0` is prime because `L` is an integral domain, and the polynomial quotients `L ⧸ I_n`
(`n ≥ 1`) and `L ⧸ I_∞` over `ZMod p` are integral domains, these presentations imply that:
* all height ideals `I_n` (`n ≥ 0`) and their union `I_∞` are prime ideals of `L`;
* `v_n ∉ I_n`, so the chain `0 = I₀ < I₁ < I₂ < … < I_∞ < L` is strictly increasing;
* for every `n`, the sequence `p, v₁, …, v_(n-1)` — as well as any sequence of lifts modulo
  `I₀, …, I_(n-1)`, and the `p`-series coefficients in any isomorphic coordinate — is a regular
  sequence on `L`, remains weakly regular in any flat `L`-algebra `S` (and regular whenever
  `I_n S ≠ ⊤`), and in particular is regular in any localization of `L` disjoint from `I_n` (such as
  the `p`-localization `L_(p) = MU_(p)*`).

## Main definitions

* `TauCeti.LazardRing.landweberGenerator`: the `p`-adapted generator `x'ₙ ∈ L₂ₙ`, equal to `vⱼ`
  when `n + 1 = pʲ` and to `xₙ` otherwise.
* `TauCeti.LazardRing.landweberMvPolynomialEquivTensor`: the isomorphism
  `MvPolynomial ℕ+ R ≃ₐ[R] R ⊗[ℤ] L` sending `X n` to `1 ⊗ₜ x'ₙ`, when `p^(pʲ - 1) - 1` is a unit
  in `R` for all `j ≠ 0`.
* `TauCeti.LazardRing.quotientHeightIdealOneEquiv`: `(L ⧸ I₁) ≃+* MvPolynomial ℕ+ (ZMod p)`.
* `TauCeti.LazardRing.quotientHeightIdealEquiv`: for `n ≥ 1`,
  `(L ⧸ I_n) ≃+* MvPolynomial {k : ℕ+ // ∀ j < n, (k : ℕ) + 1 ≠ p ^ j} (ZMod p)`.
* `TauCeti.LazardRing.quotientISupHeightIdealEquiv`:
  `(L ⧸ ⨆ n, I_n) ≃+* MvPolynomial {k : ℕ+ // ∀ j, (k : ℕ) + 1 ≠ p ^ j} (ZMod p)`.

## Main results

* `TauCeti.LazardRing.isHomogeneous_heightIdeal` and
  `TauCeti.LazardRing.isHomogeneous_iSup_heightIdeal`: `I_n` and `⨆ n, I_n` are homogeneous ideals.
* `TauCeti.LazardRing.isPrime_heightIdeal` and `TauCeti.LazardRing.isPrime_iSup_heightIdeal`:
  `I_n` (`n ≥ 0`) and `⨆ n, I_n` are prime ideals of `L`.
* `TauCeti.LazardRing.coeff_nsmulSeries_notMem_heightIdeal`,
  `TauCeti.LazardRing.heightIdeal_strictMono`, and `TauCeti.LazardRing.heightIdeal_lt_iSup`:
  `v_n ∉ I_n` and `I₀ < I₁ < I₂ < … < ⨆ m, I_m`.
* `TauCeti.LazardRing.isRegular_ofFn_of_sub_mem_heightIdeal`,
  `TauCeti.LazardRing.isRegular_ofFn_coeff_nsmulSeries`, and
  `TauCeti.LazardRing.isRegular_ofFn_coeff_nsmulSeries_of_iso`: `p, v₁, …, v_(n-1)` (and any choice
  of lifts modulo the preceding height ideals, or in any isomorphic coordinate) is a regular
  sequence on `L`.
* `TauCeti.LazardRing.isWeaklyRegular_ofFn_of_sub_mem_heightIdeal_of_flat`,
  `TauCeti.LazardRing.isRegular_ofFn_of_sub_mem_heightIdeal_of_flat`, and
  `TauCeti.LazardRing.isRegular_ofFn_of_sub_mem_heightIdeal_of_isLocalization`: weak regularity and
  regularity of lifts of `p, v₁, …, v_(n-1)` in flat `L`-algebras and localizations disjoint from
  `I_n`, together with `TauCeti.LazardRing.disjoint_algebraMapSubmonoid_primeCompl_iSup_heightIdeal`
  covering `p`-localization.

## References

* P. S. Landweber, *Annihilator ideals and primitive elements in complex bordism*, Illinois J.
  Math. 17 (1973), 273–284.
* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Chapter 4 and
  Appendix A2.1.
* J. F. Adams, *Stable Homotopy and Generalised Homology*, Part II, §§6–7.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.LazardRing

/-! ### Homogeneity of the height ideals -/

/-- The height ideals `I_n` of the universal formal group law over the Lazard ring are homogeneous
ideals, since each coefficient of `[p]_F(X)` is homogeneous. -/
theorem isHomogeneous_heightIdeal (p n : ℕ) :
    (formalGroup.heightIdeal p n).IsHomogeneous grading := by
  rw [formalGroup.heightIdeal_def]
  refine Ideal.homogeneous_span grading _ ?_
  rintro _ ⟨k, -, rfl⟩
  exact ⟨2 * (k - 1), coeff_nsmulSeries_mem_grading p k⟩

/-- The union `I_∞ = ⨆ n, I_n` of the height ideals over the Lazard ring is a homogeneous ideal. -/
theorem isHomogeneous_iSup_heightIdeal (p : ℕ) :
    (⨆ n, formalGroup.heightIdeal p n).IsHomogeneous grading :=
  Ideal.IsHomogeneous.iSup (isHomogeneous_heightIdeal p)

/-! ### Landweber's `p`-adapted generators -/

open scoped Classical in
/-- **Landweber's `p`-adapted generator** of the Lazard ring in degree `2n`: the coefficient
`vⱼ = [X^(pʲ)] [p]_F(X)` when `(n : ℕ) + 1 = p ^ j` for some `j`, and Lazard's generator
`xₙ = TauCeti.LazardRing.generator n` otherwise. -/
def landweberGenerator (p : ℕ) (n : ℕ+) : LazardRing :=
  if ∃ j, (n : ℕ) + 1 = p ^ j then
    PowerSeries.coeff ((n : ℕ) + 1) (formalGroup.nsmulSeries p)
  else
    generator n

/-- When `(n : ℕ) + 1 = p ^ j`, Landweber's generator `x'ₙ` is the coefficient `vⱼ` of `X^(pʲ)` in
the `p`-series of the universal formal group law. -/
theorem landweberGenerator_of_add_one_eq_pow {p j : ℕ} {n : ℕ+} (hn : (n : ℕ) + 1 = p ^ j) :
    landweberGenerator p n = PowerSeries.coeff (p ^ j) (formalGroup.nsmulSeries p) := by
  simp [landweberGenerator, hn]

/-- For `p > 1` and `j ≠ 0`, Landweber's generator at index `p ^ j - 1` is `vⱼ`. -/
@[simp]
theorem landweberGenerator_pow_sub_one {p : ℕ} (hp : 1 < p) {j : ℕ} (hj : j ≠ 0) :
    landweberGenerator p ⟨p ^ j - 1, Nat.sub_pos_of_lt (Nat.one_lt_pow hj hp)⟩ =
      PowerSeries.coeff (p ^ j) (formalGroup.nsmulSeries p) := by
  refine landweberGenerator_of_add_one_eq_pow ?_
  have hlt : 1 < p ^ j := Nat.one_lt_pow hj hp
  simp [Nat.sub_add_cancel hlt.le]

/-- Away from indices with `(n : ℕ) + 1 = p ^ j`, Landweber's generator `x'ₙ` agrees with Lazard's
generator `xₙ`. -/
theorem landweberGenerator_of_forall_add_one_ne_pow {p : ℕ} {n : ℕ+}
    (hn : ∀ j, (n : ℕ) + 1 ≠ p ^ j) :
    landweberGenerator p n = generator n := by
  simp [landweberGenerator, hn]

/-- Landweber's generator `x'ₙ` has degree `2n`. -/
theorem landweberGenerator_mem_grading (p : ℕ) (n : ℕ+) :
    landweberGenerator p n ∈ grading (2 * (n : ℕ)) := by
  classical
  dsimp only [landweberGenerator]
  split_ifs with h
  · simpa using coeff_nsmulSeries_mem_grading p ((n : ℕ) + 1)
  · exact generator_mem_grading n

/-- Landweber's generator `x'ₙ` lies in the augmentation ideal of the Lazard ring. -/
theorem landweberGenerator_mem_augmentationIdeal (p : ℕ) (n : ℕ+) :
    landweberGenerator p n ∈ augmentationIdeal := by
  classical
  dsimp only [landweberGenerator]
  split_ifs with h
  · exact coeff_nsmulSeries_mem_augmentationIdeal p (by have := n.pos; omega)
  · exact generator_mem_augmentationIdeal n

open scoped Classical in
/-- The leading coefficient relating `landweberGenerator p n` to `generator n` modulo `I²`. -/
private def landweberDiagCoeff (p : ℕ) (n : ℕ+) : ℤ :=
  if ∃ j, (n : ℕ) + 1 = p ^ j then (p : ℤ) ^ (n : ℕ) - 1 else 1

private theorem landweberGenerator_sub_smul_generator_mem_sq {p : ℕ} (hp : p.Prime) (n : ℕ+) :
    landweberGenerator p n - landweberDiagCoeff p n • generator n ∈ augmentationIdeal ^ 2 := by
  classical
  by_cases h : ∃ j, (n : ℕ) + 1 = p ^ j
  · obtain ⟨j, hj⟩ := h
    rw [landweberGenerator_of_add_one_eq_pow hj]
    have hex : ∃ i, (n : ℕ) + 1 = p ^ i := ⟨j, hj⟩
    simpa only [landweberDiagCoeff, hex, ↓reduceIte] using
      coeff_prime_pow_nsmulSeries_sub_smul_generator_mem_sq hp hj
  · have h' : ∀ j, (n : ℕ) + 1 ≠ p ^ j := fun j hj ↦ h ⟨j, hj⟩
    rw [landweberGenerator_of_forall_add_one_ne_pow h']
    simp [landweberDiagCoeff, h]

/-! ### Base-changed polynomial presentations -/

section BaseChange

private theorem bijective_aeval_map_landweberGenerator {p : ℕ} (hp : p.Prime) {R : Type*}
    [CommRing R] (hu : ∀ j ≠ 0, IsUnit ((p : R) ^ (p ^ j - 1) - 1)) :
    Function.Bijective
      (MvPolynomial.aeval (R := R) fun n : ℕ+ ↦
        MvPolynomial.map (Int.castRingHom R)
          (mvPolynomialEquiv.symm (landweberGenerator p n))) := by
  refine MvPolynomial.bijective_aeval_of_vars_sub_smul_X_lt
    (c := fun n ↦ (landweberDiagCoeff p n : R)) (fun n ↦ ?_) (fun n k hk ↦ ?_)
  · classical
    dsimp only [landweberDiagCoeff]
    split_ifs with h
    · obtain ⟨j, hj⟩ := h
      have hj0 : j ≠ 0 := by rintro rfl; have := n.pos; simp at hj
      have hn : (n : ℕ) = p ^ j - 1 := by omega
      simpa [hn] using hu j hj0
    · simp
  · have hsub :
        MvPolynomial.map (Int.castRingHom R) (mvPolynomialEquiv.symm (landweberGenerator p n)) -
          (landweberDiagCoeff p n : R) • MvPolynomial.X n =
        MvPolynomial.map (Int.castRingHom R)
          (mvPolynomialEquiv.symm (landweberGenerator p n) -
            landweberDiagCoeff p n • MvPolynomial.X n) := by
      simp [Algebra.smul_def]
    rw [hsub] at hk
    exact lt_of_mem_vars_mvPolynomialEquiv_symm_sub_smul_X (landweberGenerator_mem_grading p n)
      (landweberGenerator_sub_smul_generator_mem_sq hp n) (MvPolynomial.vars_map _ _ hk)

/-- **Landweber's polynomial presentation after base change.** Over any commutative ring `R` in
which `p ^ (p ^ j - 1) - 1` is a unit for every `j ≠ 0`, `R ⊗[ℤ] LazardRing` is the polynomial
`R`-algebra on the elements `1 ⊗ₜ landweberGenerator p n`. -/
def landweberMvPolynomialEquivTensor {p : ℕ} (hp : p.Prime) {R : Type*} [CommRing R]
    (hu : ∀ j ≠ 0, IsUnit ((p : R) ^ (p ^ j - 1) - 1)) :
    MvPolynomial ℕ+ R ≃ₐ[R] R ⊗[ℤ] LazardRing :=
  AlgEquiv.ofBijective
    (MvPolynomial.aeval fun n : ℕ+ ↦ (1 : R) ⊗ₜ[ℤ] landweberGenerator p n) <| by
      let e : (R ⊗[ℤ] LazardRing) ≃ₐ[R] MvPolynomial ℕ+ R :=
        (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) mvPolynomialEquiv.symm).trans
          (MvPolynomial.algebraTensorAlgEquiv ℤ R)
      have hcomp :
          e.toAlgHom.comp
            (MvPolynomial.aeval fun n : ℕ+ ↦ (1 : R) ⊗ₜ[ℤ] landweberGenerator p n) =
          MvPolynomial.aeval (R := R) fun n : ℕ+ ↦
            MvPolynomial.map (Int.castRingHom R)
              (mvPolynomialEquiv.symm (landweberGenerator p n)) :=
        MvPolynomial.algHom_ext fun n ↦ by simp [e]
      rw [← Function.Bijective.of_comp_iff' e.bijective, ← AlgEquiv.coe_toAlgHom,
        ← AlgHom.coe_comp, hcomp]
      exact bijective_aeval_map_landweberGenerator hp hu

/-- `TauCeti.LazardRing.landweberMvPolynomialEquivTensor` is evaluation at
`1 ⊗ₜ landweberGenerator p n`. -/
theorem landweberMvPolynomialEquivTensor_apply {p : ℕ} (hp : p.Prime) {R : Type*} [CommRing R]
    (hu : ∀ j ≠ 0, IsUnit ((p : R) ^ (p ^ j - 1) - 1)) (q : MvPolynomial ℕ+ R) :
    landweberMvPolynomialEquivTensor hp hu q =
      MvPolynomial.aeval (fun n : ℕ+ ↦ (1 : R) ⊗ₜ[ℤ] landweberGenerator p n) q := by
  rfl

/-- `TauCeti.LazardRing.landweberMvPolynomialEquivTensor` sends `X n` to
`1 ⊗ₜ landweberGenerator p n`. -/
@[simp]
theorem landweberMvPolynomialEquivTensor_X {p : ℕ} (hp : p.Prime) {R : Type*} [CommRing R]
    (hu : ∀ j ≠ 0, IsUnit ((p : R) ^ (p ^ j - 1) - 1)) (n : ℕ+) :
    landweberMvPolynomialEquivTensor hp hu (MvPolynomial.X n) =
      (1 : R) ⊗ₜ[ℤ] landweberGenerator p n := by
  simp [landweberMvPolynomialEquivTensor_apply]

/-- The inverse of `TauCeti.LazardRing.landweberMvPolynomialEquivTensor` sends
`1 ⊗ₜ landweberGenerator p n` to `X n`. -/
@[simp]
theorem landweberMvPolynomialEquivTensor_symm_tmul_landweberGenerator {p : ℕ} (hp : p.Prime)
    {R : Type*} [CommRing R] (hu : ∀ j ≠ 0, IsUnit ((p : R) ^ (p ^ j - 1) - 1)) (n : ℕ+) :
    (landweberMvPolynomialEquivTensor hp hu).symm ((1 : R) ⊗ₜ[ℤ] landweberGenerator p n) =
      MvPolynomial.X n := by
  rw [AlgEquiv.symm_apply_eq, landweberMvPolynomialEquivTensor_X]

/-- Over any ring `R` in which `(p : R) = 0` with `1 < p`, `p ^ (p ^ j - 1) - 1 = -1` is a unit for
every `j ≠ 0`. -/
theorem isUnit_pow_sub_one_of_natCast_eq_zero {p : ℕ} (hp : 1 < p) {R : Type*} [Ring R]
    (hp0 : (p : R) = 0) {j : ℕ} (hj : j ≠ 0) :
    IsUnit ((p : R) ^ (p ^ j - 1) - 1) := by
  have hne : p ^ j - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hj hp)
  rw [hp0, zero_pow hne, zero_sub]
  exact isUnit_one.neg

/-- Over any ring of characteristic `p > 1`, `p ^ (p ^ j - 1) - 1 = -1` is a unit for all
`j ≠ 0`. -/
theorem isUnit_pow_sub_one_of_charP {p : ℕ} (hp : 1 < p) (R : Type*) [Ring R] [CharP R p]
    {j : ℕ} (hj : j ≠ 0) :
    IsUnit ((p : R) ^ (p ^ j - 1) - 1) :=
  isUnit_pow_sub_one_of_natCast_eq_zero hp (CharP.cast_eq_zero R p) hj

/-- Over any local ring `R` in which `(p : R)` is not a unit (with `1 < p`, e.g. `ℤ_(p)`, `ℤ_p`,
`W(k)`, or `ZMod (p ^ k)`), `p ^ (p ^ j - 1) - 1` is a unit for every `j ≠ 0`. -/
theorem isUnit_pow_sub_one_of_isLocalRing {p : ℕ} (hp : 1 < p) {R : Type*} [Ring R]
    [IsLocalRing R] (hpu : ¬ IsUnit (p : R)) {j : ℕ} (hj : j ≠ 0) :
    IsUnit ((p : R) ^ (p ^ j - 1) - 1) := by
  have hne : p ^ j - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hj hp)
  rw [← neg_sub]
  exact (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    (mem_nonunits_iff.mpr ((isUnit_pow_iff hne).not.mpr hpu))).neg

/-- Over any localization `R` of `ℤ` at a prime ideal `(p)` with `1 < p` (such as `ℤ_(p)`),
`p ^ (p ^ j - 1) - 1` is a unit for every `j ≠ 0`. -/
theorem isUnit_pow_sub_one_of_isLocalizationAtPrime {p : ℕ} (hp : 1 < p) (R : Type*) [CommRing R]
    [(Ideal.span {(p : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(p : ℤ)})]
    {j : ℕ} (hj : j ≠ 0) :
    IsUnit ((p : R) ^ (p ^ j - 1) - 1) := by
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R (Ideal.span {(p : ℤ)})
  refine isUnit_pow_sub_one_of_isLocalRing hp (fun hpu ↦ ?_) hj
  rw [← map_natCast (algebraMap ℤ R),
    IsLocalization.AtPrime.isUnit_to_map_iff R (Ideal.span {(p : ℤ)})] at hpu
  exact hpu (Ideal.subset_span rfl)

end BaseChange

/-! ### Quotient presentations of `L ⧸ I_n` and `L ⧸ I_∞` -/

section Quotients

variable {p : ℕ} (hp : p.Prime)

/-- **Quotient of the Lazard ring by `I₁ = (p)`.** Modulo `p`, the Lazard ring is the polynomial
ring `(ZMod p)[x'₁, x'₂, …]` on Landweber's `p`-adapted generators. -/
def quotientHeightIdealOneEquiv :
    (LazardRing ⧸ formalGroup.heightIdeal p 1) ≃+* MvPolynomial ℕ+ (ZMod p) :=
  have hI : formalGroup.heightIdeal p 1 =
      (Ideal.span {(p : ℤ)}).map (algebraMap ℤ LazardRing) := by
    rw [formalGroup.heightIdeal_one hp, Ideal.map_span, Set.image_singleton, map_natCast]
  (Ideal.quotEquivOfEq hI).trans <|
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor LazardRing
      (Ideal.span {(p : ℤ)})).toRingEquiv.trans <|
      (Algebra.TensorProduct.congr (Int.quotientSpanNatEquivZMod p).toIntAlgEquiv
        (AlgEquiv.refl : LazardRing ≃ₐ[ℤ] LazardRing)).toRingEquiv.trans
        (landweberMvPolynomialEquivTensor hp (R := ZMod p) fun _ hj ↦
          isUnit_pow_sub_one_of_charP hp.one_lt (ZMod p) hj).symm.toRingEquiv

/-- `TauCeti.LazardRing.quotientHeightIdealOneEquiv` sends the class of `landweberGenerator p k` to
`X k`. -/
@[simp]
theorem quotientHeightIdealOneEquiv_mk_landweberGenerator (k : ℕ+) :
    quotientHeightIdealOneEquiv hp
        (Ideal.Quotient.mk (formalGroup.heightIdeal p 1) (landweberGenerator p k)) =
      MvPolynomial.X k := by
  simp only [quotientHeightIdealOneEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    Ideal.quotEquivOfEq_mk, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  simp

/-- The inverse of `TauCeti.LazardRing.quotientHeightIdealOneEquiv` sends `X k` to the class of
`landweberGenerator p k`. -/
@[simp]
theorem quotientHeightIdealOneEquiv_symm_X (k : ℕ+) :
    (quotientHeightIdealOneEquiv hp).symm (MvPolynomial.X k) =
      Ideal.Quotient.mk (formalGroup.heightIdeal p 1) (landweberGenerator p k) := by
  rw [RingEquiv.symm_apply_eq, quotientHeightIdealOneEquiv_mk_landweberGenerator]

/-- Under `quotientHeightIdealOneEquiv`, the image of `I_n` in `MvPolynomial ℕ+ (ZMod p)` is
generated by the variables `X k` with `(k : ℕ) + 1 = p ^ j` for `j < n`. -/
private theorem map_quotientHeightIdealOneEquiv_heightIdeal (n : ℕ) :
    ((formalGroup.heightIdeal p n).map (Ideal.Quotient.mk (formalGroup.heightIdeal p 1))).map
        (quotientHeightIdealOneEquiv hp : _ →+* _) =
      Ideal.span ((MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ (ZMod p)) ''
        {k : ℕ+ | ∃ j < n, (k : ℕ) + 1 = p ^ j}) := by
  rw [formalGroup.heightIdeal_eq_span hp n, Ideal.map_span, Ideal.map_span]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
    dsimp only
    rcases eq_or_ne j 0 with rfl | hj0
    · have hp_mem : PowerSeries.coeff (p ^ 0) (formalGroup.nsmulSeries p) ∈
          formalGroup.heightIdeal p 1 :=
        formalGroup.coeff_nsmulSeries_mem_heightIdeal (by simpa using hp.one_lt)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp_mem, map_zero]
      exact zero_mem _
    · let k : ℕ+ := ⟨p ^ j - 1, Nat.sub_pos_of_lt (Nat.one_lt_pow hj0 hp.one_lt)⟩
      have hk : (k : ℕ) + 1 = p ^ j := Nat.sub_add_cancel (Nat.one_lt_pow hj0 hp.one_lt).le
      rw [RingEquiv.coe_toRingHom, ← landweberGenerator_of_add_one_eq_pow hk,
        quotientHeightIdealOneEquiv_mk_landweberGenerator]
      exact Ideal.subset_span ⟨k, ⟨j, hj, hk⟩, rfl⟩
  · rintro _ ⟨k, ⟨j, hj, hkj⟩, rfl⟩
    rw [← quotientHeightIdealOneEquiv_mk_landweberGenerator hp k,
      landweberGenerator_of_add_one_eq_pow hkj]
    refine Ideal.subset_span ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩

/-- **Quotient of the Lazard ring by `I_n` (`n ≥ 1`).** Modulo `I_n`, the Lazard ring is the
polynomial ring over `ZMod p` on the generators `x'ₖ` with `k + 1 ≠ p ^ j` for all `j < n`. -/
def quotientHeightIdealEquiv {n : ℕ} (hn : 1 ≤ n) :
    (LazardRing ⧸ formalGroup.heightIdeal p n) ≃+*
      MvPolynomial {k : ℕ+ // ∀ j < n, (k : ℕ) + 1 ≠ p ^ j} (ZMod p) :=
  (DoubleQuot.quotQuotEquivQuotOfLE (formalGroup.heightIdeal_mono hn)).symm.trans <|
    (Ideal.quotientEquiv _ _ (quotientHeightIdealOneEquiv hp)
      (map_quotientHeightIdealOneEquiv_heightIdeal hp n).symm).trans <|
      (MvPolynomial.quotientSpanXImageEquiv (ZMod p)
        {k : ℕ+ | ∃ j < n, (k : ℕ) + 1 = p ^ j}).toRingEquiv.trans <|
        (MvPolynomial.renameEquiv (ZMod p)
          (Equiv.subtypeEquivRight fun k ↦ by simp)).toRingEquiv

/-- `TauCeti.LazardRing.quotientHeightIdealEquiv` sends the class of `landweberGenerator p k`, for
`k + 1` not of the form `p ^ j` (`j < n`), to the variable `X ⟨k, hk⟩`. -/
@[simp]
theorem quotientHeightIdealEquiv_mk_landweberGenerator_of_forall_ne {n : ℕ} (hn : 1 ≤ n) {k : ℕ+}
    (hk : ∀ j < n, (k : ℕ) + 1 ≠ p ^ j) :
    quotientHeightIdealEquiv hp hn
        (Ideal.Quotient.mk (formalGroup.heightIdeal p n) (landweberGenerator p k)) =
      MvPolynomial.X ⟨k, hk⟩ := by
  have hk' : k ∉ {m : ℕ+ | ∃ j < n, (m : ℕ) + 1 = p ^ j} := by
    rintro ⟨j, hj, hkj⟩
    exact hk j hj hkj
  simp [quotientHeightIdealEquiv, DoubleQuot.quotQuotMk, hk', Equiv.subtypeEquivRight_apply]

/-- The inverse of `TauCeti.LazardRing.quotientHeightIdealEquiv` sends `X k` to the class of
`landweberGenerator p k.1`. -/
@[simp]
theorem quotientHeightIdealEquiv_symm_X {n : ℕ} (hn : 1 ≤ n)
    (k : {k : ℕ+ // ∀ j < n, (k : ℕ) + 1 ≠ p ^ j}) :
    (quotientHeightIdealEquiv hp hn).symm (MvPolynomial.X k) =
      Ideal.Quotient.mk (formalGroup.heightIdeal p n) (landweberGenerator p k.1) := by
  rw [RingEquiv.symm_apply_eq, quotientHeightIdealEquiv_mk_landweberGenerator_of_forall_ne]

/-- Under `quotientHeightIdealOneEquiv`, the image of `⨆ n, I_n` in `MvPolynomial ℕ+ (ZMod p)` is
generated by all variables `X k` with `(k : ℕ) + 1 = p ^ j`. -/
private theorem map_quotientHeightIdealOneEquiv_iSup_heightIdeal :
    ((⨆ n, formalGroup.heightIdeal p n).map
         (Ideal.Quotient.mk (formalGroup.heightIdeal p 1))).map
        (quotientHeightIdealOneEquiv hp : _ →+* _) =
      Ideal.span ((MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ (ZMod p)) ''
        {k : ℕ+ | ∃ j, (k : ℕ) + 1 = p ^ j}) := by
  rw [Ideal.map_iSup, Ideal.map_iSup]
  refine le_antisymm (iSup_le fun n ↦ ?_) (Ideal.span_le.mpr ?_)
  · rw [map_quotientHeightIdealOneEquiv_heightIdeal hp n]
    exact Ideal.span_mono (Set.image_mono fun _ ⟨j, _, h⟩ ↦ ⟨j, h⟩)
  · rintro _ ⟨k, ⟨j, hkj⟩, rfl⟩
    refine Ideal.mem_iSup_of_mem (j + 1) ?_
    rw [map_quotientHeightIdealOneEquiv_heightIdeal hp (j + 1)]
    exact Ideal.subset_span ⟨k, ⟨j, j.lt_succ_self, hkj⟩, rfl⟩

/-- **Quotient of the Lazard ring by `I_∞ = ⨆ n, I_n`.** Modulo the union of all height ideals at
`p`, the Lazard ring is the polynomial ring over `ZMod p` on Lazard's generators `xₖ` for `k + 1`
not a power of `p`. -/
def quotientISupHeightIdealEquiv :
    (LazardRing ⧸ ⨆ n, formalGroup.heightIdeal p n) ≃+*
      MvPolynomial {k : ℕ+ // ∀ j, (k : ℕ) + 1 ≠ p ^ j} (ZMod p) :=
  (DoubleQuot.quotQuotEquivQuotOfLE (le_iSup (formalGroup.heightIdeal p) 1)).symm.trans <|
    (Ideal.quotientEquiv _ _ (quotientHeightIdealOneEquiv hp)
      (map_quotientHeightIdealOneEquiv_iSup_heightIdeal hp).symm).trans <|
      (MvPolynomial.quotientSpanXImageEquiv (ZMod p)
        {k : ℕ+ | ∃ j, (k : ℕ) + 1 = p ^ j}).toRingEquiv.trans <|
        (MvPolynomial.renameEquiv (ZMod p)
          (Equiv.subtypeEquivRight fun k ↦ by simp)).toRingEquiv

/-- `TauCeti.LazardRing.quotientISupHeightIdealEquiv` sends the class of `landweberGenerator p k`,
for `k + 1` not a power of `p`, to `X ⟨k, hk⟩`. -/
@[simp]
theorem quotientISupHeightIdealEquiv_mk_landweberGenerator_of_forall_ne {k : ℕ+}
    (hk : ∀ j, (k : ℕ) + 1 ≠ p ^ j) :
    quotientISupHeightIdealEquiv hp
        (Ideal.Quotient.mk (⨆ n, formalGroup.heightIdeal p n) (landweberGenerator p k)) =
      MvPolynomial.X ⟨k, hk⟩ := by
  have hk' : k ∉ {m : ℕ+ | ∃ j, (m : ℕ) + 1 = p ^ j} := by
    rintro ⟨j, hkj⟩
    exact hk j hkj
  simp [quotientISupHeightIdealEquiv, DoubleQuot.quotQuotMk, hk', Equiv.subtypeEquivRight_apply]

/-- `TauCeti.LazardRing.quotientISupHeightIdealEquiv` sends the class of Lazard's generator `xₖ`,
for `k + 1` not a power of `p`, to `X ⟨k, hk⟩`. -/
@[simp]
theorem quotientISupHeightIdealEquiv_mk_generator_of_forall_ne {k : ℕ+}
    (hk : ∀ j, (k : ℕ) + 1 ≠ p ^ j) :
    quotientISupHeightIdealEquiv hp
        (Ideal.Quotient.mk (⨆ n, formalGroup.heightIdeal p n) (generator k)) =
      MvPolynomial.X ⟨k, hk⟩ := by
  rw [← landweberGenerator_of_forall_add_one_ne_pow hk,
    quotientISupHeightIdealEquiv_mk_landweberGenerator_of_forall_ne]

/-- The inverse of `TauCeti.LazardRing.quotientISupHeightIdealEquiv` sends `X k` to the class of
`generator k.1`. -/
@[simp]
theorem quotientISupHeightIdealEquiv_symm_X (k : {k : ℕ+ // ∀ j, (k : ℕ) + 1 ≠ p ^ j}) :
    (quotientISupHeightIdealEquiv hp).symm (MvPolynomial.X k) =
      Ideal.Quotient.mk (⨆ n, formalGroup.heightIdeal p n) (generator k.1) := by
  rw [RingEquiv.symm_apply_eq, quotientISupHeightIdealEquiv_mk_generator_of_forall_ne]

end Quotients

/-! ### Primality and strict inclusion of the height ideals -/

section PrimeAndOrder

variable {p : ℕ} (hp : p.Prime)
include hp

/-- **Landweber's height ideals are prime.** For every prime `p` and every `n : ℕ`, the height ideal
`I_n` of the universal formal group law over the Lazard ring is a prime ideal. -/
theorem isPrime_heightIdeal (n : ℕ) : (formalGroup.heightIdeal p n).IsPrime := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [formalGroup.heightIdeal_zero]
    exact Ideal.isPrime_bot
  · let : Fact p.Prime := ⟨hp⟩
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have : IsDomain (LazardRing ⧸ formalGroup.heightIdeal p n) :=
      (quotientHeightIdealEquiv hp hn).toMulEquiv.isDomain _
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- **The infinite height ideal `I_∞ = ⨆ n, I_n` is prime** in the Lazard ring. -/
theorem isPrime_iSup_heightIdeal : (⨆ n, formalGroup.heightIdeal p n).IsPrime := by
  let : Fact p.Prime := ⟨hp⟩
  have : IsDomain (LazardRing ⧸ ⨆ n, formalGroup.heightIdeal p n) :=
    (quotientISupHeightIdealEquiv hp).toMulEquiv.isDomain _
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- Every height ideal `I_n` of the Lazard ring is a proper ideal. -/
theorem heightIdeal_ne_top (n : ℕ) : formalGroup.heightIdeal p n ≠ ⊤ :=
  (isPrime_heightIdeal hp n).ne_top

/-- The union `I_∞ = ⨆ n, I_n` of the height ideals is a proper ideal of the Lazard ring. -/
theorem iSup_heightIdeal_ne_top : ⨆ n, formalGroup.heightIdeal p n ≠ ⊤ :=
  (isPrime_iSup_heightIdeal hp).ne_top

/-- **Landweber's element `v_n` does not lie in `I_n`.** For every `n`, the coefficient of `X^(pⁿ)`
in the `p`-series of the universal formal group law is nonzero modulo `I_n`. -/
theorem coeff_nsmulSeries_notMem_heightIdeal (n : ℕ) :
    PowerSeries.coeff (p ^ n) (formalGroup.nsmulSeries p) ∉ formalGroup.heightIdeal p n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [hp.ne_zero]
  · let : Fact p.Prime := ⟨hp⟩
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    let k : ℕ+ := ⟨p ^ n - 1, Nat.sub_pos_of_lt (Nat.one_lt_pow hn0 hp.one_lt)⟩
    have hk_eq : (k : ℕ) + 1 = p ^ n := Nat.sub_add_cancel (Nat.one_lt_pow hn0 hp.one_lt).le
    have hk_ne : ∀ j < n, (k : ℕ) + 1 ≠ p ^ j := fun j hj ↦ by
      rw [hk_eq]
      exact (Nat.pow_lt_pow_right hp.one_lt hj).ne'
    let idx : {m : ℕ+ // ∀ j < n, (m : ℕ) + 1 ≠ p ^ j} := ⟨k, hk_ne⟩
    rw [← landweberGenerator_of_add_one_eq_pow hk_eq, ← Ideal.Quotient.eq_zero_iff_mem]
    intro h0
    have hX : (MvPolynomial.X idx : MvPolynomial _ (ZMod p)) = 0 := by
      rw [← quotientHeightIdealEquiv_mk_landweberGenerator_of_forall_ne hp hn hk_ne, h0, map_zero]
    exact MvPolynomial.X_ne_zero idx hX

/-- The height ideals of the Lazard ring satisfy `I_n < I_(n+1)` for every `n`. -/
theorem heightIdeal_lt_succ (n : ℕ) :
    formalGroup.heightIdeal p n < formalGroup.heightIdeal p (n + 1) :=
  lt_of_le_of_ne (formalGroup.heightIdeal_mono n.le_succ) fun h ↦
    coeff_nsmulSeries_notMem_heightIdeal hp n <|
      h ▸ formalGroup.coeff_nsmulSeries_mem_heightIdeal
        (Nat.pow_lt_pow_right hp.one_lt n.lt_succ_self)

/-- **Strict monotonicity of the height ideals** `I₀ < I₁ < I₂ < …` in the Lazard ring. -/
theorem heightIdeal_strictMono : StrictMono (formalGroup.heightIdeal p) :=
  strictMono_nat_of_lt_succ (heightIdeal_lt_succ hp)

/-- Distinct indices give distinct height ideals in the Lazard ring. -/
theorem heightIdeal_injective : Function.Injective (formalGroup.heightIdeal p) :=
  (heightIdeal_strictMono hp).injective

/-- Every finite height ideal `I_n` is strictly contained in `I_∞ = ⨆ m, I_m`. -/
theorem heightIdeal_lt_iSup (n : ℕ) :
    formalGroup.heightIdeal p n < ⨆ m, formalGroup.heightIdeal p m :=
  (heightIdeal_lt_succ hp n).trans_le (le_iSup (formalGroup.heightIdeal p) (n + 1))

/-- Landweber's generator `x'ₖ` lies in `I_∞ = ⨆ n, I_n` if and only if `k + 1` is a power of
`p`. -/
@[simp]
theorem landweberGenerator_mem_iSup_heightIdeal_iff {k : ℕ+} :
    landweberGenerator p k ∈ ⨆ n, formalGroup.heightIdeal p n ↔ ∃ j, (k : ℕ) + 1 = p ^ j := by
  refine ⟨fun hmem ↦ ?_, fun ⟨j, hkj⟩ ↦ ?_⟩
  · by_contra hex
    let : Fact p.Prime := ⟨hp⟩
    have hk : ∀ j, (k : ℕ) + 1 ≠ p ^ j := fun j hj ↦ hex ⟨j, hj⟩
    let idx : {m : ℕ+ // ∀ j, (m : ℕ) + 1 ≠ p ^ j} := ⟨k, hk⟩
    have h0 : Ideal.Quotient.mk (⨆ m, formalGroup.heightIdeal p m) (landweberGenerator p k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hX : (MvPolynomial.X idx : MvPolynomial _ (ZMod p)) = 0 := by
      rw [← quotientISupHeightIdealEquiv_mk_landweberGenerator_of_forall_ne hp hk, h0, map_zero]
    exact MvPolynomial.X_ne_zero idx hX
  · refine Ideal.mem_iSup_of_mem (j + 1) ?_
    rw [landweberGenerator_of_add_one_eq_pow hkj]
    exact formalGroup.coeff_nsmulSeries_mem_heightIdeal
      (Nat.pow_lt_pow_right hp.one_lt j.lt_succ_self)

/-- Landweber's generator `x'ₖ` lies in `I_n` if and only if `k + 1 = p ^ j` for some `j < n`. -/
@[simp]
theorem landweberGenerator_mem_heightIdeal_iff {n : ℕ} {k : ℕ+} :
    landweberGenerator p k ∈ formalGroup.heightIdeal p n ↔ ∃ j < n, (k : ℕ) + 1 = p ^ j := by
  refine ⟨fun hmem ↦ ?_, fun ⟨j, hj, hkj⟩ ↦ ?_⟩
  · obtain ⟨j, hkj⟩ := (landweberGenerator_mem_iSup_heightIdeal_iff hp).mp
      (Ideal.mem_iSup_of_mem n hmem)
    refine ⟨j, lt_of_not_ge fun hnj ↦ coeff_nsmulSeries_notMem_heightIdeal hp j ?_, hkj⟩
    rw [← landweberGenerator_of_add_one_eq_pow hkj]
    exact formalGroup.heightIdeal_mono hnj hmem
  · rw [landweberGenerator_of_add_one_eq_pow hkj]
    exact formalGroup.coeff_nsmulSeries_mem_heightIdeal (Nat.pow_lt_pow_right hp.one_lt hj)

/-- An integer lies in `I_∞ = ⨆ n, I_n` if and only if it is divisible by `p`. -/
@[simp]
theorem intCast_mem_iSup_heightIdeal_iff {k : ℤ} :
    (k : LazardRing) ∈ ⨆ n, formalGroup.heightIdeal p n ↔ (p : ℤ) ∣ k := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast,
    ← RingEquiv.map_eq_zero_iff (quotientISupHeightIdealEquiv hp), map_intCast,
    CharP.intCast_eq_zero_iff _ p]

/-- For `n ≥ 1`, an integer lies in `I_n` if and only if it is divisible by `p`. -/
@[simp]
theorem intCast_mem_heightIdeal_iff {n : ℕ} (hn : 1 ≤ n) {k : ℤ} :
    (k : LazardRing) ∈ formalGroup.heightIdeal p n ↔ (p : ℤ) ∣ k := by
  refine ⟨fun hk ↦ (intCast_mem_iSup_heightIdeal_iff hp).mp (Ideal.mem_iSup_of_mem n hk), ?_⟩
  rintro ⟨m, rfl⟩
  refine formalGroup.heightIdeal_mono hn ?_
  rw [formalGroup.heightIdeal_one hp, Ideal.mem_span_singleton]
  exact ⟨m, by push_cast; rfl⟩

end PrimeAndOrder

/-! ### Regular sequences in `L`, flat `L`-algebras, and localizations -/

section RegularSequence

variable {p : ℕ} (hp : p.Prime)
include hp

/-- Any lift `v` of `v_n` modulo `I_n` acts regularly on `L ⧸ I_n`. -/
theorem isSMulRegular_quotient_heightIdeal_of_sub_mem {n : ℕ} {v : LazardRing}
    (hv : v - PowerSeries.coeff (p ^ n) (formalGroup.nsmulSeries p) ∈
      formalGroup.heightIdeal p n) :
    IsSMulRegular (LazardRing ⧸ formalGroup.heightIdeal p n) v :=
  formalGroup.isSMulRegular_quotient_heightIdeal_of_sub_mem hp
    (isPrime_heightIdeal hp n) (heightIdeal_lt_succ hp n) hv

/-- Landweber's element `v_n` acts regularly on `L ⧸ I_n`. -/
theorem isSMulRegular_quotient_heightIdeal (n : ℕ) :
    IsSMulRegular (LazardRing ⧸ formalGroup.heightIdeal p n)
      (PowerSeries.coeff (p ^ n) (formalGroup.nsmulSeries p)) :=
  isSMulRegular_quotient_heightIdeal_of_sub_mem hp (by simp)

/-- **Landweber's regular sequence theorem (arbitrary lifts).** Any sequence `v₀, …, v_(n-1)` in the
Lazard ring congruent to `[X^(pⁱ)] [p]_F(X)` modulo `I_i` for each `i < n` is a regular sequence on
`LazardRing`. -/
theorem isRegular_ofFn_of_sub_mem_heightIdeal {n : ℕ} {v : Fin n → LazardRing}
    (hv : ∀ i : Fin n,
      v i - PowerSeries.coeff (p ^ (i : ℕ)) (formalGroup.nsmulSeries p) ∈
        formalGroup.heightIdeal p i) :
    RingTheory.Sequence.IsRegular LazardRing (List.ofFn v) :=
  formalGroup.isRegular_ofFn_of_sub_mem_heightIdeal hp
    (fun i _ ↦ isPrime_heightIdeal hp i) (fun i _ ↦ heightIdeal_lt_succ hp i)
    (heightIdeal_ne_top hp n) hv

/-- **Landweber's regular sequence theorem.** For every prime `p` and every `n : ℕ`, the `p`-series
coefficients `p, v₁, …, v_(n-1)` of the universal formal group law form a regular sequence on the
Lazard ring. -/
theorem isRegular_ofFn_coeff_nsmulSeries (n : ℕ) :
    RingTheory.Sequence.IsRegular LazardRing
      (List.ofFn fun i : Fin n ↦ PowerSeries.coeff (p ^ (i : ℕ)) (formalGroup.nsmulSeries p)) :=
  isRegular_ofFn_of_sub_mem_heightIdeal hp fun _ ↦ by simp

/-- **Coordinate independence of regularity.** For any formal group law `G` over the Lazard ring
isomorphic to the universal law (not necessarily strictly), its `p`-series coefficients
`v₀(G), …, v_(n-1)(G)` form a regular sequence on `LazardRing`. -/
theorem isRegular_ofFn_coeff_nsmulSeries_of_iso {G : FormalGroup LazardRing}
    (e : FormalGroupIso formalGroup G) (n : ℕ) :
    RingTheory.Sequence.IsRegular LazardRing
      (List.ofFn fun i : Fin n ↦ PowerSeries.coeff (p ^ (i : ℕ)) (G.nsmulSeries p)) :=
  (e.isRegular_ofFn_coeff_nsmulSeries_iff hp LazardRing n).mpr
    (isRegular_ofFn_coeff_nsmulSeries hp n)

section Flat

variable (S : Type*) [CommRing S] [Algebra LazardRing S] [Module.Flat LazardRing S]

/-- In any flat `LazardRing`-algebra `S`, the images of `p, v₁, …, v_(n-1)` form a weakly regular
sequence on `S`. -/
theorem isWeaklyRegular_ofFn_algebraMap_coeff_nsmulSeries_of_flat (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular S
      (List.ofFn fun i : Fin n ↦
        algebraMap LazardRing S (PowerSeries.coeff (p ^ (i : ℕ)) (formalGroup.nsmulSeries p))) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    (isRegular_ofFn_coeff_nsmulSeries hp n).1.of_flat (S := S)

/-- **Weak regularity of `p, v₁, …, v_(n-1)` in flat `LazardRing`-algebras.** In any flat
`LazardRing`-algebra `S` (such as `L[b₁, b₂, …]`, `R ⊗[ℤ] L` for flat `R`, or any localization of
`L`), any sequence of lifts of `p, v₁, …, v_(n-1)` modulo `I₀ S, …, I_(n-1) S` is weakly regular on
`S`. -/
theorem isWeaklyRegular_ofFn_of_sub_mem_heightIdeal_of_flat {n : ℕ} {v : Fin n → S}
    (hv : ∀ i : Fin n,
      v i - PowerSeries.coeff (p ^ (i : ℕ))
        ((formalGroup.map (algebraMap LazardRing S)).nsmulSeries p) ∈
          (formalGroup.map (algebraMap LazardRing S)).heightIdeal p i) :
    RingTheory.Sequence.IsWeaklyRegular S (List.ofFn v) := by
  rw [(formalGroup.map (algebraMap LazardRing S)).isWeaklyRegular_ofFn_iff_of_sub_mem_heightIdeal
    hp S hv]
  simpa only [FormalGroup.coeff_nsmulSeries_map] using
    isWeaklyRegular_ofFn_algebraMap_coeff_nsmulSeries_of_flat hp S n

/-- **Regularity of `p, v₁, …, v_(n-1)` in flat `LazardRing`-algebras.** In any flat
`LazardRing`-algebra `S` with `I_n S ≠ ⊤`, any sequence of lifts of `p, v₁, …, v_(n-1)` modulo
`I₀ S, …, I_(n-1) S` is a regular sequence on `S`. -/
theorem isRegular_ofFn_of_sub_mem_heightIdeal_of_flat {n : ℕ}
    (hne : (formalGroup.map (algebraMap LazardRing S)).heightIdeal p n ≠ ⊤) {v : Fin n → S}
    (hv : ∀ i : Fin n,
      v i - PowerSeries.coeff (p ^ (i : ℕ))
        ((formalGroup.map (algebraMap LazardRing S)).nsmulSeries p) ∈
          (formalGroup.map (algebraMap LazardRing S)).heightIdeal p i) :
    RingTheory.Sequence.IsRegular S (List.ofFn v) :=
  ⟨isWeaklyRegular_ofFn_of_sub_mem_heightIdeal_of_flat hp S hv, by
    rw [(formalGroup.map (algebraMap LazardRing S)).ofList_ofFn_eq_heightIdeal_of_sub_mem hp hv,
      Ideal.smul_eq_mul, Ideal.mul_top]
    exact hne.symm⟩

/-- In any flat `LazardRing`-algebra `S` with `I_n S ≠ ⊤`, the images of `p, v₁, …, v_(n-1)` form a
regular sequence on `S`. -/
theorem isRegular_ofFn_algebraMap_coeff_nsmulSeries_of_flat {n : ℕ}
    (hne : (formalGroup.map (algebraMap LazardRing S)).heightIdeal p n ≠ ⊤) :
    RingTheory.Sequence.IsRegular S
      (List.ofFn fun i : Fin n ↦
        algebraMap LazardRing S (PowerSeries.coeff (p ^ (i : ℕ)) (formalGroup.nsmulSeries p))) :=
  isRegular_ofFn_of_sub_mem_heightIdeal_of_flat hp S hne fun _ ↦ by
    simp [FormalGroup.coeff_nsmulSeries_map]

end Flat

section Localization

variable (M : Submonoid LazardRing) (S : Type*) [CommRing S] [Algebra LazardRing S]
  [IsLocalization M S]

/-- In any localization `S = M⁻¹ L` with `M` disjoint from `I_n`, the extended height ideal
`I_n S` is prime. -/
theorem isPrime_heightIdeal_map_of_disjoint {n : ℕ}
    (hd : Disjoint (M : Set LazardRing) (formalGroup.heightIdeal p n)) :
    ((formalGroup.map (algebraMap LazardRing S)).heightIdeal p n).IsPrime := by
  rw [← formalGroup.map_heightIdeal]
  exact IsLocalization.isPrime_of_isPrime_disjoint M S _ (isPrime_heightIdeal hp n) hd

/-- In any localization `S = M⁻¹ L` with `M` disjoint from `I_(n+1)`, the extended height ideals
satisfy `I_n S < I_(n+1) S`. -/
theorem heightIdeal_map_lt_succ_of_disjoint {n : ℕ}
    (hd : Disjoint (M : Set LazardRing) (formalGroup.heightIdeal p (n + 1))) :
    (formalGroup.map (algebraMap LazardRing S)).heightIdeal p n <
      (formalGroup.map (algebraMap LazardRing S)).heightIdeal p (n + 1) := by
  have hd_n : Disjoint (M : Set LazardRing) (formalGroup.heightIdeal p n) :=
    hd.mono_right (formalGroup.heightIdeal_mono n.le_succ)
  rw [← formalGroup.map_heightIdeal, ← formalGroup.map_heightIdeal]
  refine lt_of_le_of_ne (Ideal.map_mono (formalGroup.heightIdeal_mono n.le_succ)) fun h ↦
    (heightIdeal_lt_succ hp n).ne ?_
  rw [← IsLocalization.under_map_of_isPrime_disjoint M S (isPrime_heightIdeal hp n) hd_n,
    ← IsLocalization.under_map_of_isPrime_disjoint M S (isPrime_heightIdeal hp (n + 1)) hd, h]

/-- **Regularity of `p, v₁, …, v_(n-1)` in localizations of the Lazard ring.** In any localization
`S = M⁻¹ L` with `M` disjoint from `I_n` (including `L_(p)` and `L_(I_m)` for `m ≥ n`), any sequence
of lifts of `p, v₁, …, v_(n-1)` modulo `I₀ S, …, I_(n-1) S` is a regular sequence on `S`. -/
theorem isRegular_ofFn_of_sub_mem_heightIdeal_of_isLocalization {n : ℕ}
    (hd : Disjoint (M : Set LazardRing) (formalGroup.heightIdeal p n)) {v : Fin n → S}
    (hv : ∀ i : Fin n,
      v i - PowerSeries.coeff (p ^ (i : ℕ))
        ((formalGroup.map (algebraMap LazardRing S)).nsmulSeries p) ∈
          (formalGroup.map (algebraMap LazardRing S)).heightIdeal p i) :
    RingTheory.Sequence.IsRegular S (List.ofFn v) :=
  have : Module.Flat LazardRing S := IsLocalization.flat S M
  isRegular_ofFn_of_sub_mem_heightIdeal_of_flat hp S
    (isPrime_heightIdeal_map_of_disjoint hp M S hd).ne_top hv

/-- In any localization `S = M⁻¹ L` with `M` disjoint from `I_n`, the images of `p, v₁, …, v_(n-1)`
form a regular sequence on `S`. -/
theorem isRegular_ofFn_algebraMap_coeff_nsmulSeries_of_isLocalization {n : ℕ}
    (hd : Disjoint (M : Set LazardRing) (formalGroup.heightIdeal p n)) :
    RingTheory.Sequence.IsRegular S
      (List.ofFn fun i : Fin n ↦
        algebraMap LazardRing S (PowerSeries.coeff (p ^ (i : ℕ)) (formalGroup.nsmulSeries p))) :=
  isRegular_ofFn_of_sub_mem_heightIdeal_of_isLocalization hp M S hd fun _ ↦ by
    simp [FormalGroup.coeff_nsmulSeries_map]

end Localization

/-- The submonoid of integers prime to `p`, viewed inside the Lazard ring via
`Algebra.algebraMapSubmonoid`, is disjoint from the union `I_∞ = ⨆ n, I_n` of all height ideals
(and hence from each `I_n`), so the localization results apply to the `p`-local Lazard ring
`L_(p) = MU_(p)*`. -/
theorem disjoint_algebraMapSubmonoid_primeCompl_iSup_heightIdeal
    [(Ideal.span {(p : ℤ)}).IsPrime] :
    Disjoint
      (Algebra.algebraMapSubmonoid LazardRing (Ideal.span {(p : ℤ)}).primeCompl : Set LazardRing)
      ((⨆ n, formalGroup.heightIdeal p n : Ideal LazardRing) : Set LazardRing) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, hk, rfl⟩ hmem
  simp only [SetLike.mem_coe, eq_intCast] at hmem
  exact hk (Ideal.mem_span_singleton.mpr ((intCast_mem_iSup_heightIdeal_iff hp).mp hmem))

end RegularSequence

end TauCeti.LazardRing
