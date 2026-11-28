/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.ModularForms.LFunction
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.LSeries.EulerProduct
import TauCeti.NumberTheory.ModularForms.LFunction.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import TauCeti.NumberTheory.ModularForms.Newforms.PeterssonAdjoint

/-!
# The L-functions of newforms with the same eigenvalues at almost all primes

Let `f` and `g` be newforms of the same weight `k` and levels `N`, `M`, with nebentypes `χ` and
`χ'`, and let `Q` be a common multiple of `N` and `M` such that `a_p(f) = a_p(g)` at every prime
`p ∤ Q`. Nothing is assumed about the nebentypes. At such a prime, with `a = a_p`, `X = p^(-s)`,
`w = 2s - k + 1` and `Y = p^(k-1) X² = p^(-w)`, the Euler factors of `f` and `g` are
`1 - a X + χ(p) Y` and `1 - a X + χ'(p) Y`, and they may differ: when `a ≠ 0` the Petersson
adjoint relation `a = χ(p) conj a` forces `χ(p) = χ'(p)`, but when `a = 0` nothing relates
`χ(p)` and `χ'(p)`. In either case `a (χ(p) - χ'(p)) = 0`, and this is exactly the condition
under which

`(1 - a X + χ(p) Y) (1 - χ(p) Y) (1 - χ'(p)² Y²)`
`  = (1 - a X + χ'(p) Y) (1 - χ'(p) Y) (1 - χ(p)² Y²)`.

The two sides are the local factors at `p` of the reciprocals of `L(f, s) L(w, χ) L(2w, χ'²)` and
of `L(g, s) L(w, χ') L(2w, χ²)`, with the nebentypes raised to level `Q`. Removing the Euler
factors of `f` and `g` at the primes dividing `Q` therefore gives an identity of Euler products
on the half-plane of absolute convergence,

`L(f, s) ∏_{p ∣ Q} E_p(f, s) L(w, χ) L(2w, χ'²)`
`  = L(g, s) ∏_{p ∣ Q} E_p(g, s) L(w, χ') L(2w, χ²)`,

where `E_p(f, s) = 1 - a_p(f) p^(-s) + χ(p) p^(k-1) p^(-2s)`, the nebentypus being extended by
zero at the primes dividing the level. All the functions in it are entire, except the Dirichlet
L-functions of trivial characters at their pole, so the identity holds on all of `ℂ` away from
the two points where `w = 1` or `2w = 1`.

The identity is the input for separating the nebentypes analytically, which strong multiplicity
one across levels (Miyake, Theorem 4.6.19) needs when only the eigenvalues at the primes are
known. Both sides are products of L-functions with functional equations: Hecke's for
`L(f, s)` and `L(g, s)`, relating them to the conjugate newforms, and the classical ones for the
Dirichlet L-functions. Since `χ(-1) = χ'(-1) = (-1)^k` the gamma factors of the two sides agree.
The reflection `s ↦ k - s` sends `w` to `2 - w`, and the functional equation turns `L(2 - w, χ)`
into `L(w - 1, χ⁻¹)` up to elementary factors at the primes dividing `Q`. Comparing the
coefficients of the resulting Dirichlet series at `ℓ²`, for a prime `ℓ ∤ Q`, then gives
`χ(ℓ) = χ'(ℓ)`.

## Main results

* `HeckeRing.GL2.Newform.LSeries_mul_prod_mul_LFunction_mul_LFunction_eq`: the identity of
  Euler products on `Re s > (k + 1) / 2`.
* `HeckeRing.GL2.Newform.L_mul_prod_mul_LFunction_mul_LFunction_eq`: the identity of the
  continuations, at every `s` with `2s - k + 1 ≠ 1` and `2(2s - k + 1) ≠ 1`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.19, and §4.3 for the functional
  equations.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.9 for
  the Euler product.
-/

public section

open UpperHalfPlane LSeries DirichletCharacter CongruenceSubgroup Filter Topology

namespace HeckeRing.GL2.Newform

variable {N M Q : ℕ} [NeZero N] [NeZero M] [NeZero Q] {k : ℤ}

/-- The Euler product of `L(f, s) ∏_{p ∣ Q} E_p(f, s) L(w, χ) L(2w, ψ²)` for a newform `f` of
nebentypus `χ`, raised to a multiple `Q` of its level, and a Dirichlet character `ψ` modulo `Q`,
where `w = 2s - k + 1`: at a prime `p ∤ Q` its local factor is the product of the inverses of
`E_p(f, s)`, `1 - χ(p) p^(-w)` and `1 - ψ(p)² p^(-2w)`, and at a prime `p ∣ Q` it is `1`. -/
private theorem hasProd_mul_prod_mul_LFunction (f : Newform N k) (hN : N ∣ Q)
    (ψ : DirichletCharacter ℂ Q) {s : ℂ} (hs : ((k : ℝ) + 1) / 2 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        (if (p : ℕ).Coprime Q then
          (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
            f.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))⁻¹ else 1) *
          (1 - changeLevel hN f.dirichletLift p * (p : ℂ) ^ (-(2 * s - k + 1)))⁻¹ *
          (1 - (ψ ^ 2) p * (p : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹)
      (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s *
          (∏ p ∈ Q.primeFactors, (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
            f.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))) *
          LFunction (changeLevel hN f.dirichletLift) (2 * s - k + 1) *
          LFunction (ψ ^ 2) (2 * (2 * s - k + 1))) := by
  have hsum := CuspForm.LSeriesSummable_qExpansion_coeff f.toCuspForm hs
  rw [strictWidthInfty_Gamma1] at hsum
  have h₁ : (qExpansion 1 f.toEigenform.toCuspForm).coeff 1 = 1 := by simp
  have hw : 1 < (2 * s - k + 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.intCast_re,
      Complex.one_re]
    norm_num
    linarith
  have hw₂ : 1 < (2 * (2 * s - k + 1)).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  -- the coefficients of `f` satisfy the hypotheses of the general Euler product
  have hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      (qExpansion 1 f.toCuspForm).coeff (m * n) =
        (qExpansion 1 f.toCuspForm).coeff m * (qExpansion 1 f.toCuspForm).coeff n :=
    fun _ _ hmn ↦ by simpa using f.toEigenform.qExpansion_coeff_mul h₁ hmn
  have hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      (qExpansion 1 f.toCuspForm).coeff (p ^ (r + 2)) =
        (qExpansion 1 f.toCuspForm).coeff p * (qExpansion 1 f.toCuspForm).coeff (p ^ (r + 1)) -
          f.dirichletLift p * (p : ℂ) ^ (k - 1) * (qExpansion 1 f.toCuspForm).coeff (p ^ r) :=
    fun p hp r ↦ by
      simpa [dirichletLift_def, mul_assoc] using f.toEigenform.qExpansion_coeff_prime_pow_add_two
        h₁ hp r
  rw [← TauCeti.LSeries.LSeries_coprime_eq_mul_prod_of_recurrence
    (c := fun p ↦ f.dirichletLift p * (p : ℂ) ^ (k - 1)) (by simp) hmul (fun p hp r ↦ by
      simpa only [mul_assoc] using hrec p hp r) hsum (NeZero.ne Q),
    LFunction_eq_LSeries _ hw, LFunction_eq_LSeries _ hw₂]
  exact ((TauCeti.LSeries.LSeries_coprime_eulerProduct_hasProd_of_recurrence
    (c := fun p ↦ f.dirichletLift p * (p : ℂ) ^ (k - 1)) (by simp) hmul (fun p hp r ↦ by
      simpa only [mul_assoc] using hrec p hp r) hsum Q).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd _ hw)).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd _ hw₂) |>.congr_fun
    fun p ↦ by simp only [mul_assoc]

omit [NeZero Q] in
/-- The local factors of `hasProd_mul_prod_mul_LFunction` for `f` paired with `χ'` and for `g`
paired with `χ` agree at every prime, when `a_p(f) = a_p(g)` at the primes `p ∤ Q`. At a prime
`p ∤ Q` this is the identity
`(1 - a X + u Y) (1 - u Y) (1 - v² Y²) = (1 - a X + v Y) (1 - v Y) (1 - u² Y²)`, where `u`, `v`
are the nebentypus values at `p`, which holds because `a (u - v) = 0`. -/
private theorem localFactor_eq (f : Newform N k) (g : Newform M k) (hN : N ∣ Q) (hM : M ∣ Q)
    (h : ∀ p : ℕ, p.Prime → p.Coprime Q →
      (qExpansion 1 f.toCuspForm).coeff p = (qExpansion 1 g.toCuspForm).coeff p)
    (s : ℂ) (p : Nat.Primes) :
    (if (p : ℕ).Coprime Q then
        (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          f.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))⁻¹ else 1) *
        (1 - changeLevel hN f.dirichletLift p * (p : ℂ) ^ (-(2 * s - k + 1)))⁻¹ *
        (1 - (changeLevel hM g.dirichletLift ^ 2) p * (p : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ =
      (if (p : ℕ).Coprime Q then
        (1 - (qExpansion 1 g.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          g.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))⁻¹ else 1) *
        (1 - changeLevel hM g.dirichletLift p * (p : ℂ) ^ (-(2 * s - k + 1)))⁻¹ *
        (1 - (changeLevel hN f.dirichletLift ^ 2) p * (p : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  by_cases hpQ : (p : ℕ).Coprime Q
  swap
  · -- at a prime dividing `Q` every factor is `1`
    have h0 (χ : DirichletCharacter ℂ Q) : χ p = 0 :=
      MulChar.map_nonunit _ (mt (ZMod.isUnit_iff_coprime _ _).mp hpQ)
    simp only [ite_eq_right hpQ, h0, zero_mul, sub_zero, inv_one]
  -- at a prime `p ∤ Q` write `a = a_p`, `u = χ(p)`, `v = χ'(p)` and `Y = p^(-w)`
  have hpN := hpQ.coprime_dvd_right hN
  have hpM := hpQ.coprime_dvd_right hM
  set a := (qExpansion 1 f.toCuspForm).coeff p
  set u := f.dirichletLift p with hu
  set v := g.dirichletLift p with hv
  set X := (p : ℂ) ^ (-s)
  set Y := (p : ℂ) ^ (-(2 * s - k + 1)) with hY
  have hga : (qExpansion 1 g.toCuspForm).coeff p = a := (h p p.prop hpQ).symm
  have hYX : (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s) = Y := by
    rw [hY, ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hp0]
    congr 1
    push_cast
    ring
  have hY2 : (p : ℂ) ^ (-(2 * (2 * s - k + 1))) = Y ^ 2 := by
    rw [hY, ← Complex.cpow_nat_mul]
    congr 1
    push_cast
    ring
  have hsq (χ : DirichletCharacter ℂ Q) : (χ ^ 2) p = χ p ^ 2 := MulChar.pow_apply' χ two_ne_zero _
  -- `a (u - v) = 0`: if `a ≠ 0`, the Petersson adjoint relation gives `u = v`
  have hav : a * (u - v) = 0 := by
    by_cases ha : a = 0
    · rw [ha, zero_mul]
    have hf := f.qExpansion_coeff_eq_eigenvalue ⟨p, p.prop.pos⟩ hpN
    have hg := g.qExpansion_coeff_eq_eigenvalue ⟨p, p.prop.pos⟩ hpM
    simp only [PNat.mk_coe] at hf hg
    have := f.toEigenformAwayFromLevel.χ_unitOfCoprime_eq_of_eigenvalue_eq
      g.toEigenformAwayFromLevel p.prop hpN hpM (hf.symm.trans (hga.symm.trans hg)) (hf ▸ ha)
    rw [hu, hv, dirichletLift_apply_of_coprime f hpN, dirichletLift_apply_of_coprime g hpM]
    exact mul_eq_zero_of_right _ (sub_eq_zero.mpr (congrArg Units.val this))
  simp only [ite_eq_left hpQ, changeLevel_natCast_of_coprime _ _ hpQ, hsq, hga, ← hu, ← hv,
    mul_assoc, hYX, hY2, ← mul_inv]
  congr 1
  linear_combination (X * Y * (1 - u * Y) * (1 - v * Y)) * hav

/-- **The Euler-product identity of two newforms with the same good eigenvalues.** Let `f`, `g`
be newforms of weight `k` and levels `N`, `M`, both dividing `Q`, with
`a_p(f) = a_p(g)` at every prime `p ∤ Q`, and let `χ`, `χ'` be their nebentypes raised to level
`Q`. With `w = 2s - k + 1` and `E_p(f, s) = 1 - a_p(f) p^(-s) + χ(p) p^(k-1) p^(-2s)` (the
nebentypus extended by zero at the primes dividing `N`), on `Re s > (k + 1) / 2`

`L(f, s) ∏_{p ∣ Q} E_p(f, s) L(w, χ) L(2w, χ'²)`
`  = L(g, s) ∏_{p ∣ Q} E_p(g, s) L(w, χ') L(2w, χ²)`.

No relation between the nebentypes is assumed. -/
theorem LSeries_mul_prod_mul_LFunction_mul_LFunction_eq (f : Newform N k) (g : Newform M k)
    (hN : N ∣ Q) (hM : M ∣ Q)
    (h : ∀ p : ℕ, p.Prime → p.Coprime Q →
      (qExpansion 1 f.toCuspForm).coeff p = (qExpansion 1 g.toCuspForm).coeff p)
    {s : ℂ} (hs : ((k : ℝ) + 1) / 2 < s.re) :
    LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s *
        (∏ p ∈ Q.primeFactors, (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          f.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))) *
        LFunction (changeLevel hN f.dirichletLift) (2 * s - k + 1) *
        LFunction (changeLevel hM g.dirichletLift ^ 2) (2 * (2 * s - k + 1)) =
      LSeries (fun n ↦ (qExpansion 1 g.toCuspForm).coeff n) s *
        (∏ p ∈ Q.primeFactors, (1 - (qExpansion 1 g.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          g.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))) *
        LFunction (changeLevel hM g.dirichletLift) (2 * s - k + 1) *
        LFunction (changeLevel hN f.dirichletLift ^ 2) (2 * (2 * s - k + 1)) :=
  (hasProd_mul_prod_mul_LFunction f hN (changeLevel hM g.dirichletLift) hs).unique
    ((hasProd_mul_prod_mul_LFunction g hM (changeLevel hN f.dirichletLift) hs).congr_fun
      (localFactor_eq f g hN hM h s))

/-- The function `L(f, s) ∏_{p ∣ Q} E_p(f, s) L(w, χ) L(2w, ψ)` of
`L_mul_prod_mul_LFunction_mul_LFunction_eq`, with `w = 2s - k + 1`, is analytic away from the
two points `w = 1` and `2w = 1`. -/
private theorem analyticOnNhd_L_mul_prod_mul_LFunction_mul_LFunction (f : Newform N k)
    (hk : 0 < k) (χ ψ : DirichletCharacter ℂ Q) :
    AnalyticOnNhd ℂ (fun z ↦ ModularForm.L hk f.toCuspForm z *
        (∏ p ∈ Q.primeFactors, (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-z) +
          f.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * z))) *
        LFunction χ (2 * z - k + 1) * LFunction ψ (2 * (2 * z - k + 1)))
      {z | 2 * z - k + 1 ≠ 1 ∧ 2 * (2 * z - k + 1) ≠ 1} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_)
    ((isOpen_ne_fun (by fun_prop) (by fun_prop)).inter (isOpen_ne_fun (by fun_prop) (by fun_prop)))
  refine ((((CuspForm.differentiable_L hk f.toCuspForm) z).fun_mul
    (DifferentiableAt.fun_finsetProd fun p hp ↦ ?_)).fun_mul ?_).fun_mul ?_
  · have : NeZero (p : ℂ) := ⟨Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  · exact (differentiableAt_LFunction χ _ (Or.inl hz.1)).comp z (by fun_prop)
  · exact (differentiableAt_LFunction ψ _ (Or.inl hz.2)).comp z (by fun_prop)

/-- **The Euler-product identity of two newforms with the same good eigenvalues, continued to
`ℂ`.** Let `f`, `g` be newforms of positive weight `k` and levels `N`, `M`, both dividing `Q`,
with `a_p(f) = a_p(g)` at every prime `p ∤ Q`, and let `χ`, `χ'` be their nebentypes raised to
level `Q`. With `w = 2s - k + 1` and `E_p(f, s) = 1 - a_p(f) p^(-s) + χ(p) p^(k-1) p^(-2s)`,

`L(f, s) ∏_{p ∣ Q} E_p(f, s) L(w, χ) L(2w, χ'²)`
`  = L(g, s) ∏_{p ∣ Q} E_p(g, s) L(w, χ') L(2w, χ²)`

for the entire continuations `ModularForm.L` and the continued Dirichlet L-functions, at every
`s` with `w ≠ 1` and `2w ≠ 1`. -/
theorem L_mul_prod_mul_LFunction_mul_LFunction_eq (f : Newform N k) (g : Newform M k)
    (hk : 0 < k) (hN : N ∣ Q) (hM : M ∣ Q)
    (h : ∀ p : ℕ, p.Prime → p.Coprime Q →
      (qExpansion 1 f.toCuspForm).coeff p = (qExpansion 1 g.toCuspForm).coeff p)
    {s : ℂ} (hs₁ : 2 * s - k + 1 ≠ 1) (hs₂ : 2 * (2 * s - k + 1) ≠ 1) :
    ModularForm.L hk f.toCuspForm s *
        (∏ p ∈ Q.primeFactors, (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          f.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))) *
        LFunction (changeLevel hN f.dirichletLift) (2 * s - k + 1) *
        LFunction (changeLevel hM g.dirichletLift ^ 2) (2 * (2 * s - k + 1)) =
      ModularForm.L hk g.toCuspForm s *
        (∏ p ∈ Q.primeFactors, (1 - (qExpansion 1 g.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          g.dirichletLift p * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))) *
        LFunction (changeLevel hM g.dirichletLift) (2 * s - k + 1) *
        LFunction (changeLevel hN f.dirichletLift ^ 2) (2 * (2 * s - k + 1)) := by
  -- both sides are analytic off the two points `w = 1` and `2w = 1`, whose complement is
  -- connected, and they agree on the half-plane `Re s > k/2 + 1`
  set U : Set ℂ := {z | 2 * z - k + 1 ≠ 1 ∧ 2 * (2 * z - k + 1) ≠ 1}
  have hUc : IsPreconnected U := by
    convert (((Set.countable_singleton ((2 * (k : ℂ) - 1) / 4)).insert ((k : ℂ) / 2)
      ).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected using 1
    ext z
    simp only [U, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or]
    refine and_congr (not_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩) (not_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩)
    · linear_combination h / 2
    · rw [h]; ring
    · linear_combination h / 4
    · rw [h]; ring
  -- a point of the half-plane of absolute convergence
  set z₀ : ℂ := ((k + 2 : ℤ) : ℂ)
  have hz₀ : (k : ℝ) / 2 + 1 < z₀.re := by
    have : (0 : ℝ) < k := mod_cast hk
    rw [Complex.intCast_re]
    push_cast
    linarith
  have hz₀U : z₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [show 2 * z₀ - k + 1 = ((k + 5 : ℤ) : ℂ) by push_cast [z₀]; ring]
      exact_mod_cast (by omega : k + 5 ≠ 1)
    · rw [show 2 * (2 * z₀ - k + 1) = ((2 * k + 10 : ℤ) : ℂ) by push_cast [z₀]; ring]
      exact_mod_cast (by omega : 2 * k + 10 ≠ 1)
  refine (analyticOnNhd_L_mul_prod_mul_LFunction_mul_LFunction f hk _ _
    ).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_L_mul_prod_mul_LFunction_mul_LFunction g hk _ _) hUc hz₀U ?_ ⟨hs₁, hs₂⟩
  filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hz₀] with z hz
  have hz' : ((k : ℝ) + 1) / 2 < z.re := by
    have : (0 : ℝ) < k := mod_cast hk
    have : (k : ℝ) / 2 + 1 < z.re := hz
    linarith
  have hL {R : ℕ} [NeZero R] (F : Newform R k) :
      ModularForm.L hk F.toCuspForm z = LSeries (fun n ↦ (qExpansion 1 F.toCuspForm).coeff n) z :=
    by simpa using (CuspForm.LSeries_qExpansion_coeff_eq hk F.toCuspForm hz).symm
  simp only [hL]
  exact LSeries_mul_prod_mul_LFunction_mul_LFunction_eq f g hN hM h hz'

end HeckeRing.GL2.Newform
