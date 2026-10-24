/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.RingTheory.PowerSeries.Evaluation
-- Proof-only: lowest homogeneous components of powers.
import TauCeti.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Power series substitution: nilpotent series, orders, algebra maps, and the binomial series

Mathlib substitutes a power series `b` with nilpotent constant coefficient into a power series
`f` through `PowerSeries.subst b f`, and records the side condition on `b` as
`PowerSeries.HasSubst b`.

Over a ring without zero divisors, substituting a series `φ` of zero constant coefficient
multiplies orders: `ord (f (φ)) = ord φ * ord f`. Mathlib records only the inequality
`PowerSeries.le_order_subst`. The equality shows that substitution of a nonzero such `φ` is
injective, which is what extends it to Laurent series by passing to fraction fields.

Substitution of series of zero constant coefficient is compatible with congruences modulo
powers of `X`, in both the substituted series and the series substituted into. This makes
truncation modulo `X ^ n` compatible with composition of formal coordinates. Substituting a
multivariate series `φ` of zero constant coefficient into `f = c Xⁿ + ⋯` gives
`f (φ) = c φ₁ ^ n + ⋯` in lowest degree, where `φ₁` is the linear part of `φ`. For a family of
series substituted into a multivariate series `G`, a perturbation `X ^ m * r` of the entry `a s`
is invisible below degree `m` and acts in degree `m` through the coefficient of `Xₛ` alone;
this drives degree-by-degree solutions of equations such as `G(f(X), X) = 0`.

Substitution at a nilpotent series depends on only finitely many coefficients. The substituted
series may be multivariate, with coefficients in an algebra over the coefficient ring. At a
nilpotent constant it is the constant series obtained by evaluating a finite polynomial truncation.
This connects formal identities with polynomial maps on nilpotent elements.

An algebra map on power series whose value at `X` has nilpotent constant coefficient is the
corresponding substitution, without any continuity hypothesis. Over a field, every algebra
endomorphism of the power series ring has this form. In particular, a perturbation `X + h` of `X`
with `h ^ 2 = 0` substitutes by the first-order Taylor formula `f (X + h) = f + h f'`, since the
right-hand side is multiplicative in `f` by the Leibniz rule.

This file also records that the substitution `X ↦ (1 + X) ^ u - 1`, for a binomial series
`(1 + X) ^ u`, is legitimate: it is the change of variable relating the power-series coordinates
of a completed group algebra attached to two topological generators.

## Main results

* `PowerSeries.HasSubst.C`: a nilpotent constant can be substituted.
* `PowerSeries.subst_one`: substitution preserves the constant series one.
* `PowerSeries.subst_eq_aeval_trunc_of_pow_eq_zero`: substitution at a series with a vanishing
  power is evaluation of a finite truncation.
* `PowerSeries.subst_C_eq_C_aeval_trunc`: substitution at a nilpotent constant is the constant
  series obtained by evaluating a finite truncation.
* `PowerSeries.order_subst`: `ord (f (φ)) = ord φ * ord f` when `φ` has zero constant
  coefficient.
* `PowerSeries.subst_eq_zero_iff`: substitution of a nonzero `φ` of zero constant coefficient
  has trivial kernel.
* `PowerSeries.toNat_order_ne_zero`: such a `φ` has positive integer order.
* `PowerSeries.coeff_one_subst`: linear coefficients multiply under substitution.
* `PowerSeries.X_pow_dvd_subst`: substitution preserves divisibility by `X ^ n`.
* `PowerSeries.X_pow_dvd_subst_sub_subst`: substitution respects congruence modulo `X ^ n` of
  the substituted series.
* `PowerSeries.homogeneousComponent_subst_of_le_order`: if `f` has order at least `n`, the
  degree-`n` homogeneous component of `f (φ)` is `c φ₁ ^ n`, for `c` the coefficient of `Xⁿ` in
  `f` and `φ₁` the linear part of `φ`.
* `PowerSeries.coeff_subst_update_add_X_pow_mul`: perturbing one entry `a s` of a substituted
  family by `X ^ m * r` changes coefficients only from degree `m` on, and in degree `m` only
  through the linear term `Xₛ` of the multivariate series.
* `PowerSeries.algHom_eq_substAlgHom`: an algebra map `R⟦X⟧ → S⟦X⟧` sending `X` to a
  substitutable series is a substitution.
* `PowerSeries.subst_X_add_of_sq_eq_zero`: `f (X + h) = f + h f'` when `h ^ 2 = 0`.
* `AlgHom.apply_eq_subst`: over a field, every algebra endomorphism of `K⟦X⟧` is substitution by
  its value at `X`.
* `TauCeti.hasSubst_binomialSeries_sub_one`: `(1 + X) ^ u - 1` can be substituted.
-/

public section

namespace PowerSeries

/-- A nilpotent constant can be substituted into a power series. -/
theorem HasSubst.C {R : Type*} [CommRing R] {x : R} (hx : IsNilpotent x) :
    HasSubst (C x) := by
  simpa only [HasSubst, ← constantCoeff_eq, constantCoeff_C] using hx

/-- Substitution preserves the constant series one. -/
@[simp]
theorem subst_one {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {τ : Type*} {a : MvPowerSeries τ S} (ha : HasSubst a) :
    (1 : R⟦X⟧).subst a = 1 := by
  rw [← coe_substAlgHom ha, map_one]

section Nilpotent

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Substituting a possibly multivariate series over an `R`-algebra whose `n`th power vanishes
uses only the coefficients below `n`. -/
theorem subst_eq_aeval_trunc_of_pow_eq_zero {τ : Type*} {a : MvPowerSeries τ S} {n : ℕ}
    (hn : a ^ n = 0) (f : R⟦X⟧) :
    f.subst a = Polynomial.aeval a (trunc n f) := by
  have ha : HasSubst a := IsNilpotent.map ⟨n, hn⟩ MvPowerSeries.constantCoeff
  conv_lhs => rw [eq_X_pow_mul_shift_add_trunc n f]
  rw [subst_add ha, subst_mul ha, subst_pow ha, subst_X ha, hn, zero_mul, zero_add,
    subst_coe ha]

/-- A nilpotent constant in an `R`-algebra substitutes by algebra evaluation of a finite
truncation. -/
theorem subst_C_eq_C_aeval_trunc {x : S} {n : ℕ} (hn : x ^ n = 0) (f : R⟦X⟧) :
    f.subst (C x) = C (Polynomial.aeval x (trunc n f)) := by
  rw [subst_eq_aeval_trunc_of_pow_eq_zero (n := n) (by rw [← map_pow, hn, map_zero])]
  simpa only [IsScalarTower.toAlgHom_apply, algebraMap_eq] using
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R S S⟦X⟧) x (trunc n f)

end Nilpotent

/-- A nonzero power series of zero constant coefficient has positive integer order, so it
multiplies orders under substitution by a positive integer. -/
theorem toNat_order_ne_zero {R : Type*} [Semiring R] {φ : R⟦X⟧} (hφ : constantCoeff φ = 0)
    (hφ₀ : φ ≠ 0) : φ.order.toNat ≠ 0 := by
  rw [Ne, ENat.toNat_eq_zero, not_or, order_eq_top]
  exact ⟨order_ne_zero_iff_constCoeff_eq_zero.mpr hφ, hφ₀⟩

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {φ : R⟦X⟧}

/-- Substituting a power series `φ` of zero constant coefficient multiplies orders:
`ord (f (φ)) = ord φ * ord f`. -/
theorem order_subst (hφ : constantCoeff φ = 0) (f : R⟦X⟧) :
    PowerSeries.order (f.subst φ) = φ.order * f.order := by
  have ha : HasSubst φ := .of_constantCoeff_zero' hφ
  rcases eq_or_ne f 0 with rfl | hf
  · rw [← coe_substAlgHom ha, map_zero, order_zero, ENat.mul_top]
    exact order_ne_zero_iff_constCoeff_eq_zero.mpr hφ
  have : Nontrivial R := have := nontrivial_of_ne f 0 hf; (C (R := R)).domain_nontrivial
  -- Write `f = X ^ m * g` with `m = ord f`; then `g (φ)` has the nonzero constant coefficient
  -- of `g`, so it has order zero.
  have hg : PowerSeries.order (f.divXPowOrder.subst φ) = 0 := by
    rw [← not_ne_iff, order_ne_zero_iff_constCoeff_eq_zero]
    have h := constantCoeff_subst_of_constantCoeff_zero hφ f.divXPowOrder
    rw [Algebra.algebraMap_self_apply] at h
    -- `h` is stated with the multivariate constant coefficient, which is the univariate one
    rw [show constantCoeff (f.divXPowOrder.subst φ) = f.divXPowOrder.constantCoeff from h]
    exact constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf
  nth_rw 1 [← X_pow_order_mul_divXPowOrder (f := f)]
  rw [subst_mul ha, subst_pow ha, subst_X ha, order_mul, order_pow, hg, add_zero, nsmul_eq_mul,
    coe_toNat_order hf, mul_comm]

/-- Substituting a nonzero power series `φ` of zero constant coefficient sends only `0` to `0`. -/
theorem subst_eq_zero_iff (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {f : R⟦X⟧} :
    (f.subst φ : R⟦X⟧) = 0 ↔ f = 0 := by
  have h₀ := order_ne_zero_iff_constCoeff_eq_zero.mpr hφ
  have h₁ : φ.order ≠ ⊤ := order_eq_top.not.mpr hφ₀
  rw [← order_eq_top, ← order_eq_top (φ := f), order_subst hφ]
  exact WithTop.mul_eq_top_iff.trans (by tauto)

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The linear coefficient of `f (a)`, for `a` of zero constant coefficient, is the product of
the linear coefficients of `f` and `a`. -/
theorem coeff_one_subst {a : S⟦X⟧} (ha : constantCoeff a = 0) (f : R⟦X⟧) :
    coeff 1 (f.subst a) = algebraMap R S (coeff 1 f) * coeff 1 a := by
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr ha
  rw [coeff_subst' (.of_constantCoeff_zero' ha), finsum_eq_single _ 1, pow_one, Algebra.smul_def]
  -- `(X * b) ^ d` has no linear term unless `d = 1`
  rintro (_ | _ | d) hd
  · simp
  · exact absurd rfl hd
  · simp [mul_pow, coeff_X_pow_mul']

/-- An `R`-algebra map `σ : R⟦X⟧ → S⟦X⟧` such that `σ X` can be substituted is the
substitution `f ↦ f (σ X)`. No continuity hypothesis is needed. -/
theorem algHom_eq_substAlgHom {σ : R⟦X⟧ →ₐ[R] S⟦X⟧} (hσ : HasSubst (σ X)) :
    σ = substAlgHom hσ := by
  have hpoly (g : Polynomial R) : σ (g : R⟦X⟧) = substAlgHom hσ (g : R⟦X⟧) := by
    rw [algHom_coe_eq_aeval, algHom_coe_eq_aeval, substAlgHom_X]
  refine AlgHom.ext fun f ↦ ext fun n ↦ ?_
  obtain ⟨m, hm⟩ := (hσ.eventually_coeff_pow_eq_zero n).exists_forall_of_atTop
  have key (g : S⟦X⟧) : coeff n (σ X ^ m * g) = 0 := by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [hm m le_rfl p.1 (by grind [Finset.mem_antidiagonal]), zero_mul]
  -- The maps agree on the polynomial truncation. The remaining multiple of `X ^ m` has
  -- zero coefficients through degree `n` after either map is applied.
  rw [eq_X_pow_mul_shift_add_trunc m f]
  simp only [map_add, map_mul, map_pow, substAlgHom_X, key, zero_add]
  rw [hpoly]

/-- The first-order Taylor formula: substituting a square-zero perturbation `X + h` of `X` gives
`f (X + h) = f + h f'`. -/
theorem subst_X_add_of_sq_eq_zero {h : S⟦X⟧} (hh : h ^ 2 = 0) (f : S⟦X⟧) :
    f.subst (X + h) = f + h * d⁄dX f := by
  -- `f ↦ f + h f'` is an algebra map, multiplicative by the Leibniz rule and `h ^ 2 = 0`, and it
  -- sends `X` to `X + h`, so it is the substitution of `X + h`.
  let T : S⟦X⟧ →ₐ[S] S⟦X⟧ :=
    { toFun g := g + h * d⁄dX g
      map_one' := by simp
      map_mul' g₁ g₂ := by
        simp only [Derivation.leibniz, smul_eq_mul]
        linear_combination (-(d⁄dX g₁ * d⁄dX g₂)) * hh
      map_zero' := by simp
      map_add' g₁ g₂ := by
        simp only [map_add]
        ring
      commutes' r := by simp }
  have hT (g : S⟦X⟧) : T g = g + h * d⁄dX g := rfl
  have hTX : T X = X + h := by rw [hT, derivative_X, mul_one]
  have hσ := congr($(algHom_eq_substAlgHom (σ := T) (hTX ▸ HasSubst.X'.add (.map ⟨2, hh⟩ _))) f)
  rw [coe_substAlgHom, hTX, hT] at hσ
  exact hσ.symm

/-- Substituting a series of zero constant coefficient preserves divisibility by `X ^ n`. -/
theorem X_pow_dvd_subst {a : S⟦X⟧} (ha : constantCoeff a = 0) {n : ℕ} {f : R⟦X⟧}
    (hf : X ^ n ∣ f) : X ^ n ∣ f.subst a := by
  have ha' : HasSubst a := .of_constantCoeff_zero' ha
  obtain ⟨g, rfl⟩ := hf
  rw [subst_mul ha', subst_pow ha', subst_X ha']
  exact (pow_dvd_pow_of_dvd (X_dvd_iff.mpr ha) n).mul_right _

/-- Substitution respects congruence modulo `X ^ n` of the substituted series: if `a ≡ b` modulo
`X ^ n`, then `f (a) ≡ f (b)` modulo `X ^ n`. -/
theorem X_pow_dvd_subst_sub_subst {a b : S⟦X⟧} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) {n : ℕ} (hab : X ^ n ∣ a - b) (f : R⟦X⟧) :
    X ^ n ∣ f.subst a - f.subst b := by
  have ha' : HasSubst a := .of_constantCoeff_zero' ha
  have hb' : HasSubst b := .of_constantCoeff_zero' hb
  -- On the polynomial truncation this is `a - b ∣ p (a) - p (b)`; the remaining multiple of
  -- `X ^ n` stays one after either substitution.
  rw [eq_X_pow_mul_shift_add_trunc n f, subst_add ha', subst_add hb', add_sub_add_comm]
  refine dvd_add (dvd_sub (X_pow_dvd_subst ha (dvd_mul_right _ _))
    (X_pow_dvd_subst hb (dvd_mul_right _ _))) (hab.trans ?_)
  rw [subst_coe ha', subst_coe hb', ← Polynomial.eval_map_algebraMap,
    ← Polynomial.eval_map_algebraMap]
  exact Polynomial.sub_dvd_eval_sub _ _ _

/-- **The lowest homogeneous component of a substitution.** If `φ` is a multivariate power
series of zero constant coefficient and `f` has order at least `n`, then the degree-`n` homogeneous
component of `f (φ)` is `c φ₁ ^ n`, where `c` is the coefficient of `Xⁿ` in `f` and `φ₁` is the
linear part of `φ`. -/
theorem homogeneousComponent_subst_of_le_order {σ : Type*} {φ : MvPowerSeries σ S}
    (hφ : MvPowerSeries.constantCoeff φ = 0) {f : R⟦X⟧} {n : ℕ} (hn : n ≤ f.order) :
    MvPowerSeries.homogeneousComponent n (f.subst φ) =
      MvPowerSeries.C (algebraMap R S (coeff n f)) *
        MvPowerSeries.homogeneousComponent 1 φ ^ n := by
  have hφ' : HasSubst φ := .of_constantCoeff_zero hφ
  obtain ⟨g, rfl⟩ : X ^ n ∣ f :=
    X_pow_dvd_iff.mpr fun m hm ↦ coeff_of_lt_order m ((Nat.cast_lt.mpr hm).trans_le hn)
  -- `f (φ) = φ ^ n * g (φ)`, and the degree-zero component of `g (φ)` is its constant term
  have hmul := MvPowerSeries.homogeneousComponent_mul_of_le_order (p := n) (q := 0)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hφ)
    (zero_le (a := (g.subst φ : MvPowerSeries σ S).order))
  have hpow := MvPowerSeries.homogeneousComponent_pow_of_le_order (p := 1)
    (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hφ) n
  simp only [add_zero, mul_one] at hmul hpow
  rw [subst_mul hφ', subst_pow hφ', subst_X hφ', hmul, hpow]
  simp [mul_comm, constantCoeff_subst_of_constantCoeff_zero hφ, coeff_mul_X_pow']

end Algebra

section Perturbation

variable {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Two series of zero constant coefficient can be substituted as a pair. -/
theorem hasSubst_pair {f g : S⟦X⟧} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    MvPowerSeries.HasSubst ![f, g] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s ↦ by
    fin_cases s <;> simp [← constantCoeff_eq, hf, hg]

/-- Perturbing `f` by `X ^ m * r` in `f ^ i * c` changes the coefficient of degree `m` by
`i * 0 ^ (i - 1) * r(0) * c(0)`, and no coefficient of lower degree. -/
private theorem coeff_add_X_pow_mul_pow_mul {f : S⟦X⟧} (hf : constantCoeff f = 0) (r c : S⟦X⟧)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≤ m) (i : ℕ) :
    coeff n ((f + X ^ m * r) ^ i * c) = coeff n (f ^ i * c) +
      if n = m then (i : S) * 0 ^ (i - 1) * constantCoeff r * constantCoeff c else 0 := by
  have hfr : constantCoeff (f + X ^ m * r) = 0 := by simp [hf, hm]
  have h : (f + X ^ m * r) ^ i * c - f ^ i * c =
      X ^ m * ((∑ k ∈ Finset.range i, (f + X ^ m * r) ^ k * f ^ (i - 1 - k)) * r * c) := by
    rw [← sub_mul, ← geom_sum₂_mul, add_sub_cancel_left]
    ring
  rw [← sub_eq_iff_eq_add', ← map_sub, h, coeff_X_pow_mul']
  by_cases hnm : n = m
  · -- the constant coefficient of the geometric sum is `i * 0 ^ (i - 1)`
    simp [hnm, map_sum, hf, hfr, geom_sum₂_self, mul_assoc]
  · simp [hnm, show ¬ m ≤ n by omega]

/-- Perturbing the entry `a s` of a substituted family `a` by `X ^ m * r` leaves the
coefficients of degree below `m` unchanged, and changes the coefficient of degree `m` by
`r(0)` times the coefficient of `Xₛ` in `G`. -/
theorem coeff_subst_update_add_X_pow_mul [DecidableEq σ] (G : MvPowerSeries σ R)
    {a : σ → S⟦X⟧} (ha : MvPowerSeries.HasSubst a) (ha₀ : ∀ t, constantCoeff (a t) = 0) (s : σ)
    (r : S⟦X⟧) {m n : ℕ} (hm : m ≠ 0) (hn : n ≤ m) :
    coeff n (G.subst (Function.update a s (a s + X ^ m * r))) = coeff n (G.subst a) +
      if n = m then
        algebraMap R S (MvPowerSeries.coeff (Finsupp.single s 1) G) * constantCoeff r
      else 0 := by
  set b := Function.update a s (a s + X ^ m * r) with hb_def
  have hb : MvPowerSeries.HasSubst b := by
    refine ⟨fun t ↦ ?_, fun d ↦ ((ha.coeff_zero d).union (Set.finite_singleton s)).subset
      fun t ht ↦ ?_⟩
    · rcases eq_or_ne t s with rfl | ht
      · simp [b, ← constantCoeff_eq, ha₀, hm]
      · simp [b, ht, ← constantCoeff_eq, ha₀]
    · rcases eq_or_ne t s with rfl | hts
      · exact Or.inr rfl
      · exact Or.inl (by simpa [b, hts] using ht)
  -- each monomial splits as a power of the perturbed entry times a factor `c d` not involving it
  set c : (σ →₀ ℕ) → S⟦X⟧ := fun d ↦ (d.erase s).prod fun t e ↦ a t ^ e
  have hprod (x : σ → S⟦X⟧) (hx : ∀ t ≠ s, x t = a t) (d : σ →₀ ℕ) :
      (d.prod fun t e ↦ x t ^ e) = x s ^ d s * c d := by
    rw [← Finsupp.mul_prod_erase' d s _ fun _ ↦ pow_zero _]
    congr 1
    exact Finsupp.prod_congr fun t ht ↦ by rw [hx t (by rintro rfl; simp at ht)]
  have key (d : σ →₀ ℕ) : coeff n (d.prod fun t e ↦ b t ^ e) =
      coeff n (d.prod fun t e ↦ a t ^ e) +
        if n = m then (d s : S) * 0 ^ (d s - 1) * constantCoeff r * constantCoeff (c d) else 0 := by
    rw [hprod b (fun t ht ↦ Function.update_of_ne ht _ _) d, hprod a (fun _ _ ↦ rfl) d,
      hb_def, Function.update_self]
    exact coeff_add_X_pow_mul_pow_mul (ha₀ s) r (c d) hm hn (d s)
  -- only the monomial `Xₛ` feels the perturbation in degree `m`
  have hw (d : σ →₀ ℕ) (hd : d ≠ Finsupp.single s 1) :
      (d s : S) * 0 ^ (d s - 1) * constantCoeff r * constantCoeff (c d) = 0 := by
    by_cases h₁ : d.erase s = 0
    · have h₀ : d s ≠ 1 := fun h₀ ↦ hd <| by
        rw [← Finsupp.single_add_erase s d, h₁, h₀, add_zero]
      rcases Nat.lt_or_gt_of_ne h₀ with h₀ | h₀
      · simp [show d s = 0 by omega]
      · simp [zero_pow (show d s - 1 ≠ 0 by omega)]
    · obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr h₁
      have hc : constantCoeff (c d) = 0 := by
        simp only [c, Finsupp.prod, map_prod, map_pow, ha₀]
        exact Finset.prod_eq_zero ht (zero_pow (Finsupp.mem_support_iff.mp ht))
      simp [hc]
  have hA := MvPowerSeries.coeff_subst_finite ha G (Finsupp.single () n)
  rw [coeff, MvPowerSeries.coeff_subst hb, MvPowerSeries.coeff_subst ha]
  rw [← coeff_def Finsupp.single_eq_same] at hA ⊢
  simp_rw [key, smul_add]
  rw [finsum_add_distrib hA, add_right_inj, finsum_eq_single _ (Finsupp.single s 1)]
  · split_ifs <;> simp [c, Algebra.smul_def]
  · intro d hd
    simp [hw d hd]
  · refine (Set.finite_singleton (Finsupp.single s 1)).subset fun d hd ↦ ?_
    by_contra h
    exact hd (by simp [hw d h])

end Perturbation

end PowerSeries

section Field

open PowerSeries

/-- Over a field `K`, every `K`-algebra endomorphism of `K⟦X⟧` sends `X` to a series of zero
constant coefficient. -/
theorem AlgHom.constantCoeff_apply_X {K : Type*} [Field K] (σ : K⟦X⟧ →ₐ[K] K⟦X⟧) :
    constantCoeff (σ X) = 0 := by
  by_contra hc
  -- If the constant coefficient were `c ≠ 0`, the unit `X - c` would map to a nonunit.
  have hu : IsUnit (X - C (constantCoeff (σ X)) : K⟦X⟧) := by
    simpa [isUnit_iff_constantCoeff] using hc
  have hσ : σ (X - C (constantCoeff (σ X))) = σ X - C (constantCoeff (σ X)) := by
    rw [map_sub, ← algebraMap_eq, AlgHom.commutes]
  simpa [hσ, isUnit_iff_constantCoeff] using hu.map σ

/-- Over a field `K`, every `K`-algebra endomorphism `σ` of `K⟦X⟧` is the substitution
`f ↦ f (σ X)`. -/
theorem AlgHom.apply_eq_subst {K : Type*} [Field K] (σ : K⟦X⟧ →ₐ[K] K⟦X⟧) (f : K⟦X⟧) :
    σ f = f.subst (σ X) := by
  let hσ : HasSubst (σ X) := .of_constantCoeff_zero' σ.constantCoeff_apply_X
  rw [← coe_substAlgHom hσ, ← algHom_eq_substAlgHom hσ]

end Field

namespace TauCeti

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The binomial series `(1 + X) ^ u - 1` has constant coefficient zero, so power series can be
substituted into it. -/
theorem hasSubst_binomialSeries_sub_one [BinomialRing R] (u : R) :
    HasSubst (binomialSeries S u - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

end TauCeti
