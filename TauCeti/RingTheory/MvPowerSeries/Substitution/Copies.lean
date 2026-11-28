/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.MvPowerSeries.Derivative
import Mathlib.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.Normed.Ring.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import TauCeti.Data.Finsupp.MapDomain.Prod

/-!
# Substituting a linear combination of copies of the variables

For a finite type `K` and coefficients `a : K → R`, the substitution
`copySubst a : F ↦ F (∑ k, a k • z_k)` replaces each variable `z_x` of a power series `F` by the
same linear combination `∑ k, a k • z_(x, k)` of `K` copies of it. The copy `k` of the variable
`x` is the variable `(x, k)` of `MvPowerSeries (σ × K) R`. The set `σ` of variables may be
infinite; the chain rule and the coefficient formula take it finite.

Products `∏ c, G_c (z_c)` of series in separate copies of the variables arise in this way, and
the substitution of copies writes a coefficient of such a product as an integral combination of
coefficients of the factors. The coefficient formula is the multinomial theorem: the coefficient
of `z ^ γ` in `F (∑ a_k z_k)` is `a ^ γ` times a product of multinomial coefficients times the
coefficient of `F` at the exponent `γ.mapDomain Prod.fst`, which adds up the copies of each
variable. Over an ultrametric ring with integral `a_k`, the coefficients of `F (∑ a_k z_k)` are
therefore no larger than those of `F`.

## Main definitions and results

* `MvPowerSeries.copySubst a`: the algebra map `F ↦ F (∑ k, a k • z_k)`.
* `MvPowerSeries.pderiv_copySubst`: the chain rule.
* `MvPowerSeries.killCompl_copySubst`: setting all copies but one to zero gives `F (a_k z)`.
* `MvPowerSeries.rescale_copySubst`, `MvPowerSeries.map_copySubst`: compatibility with scaling
  and with ring maps.
* `MvPowerSeries.coeff_copySubst`: the coefficients, by the multinomial theorem.
* `MvPowerSeries.norm_coeff_copySubst_le`: over an ultrametric ring, integral `a_k` do not
  enlarge coefficients.

## References

* `hasSubst_sum_smul_X`, `copySubst`, `copySubst_apply`, `pderiv_copySubst`, `map_copySubst`,
  `killCompl_copySubst`, `rescale_copySubst`, `coeff_copySubst` and `norm_coeff_copySubst_le` are
  adapted from `New.hasSubst_sum_smul_X`, `New.copySubst`, `New.copySubst_apply`,
  `New.pderiv_copySubst`, `New.map_copySubst`, `New.killCompl_copySubst`,
  `New.rescale_copySubst`, `New.coeff_copySubst` and `New.norm_coeff_copySubst_le` in
  `src/New/Derivatives/Sharpness/LeastValuation.lean` of
  <https://github.com/leanprover-community/riemann-hypothesis/tree/3ad0b4b58709>. There the
  variables are finite, the coefficient formula is proved over a domain of characteristic zero,
  from a factorial identity through jets along linear substitutions, and the norm bound is over
  `ℂ_[p]`. Here the substitution allows any set of variables, the formula holds over every
  commutative ring, proved by the multinomial theorem, and the bound holds over every ultrametric
  seminormed commutative ring with `‖1‖ = 1`; its intermediate step
  `MvPowerSeries.coeff_prod_sum_smul_X_pow` is new.
-/

public section

namespace MvPowerSeries

open Finset

variable {σ K R : Type*} [Fintype K] [CommRing R]

/-- The linear forms `∑ k, a k • z_(x, k)` can be substituted, for any set of variables: they
have no constant term, and a monomial occurs in the forms of only finitely many variables. -/
theorem hasSubst_sum_smul_X (a : K → R) :
    HasSubst fun x : σ ↦ ∑ k : K, a k • (X (x, k) : MvPowerSeries (σ × K) R) := by
  classical
  refine ⟨fun _ ↦ by simp, fun d ↦ (d.support.image Prod.fst).finite_toSet.subset fun x hx ↦ ?_⟩
  obtain ⟨k, -, hk⟩ :=
    exists_ne_zero_of_sum_ne_zero (by simpa only [Set.mem_ofPred_eq, map_sum] using hx)
  rw [coeff_smul, coeff_X] at hk
  split_ifs at hk with h
  · exact mem_image.2 ⟨(x, k), by simp [h], rfl⟩
  · exact absurd (mul_zero _) hk

/-- The substitution `F ↦ F (∑ k, a k • z_k)` of a linear combination of copies `z_k` of the
variables, with the same coefficients `a k` for every variable. The copy `k` of the variable `x`
is the variable `(x, k)`. -/
noncomputable def copySubst (a : K → R) : MvPowerSeries σ R →ₐ[R] MvPowerSeries (σ × K) R :=
  substAlgHom (hasSubst_sum_smul_X a)

theorem copySubst_def (a : K → R) :
    copySubst (σ := σ) a = substAlgHom (hasSubst_sum_smul_X a) := by
  rfl

theorem copySubst_apply (a : K → R) (F : MvPowerSeries σ R) :
    copySubst a F = F.subst fun x : σ ↦ ∑ k : K, a k • (X (x, k) : MvPowerSeries (σ × K) R) :=
  by rw [copySubst_def, substAlgHom_apply]

/-- The variable `z_x` goes to the linear form `∑ k, a k • z_(x, k)`. -/
@[simp]
theorem copySubst_X (a : K → R) (x : σ) :
    copySubst a (X x : MvPowerSeries σ R) = ∑ k : K, a k • X (x, k) := by
  rw [copySubst_apply, subst_X (hasSubst_sum_smul_X a)]

/-- **The chain rule** for copies: the derivative of `F (∑ a_l z_l)` in the copy `k` of the
variable `x` is `a k` times `(∂_x F) (∑ a_l z_l)`. -/
theorem pderiv_copySubst [Finite σ] (a : K → R) (F : MvPowerSeries σ R) (x : σ) (k : K) :
    pderiv (x, k) (copySubst a F) = a k • copySubst a (pderiv x F) := by
  classical
  have := Fintype.ofFinite σ
  have h_form (y : σ) : pderiv (x, k) (∑ k' : K, a k' • (X (y, k') : MvPowerSeries (σ × K) R)) =
      if y = x then a k • (1 : MvPowerSeries (σ × K) R) else 0 := by
    simp [pderiv_X, Pi.single_apply, Prod.ext_iff, ite_and]
  simp [copySubst_apply, pderiv_subst (hasSubst_sum_smul_X a), h_form, -map_sum]

/-- The substitution of copies commutes with a change of coefficients along a ring map. -/
theorem map_copySubst {S : Type*} [CommRing S] (f : R →+* S) (a : K → R)
    (F : MvPowerSeries σ R) :
    map f (copySubst a F) = copySubst (fun k : K ↦ f (a k)) (map f F) := by
  rw [copySubst_apply, copySubst_apply, map_subst (hasSubst_sum_smul_X a)]
  simp [smul_eq_C_mul]

/-- Setting all copies but the `k`-th to zero turns `F (∑ a_l z_l)` into `F (a_k z)`. -/
theorem killCompl_copySubst (a : K → R) (F : MvPowerSeries σ R) (k : K) :
    killCompl (Function.Embedding.sectL σ k) (copySubst a F) = rescale (fun _ : σ ↦ a k) F := by
  classical
  have h_form (x : σ) : killCompl (Function.Embedding.sectL σ k)
      (∑ k' : K, a k' • (X (x, k') : MvPowerSeries (σ × K) R)) = a k • X x := by
    rw [map_sum, sum_eq_single_of_mem k (mem_univ k), map_smul]
    · exact congrArg (a k • ·) (killCompl_X x)
    exact fun k' _ hk' ↦ by simp [killCompl_X_eq_zero, Prod.ext_iff, hk'.symm]
  ext d
  -- Both coefficients are sums over the monomials of `F`; compare them term by term.
  rw [coeff_killCompl, copySubst_apply, coeff_subst (hasSubst_sum_smul_X a), rescale_eq_subst,
    coeff_subst (HasSubst.smul_X _)]
  refine finsum_congr fun n ↦ ?_
  simp only [← coeff_killCompl, map_finsuppProd, map_pow, h_form, Pi.smul_apply']

/-- Scaling all variables by `r` commutes with the substitution of copies: both composites send
`F` to `F (∑ r a_k z_k)`. -/
theorem rescale_copySubst (a : K → R) (r : R) (F : MvPowerSeries σ R) :
    rescale (fun _ : σ × K ↦ r) (copySubst a F) = copySubst a (rescale (fun _ : σ ↦ r) F) := by
  have ha := hasSubst_sum_smul_X (σ := σ) a
  have hr := HasSubst.smul_X (σ := σ × K) (fun _ ↦ r)
  rw [copySubst_apply, copySubst_apply, rescale_eq_subst, rescale_eq_subst,
    subst_comp_subst_apply ha hr, subst_comp_subst_apply (HasSubst.smul_X _) ha]
  congr 1
  funext x
  -- Both sides are the linear form `∑ r a_k z_k`.
  trans ∑ k : K, r • a k • (X (x, k) : MvPowerSeries (σ × K) R)
  · simp only [← coe_substAlgHom hr, map_sum, map_smul, substAlgHom_X, Pi.smul_apply',
      smul_comm r]
  · symm
    rw [Pi.smul_apply', ← coe_substAlgHom ha, map_smul, substAlgHom_X, smul_sum]

section Fintype

variable [Fintype σ]

/-- **The multinomial theorem for copies.** The coefficient of `z ^ γ` in the product of the
powers `(∑ k, a k • z_(x, k)) ^ d x` is `a ^ γ` times the product of the multinomial coefficients
of the exponents `γ (x, k)`, `k : K`, if the copies of each variable `x` in `γ` add up to `d x`,
and zero otherwise. -/
theorem coeff_prod_sum_smul_X_pow [DecidableEq σ] (a : K → R) (d : σ →₀ ℕ) (γ : σ × K →₀ ℕ) :
    coeff γ (∏ x : σ, (∑ k : K, a k • (X (x, k) : MvPowerSeries (σ × K) R)) ^ d x) =
      if γ.mapDomain Prod.fst = d then
        (∏ y : σ × K, a y.2 ^ γ y) * ∏ x : σ, (Nat.multinomial univ fun k : K ↦ γ (x, k) : R)
      else 0 := by
  classical
  -- Expand each power by the multinomial theorem into monomials.
  have h_pow (x : σ) : (∑ k : K, a k • (X (x, k) : MvPowerSeries (σ × K) R)) ^ d x =
      ∑ f ∈ piAntidiag univ (d x), monomial (∑ k : K, Finsupp.single (x, k) (f k))
        ((Nat.multinomial univ f : R) * ∏ k : K, a k ^ f k) := by
    rw [sum_pow_eq_sum_piAntidiag]
    refine sum_congr rfl fun f _ ↦ ?_
    simp_rw [smul_pow, X_pow_eq, smul_eq_C_mul, ← monomial_zero_eq_C_apply, monomial_mul_monomial,
      zero_add, mul_one]
    rw [prod_monomial, ← map_natCast (C (σ := σ × K) (R := R)), ← monomial_zero_eq_C_apply,
      monomial_mul_monomial, zero_add]
  -- The exponent of the term of a choice `F` determines `F`.
  have h_exp (F : σ → K → ℕ) : γ = (∑ x : σ, ∑ k : K, Finsupp.single (x, k) (F x k)) ↔
      (fun x k ↦ γ (x, k)) = F := by
    have h_apply (y : σ × K) : (∑ x : σ, ∑ k : K, Finsupp.single (x, k) (F x k)) y = F y.1 y.2 := by
      simp [Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.ext_iff, ite_and]
    constructor
    · rintro h
      funext x k
      rw [h, h_apply]
    · rintro rfl
      ext y
      rw [h_apply]
  have h_mem : (fun x k ↦ γ (x, k)) ∈ Fintype.piFinset (fun x : σ ↦ piAntidiag univ (d x)) ↔
      γ.mapDomain Prod.fst = d := by
    simp [Fintype.mem_piFinset, mem_piAntidiag, Finsupp.ext_iff, Finsupp.mapDomain_fst_apply]
  simp_rw [h_pow, prod_univ_sum, prod_monomial, map_sum, coeff_monomial, h_exp, sum_ite_eq]
  simp only [h_mem]
  split_ifs
  · rw [prod_mul_distrib, mul_comm, Fintype.prod_prod_type]
  · rfl

/-- **The coefficients of a substitution of copies.** The coefficient of `z ^ γ` in
`F (∑ a_k z_k)` is `a ^ γ` times the product of the multinomial coefficients of the exponents
`γ (x, k)`, `k : K`, times the coefficient of `F` at `γ.mapDomain Prod.fst`, which adds up the
copies of each variable in `γ`. -/
theorem coeff_copySubst (a : K → R) (F : MvPowerSeries σ R) (γ : σ × K →₀ ℕ) :
    coeff γ (copySubst a F) = (∏ y : σ × K, a y.2 ^ γ y) *
      (∏ x : σ, (Nat.multinomial univ fun k : K ↦ γ (x, k) : R)) *
        coeff (γ.mapDomain Prod.fst) F := by
  classical
  rw [copySubst_apply, coeff_subst (hasSubst_sum_smul_X a),
    finsum_eq_single _ (γ.mapDomain Prod.fst)]
  · rw [Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
    simp only [coeff_prod_sum_smul_X_pow, ↓reduceIte, smul_eq_mul, mul_comm]
  · intro d hd
    rw [Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
    simp [coeff_prod_sum_smul_X_pow, Ne.symm hd]

end Fintype

/-- **Integral copies do not enlarge coefficients.** Over an ultrametric ring, if the
coefficients `a k` have norm at most `1`, then each coefficient of `F (∑ a_k z_k)` is at most as
large as the coefficient of `F` at the exponent that adds up the copies of each variable. -/
theorem norm_coeff_copySubst_le [Finite σ] {R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] {a : K → R} (ha : ∀ k, ‖a k‖ ≤ 1) (F : MvPowerSeries σ R)
    (γ : σ × K →₀ ℕ) :
    ‖coeff γ (copySubst a F)‖ ≤ ‖coeff (γ.mapDomain Prod.fst) F‖ := by
  have := Fintype.ofFinite σ
  rw [coeff_copySubst]
  have h_prod : ‖∏ y : σ × K, a y.2 ^ γ y‖ ≤ 1 :=
    TauCeti.norm_prod_le_one fun y _ ↦
      (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) (ha y.2))
  have h_mult : ‖∏ x : σ, (Nat.multinomial univ fun k : K ↦ γ (x, k) : R)‖ ≤ 1 :=
    TauCeti.norm_prod_le_one fun _ _ ↦ IsUltrametricDist.norm_natCast_le_one R _
  exact TauCeti.norm_mul_le_of_norm_le_one_left
    (TauCeti.norm_mul_le_of_norm_le_one_right h_mult _ |>.trans h_prod) _

end MvPowerSeries
