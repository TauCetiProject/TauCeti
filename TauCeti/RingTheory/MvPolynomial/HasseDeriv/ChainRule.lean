/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Hasse derivatives after a linear substitution

Substitute linear forms `gₛ(Y)` (homogeneous polynomials of degree one) for the variables `Xₛ` of
a polynomial `G`. Since `gₛ(Y + T) = gₛ(Y) + gₛ(T)`, the Taylor expansion of `G` at `g(Y)` gives
the chain rule for Hasse derivatives
`∂_Y^k (G(g(Y))) = ∑_{|e| = |k|} c_{e,k} (∂_X^e G)(g(Y))`, where `c_{e,k} = [T^k] g(T)^e`.

For a *block-linear* substitution `X_{h,l} = ∑ₐ A_{h,l,a} Y_{h,a}`, in which the variables of
block `h` only involve the parameters of block `h`, the coefficient `c_{e,k}` vanishes unless `e`
and `k` have the same degree `∑ₗ e_{h,l} = ∑ₐ k_{h,a}` in every block. Consequently a nonzero jet
of the substituted polynomial `(∂^i F)(AY)` at a point `y` forces a nonzero jet `∂^(i + e) F` of
`F` at `Ay`, with `e` of the same block degrees as `k`. This is how a nonzero jet of an auxiliary
polynomial restricted to a family of subspaces produces a nonzero jet of the polynomial itself,
in Schmidt's subspace theorem.

## Main definitions

* `MvPolynomial.blockLinearForm A`: the block-linear forms `X_{h,l} ↦ ∑ₐ A_{h,l,a} Y_{h,a}`.

## Main results

* `MvPolynomial.taylor_X_map_C_of_isHomogeneous_one`: a linear form satisfies
  `ℓ(X + Y) = ℓ(X) + ℓ(Y)`.
* `MvPolynomial.hasseDeriv_aeval`: the chain rule for Hasse derivatives after substituting
  linear forms.
* `MvPolynomial.isWeightedHomogeneous_blockLinearForm`: with the indicator weight of a block `b`,
  a block-linear form has weight `1` on the variables of block `b` and `0` on the others.
* `MvPolynomial.sum_eq_sum_of_coeff_aeval_blockLinearForm_ne_zero`: `c_{e,k} ≠ 0` forces equal
  block degrees.
* `MvPolynomial.degreeOf_aeval_blockLinearForm_le`: block degrees `≤ d h` bound the degree of the
  substituted polynomial in each parameter of block `h`.
* `MvPolynomial.hasseDeriv_aeval_blockLinearForm_hasseDeriv`: the chain rule
  `∂_Y^k ((∂_X^i F)(AY)) = ∑_{e ∈ E(k)} c_{e,k} binom(i + e, i) (∂_X^(i + e) F)(AY)`, the sum
  running over the `e` with the block degrees of `k`.
* `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_blockLinearForm`: a nonzero jet of `(∂^i F)(AY)`
  at `y` gives a nonzero jet `∂^(i + e) F` at `Ay` with `e` of the block degrees of `k`.

## References

* J.-H. Evertse, *An improvement of the quantitative subspace theorem*, Compositio Math. 101
  (1996), §7, Lemma 26.
-/

public section

namespace MvPolynomial

open Finset

variable {R σ τ : Type*} [CommSemiring R]

section LinearForm

/-- A linear form `ℓ` (a homogeneous polynomial of degree one) satisfies
`ℓ(X + Y) = ℓ(X) + ℓ(Y)`: its Taylor shift at the generic point is `ℓ(X) + ℓ(Y)`. -/
theorem taylor_X_map_C_of_isHomogeneous_one {ℓ : MvPolynomial τ R} (hℓ : ℓ.IsHomogeneous 1) :
    taylor (X : τ → MvPolynomial τ R) (map C ℓ) = map C ℓ + C ℓ := by
  have hmem : ℓ ∈ Submodule.span R (Set.range (X : τ → MvPolynomial τ R)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hℓ
  clear hℓ
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    simp [taylor_X]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    abel
  | smul r x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_mul, hx, map_C, taylor_C, map_mul]
    ring

/-- Substituting linear forms `g` commutes with Taylor shifts at the generic point:
`G(g(Y + T)) = ∑_e (∂^e G)(g(Y)) g(T)^e`. -/
theorem taylor_X_map_C_aeval {g : σ → MvPolynomial τ R} (hg : ∀ s, (g s).IsHomogeneous 1)
    (G : MvPolynomial σ R) :
    taylor (X : τ → MvPolynomial τ R) (map C (aeval g G)) =
      eval₂ (C.comp (aeval g).toRingHom) (fun s ↦ map C (g s))
        (taylor (X : σ → MvPolynomial σ R) (map C G)) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq, eval₂_add]
  | mul_X p s hp =>
    simp only [map_mul, hp, eval₂_mul, aeval_X, map_X, taylor_X,
      taylor_X_map_C_of_isHomogeneous_one (hg s), eval₂_add, eval₂_X, eval₂_C,
      RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- **The chain rule for Hasse derivatives** after substituting linear forms `gₛ` for the
variables `Xₛ`: `∂^k (G(g)) = ∑_{|e| = |k|} c_{e,k} (∂^e G)(g)`, where `c_{e,k} = [Y^k] g^e` is
the coefficient of `Y^k` in `∏ₛ gₛ^(eₛ)`. -/
theorem hasseDeriv_aeval [Fintype σ] [DecidableEq σ] {g : σ → MvPolynomial τ R}
    (hg : ∀ s, (g s).IsHomogeneous 1) (k : τ →₀ ℕ) (G : MvPolynomial σ R) :
    hasseDeriv k (aeval g G) =
      ∑ e ∈ univ.finsuppAntidiag k.degree,
        (aeval g (monomial e (1 : R))).coeff k • aeval g (hasseDeriv e G) := by
  set T := taylor (X : σ → MvPolynomial σ R) (map C G)
  have hT (e : σ →₀ ℕ) : T.coeff e = hasseDeriv e G := coeff_taylor_X_map_C e G
  have hterm (e : σ →₀ ℕ) :
      ((C.comp (aeval g).toRingHom) (T.coeff e) * ∏ s ∈ e.support, map C (g s) ^ e s).coeff k =
        (aeval g (monomial e (1 : R))).coeff k • aeval g (hasseDeriv e G) := by
    simp only [hT, ← map_pow, ← map_prod, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, coeff_C_mul, coeff_map, aeval_monomial, map_one, one_mul, Finsupp.prod,
      smul_eq_C_mul, mul_comm]
  rw [← coeff_taylor_X_map_C, taylor_X_map_C_aeval hg, eval₂_eq, coeff_sum]
  refine (sum_congr rfl fun e _ ↦ hterm e).trans ?_
  -- Only the `e` with `∂^e G ≠ 0` (the support of `T`) and `|e| = |k|` contribute.
  calc ∑ e ∈ T.support, (aeval g (monomial e (1 : R))).coeff k • aeval g (hasseDeriv e G)
      = ∑ e ∈ T.support ∪ univ.finsuppAntidiag k.degree,
          (aeval g (monomial e (1 : R))).coeff k • aeval g (hasseDeriv e G) :=
        sum_subset subset_union_left fun e _ he ↦ by
          rw [← hT, notMem_support_iff.1 he, map_zero, smul_zero]
    _ = ∑ e ∈ univ.finsuppAntidiag k.degree,
          (aeval g (monomial e (1 : R))).coeff k • aeval g (hasseDeriv e G) := by
        refine (sum_subset subset_union_right fun e _ he ↦ ?_).symm
        have hdeg : k.degree ≠ 1 * e.degree := by
          simpa [mem_finsuppAntidiag, Finsupp.degree_eq_sum, eq_comm] using he
        have hc : (aeval g (monomial e (1 : R))).coeff k = 0 :=
          ((isHomogeneous_monomial (1 : R) rfl).aeval g hg).coeff_eq_zero hdeg
        rw [hc, zero_smul]

end LinearForm

section BlockLinear

variable {ι κ : Type*} [Fintype τ]

/-- The block-linear forms `X_{h,l} ↦ ∑ₐ A_{h,l,a} Y_{h,a}`: the variable `l` of block `h` becomes
a linear form in the parameters `Y_{h,a}` of the same block. -/
noncomputable def blockLinearForm (A : ι → κ → τ → R) (p : ι × κ) : MvPolynomial (ι × τ) R :=
  ∑ a, C (A p.1 p.2 a) * X (p.1, a)

theorem blockLinearForm_apply (A : ι → κ → τ → R) (p : ι × κ) :
    blockLinearForm A p = ∑ a, C (A p.1 p.2 a) * X (p.1, a) :=
  (rfl)

/-- The value of a block-linear form at `y` is `∑ₐ A_{h,l,a} y_{h,a}`. -/
@[simp]
theorem eval_blockLinearForm (A : ι → κ → τ → R) (y : ι × τ → R) (p : ι × κ) :
    eval y (blockLinearForm A p) = ∑ a, A p.1 p.2 a * y (p.1, a) := by
  simp [blockLinearForm_apply]

/-- Evaluating after the block-linear substitution is evaluating at the point `Ay`. -/
theorem eval_aeval_blockLinearForm (A : ι → κ → τ → R) (y : ι × τ → R)
    (F : MvPolynomial (ι × κ) R) :
    eval y (aeval (blockLinearForm A) F) = eval (fun p ↦ ∑ a, A p.1 p.2 a * y (p.1, a)) F := by
  simpa only [aeval_eq_eval, eval_blockLinearForm] using
    comp_aeval_apply (blockLinearForm A) (aeval y) F

/-- Block-linear forms are linear forms: homogeneous of degree one. -/
theorem isHomogeneous_blockLinearForm (A : ι → κ → τ → R) (p : ι × κ) :
    (blockLinearForm A p).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ isHomogeneous_C_mul_X _ _

/-- With the indicator weight of block `b`, the block-linear form of a variable of block `h` is
weighted homogeneous of weight `1` if `h = b` and `0` otherwise. -/
theorem isWeightedHomogeneous_blockLinearForm [DecidableEq ι] (A : ι → κ → τ → R)
    (b : ι) (p : ι × κ) :
    (blockLinearForm A p).IsWeightedHomogeneous (fun q : ι × τ ↦ if q.1 = b then 1 else 0)
      (if p.1 = b then 1 else 0) :=
  IsWeightedHomogeneous.sum _ _ _ fun a _ ↦ (isWeightedHomogeneous_X _ _ (p.1, a)).C_mul _

/-- **Block degrees of the substitution coefficients.** If the coefficient
`c_{e,k} = [Y^k] ∏_{h,l} (∑ₐ A_{h,l,a} Y_{h,a})^(e_{h,l})` is nonzero, then `e` and `k` have the
same degree in every block: `∑ₗ e_{b,l} = ∑ₐ k_{b,a}`. -/
theorem sum_eq_sum_of_coeff_aeval_blockLinearForm_ne_zero [Fintype κ]
    {A : ι → κ → τ → R} {e : ι × κ →₀ ℕ} {k : ι × τ →₀ ℕ}
    (h : (aeval (blockLinearForm A) (monomial e (1 : R))).coeff k ≠ 0) (b : ι) :
    ∑ l, e (b, l) = ∑ a, k (b, a) := by
  classical
  have hw := IsWeightedHomogeneous.aeval
    (isWeightedHomogeneous_monomial (fun p : ι × κ ↦ if p.1 = b then 1 else 0) e (1 : R) rfl)
    (isWeightedHomogeneous_blockLinearForm A b)
  rw [← Finsupp.weight_ite_fst_eq_sum, ← Finsupp.weight_ite_fst_eq_sum, hw h]

/-- **Degrees after a block-linear substitution.** If every monomial of `F` has degree at most
`d h` in each block `h`, then the substituted polynomial `F(AY)` has degree at most `d h` in each
parameter `Y_{h,a}` of block `h`. -/
theorem degreeOf_aeval_blockLinearForm_le [Fintype κ] (A : ι → κ → τ → R)
    {F : MvPolynomial (ι × κ) R} {d : ι → ℕ} (hF : ∀ μ ∈ F.support, ∀ h, ∑ l, μ (h, l) ≤ d h)
    (q : ι × τ) : (aeval (blockLinearForm A) F).degreeOf q ≤ d q.1 := by
  classical
  refine degreeOf_le_iff.2 fun ν hν ↦ ?_
  rw [← support_sum_monomial_coeff F, map_sum] at hν
  obtain ⟨μ, hμ, hν⟩ := mem_biUnion.1 (support_sum hν)
  -- The substituted monomial `μ` has the block degree of `μ` in block `q.1`, hence so does `ν`.
  have hw := IsWeightedHomogeneous.aeval
    (isWeightedHomogeneous_monomial (fun p : ι × κ ↦ if p.1 = q.1 then 1 else 0) μ
      (F.coeff μ) rfl)
    (isWeightedHomogeneous_blockLinearForm A q.1)
  have hblock := hw (mem_support_iff.1 hν)
  rw [Finsupp.weight_ite_fst_eq_sum, Finsupp.weight_ite_fst_eq_sum] at hblock
  calc ν q ≤ ∑ a, ν (q.1, a) :=
        single_le_sum (f := fun a ↦ ν (q.1, a)) (fun _ _ ↦ Nat.zero_le _) (mem_univ q.2)
    _ = ∑ l, μ (q.1, l) := hblock
    _ ≤ d q.1 := hF μ hμ q.1

/-- **The chain rule for a block-linear substitution**:
`∂_Y^k ((∂_X^i F)(AY)) = ∑_{e ∈ E(k)} c_{e,k} binom(i + e, i) (∂_X^(i + e) F)(AY)`, where
`c_{e,k} = [Y^k] ∏_{h,l} (∑ₐ A_{h,l,a} Y_{h,a})^(e_{h,l})` and `E(k)` consists of the `e` with
the block degrees `∑ₗ e_{h,l} = ∑ₐ k_{h,a}` of `k`. -/
theorem hasseDeriv_aeval_blockLinearForm_hasseDeriv [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (A : ι → κ → τ → R) (F : MvPolynomial (ι × κ) R) (i : ι × κ →₀ ℕ)
    (k : ι × τ →₀ ℕ) :
    hasseDeriv k (aeval (blockLinearForm A) (hasseDeriv i F)) =
      ∑ e ∈ univ.finsuppAntidiag k.degree with ∀ b, ∑ l, e (b, l) = ∑ a, k (b, a),
        (aeval (blockLinearForm A) (monomial e (1 : R))).coeff k •
          (e.prod fun p n ↦ (n + i p).choose n) •
            aeval (blockLinearForm A) (hasseDeriv (i + e) F) := by
  rw [hasseDeriv_aeval (isHomogeneous_blockLinearForm A), sum_filter_of_ne fun e _ he ↦
    sum_eq_sum_of_coeff_aeval_blockLinearForm_ne_zero (left_ne_zero_of_smul he)]
  refine sum_congr rfl fun e _ ↦ ?_
  rw [← LinearMap.comp_apply, hasseDeriv_comp, LinearMap.smul_apply, map_nsmul, add_comm e]

/-- **Nonzero jets after a block-linear substitution.** If the jet `∂_Y^k` of the substituted
derivative `(∂_X^i F)(AY)` is nonzero at `y`, then some jet `∂^(i + e) F` of `F` is nonzero at the
point `Ay`, where `e` has the block degrees `∑ₗ e_{h,l} = ∑ₐ k_{h,a}` of `k`. -/
theorem exists_eval_hasseDeriv_ne_zero_of_blockLinearForm [Finite ι] [Fintype κ]
    (A : ι → κ → τ → R) (F : MvPolynomial (ι × κ) R) (i : ι × κ →₀ ℕ) (k : ι × τ →₀ ℕ)
    (y : ι × τ → R) (h : eval y (hasseDeriv k (aeval (blockLinearForm A) (hasseDeriv i F))) ≠ 0) :
    ∃ e : ι × κ →₀ ℕ, (∀ b, ∑ l, e (b, l) = ∑ a, k (b, a)) ∧
      eval (fun p ↦ ∑ a, A p.1 p.2 a * y (p.1, a)) (hasseDeriv (i + e) F) ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  rw [hasseDeriv_aeval_blockLinearForm_hasseDeriv, map_sum] at h
  obtain ⟨e, he, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  refine ⟨e, (mem_filter.1 he).2, fun h0 ↦ hne ?_⟩
  rw [smul_eval, map_nsmul, eval_aeval_blockLinearForm, h0, nsmul_zero, mul_zero]

/-- For `F = X²` and the substitution `X ↦ 2Y`, `∂¹((∂¹F)(2Y)) = 4`; omitting the binomial
coefficient `binom(i + e, i)` of the chain rule would give `2`. -/
example : hasseDeriv (Finsupp.single ((), ()) 1)
    (aeval (blockLinearForm fun (_ : Unit) (_ : Unit) (_ : Unit) ↦ (2 : ℚ))
      (hasseDeriv (Finsupp.single ((), ()) 1) (X ((), ()) ^ 2 : MvPolynomial (Unit × Unit) ℚ))) =
        4 := by
  simp only [X_pow_eq_monomial, hasseDeriv_monomial, ← Finsupp.single_tsub, Nat.add_one_sub_one,
    Finsupp.single_eq_same, Nat.choose_zero_right, Finsupp.prod_single_index,
    Nat.choose_succ_self_right, Nat.reduceAdd, Nat.cast_ofNat, mul_one, aeval_monomial,
    algebraMap_eq, blockLinearForm_apply, univ_unique, PUnit.default_eq_unit, sum_singleton,
    pow_zero, pow_one]
  rw [← mul_assoc, ← C_mul, ← smul_eq_C_mul, map_smul, hasseDeriv_X]
  norm_num [smul_eq_C_mul, map_ofNat]

end BlockLinear

end MvPolynomial
