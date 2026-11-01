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

Block-linear substitutions compose by multiplying their matrices block by block. When the
matrices `A_h` are invertible, the new variables `Y_{h,a}` are coordinates given by a system of
linear forms on each block, and the chain rule reads Hasse derivatives in these coordinates:
`(∂_X^I P)(AY)` is a combination of the derivatives `∂_Y^e (P(AY))` of the block degrees of `I`.
So a derivative of order `I` shifts the exponents of the coordinates by at most the block degrees
of `I`. If the coefficients of `P(AY)` vanish at every monomial whose exponents `N_{h,i}` of one
coordinate `i` have weighted sum `∑_h N_{h,i} / d_h` below a threshold, then those of `(∂^I P)(AY)`
vanish below the threshold lowered by the weighted order `∑_h (∑_l I_{h,l}) / d_h` of `I`. This is
how the vanishing conditions imposed on Schmidt's multihomogeneous auxiliary polynomial in the
coordinates of the linear forms pass to its derivatives. The coefficients may lie in any
commutative semiring: no assumption on the characteristic is needed.

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
* `MvPolynomial.aeval_blockLinearForm_mul`: substituting along the blockwise products `A_h B_h` is
  substituting along `A` and then along `B`.
* `MvPolynomial.aeval_blockLinearForm_hasseDeriv`: for mutually inverse `A` and `B`,
  `(∂_X^I P)(AY) = ∑_{e ∈ E(I)} c_{e,I} ∂_Y^e (P(AY))`, with `c_{e,I} = [X^I] (BX)^e`.
* `MvPolynomial.coeff_aeval_blockLinearForm_hasseDeriv_eq_zero`: vanishing of the coefficients of
  `P(AY)` below a weighted threshold in one coordinate passes to `(∂^I P)(AY)`, below the threshold
  lowered by the weighted order of `I`.

## References

* J.-H. Evertse, *An improvement of the quantitative subspace theorem*, Compositio Math. 101
  (1996), §7, Lemma 26.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §7.5.14.
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

/-- The block-linear forms `X_{h,l} ↦ ∑ₐ A_{h,l,a} Y_{h,a}` of a family of matrices `A_h`: the
variable `l` of block `h` becomes a linear form in the parameters `Y_{h,a}` of the same block. -/
noncomputable def blockLinearForm (A : ι → Matrix κ τ R) (p : ι × κ) : MvPolynomial (ι × τ) R :=
  ∑ a, C (A p.1 p.2 a) * X (p.1, a)

theorem blockLinearForm_apply (A : ι → Matrix κ τ R) (p : ι × κ) :
    blockLinearForm A p = ∑ a, C (A p.1 p.2 a) * X (p.1, a) :=
  (rfl)

/-- The value of a block-linear form at `y` is `∑ₐ A_{h,l,a} y_{h,a}`. -/
@[simp]
theorem eval_blockLinearForm (A : ι → Matrix κ τ R) (y : ι × τ → R) (p : ι × κ) :
    eval y (blockLinearForm A p) = ∑ a, A p.1 p.2 a * y (p.1, a) := by
  simp [blockLinearForm_apply]

/-- Evaluating after the block-linear substitution is evaluating at the point `Ay`. -/
theorem eval_aeval_blockLinearForm (A : ι → Matrix κ τ R) (y : ι × τ → R)
    (F : MvPolynomial (ι × κ) R) :
    eval y (aeval (blockLinearForm A) F) = eval (fun p ↦ ∑ a, A p.1 p.2 a * y (p.1, a)) F := by
  simpa only [aeval_eq_eval, eval_blockLinearForm] using
    comp_aeval_apply (blockLinearForm A) (aeval y) F

/-- Block-linear forms are linear forms: homogeneous of degree one. -/
theorem isHomogeneous_blockLinearForm (A : ι → Matrix κ τ R) (p : ι × κ) :
    (blockLinearForm A p).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ isHomogeneous_C_mul_X _ _

/-- With the indicator weight of block `b`, the block-linear form of a variable of block `h` is
weighted homogeneous of weight `1` if `h = b` and `0` otherwise. -/
theorem isWeightedHomogeneous_blockLinearForm [DecidableEq ι] (A : ι → Matrix κ τ R)
    (b : ι) (p : ι × κ) :
    (blockLinearForm A p).IsWeightedHomogeneous (fun q : ι × τ ↦ if q.1 = b then 1 else 0)
      (if p.1 = b then 1 else 0) :=
  IsWeightedHomogeneous.sum _ _ _ fun a _ ↦ (isWeightedHomogeneous_X _ _ (p.1, a)).C_mul _

/-- **Block degrees of the substitution coefficients.** If the coefficient
`c_{e,k} = [Y^k] ∏_{h,l} (∑ₐ A_{h,l,a} Y_{h,a})^(e_{h,l})` is nonzero, then `e` and `k` have the
same degree in every block: `∑ₗ e_{b,l} = ∑ₐ k_{b,a}`. -/
theorem sum_eq_sum_of_coeff_aeval_blockLinearForm_ne_zero [Fintype κ]
    {A : ι → Matrix κ τ R} {e : ι × κ →₀ ℕ} {k : ι × τ →₀ ℕ}
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
theorem degreeOf_aeval_blockLinearForm_le [Fintype κ] (A : ι → Matrix κ τ R)
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
    [DecidableEq κ] (A : ι → Matrix κ τ R) (F : MvPolynomial (ι × κ) R) (i : ι × κ →₀ ℕ)
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
    (A : ι → Matrix κ τ R) (F : MvPolynomial (ι × κ) R) (i : ι × κ →₀ ℕ) (k : ι × τ →₀ ℕ)
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
    (aeval (blockLinearForm fun (_ : Unit) ↦ Matrix.of fun (_ : Unit) (_ : Unit) ↦ (2 : ℚ))
      (hasseDeriv (Finsupp.single ((), ()) 1) (X ((), ()) ^ 2 : MvPolynomial (Unit × Unit) ℚ))) =
        4 := by
  simp only [X_pow_eq_monomial, hasseDeriv_monomial, ← Finsupp.single_tsub, Nat.add_one_sub_one,
    Finsupp.single_eq_same, Nat.choose_zero_right, Finsupp.prod_single_index,
    Nat.choose_succ_self_right, Nat.reduceAdd, Nat.cast_ofNat, mul_one, aeval_monomial,
    algebraMap_eq, blockLinearForm_apply, Matrix.of_apply, univ_unique, PUnit.default_eq_unit,
    sum_singleton, pow_zero, pow_one]
  rw [← mul_assoc, ← C_mul, ← smul_eq_C_mul, map_smul, hasseDeriv_X]
  norm_num [smul_eq_C_mul, map_ofNat]

end BlockLinear

section Coordinates

variable {ι κ υ : Type*} [Fintype τ] [Fintype υ]

/-- Composing block-linear substitutions multiplies their matrices block by block: substituting
`X_{h,l} ↦ ∑ₐ A_{h,l,a} Y_{h,a}` and then `Y_{h,a} ↦ ∑_b B_{h,a,b} Z_{h,b}` turns `X_{h,l}` into
the block-linear form of the product `A_h B_h`. -/
theorem aeval_blockLinearForm_blockLinearForm (A : ι → Matrix κ τ R) (B : ι → Matrix τ υ R)
    (p : ι × κ) :
    aeval (blockLinearForm B) (blockLinearForm A p) = blockLinearForm (fun h ↦ A h * B h) p := by
  simp only [blockLinearForm_apply, map_sum, map_mul, algHom_C, aeval_X, algebraMap_eq,
    Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
  exact sum_comm

/-- Block-linear substitutions compose contravariantly: substituting along the blockwise products
`A_h B_h` is substituting along `A` and then along `B`. -/
theorem aeval_blockLinearForm_mul (A : ι → Matrix κ τ R) (B : ι → Matrix τ υ R) :
    aeval (blockLinearForm fun h ↦ A h * B h) =
      (aeval (blockLinearForm B)).comp (aeval (blockLinearForm A)) := by
  rw [comp_aeval]
  exact congrArg aeval (funext fun p ↦ (aeval_blockLinearForm_blockLinearForm A B p).symm)

/-- The block-linear forms of the identity matrices are the variables. -/
@[simp]
theorem blockLinearForm_one [DecidableEq κ] [Fintype κ] :
    blockLinearForm (fun _ : ι ↦ (1 : Matrix κ κ R)) = X := by
  funext p
  simp [blockLinearForm_apply, Matrix.one_apply]

/-- Substituting along mutually inverse block-linear forms recovers the polynomial. -/
theorem aeval_blockLinearForm_aeval_blockLinearForm_of_mul_eq_one [DecidableEq κ] [Fintype κ]
    {A : ι → Matrix κ τ R} {B : ι → Matrix τ κ R} (hAB : ∀ h, A h * B h = 1)
    (F : MvPolynomial (ι × κ) R) :
    aeval (blockLinearForm B) (aeval (blockLinearForm A) F) = F := by
  rw [← AlgHom.comp_apply, ← aeval_blockLinearForm_mul, funext hAB, blockLinearForm_one,
    aeval_X_left_apply]

/-- **Hasse derivatives in the coordinates of a block-linear change of variables.** Let `A_h` and
`B_h` be mutually inverse matrices and `Q = P(AY)`, so that `P = Q(BX)`. Read in the coordinates
`Y`, the derivative `∂_X^I P` is a combination of the derivatives of `Q` of the same block degrees
as `I`: `(∂_X^I P)(AY) = ∑_{e ∈ E(I)} c_{e,I} ∂_Y^e Q`, where
`c_{e,I} = [X^I] ∏_{h,l} (∑ₐ B_{h,l,a} X_{h,a})^(e_{h,l})` and `E(I)` consists of the `e` with
`∑ₗ e_{h,l} = ∑ₗ I_{h,l}` for every block `h`. -/
theorem aeval_blockLinearForm_hasseDeriv [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {A B : ι → Matrix κ κ R} (hAB : ∀ h, A h * B h = 1) (hBA : ∀ h, B h * A h = 1)
    (P : MvPolynomial (ι × κ) R) (I : ι × κ →₀ ℕ) :
    aeval (blockLinearForm A) (hasseDeriv I P) =
      ∑ e ∈ univ.finsuppAntidiag I.degree with ∀ h, ∑ l, e (h, l) = ∑ l, I (h, l),
        (aeval (blockLinearForm B) (monomial e (1 : R))).coeff I •
          hasseDeriv e (aeval (blockLinearForm A) P) := by
  conv_lhs => rw [← aeval_blockLinearForm_aeval_blockLinearForm_of_mul_eq_one hAB P]
  rw [hasseDeriv_aeval (isHomogeneous_blockLinearForm B), sum_filter_of_ne fun e _ he ↦
    sum_eq_sum_of_coeff_aeval_blockLinearForm_ne_zero (left_ne_zero_of_smul he), map_sum]
  refine sum_congr rfl fun e _ ↦ ?_
  rw [map_smul, aeval_blockLinearForm_aeval_blockLinearForm_of_mul_eq_one hBA]

/-- **Vanishing coefficients in the coordinates of a system of linear forms.** Let `A_h` be
invertible matrices, so that the coordinates `Y_{h,a}` of `X_{h,l} = ∑ₐ A_{h,l,a} Y_{h,a}` are
linear forms in the variables of block `h`, and let `Q = P(AY)` be `P` written in these
coordinates. Fix a coordinate `i`, degrees `d h`, and a threshold `θ`. If the coefficient of `Q` at
every monomial `N` with `∑_h N_{h,i} / d_h < θ` vanishes, then the coefficient of `(∂^I P)(AY)` at
every monomial `J` with `∑_h J_{h,i} / d_h < θ - ∑_h (∑_l I_{h,l}) / d_h` vanishes: a derivative
lowers the threshold by its weighted order. -/
theorem coeff_aeval_blockLinearForm_hasseDeriv_eq_zero {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : ι → Matrix κ κ R} (hA : ∀ h, IsUnit (A h)) {P : MvPolynomial (ι × κ) R} (d : ι → ℕ)
    (i : κ) {θ : 𝕜}
    (hP : ∀ N : ι × κ →₀ ℕ, ∑ h, (N (h, i) : 𝕜) / d h < θ →
      (aeval (blockLinearForm A) P).coeff N = 0)
    (I : ι × κ →₀ ℕ) {J : ι × κ →₀ ℕ}
    (hJ : ∑ h, (J (h, i) : 𝕜) / d h + ∑ h, (∑ l, (I (h, l) : 𝕜)) / d h < θ) :
    (aeval (blockLinearForm A) (hasseDeriv I P)).coeff J = 0 := by
  classical
  rw [aeval_blockLinearForm_hasseDeriv (B := fun h ↦ ↑(hA h).unit⁻¹)
    (fun h ↦ (hA h).mul_val_inv) (fun h ↦ (hA h).val_inv_mul), coeff_sum]
  refine sum_eq_zero fun e he ↦ ?_
  rw [coeff_smul, hasseDeriv_coeff, hP (J + e) ?_, mul_zero, smul_zero]
  -- `e` has the block degrees of `I`, so its weight in coordinate `i` is at most that of `I`.
  have hblock := (mem_filter.1 he).2
  calc ∑ h, ((J + e) (h, i) : 𝕜) / d h
      = ∑ h, (J (h, i) : 𝕜) / d h + ∑ h, (e (h, i) : 𝕜) / d h := by
        simp only [Finsupp.add_apply, Nat.cast_add, add_div, sum_add_distrib]
    _ ≤ ∑ h, (J (h, i) : 𝕜) / d h + ∑ h, (∑ l, (I (h, l) : 𝕜)) / d h := by
        gcongr with h
        rw [← Nat.cast_sum, ← hblock h, Nat.cast_sum]
        exact single_le_sum (f := fun l ↦ (e (h, l) : 𝕜)) (fun _ _ ↦ Nat.cast_nonneg _)
          (mem_univ i)
    _ < θ := hJ

/-- With `X_0 = Y_0 + Y_1` and `X_1 = Y_1`, the polynomial `P = X_0 - X_1` is `Y_0` in the
coordinates `Y`, so its coefficients vanish at every monomial of degree `0` in `Y_0`. -/
example : aeval (blockLinearForm fun _ : Unit ↦ !![(1 : ℚ), 1; 0, 1])
    (X ((), 0) - X ((), 1) : MvPolynomial (Unit × Fin 2) ℚ) = X ((), 0) := by
  simp [blockLinearForm_apply, Fin.sum_univ_two]

/-- The derivative `∂P/∂X_1 = -1` of the same `P` has the nonzero constant coefficient `-1`: its
order in a direction other than `0` still lowers the threshold in coordinate `0`, so
`coeff_aeval_blockLinearForm_hasseDeriv_eq_zero` needs the full block degrees of `I`, not just
`I_{h,0}`. -/
example : (aeval (blockLinearForm fun _ : Unit ↦ !![(1 : ℚ), 1; 0, 1])
    (hasseDeriv (Finsupp.single ((), 1) 1)
      (X ((), 0) - X ((), 1) : MvPolynomial (Unit × Fin 2) ℚ))).coeff 0 = -1 := by
  simp [hasseDeriv_X, Finsupp.single_left_inj one_ne_zero]

end Coordinates

end MvPolynomial
