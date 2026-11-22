/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Mul
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Evaluating restricted power series at bounded arguments

Let `R` and `S` be ultrametric normed commutative rings, with `S` complete, let `φ : R →+* S` not
increase norms, and let `a : Fin k → S` satisfy `‖a i‖ ≤ c i` for a polyradius `c`. For a series
`f = ∑ₜ fₜ Xᵗ` restricted at `c`, the monomial values satisfy

```text
‖φ(fₜ) aᵗ‖ ≤ ‖fₜ‖ cᵗ → 0,
```

so they are summable in `S`, and their sum `f(a)` defines a ring homomorphism
`R{X/c} → S` with `C r ↦ φ r` and `X i ↦ a i`. It does not increase norms, and it is the only
continuous ring homomorphism with these values on constants and variables, because the
polynomials are dense in `R{X/c}`. This is the universal property of the Tate algebra `R{X/c}`
among complete ultrametric normed rings, at arguments whose norms reach the real radii `c i`.

The value `f(a)` is the sum `TauCeti.Huber.weightedEval φ a f` of the evaluation of weighted
restricted series in Huber's sense (Wedhorn, Proposition 5.50), and additivity and the Cauchy
product formula are `TauCeti.Huber.weightedEval_add_of_summable` and
`TauCeti.Huber.weightedEval_mul_of_summable`; what is new here is the summability, from the Gauss
norm. Huber's weights are subsets of `R`, so they reach only radii that are norms of elements of
`R`, and Mathlib's `MvPowerSeries.eval₂` evaluates only at topologically nilpotent arguments.
Arbitrary real radii are what present rings of convergent functions on annuli as quotients of Tate
algebras, as in Kedlaya's Lemma 4.9 for the interval rings of the Fargues–Fontaine curve.

## Main definitions

* `MvPowerSeries.restrictedEval₂`: the evaluation `R{X/c} →+* S`, `f ↦ f(a)`.

## Main results

* `MvPowerSeries.hasSum_restrictedEval₂`: `f(a)` is the sum of the monomial values `φ(fₜ) aᵗ`.
* `MvPowerSeries.restrictedEval₂_monomial`, `MvPowerSeries.restrictedEval₂_algebraMap` and
  `MvPowerSeries.restrictedEval₂_X`: the values on monomials, constants and variables.
* `MvPowerSeries.restrictedEval₂_polynomial`: on polynomials, evaluation is `MvPolynomial.eval₂`.
* `MvPowerSeries.norm_restrictedEval₂_le`: evaluation does not increase the Gauss norm.
* `MvPowerSeries.norm_restrictedEval₂_sub_le`: ultrametric Lipschitz bound for `a ↦ f(a)`.
* `MvPowerSeries.lipschitzWith_restrictedEval₂_arg` and
  `MvPowerSeries.continuous_restrictedEval₂_arg`: for fixed `f`, `a ↦ f(a)` is Lipschitz and
  continuous on the closed polydisc `{a | ∀ i, ‖a i‖ ≤ c i}`.
* `MvPowerSeries.eq_restrictedEval₂`: a continuous ring homomorphism out of `R{X/c}` is determined
  by its values on constants and variables.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1, for
  restricted power series.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50, for evaluation of restricted
  power series.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Lemma 4.9, for evaluation at real radii.
-/

public section

namespace MvPowerSeries

open Filter TauCeti.Huber
open scoped Topology

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [NormedCommRing S]
  {c : Fin k → ℝ} (φ : R →+* S) (a : Fin k → S)

/-- A monomial value `φ(fₜ) aᵗ` is bounded by the weighted coefficient norm `‖fₜ‖ cᵗ`. -/
private theorem norm_weightedEvalTerm_le (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (ha : ∀ i, ‖a i‖ ≤ c i)
    (f : MvPowerSeries (Fin k) R) (t : Fin k →₀ ℕ) :
    ‖weightedEvalTerm φ a f t‖ ≤ ‖coeff t f‖ * t.prod (c · ^ ·) := by
  rw [weightedEvalTerm_def, ← Finsupp.prod_fintype t (a · ^ ·) fun _ ↦ pow_zero _]
  -- only positive exponents occur in `t.prod`, so no bound on `‖1‖` is needed
  rcases t.support.eq_empty_or_nonempty with h | h
  · simpa [Finsupp.prod, h] using hφ _
  refine (norm_mul_le _ _).trans (mul_le_mul (hφ _) ?_ (norm_nonneg _) (norm_nonneg _))
  exact (Finset.norm_prod_le' _ h _).trans (Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _)
    fun i hi ↦ (norm_pow_le' _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
      (pow_le_pow_left₀ (norm_nonneg _) (ha i) _))

/-- The monomial values of a restricted series at a bounded argument tend to zero. -/
theorem IsRestricted.tendsto_weightedEvalTerm (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (ha : ∀ i, ‖a i‖ ≤ c i)
    {f : MvPowerSeries (Fin k) R} (hf : IsRestricted c f) :
    Tendsto (weightedEvalTerm φ a f) cofinite (𝓝 0) :=
  squeeze_zero_norm (norm_weightedEvalTerm_le φ a hφ ha f) hf

variable [IsUltrametricDist S] [CompleteSpace S]

/-- The monomial values of a restricted series at a bounded argument are summable. -/
theorem IsRestricted.summable_weightedEvalTerm (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (ha : ∀ i, ‖a i‖ ≤ c i)
    {f : MvPowerSeries (Fin k) R} (hf : IsRestricted c f) :
    Summable (weightedEvalTerm φ a f) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (hf.tendsto_weightedEvalTerm φ a hφ ha)

variable [IsUltrametricDist R]

/-- **Evaluation of restricted power series at bounded arguments.** For a norm-nonincreasing
`φ : R →+* S` into a complete ultrametric normed ring and arguments `a i` of norm at most `c i`,
the ring homomorphism `R{X/c} → S` sending `f = ∑ₜ fₜ Xᵗ` to `f(a) = ∑ₜ φ(fₜ) aᵗ`, that is,
`TauCeti.Huber.weightedEval φ a f`. -/
noncomputable def restrictedEval₂ (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (ha : ∀ i, ‖a i‖ ≤ c i) :
    IsRestricted.subring (R := R) c →+* S where
  toFun f := weightedEval φ a f
  map_one' := by simpa using weightedEval_C φ a 1
  map_mul' f g := by
    -- the ultrametric norm makes `S` a nonarchimedean ring, for the summability of products
    have : NonarchimedeanRing S :=
      { toIsTopologicalRing := inferInstance
        is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
    have hf := f.property.summable_weightedEvalTerm φ a hφ ha
    have hg := g.property.summable_weightedEvalTerm φ a hφ ha
    exact weightedEval_mul_of_summable hf hg (hf.mul_of_nonarchimedean hg)
  map_zero' := weightedEval_zero φ a
  map_add' f g := weightedEval_add_of_summable (f.property.summable_weightedEvalTerm φ a hφ ha)
    (g.property.summable_weightedEvalTerm φ a hφ ha)

variable (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (ha : ∀ i, ‖a i‖ ≤ c i)

/-- The evaluation `f(a)` is `TauCeti.Huber.weightedEval φ a f`. -/
theorem restrictedEval₂_apply (f : IsRestricted.subring (R := R) c) :
    restrictedEval₂ φ a hφ ha f = weightedEval φ a f := (rfl)

/-- The evaluation `f(a)` is the sum of the monomial values `φ(fₜ) aᵗ`. -/
theorem hasSum_restrictedEval₂ (f : IsRestricted.subring (R := R) c) :
    HasSum (weightedEvalTerm φ a f) (restrictedEval₂ φ a hφ ha f) := by
  rw [restrictedEval₂_apply, weightedEval_def]
  exact (f.property.summable_weightedEvalTerm φ a hφ ha).hasSum

/-- The evaluation of a monomial `r Xᵗ` is `φ(r) aᵗ`. -/
@[simp]
theorem restrictedEval₂_monomial (t : Fin k →₀ ℕ) (r : R) :
    restrictedEval₂ φ a hφ ha ⟨monomial t r, isRestricted_monomial c t r⟩ =
      φ r * ∏ i, a i ^ t i :=
  weightedEval_monomial φ a t r

/-- Evaluation extends `φ` on constants. -/
@[simp]
theorem restrictedEval₂_algebraMap (r : R) :
    restrictedEval₂ φ a hφ ha (algebraMap R (IsRestricted.subring (R := R) c) r) = φ r := by
  rw [restrictedEval₂_apply, coe_algebraMap_isRestrictedSubring, weightedEval_C]

/-- Evaluation sends the variable `X i` to `a i`. -/
@[simp]
theorem restrictedEval₂_X (i : Fin k) :
    restrictedEval₂ φ a hφ ha ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩ = a i :=
  weightedEval_X φ a i

/-- **Evaluation extends polynomial evaluation**: the value of a polynomial `p` at `a` is
`MvPolynomial.eval₂ φ a p`. -/
@[simp]
theorem restrictedEval₂_polynomial (p : MvPolynomial (Fin k) R) :
    restrictedEval₂ φ a hφ ha ⟨(p : MvPowerSeries (Fin k) R), p.isRestricted c⟩ =
      MvPolynomial.eval₂ φ a p := by
  rw [← TauCeti.MvPowerSeries.polynomialToRestricted_apply, ← MvPolynomial.coe_eval₂Hom]
  refine DFunLike.congr_fun (MvPolynomial.ringHom_ext
    (f := (restrictedEval₂ φ a hφ ha).comp
      (TauCeti.MvPowerSeries.polynomialToRestricted c).toRingHom)
    (fun b ↦ ?_) fun i ↦ ?_) p
  · simp [← MvPolynomial.algebraMap_eq, restrictedEval₂_algebraMap]
  · simp [restrictedEval₂_X]

variable [∀ i, Fact (0 < c i)]

/-- **Evaluation does not increase the Gauss norm**: `‖f(a)‖ ≤ ‖f‖`. -/
theorem norm_restrictedEval₂_le (f : IsRestricted.subring (R := R) c) :
    ‖restrictedEval₂ φ a hφ ha f‖ ≤ ‖f‖ := by
  rw [restrictedEval₂_apply, weightedEval_def]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg f) fun t ↦
    (norm_weightedEvalTerm_le φ a hφ ha _ t).trans (norm_coeff_mul_prod_le f t)

/-- Evaluation is `1`-Lipschitz for the Gauss norm, hence continuous. -/
theorem continuous_restrictedEval₂ : Continuous (restrictedEval₂ φ a hφ ha) :=
  AddMonoidHomClass.continuous_of_bound (restrictedEval₂ φ a hφ ha) 1 fun f ↦ by
    simpa using norm_restrictedEval₂_le φ a hφ ha f

/-- **Uniqueness of evaluation**: a continuous ring homomorphism `R{X/c} → S` that extends `φ` on
constants and sends each `X i` to `a i` is the evaluation `f ↦ f(a)`. -/
theorem eq_restrictedEval₂ (ψ : IsRestricted.subring (R := R) c →+* S) (hψ : Continuous ψ)
    (hC : ∀ r, ψ (algebraMap R _ r) = φ r)
    (hX : ∀ i, ψ ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩ = a i) :
    ψ = restrictedEval₂ φ a hφ ha := by
  refine DFunLike.coe_injective (hψ.ext_on (dense_closure_monomial dense_univ)
    (continuous_restrictedEval₂ φ a hφ ha) fun f hf ↦ ?_)
  induction hf using AddSubgroup.closure_induction with
  | mem _ h =>
    obtain ⟨⟨t, r⟩, -, rfl⟩ := h
    dsimp only
    rw [restrictedEval₂_monomial, mk_monomial_eq_algebraMap_mul_prod, map_mul, map_finsuppProd]
    simp [hC, hX, Finsupp.prod_fintype]
  | zero => simp
  | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
  | neg _ _ h => simp [h]

omit [CompleteSpace S] [IsUltrametricDist R] [∀ i, Fact (0 < c i)] in
/-- Ultrametric difference bound for each monomial term of `restrictedEval₂`. -/
private theorem norm_weightedEvalTerm_sub_le (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) {a b : Fin k → S}
    (ha : ∀ i, ‖a i‖ ≤ c i) (hb : ∀ i, ‖b i‖ ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ)
    (hab : ∀ i, ‖a i - b i‖ ≤ δ * c i) (f : MvPowerSeries (Fin k) R) (t : Fin k →₀ ℕ) :
    ‖weightedEvalTerm φ a f t - weightedEvalTerm φ b f t‖ ≤
      δ * (‖coeff t f‖ * t.prod (c · ^ ·)) := by
  rw [weightedEvalTerm_def, weightedEvalTerm_def,
    ← Finsupp.prod_fintype t (a · ^ ·) fun _ ↦ pow_zero _,
    ← Finsupp.prod_fintype t (b · ^ ·) fun _ ↦ pow_zero _, ← mul_sub, Finsupp.prod, Finsupp.prod,
    Finsupp.prod]
  have hprod : ‖∏ i ∈ t.support, a i ^ t i - ∏ i ∈ t.support, b i ^ t i‖ ≤
      δ * ∏ i ∈ t.support, c i ^ t i :=
    TauCeti.norm_prod_sub_prod_le_mul_prod hδ
      (fun i hi ↦ (norm_pow_le' _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
        (pow_le_pow_left₀ (norm_nonneg _) (ha i) _))
      (fun i hi ↦ (norm_pow_le' _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
        (pow_le_pow_left₀ (norm_nonneg _) (hb i) _))
      (fun i _ ↦ TauCeti.norm_pow_sub_pow_le_mul_pow hδ (ha i) (hb i) (hab i) (t i))
  calc ‖φ (coeff t f) * (∏ i ∈ t.support, a i ^ t i - ∏ i ∈ t.support, b i ^ t i)‖
      ≤ ‖φ (coeff t f)‖ * ‖∏ i ∈ t.support, a i ^ t i - ∏ i ∈ t.support, b i ^ t i‖ :=
        norm_mul_le _ _
    _ ≤ ‖coeff t f‖ * (δ * ∏ i ∈ t.support, c i ^ t i) :=
        mul_le_mul (hφ _) hprod (norm_nonneg _) (norm_nonneg _)
    _ = δ * (‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i) := by ring

/-- **Ultrametric Lipschitz bound in the evaluation argument.** If `a` and `b` lie in the closed
polydisc of polyradius `c` and satisfy `‖a i - b i‖ ≤ δ * c i` for every `i`, then
`‖f(a) - f(b)‖ ≤ δ * ‖f‖`. -/
theorem norm_restrictedEval₂_sub_le (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) {a b : Fin k → S}
    (ha : ∀ i, ‖a i‖ ≤ c i) (hb : ∀ i, ‖b i‖ ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ)
    (hab : ∀ i, ‖a i - b i‖ ≤ δ * c i) (f : IsRestricted.subring (R := R) c) :
    ‖restrictedEval₂ φ a hφ ha f - restrictedEval₂ φ b hφ hb f‖ ≤ δ * ‖f‖ := by
  have hsum := (hasSum_restrictedEval₂ φ a hφ ha f).sub (hasSum_restrictedEval₂ φ b hφ hb f)
  rw [← hsum.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (mul_nonneg hδ (norm_nonneg f))
    fun t ↦ (norm_weightedEvalTerm_sub_le φ hφ ha hb hδ hab _ t).trans
      (mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le f t) hδ)

/-- **Evaluation of a fixed restricted series is Lipschitz in its argument** on the closed
polydisc `{a | ∀ i, ‖a i‖ ≤ c i}`. -/
theorem lipschitzWith_restrictedEval₂_arg (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (f : IsRestricted.subring (R := R) c) :
    LipschitzWith ((Finset.univ.sup fun i : Fin k ↦ Real.toNNReal (c i)⁻¹) * ‖f‖₊)
      (fun a : {a : Fin k → S // ∀ i, ‖a i‖ ≤ c i} ↦
        restrictedEval₂ φ a.val hφ a.property f) := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  set M : NNReal := Finset.univ.sup fun i : Fin k ↦ Real.toNNReal (c i)⁻¹
  have hle : ∀ i : Fin k, ‖a.val i - b.val i‖ ≤ ((M : ℝ) * dist a b) * c i := fun i ↦ by
    have hci : 0 < c i := Fact.out
    have hMi : (c i)⁻¹ ≤ (M : ℝ) := by
      have h1 : Real.toNNReal (c i)⁻¹ ≤ M :=
        Finset.le_sup (f := fun i : Fin k ↦ Real.toNNReal (c i)⁻¹) (Finset.mem_univ i)
      exact (Real.coe_toNNReal (c i)⁻¹ (inv_nonneg.mpr hci.le)).symm.trans_le
        (NNReal.coe_le_coe.mpr h1)
    have hdist : ‖a.val i - b.val i‖ ≤ dist a b := by
      rw [← dist_eq_norm]
      exact dist_le_pi_dist a.val b.val i
    calc ‖a.val i - b.val i‖ ≤ dist a b := hdist
      _ = (c i)⁻¹ * dist a b * c i := by field_simp [hci.ne']
      _ ≤ (M : ℝ) * dist a b * c i := by gcongr
  rw [dist_eq_norm, NNReal.coe_mul, coe_nnNorm]
  exact (norm_restrictedEval₂_sub_le φ hφ a.property b.property
    (mul_nonneg M.coe_nonneg dist_nonneg) hle f).trans_eq
    (mul_right_comm (M : ℝ) (dist a b) ‖f‖)

/-- **Evaluation of a fixed restricted series is continuous in its argument** on the closed
polydisc `{a | ∀ i, ‖a i‖ ≤ c i}`. -/
theorem continuous_restrictedEval₂_arg (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (f : IsRestricted.subring (R := R) c) :
    Continuous fun a : {a : Fin k → S // ∀ i, ‖a i‖ ≤ c i} ↦
      restrictedEval₂ φ a.val hφ a.property f :=
  (lipschitzWith_restrictedEval₂_arg φ hφ f).continuous

end MvPowerSeries
