/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import TauCeti.RingTheory.PowerSeries.Entire.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt

/-!
# Evaluation of entire power series

For a power series `f = ∑ aₙ Xⁿ` over a commutative ring `R` and an element `b` of an `R`-algebra
`A`, `PowerSeries.evalAt f b` is the infinite sum `∑ₙ aₙ • bⁿ`, with the junk value `0` when the
sum does not converge. When `R` is normed, `A` is a complete normed ring with
`‖r • x‖ ≤ ‖r‖ ‖x‖`, and `f` is entire, the sum converges absolutely at every `b`: since `f` is
restricted at the radius `2 ‖b‖`, its terms are bounded by a constant times `2⁻ⁿ`. No ultrametric
hypothesis is needed for convergence, so this evaluates entire series both at operators on
`p`-adic Banach spaces and in complex Banach algebras. On the subring of entire series,
evaluation at `b` is a ring homomorphism (`PowerSeries.IsEntire.evalAtHom`); it commutes with
continuous algebra homomorphisms.

The same bound shows that an entire series `F = ∑ Fₙ Xⁿ` with coefficients in a complete normed
ring, such as a series of operators, can be evaluated at every scalar: the sum
`PowerSeries.evalScalar F a = ∑ₙ aⁿ • Fₙ` converges absolutely.

A consequence used for Fredholm determinants: if `f(0) = 1` and `f(a) = 0`, then `a` is a unit
with inverse `-∑ₙ aₙ₊₁ • aⁿ`, since `f(a) = 1 + a ∑ₙ aₙ₊₁ • aⁿ`.

The same identity `f(x) = a₀ + x ∑ₙ aₙ₊₁ • xⁿ`, together with continuity of `f` at `0`, gives an
identity principle over coefficient rings: an entire series over a complete normed commutative
ring vanishing at non-zero-divisors accumulating at `0` is zero. Over Tate scalars, where the
powers of a pseudo-uniformiser are such points, an entire series is therefore determined by its
values.

## Main definitions

* `PowerSeries.IsEntire.evalAtHom`: evaluation at `b` as a ring homomorphism on entire series.

## Main results

* `PowerSeries.IsEntire.hasSum_evalAt`: the series `∑ aₙ • bⁿ` converges to `f(b)`.
* `PowerSeries.IsEntire.hasSum_evalScalar`: the series `∑ aⁿ • Fₙ` converges to `F(a)`.
* `PowerSeries.IsEntire.evalScalar_add`: evaluation at a scalar is additive on entire series.
* `PowerSeries.IsEntire.evalAt_add`, `PowerSeries.IsEntire.evalAt_mul`: evaluation is additive and
  multiplicative on entire series.
* `PowerSeries.IsEntire.evalAt_sum`: evaluation commutes with finite sums of entire series.
* `PowerSeries.IsEntire.map_evalAt`: naturality in the algebra.
* `PowerSeries.IsEntire.evalAt_map`: naturality in continuous coefficient homomorphisms.
* `PowerSeries.IsEntire.evalAt_hasseDeriv_X_sub_C_pow_mul`: the evaluated Leibniz rule
  `(Δʲ ((X - a)ᵐ g))(a) = (Δʲ⁻ᵐ g)(a)` for `m ≤ j`, and `0` otherwise.
* `PowerSeries.IsEntire.isUnit_of_evalAt_eq_zero` and
  `PowerSeries.IsEntire.inverse_eq_of_evalAt_eq_zero`: a zero of an entire series with constant
  coefficient `1` is a unit, with explicit inverse.
* `PowerSeries.IsEntire.tendsto_evalAt_nhds_zero_nhds_constantCoeff`: continuity of evaluation at
  `0`.
* `PowerSeries.IsEntire.eq_zero_of_frequently_evalAt_eq_zero`,
  `PowerSeries.IsEntire.eq_of_forall_evalAt_eq`: the identity principle.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

section Normed

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
  {f g : R⟦X⟧}

/-- For an entire series `f = ∑ aₙ Xⁿ`, the terms `aₙ • bⁿ` are absolutely summable. -/
theorem IsEntire.summable_norm_smul_pow (hf : f.IsEntire) (b : A) :
    Summable fun n ↦ ‖coeff n f • b ^ n‖ := by
  -- `‖bⁿ‖ ≤ ‖b‖ⁿ` only holds for `n ≥ 1`, so the term of index `0` is set aside
  rw [← summable_nat_add_iff 1]
  refine ((summable_nat_add_iff 1).mpr (hf.summable_norm_coeff_mul_pow ‖b‖)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  exact (norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_pow_le' b n.succ_pos) (norm_nonneg _))

/-- In a normed algebra with `‖1‖ = 1`, `‖f(b)‖ ≤ ∑ ‖aₙ‖ ‖b‖ⁿ`. -/
theorem IsEntire.norm_evalAt_le [NormOneClass A] (hf : f.IsEntire) (b : A) :
    ‖f.evalAt b‖ ≤ ∑' n, ‖coeff n f‖ * ‖b‖ ^ n := by
  rw [evalAt_def]
  exact (norm_tsum_le_tsum_norm (hf.summable_norm_smul_pow b)).trans <|
    (hf.summable_norm_smul_pow b).tsum_le_tsum (fun n ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_pow_le b n) (norm_nonneg _)))
      (hf.summable_norm_coeff_mul_pow ‖b‖)

variable [CompleteSpace A]

/-- For an entire series `f = ∑ aₙ Xⁿ`, the terms `aₙ • bⁿ` are summable in a complete
algebra. -/
theorem IsEntire.summable_smul_pow (hf : f.IsEntire) (b : A) :
    Summable fun n ↦ coeff n f • b ^ n :=
  (hf.summable_norm_smul_pow b).of_norm

/-- **Evaluation of entire series.** For an entire series `f = ∑ aₙ Xⁿ` and any `b` in a complete
normed algebra, the series `∑ aₙ • bⁿ` converges to `f(b)`. -/
theorem IsEntire.hasSum_evalAt (hf : f.IsEntire) (b : A) :
    HasSum (fun n ↦ coeff n f • b ^ n) (f.evalAt b) := by
  rw [evalAt_def]
  exact (hf.summable_smul_pow b).hasSum

/-- Evaluation is additive on entire series. -/
theorem IsEntire.evalAt_add (hf : f.IsEntire) (hg : g.IsEntire) (b : A) :
    (f + g).evalAt b = f.evalAt b + g.evalAt b := by
  rw [evalAt_def]
  exact HasSum.tsum_eq (by simpa [add_smul] using (hf.hasSum_evalAt b).add (hg.hasSum_evalAt b))

/-- Evaluation commutes with subtraction of entire series. -/
theorem IsEntire.evalAt_sub (hf : f.IsEntire) (hg : g.IsEntire) (b : A) :
    (f - g).evalAt b = f.evalAt b - g.evalAt b := by
  rw [sub_eq_add_neg, hf.evalAt_add hg.neg, evalAt_neg, sub_eq_add_neg]

/-- Evaluation commutes with scalar multiplication of entire series. -/
theorem IsEntire.evalAt_smul (hf : f.IsEntire) (a : R) (b : A) :
    (a • f).evalAt b = a • f.evalAt b := by
  rw [evalAt_def]
  exact HasSum.tsum_eq (by simpa [mul_smul] using (hf.hasSum_evalAt b).const_smul a)

/-- Evaluation commutes with finite sums of entire series. -/
theorem IsEntire.evalAt_sum {ι : Type*} (s : Finset ι) {f : ι → R⟦X⟧}
    (hf : ∀ i ∈ s, (f i).IsEntire) (b : A) :
    (∑ i ∈ s, f i).evalAt b = ∑ i ∈ s, (f i).evalAt b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      (hf i (by simp)).evalAt_add (IsEntire.sum fun j hj ↦ hf j (by simp [hj])),
      ih fun j hj ↦ hf j (by simp [hj])]

/-- Evaluation is multiplicative on entire series: this is the Cauchy product formula for the
absolutely convergent series `∑ aₙ • bⁿ` and `∑ cₙ • bⁿ`. -/
theorem IsEntire.evalAt_mul (hf : f.IsEntire) (hg : g.IsEntire) (b : A) :
    (f * g).evalAt b = f.evalAt b * g.evalAt b := by
  rw [evalAt_def, evalAt_def, evalAt_def,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hf.summable_norm_smul_pow b)
      (hg.summable_norm_smul_pow b)]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [← Finset.mem_antidiagonal.mp hp, pow_add, smul_mul_smul_comm]

variable (R) in
/-- **Evaluation of entire series at `b`** as a ring homomorphism from the subring of entire
series to a complete normed algebra. -/
noncomputable def IsEntire.evalAtHom (b : A) : IsEntire.subring R →+* A where
  toFun f := (f : R⟦X⟧).evalAt b
  map_one' := evalAt_one b
  map_mul' f g := (IsEntire.mem_subring.mp f.2).evalAt_mul (IsEntire.mem_subring.mp g.2) b
  map_zero' := evalAt_zero b
  map_add' f g := (IsEntire.mem_subring.mp f.2).evalAt_add (IsEntire.mem_subring.mp g.2) b

/-- The evaluation homomorphism at `b` sends an entire series `f` to `f(b)`. -/
@[simp]
theorem IsEntire.evalAtHom_apply (b : A) (f : IsEntire.subring R) :
    IsEntire.evalAtHom R b f = (f : R⟦X⟧).evalAt b :=
  (rfl)

/-- Evaluation commutes with powers of entire series. -/
theorem IsEntire.evalAt_pow (hf : f.IsEntire) (n : ℕ) (b : A) :
    (f ^ n).evalAt b = f.evalAt b ^ n := by
  simpa using map_pow (IsEntire.evalAtHom R b) ⟨f, IsEntire.mem_subring.mpr hf⟩ n

/-- Evaluation of entire series commutes with continuous algebra homomorphisms:
`ψ (f(b)) = f(ψ b)`. -/
theorem IsEntire.map_evalAt {B F : Type*} [Semiring B] [Algebra R B] [TopologicalSpace B]
    [T2Space B] [FunLike F A B] [AlgHomClass F R A B] (hf : f.IsEntire) (ψ : F)
    (hψ : Continuous ψ) (b : A) : ψ (f.evalAt b) = f.evalAt (ψ b) := by
  rw [← ((hf.hasSum_evalAt b).map ψ hψ).tsum_eq, evalAt_def]
  simp [map_smul, map_pow]

/-- Evaluation of entire series commutes with continuous coefficient homomorphisms:
`(φ f)(φ a) = φ (f(a))`. -/
theorem IsEntire.evalAt_map {S : Type*} [CommRing S] [TopologicalSpace S] [T2Space S]
    [CompleteSpace R] (hf : f.IsEntire) (φ : R →+* S) (hφ : Continuous φ) (a : R) :
    (PowerSeries.map φ f).evalAt (φ a) = φ (f.evalAt a) := by
  rw [← ((hf.hasSum_evalAt a).map φ hφ).tsum_eq, evalAt_def]
  simp [map_pow]

/-- **Evaluated Leibniz rule at `a` for `(X - a)ᵐ g`.** For entire `g`, the Hasse derivative of
order `j` of `(X - a)ᵐ g` at `a` is the Hasse derivative of order `j - m` of `g` at `a` when
`m ≤ j`, and `0` otherwise. -/
@[simp]
theorem IsEntire.evalAt_hasseDeriv_X_sub_C_pow_mul [CompleteSpace R] (hg : g.IsEntire) (a : R)
    (m j : ℕ) :
    (PowerSeries.hasseDeriv j ((X - C a) ^ m * g)).evalAt a =
      if m ≤ j then (PowerSeries.hasseDeriv (j - m) g).evalAt a else 0 := by
  have hP : ((X - C a) ^ m : R⟦X⟧).IsEntire := (isEntire_X.sub (isEntire_C a)).pow m
  rw [hasseDeriv_mul, IsEntire.evalAt_sum _ fun ij _ ↦ (hP.hasseDeriv _).mul (hg.hasseDeriv _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [(hP.hasseDeriv _).evalAt_mul (hg.hasseDeriv _), evalAt_hasseDeriv_X_sub_C_pow, ite_mul,
    one_mul, zero_mul]
  simp [Finset.sum_ite_eq']

/-- The value of an entire series at `b` is `a₀ + b ∑ₙ aₙ₊₁ • bⁿ`. -/
theorem IsEntire.evalAt_eq_algebraMap_add_mul (hf : f.IsEntire) (b : A) :
    f.evalAt b =
      algebraMap R A (constantCoeff f) + b * (mk fun n ↦ coeff (n + 1) f).evalAt b := by
  conv_lhs => rw [eq_X_mul_shift_add_const f]
  rw [(isEntire_X.mul hf.mk_coeff_succ).evalAt_add (isEntire_C _), isEntire_X.evalAt_mul
    hf.mk_coeff_succ, evalAt_X, evalAt_C, add_comm]

/-- If an entire series has constant coefficient `1` and vanishes at `a`, then `a` times
`-∑ₙ aₙ₊₁ • aⁿ` is `1` on both sides. -/
private theorem IsEntire.mul_eq_one_of_evalAt_eq_zero (hf : f.IsEntire)
    (h0 : constantCoeff f = 1) {a : A} (ha : f.evalAt a = 0) :
    a * -(mk fun n ↦ coeff (n + 1) f).evalAt a = 1 ∧
      -(mk fun n ↦ coeff (n + 1) f).evalAt a * a = 1 := by
  have h := hf.evalAt_eq_algebraMap_add_mul a
  rw [ha, h0, map_one, eq_comm, add_eq_zero_iff_eq_neg'] at h
  have h' := (commute_evalAt (mk fun n ↦ coeff (n + 1) f) a).eq ▸ h
  exact ⟨by rw [mul_neg, h, neg_neg], by rw [neg_mul, h', neg_neg]⟩

/-- **Zeros of entire series with constant coefficient `1` are units.** If an entire series `f`
with `f(0) = 1` vanishes at `a`, then `a` is invertible. -/
theorem IsEntire.isUnit_of_evalAt_eq_zero (hf : f.IsEntire) (h0 : constantCoeff f = 1) {a : A}
    (ha : f.evalAt a = 0) : IsUnit a :=
  let h := hf.mul_eq_one_of_evalAt_eq_zero h0 ha
  ⟨⟨a, _, h.1, h.2⟩, rfl⟩

/-- If an entire series `f = ∑ aₙ Xⁿ` with `a₀ = 1` vanishes at `a`, then the inverse of `a` is
`-∑ₙ aₙ₊₁ • aⁿ`. -/
theorem IsEntire.inverse_eq_of_evalAt_eq_zero (hf : f.IsEntire) (h0 : constantCoeff f = 1)
    {a : A} (ha : f.evalAt a = 0) :
    Ring.inverse a = -(mk fun n ↦ coeff (n + 1) f).evalAt a :=
  let h := hf.mul_eq_one_of_evalAt_eq_zero h0 ha
  Ring.inverse_unit ⟨a, _, h.1, h.2⟩

/-- **Continuity at `0`.** For an entire series `f = ∑ aₙ Xⁿ`, the value `f(b)` tends to
`f(0) = a₀` as `b` tends to `0`. -/
theorem IsEntire.tendsto_evalAt_nhds_zero_nhds_constantCoeff [NormOneClass A]
    (hf : f.IsEntire) :
    Tendsto (fun b : A ↦ f.evalAt b) (𝓝 0) (𝓝 (algebraMap R A (constantCoeff f))) := by
  set g : R⟦X⟧ := mk fun n ↦ coeff (n + 1) f
  have hg : g.IsEntire := hf.mk_coeff_succ
  set C := ∑' n, ‖coeff n g‖
  -- For `‖b‖ ≤ 1`, `‖f(b) - a₀‖ = ‖b g(b)‖ ≤ ‖b‖ ∑ ‖gₙ‖`.
  have hC (b : A) (hb : ‖b‖ ≤ 1) : ‖g.evalAt b‖ ≤ C :=
    (hg.norm_evalAt_le b).trans <| by
      simpa using (hg.summable_norm_coeff_mul_pow ‖b‖).tsum_le_tsum
        (fun n ↦ mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg b) hb) (norm_nonneg _))
        (by simpa using hg.summable_norm_coeff_mul_pow 1)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (g := fun b : A ↦ ‖b‖ * C)
    (.of_forall fun _ ↦ norm_nonneg _) ?_ (by simpa using tendsto_norm_zero.mul_const C))
  filter_upwards [Metric.closedBall_mem_nhds (0 : A) one_pos] with b hb
  rw [mem_closedBall_zero_iff] at hb
  rw [hf.evalAt_eq_algebraMap_add_mul b, add_sub_cancel_left]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hC b hb) (norm_nonneg b))

/-- **Identity principle for entire series over a ring.** An entire series over a complete normed
commutative ring that vanishes at non-zero-divisors accumulating at `0` is zero. Over a normed
field the non-zero-divisors are the nonzero elements; over Tate scalars the powers of a
pseudo-uniformiser are non-zero-divisors tending to `0`. -/
theorem IsEntire.eq_zero_of_frequently_evalAt_eq_zero [NormOneClass R] [CompleteSpace R]
    (hf : f.IsEntire) (h : ∃ᶠ x in 𝓝 (0 : R), x ∈ nonZeroDivisors R ∧ f.evalAt x = 0) :
    f = 0 := by
  -- A series vanishing at such points has constant coefficient `0`, by continuity at `0`, and the
  -- series `∑ aₙ₊₁ Xⁿ` vanishes at the same points, since `f(x) = a₀ + x ∑ aₙ₊₁ xⁿ`.
  have key (g : R⟦X⟧) (hg : g.IsEntire)
      (h : ∃ᶠ x in 𝓝 (0 : R), x ∈ nonZeroDivisors R ∧ g.evalAt x = 0) :
      constantCoeff g = 0 ∧ ∃ᶠ x in 𝓝 (0 : R),
        x ∈ nonZeroDivisors R ∧ (mk fun n ↦ coeff (n + 1) g).evalAt x = 0 := by
    have h0 : constantCoeff g = 0 := by
      simpa using mem_closure_of_frequently_of_tendsto (s := {0}) (h.mono fun x hx ↦ hx.2)
        hg.tendsto_evalAt_nhds_zero_nhds_constantCoeff
    refine ⟨h0, h.mono fun x ⟨hx, hgx⟩ ↦ ⟨hx, ?_⟩⟩
    rwa [hg.evalAt_eq_algebraMap_add_mul, h0, map_zero, zero_add,
      mul_left_mem_nonZeroDivisors_eq_zero_iff hx] at hgx
  ext n
  induction n generalizing f with
  | zero => simpa using (key f hf h).1
  | succ n ih => simpa using ih hf.mk_coeff_succ (key f hf h).2

/-- **Entire series are determined by their values** over a complete normed commutative ring in
which non-zero-divisors accumulate at `0`, such as a nontrivially normed field or a ring with Tate
scalars. -/
theorem IsEntire.eq_of_forall_evalAt_eq [NormOneClass R] [CompleteSpace R] (hf : f.IsEntire)
    (hg : g.IsEntire) (hR : ∃ᶠ x in 𝓝 (0 : R), x ∈ nonZeroDivisors R)
    (h : ∀ x : R, f.evalAt x = g.evalAt x) : f = g :=
  sub_eq_zero.1 <| (hf.sub hg).eq_zero_of_frequently_evalAt_eq_zero <|
    hR.mono fun x hx ↦ ⟨hx, by rw [hf.evalAt_sub hg, h, sub_self]⟩

end Normed

section Scalar

variable {R A : Type*} [SeminormedRing R] [NormedRing A] [Module R A] [IsBoundedSMul R A]
  {F : A⟦X⟧}

/-- For an entire series `F = ∑ Fₙ Xⁿ` over a normed ring, the terms `aⁿ • Fₙ` of its value at a
scalar `a` are absolutely summable. -/
theorem IsEntire.summable_norm_pow_smul_coeff (hF : F.IsEntire) (a : R) :
    Summable fun n ↦ ‖a ^ n • coeff n F‖ := by
  -- `‖aⁿ‖ ≤ ‖a‖ⁿ` only holds for `n ≥ 1`, so the term of index `0` is set aside
  rw [← summable_nat_add_iff 1]
  refine ((summable_nat_add_iff 1).mpr (hF.summable_norm_coeff_mul_pow ‖a‖)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  exact (norm_smul_le _ _).trans <| (mul_le_mul_of_nonneg_right (norm_pow_le' a n.succ_pos)
    (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- **Evaluation of entire series at scalars.** For an entire series `F = ∑ Fₙ Xⁿ` over a complete
normed ring and any scalar `a`, the series `∑ aⁿ • Fₙ` converges to `F(a)`. -/
theorem IsEntire.hasSum_evalScalar [CompleteSpace A] (hF : F.IsEntire) (a : R) :
    HasSum (fun n ↦ a ^ n • coeff n F) (F.evalScalar a) := by
  rw [evalScalar_def]
  exact (hF.summable_norm_pow_smul_coeff a).of_norm.hasSum

/-- Evaluation at a scalar is additive on entire series over a complete normed ring. -/
theorem IsEntire.evalScalar_add [CompleteSpace A] {G : A⟦X⟧} (hF : F.IsEntire) (hG : G.IsEntire)
    (a : R) : (F + G).evalScalar a = F.evalScalar a + G.evalScalar a :=
  PowerSeries.evalScalar_add (hF.summable_norm_pow_smul_coeff a).of_norm
    (hG.summable_norm_pow_smul_coeff a).of_norm

end Scalar

end PowerSeries
