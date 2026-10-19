/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import TauCeti.RingTheory.PowerSeries.Entire.Basic
public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Evaluation of entire power series

For a power series `f = ∑ aₙ Xⁿ` over a commutative ring `R` and an element `b` of an `R`-algebra
`A` with a topology, `PowerSeries.evalAt f b` is the infinite sum `∑ₙ aₙ • bⁿ`, with the junk
value `0` when the sum does not converge. The algebra `A` need not be commutative: the scalars
`aₙ` act centrally, so the values of `f` at `b` commute with `b`.

When `R` is normed, `A` is a complete normed ring with `‖r • x‖ ≤ ‖r‖ ‖x‖`, and `f` is entire, the
sum converges absolutely at every `b`: since `f` is restricted at the radius `2 ‖b‖`, its terms are
bounded by a constant times `2⁻ⁿ`. No ultrametric hypothesis is needed for convergence, so this
evaluates entire series both at operators on `p`-adic Banach spaces and in complex Banach
algebras. On
the subring of entire series, evaluation at `b` is a ring homomorphism
(`PowerSeries.IsEntire.evalAtHom`); it extends polynomial evaluation and commutes with continuous
algebra homomorphisms and with extension of scalars. In an ultrametric algebra, `‖f(b)‖` is
bounded by the Gauss norm of `f` at every radius `r ≥ ‖b‖`.

A consequence used for Fredholm determinants: if `f(0) = 1` and `f(a) = 0`, then `a` is a unit
with inverse `-∑ₙ aₙ₊₁ • aⁿ`, since `f(a) = 1 + a ∑ₙ aₙ₊₁ • aⁿ`.

Over a field `𝕜`, the same sum is Mathlib's `FormalMultilinearSeries.ofScalarsSum`
(`PowerSeries.evalAt_eq_ofScalarsSum`); that construction needs a field of scalars, while the
coefficient rings here may have nilpotents.

## Main definitions

* `PowerSeries.evalAt`: the value `∑ₙ aₙ • bⁿ` of a power series at `b`.
* `PowerSeries.IsEntire.evalAtHom`: evaluation at `b` as a ring homomorphism on entire series.

## Main results

* `PowerSeries.IsEntire.summable_norm_coeff_mul_pow`: `∑ ‖aₙ‖ tⁿ` converges for every real `t`.
* `PowerSeries.IsEntire.hasSum_evalAt`: the series `∑ aₙ • bⁿ` converges to `f(b)`.
* `PowerSeries.evalAt_coe`: on polynomials, `evalAt` is `Polynomial.aeval`.
* `PowerSeries.IsEntire.evalAt_add`, `PowerSeries.IsEntire.evalAt_mul`: evaluation is additive and
  multiplicative on entire series.
* `PowerSeries.IsEntire.norm_evalAt_le_gaussNorm`: in an ultrametric algebra, `‖f(b)‖` is at most
  the Gauss norm of `f` at any radius `r ≥ ‖b‖`.
* `PowerSeries.IsEntire.map_evalAt`, `PowerSeries.evalAt_map`: naturality in the algebra and in
  the coefficients.
* `PowerSeries.IsEntire.isUnit_of_evalAt_eq_zero` and
  `PowerSeries.IsEntire.inverse_eq_of_evalAt_eq_zero`: a zero of an entire series with constant
  coefficient `1` is a unit, with explicit inverse.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]

/-- The value `f(b) = ∑ₙ aₙ • bⁿ` of the power series `f = ∑ aₙ Xⁿ` at an element `b` of a
topological `R`-algebra, defined as an infinite sum. It takes the junk value `0` when the sum does
not converge; for entire `f` over a normed ring it converges in every complete normed algebra
(`PowerSeries.IsEntire.hasSum_evalAt`). -/
noncomputable def evalAt (f : R⟦X⟧) (b : A) : A :=
  ∑' n, coeff n f • b ^ n

/-- The value `f(b)` is the infinite sum `∑ₙ aₙ • bⁿ`. -/
theorem evalAt_def (f : R⟦X⟧) (b : A) : f.evalAt b = ∑' n, coeff n f • b ^ n :=
  (rfl)

/-- On polynomials, evaluation is `Polynomial.aeval`. -/
@[simp]
theorem evalAt_coe (p : Polynomial R) (b : A) : (p : R⟦X⟧).evalAt b = Polynomial.aeval b p := by
  rw [evalAt_def, tsum_eq_sum (s := Finset.range (p.natDegree + 1)),
    Polynomial.aeval_eq_sum_range]
  · simp
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- The zero series evaluates to zero. -/
@[simp]
theorem evalAt_zero (b : A) : (0 : R⟦X⟧).evalAt b = 0 := by
  simpa using evalAt_coe (0 : Polynomial R) b

/-- A constant series evaluates to its constant, mapped into the algebra. -/
@[simp]
theorem evalAt_C (a : R) (b : A) : (C a).evalAt b = algebraMap R A a := by
  simpa using evalAt_coe (Polynomial.C a) b

/-- The series `1` evaluates to `1`. -/
@[simp]
theorem evalAt_one (b : A) : (1 : R⟦X⟧).evalAt b = 1 := by
  simpa using evalAt_coe (1 : Polynomial R) b

/-- The variable `X` evaluates to the point of evaluation. -/
@[simp]
theorem evalAt_X (b : A) : (X : R⟦X⟧).evalAt b = b := by
  simpa using evalAt_coe (Polynomial.X : Polynomial R) b

/-- The monomial `a Xⁿ` evaluates to `a • bⁿ`. -/
@[simp]
theorem evalAt_monomial (n : ℕ) (a : R) (b : A) : (monomial n a).evalAt b = a • b ^ n := by
  simpa [Algebra.smul_def] using evalAt_coe (Polynomial.monomial n a) b

/-- At the point `0`, a power series evaluates to its constant coefficient. -/
@[simp]
theorem evalAt_at_zero (f : R⟦X⟧) : f.evalAt (0 : A) = algebraMap R A (constantCoeff f) := by
  rw [evalAt_def, tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn]]
  simp [Algebra.smul_def]

/-- Evaluation is compatible with extension of scalars: mapping the coefficients along
`R → S` does not change the value at a point of an `S`-algebra. -/
@[simp]
theorem evalAt_map {S : Type*} [CommSemiring S] [Algebra R S] [Algebra S A] [IsScalarTower R S A]
    (f : R⟦X⟧) (b : A) : (map (algebraMap R S) f).evalAt b = f.evalAt b := by
  simp [evalAt_def]

/-- Over a field, `evalAt` is the sum `FormalMultilinearSeries.ofScalarsSum` of the scalar
series with the same coefficients. -/
theorem evalAt_eq_ofScalarsSum {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E]
    [TopologicalSpace E] [IsTopologicalRing E] (f : 𝕜⟦X⟧) (x : E) :
    f.evalAt x = FormalMultilinearSeries.ofScalarsSum (E := E) (fun n ↦ coeff n f) x :=
  (FormalMultilinearSeries.ofScalars_sum_eq _ x).symm

/-- The values of a series at `b` commute with `b`. -/
theorem commute_evalAt [IsTopologicalSemiring A] [T2Space A] (f : R⟦X⟧) (b : A) :
    Commute b (f.evalAt b) :=
  Commute.tsum_right _ fun n ↦ ((Commute.refl b).pow_right n).smul_right _

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [T2Space A]

/-- Evaluation commutes with negation. -/
@[simp]
theorem evalAt_neg (f : R⟦X⟧) (b : A) : (-f).evalAt b = -f.evalAt b := by
  simp [evalAt_def, neg_smul, tsum_neg]

end Ring

section NormedRing

variable {R : Type*} [NormedRing R] {f : R⟦X⟧}

/-- For an entire series `f = ∑ aₙ Xⁿ`, the series `∑ ‖aₙ‖ tⁿ` converges for every real `t`. -/
theorem IsEntire.summable_norm_coeff_mul_pow (hf : f.IsEntire) (t : ℝ) :
    Summable fun n ↦ ‖coeff n f‖ * t ^ n := by
  -- restrictedness at the radius `2 |t|` bounds the terms by a multiple of `2⁻ⁿ`
  obtain ⟨B, hB⟩ := ((isRestricted_iff' (2 * |t|) f).mp (hf.isRestricted _)).bddAbove_range
  refine Summable.of_norm_bounded (summable_geometric_two.mul_left B) fun n ↦ ?_
  have hn : ‖coeff n f‖ * (2 * |t|) ^ n ≤ B := hB ⟨n, rfl⟩
  calc ‖‖coeff n f‖ * t ^ n‖ = ‖coeff n f‖ * (2 * |t|) ^ n * (1 / 2) ^ n := by
        rw [norm_mul, norm_norm, norm_pow, Real.norm_eq_abs, mul_assoc, ← mul_pow, mul_one_div,
          mul_div_cancel_left₀ _ two_ne_zero]
    _ ≤ B * (1 / 2) ^ n := by gcongr

/-- The series `∑ aₙ₊₁ Xⁿ` obtained from an entire series by dropping the constant term and
dividing by `X` is entire. -/
theorem IsEntire.mk_coeff_succ (hf : f.IsEntire) : (mk fun n ↦ coeff (n + 1) f).IsEntire := by
  refine isEntire_iff_forall_pos.mpr fun r hr ↦ (isRestricted_iff' r _).mpr ?_
  have h := ((tendsto_add_atTop_iff_nat 1).mpr
    ((isRestricted_iff' r f).mp (hf.isRestricted r))).mul_const r⁻¹
  rw [zero_mul] at h
  refine h.congr fun n ↦ ?_
  rw [coeff_mk, pow_succ, ← mul_assoc, mul_inv_cancel_right₀ hr.ne']

end NormedRing

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
    ‖f.evalAt b‖ ≤ ∑' n, ‖coeff n f‖ * ‖b‖ ^ n :=
  (norm_tsum_le_tsum_norm (hf.summable_norm_smul_pow b)).trans <|
    (hf.summable_norm_smul_pow b).tsum_le_tsum (fun n ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_pow_le b n) (norm_nonneg _)))
      (hf.summable_norm_coeff_mul_pow ‖b‖)

/-- In an ultrametric normed algebra with `‖1‖ = 1`, the value of an entire series at a point `b`
with `‖b‖ ≤ r` is bounded by the Gauss norm of the series at the radius `r`. -/
theorem IsEntire.norm_evalAt_le_gaussNorm [IsUltrametricDist A] [NormOneClass A]
    (hf : f.IsEntire) {b : A} {r : ℝ} (hb : ‖b‖ ≤ r) :
    ‖f.evalAt b‖ ≤ gaussNorm norm r f :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gaussNorm_nonneg _ _ _ norm_nonneg)
    fun n ↦ (norm_smul_le _ _).trans <|
      (mul_le_mul_of_nonneg_left ((norm_pow_le b n).trans
        (pow_le_pow_left₀ (norm_nonneg b) hb n)) (norm_nonneg _)).trans <|
      le_gaussNorm _ _ _ (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (hf.isRestricted r)) n

variable [CompleteSpace A]

/-- For an entire series `f = ∑ aₙ Xⁿ`, the terms `aₙ • bⁿ` are summable in a complete
algebra. -/
theorem IsEntire.summable_smul_pow (hf : f.IsEntire) (b : A) :
    Summable fun n ↦ coeff n f • b ^ n :=
  (hf.summable_norm_smul_pow b).of_norm

/-- **Evaluation of entire series.** For an entire series `f = ∑ aₙ Xⁿ` and any `b` in a complete
normed algebra, the series `∑ aₙ • bⁿ` converges to `f(b)`. -/
theorem IsEntire.hasSum_evalAt (hf : f.IsEntire) (b : A) :
    HasSum (fun n ↦ coeff n f • b ^ n) (f.evalAt b) :=
  (hf.summable_smul_pow b).hasSum

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

end Normed

end PowerSeries
