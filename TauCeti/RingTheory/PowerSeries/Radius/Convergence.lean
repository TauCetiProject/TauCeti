/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Radius.Basic

/-!
# Convergence of power series in extensions and the convergence-point radius

Let `f = ∑ aₙ Xⁿ` be a power series over a normed ring `R` and let `A` be a seminormed `R`-module
ring with multiplicative scalar and power norms (`‖r • x‖ = ‖r‖ ‖x‖` and `‖x * y‖ = ‖x‖ ‖y‖`),
such as a normed field extension `L / K`. For `n ≥ 1` the `n`-th term of `f(x) = ∑ aₙ • xⁿ` has
norm `‖aₙ • xⁿ‖ = ‖aₙ‖ ‖x‖ⁿ`. Consequently:

* if `∑ aₙ • xⁿ` is summable at `x : A`, its terms tend to zero, so `f` is restricted at `‖x‖` and
  `‖x‖ₑ ≤ f.radius` (`PowerSeries.isRestricted_of_summable_smul_pow`,
  `PowerSeries.le_radius_of_summable_smul_pow`), with neither completeness nor an ultrametric
  hypothesis;
* in any complete target `A` with bounded scalar action, `∑ aₙ • xⁿ` is absolutely summable and
  sums to `f.evalAt x` at every `x` with `‖x‖ₑ < f.radius`
  (`PowerSeries.summable_norm_smul_pow_of_lt_radius`, `PowerSeries.hasSum_evalAt_of_lt_radius`);
* when `A` is complete and ultrametric, summability of `∑ aₙ • xⁿ` at `x` is equivalent to
  `f.IsRestricted ‖x‖` (`PowerSeries.summable_smul_pow_iff_isRestricted`). At a restricted radius
  `r`, the series converges on the entire closed ball `{y : A | ‖y‖ ≤ r}` with the Gauss-norm
  evaluation bound `‖f.evalAt y‖ ≤ gaussNorm norm r f`
  (`PowerSeries.IsRestricted.summable_smul_pow`, `PowerSeries.IsRestricted.hasSum_evalAt`,
  `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm`), and conversely convergence throughout
  `{y : A | ‖y‖ ≤ r}` implies `f.IsRestricted r` whenever `r` is attained by a norm in `A`
  (`PowerSeries.forall_norm_le_summable_iff_isRestricted`).

Because `PowerSeries.radius f` is an intrinsic invariant of the coefficient norms, it does not
change when an extension is introduced. The supremum of `‖x‖ₑ` over the convergence points `x : A`
is defined separately as `PowerSeries.convergenceRadius A f`. It never exceeds `f.radius`
(`PowerSeries.convergenceRadius_le_radius`), and it equals `f.radius` when `A` is complete and its
positive norms are dense in `(0, ∞)`
(`PowerSeries.convergenceRadius_eq_radius_of_Ioi_subset_closure`,
`PowerSeries.convergenceRadius_eq_radius`). When the norms of `A` omit an open interval
`(r₁, r₂)` containing `f.radius`, `f.convergenceRadius A ≤ r₁ < f.radius`
(`PowerSeries.convergenceRadius_lt_radius_of_mem_Ioo`).

## Main definitions

* `PowerSeries.convergenceRadius A f`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over the points `x : A` at
  which `∑ aₙ • xⁿ` is summable.

## Main results

* `PowerSeries.tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted` and
  `PowerSeries.summable_smul_pow_iff_isRestricted`: term decay, and in a complete ultrametric
  target summability, at `x` are equivalent to `f.IsRestricted ‖x‖`.
* `PowerSeries.forall_norm_le_summable_iff_isRestricted` and
  `PowerSeries.forall_norm_le_hasSum_evalAt_iff_isRestricted`: closed-ball convergence at an
  attained radius `r` is equivalent to `f.IsRestricted r`.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm`: `‖f.evalAt y‖ ≤ gaussNorm norm r f` on the
  closed ball `{y | ‖y‖ ≤ r}` at a restricted radius `r`.
* `PowerSeries.convergenceRadius_le_radius`: `f.convergenceRadius A ≤ f.radius`.
* `PowerSeries.convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt`,
  `PowerSeries.convergenceRadius_eq_radius_of_Ioi_subset_closure`, and
  `PowerSeries.convergenceRadius_eq_radius`: equality when the positive norms of a complete target
  are dense in `(0, ∞)`.
* `PowerSeries.convergenceRadius_le_of_radius_lt` and
  `PowerSeries.convergenceRadius_lt_radius_of_mem_Ioo`: strict inequality when `f.radius` falls in
  a gap of the norm set of `A`.
* `PowerSeries.min_convergenceRadius_le_convergenceRadius_add` and
  `PowerSeries.min_convergenceRadius_le_convergenceRadius_mul`: ultrametric sum and product bounds.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §1.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 6 §1.
-/

public section

namespace PowerSeries

open Filter
open scoped NNReal ENNReal Topology

section Pointwise

section NormSMul

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMulZeroClass R A]
  [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- When scalar multiplication and powers preserve norms, the terms `aₙ • xⁿ` tend to zero if and
only if `f` is restricted at `‖x‖`. -/
theorem tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted :
    Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0) ↔ f.IsRestricted ‖x‖ := by
  rw [tendsto_iff_norm_sub_tendsto_zero, isRestricted_iff']
  refine tendsto_congr' ?_
  -- `‖xⁿ‖ = ‖x‖ⁿ` needs `n ≥ 1` without `NormOneClass A`.
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sub_zero, norm_smul]
  refine congrArg (‖coeff n f‖ * ·) ?_
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k _ ih => rw [pow_succ x k, norm_mul, ih, ← pow_succ]

/-- For a point `x` of norm `r`, the terms `aₙ • xⁿ` tend to zero if and only if `f` is restricted
at `r`. -/
theorem tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted_of_norm_eq (hx : ‖x‖ = r) :
    Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0) ↔ f.IsRestricted r :=
  hx ▸ tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted

/-- Summability of `∑ aₙ • xⁿ` at `x` implies that `f` is restricted at `‖x‖`. -/
theorem isRestricted_of_summable_smul_pow (h : Summable fun n ↦ coeff n f • x ^ n) :
    f.IsRestricted ‖x‖ :=
  tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted.mp h.tendsto_atTop_zero

/-- Summability of `∑ aₙ • xⁿ` at a point `x` of norm `r` implies that `f` is restricted at `r`. -/
theorem isRestricted_of_summable_smul_pow_of_norm_eq (hx : ‖x‖ = r)
    (h : Summable fun n ↦ coeff n f • x ^ n) : f.IsRestricted r :=
  hx ▸ isRestricted_of_summable_smul_pow h

/-- If `∑ aₙ • xⁿ` is summable at `x`, then `‖x‖ₑ ≤ f.radius`. -/
theorem le_radius_of_summable_smul_pow (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.radius := by
  simpa using le_radius_of_isRestricted (isRestricted_of_summable_smul_pow h)

/-- If `∑ aₙ • yⁿ` is summable at every point `y` of the closed ball `{y : A | ‖y‖ ≤ r}` and `r`
is attained by a norm in `A`, then `f` is restricted at `r`. -/
theorem isRestricted_of_forall_norm_le_summable
    (h : ∀ y : A, ‖y‖ ≤ r → Summable fun n ↦ coeff n f • y ^ n) (hr : ∃ x : A, ‖x‖ = r) :
    f.IsRestricted r := by
  obtain ⟨x, rfl⟩ := hr
  exact isRestricted_of_summable_smul_pow (h x le_rfl)

end NormSMul

section Interior

/-- Strictly inside `f.radius`, the terms `aₙ • xⁿ` are absolutely summable in any seminormed ring
with a bounded scalar action. -/
theorem summable_norm_smul_pow_of_lt_radius {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMulZeroClass R A] [IsBoundedSMul R A] {f : R⟦X⟧} {x : A} (hx : ‖x‖ₑ < f.radius) :
    Summable fun n ↦ ‖coeff n f • x ^ n‖ := by
  obtain ⟨r, hxr, hrf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hx
  have hf : f.IsRestricted r := isRestricted_of_lt_radius (by simpa using hrf)
  have hxr' : |‖x‖| < |(r : ℝ)| := by
    rw [abs_norm, abs_of_nonneg r.coe_nonneg]
    exact mod_cast eNorm_lt_coe.mp hxr
  exact summable_norm_smul_pow_of_summable_norm_mul_pow (hf.summable_norm_coeff_mul_pow hxr')

/-- Strictly inside `f.radius`, the series `∑ aₙ • xⁿ` is summable in any complete seminormed ring
with a bounded scalar action. -/
theorem summable_smul_pow_of_lt_radius {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMulZeroClass R A] [IsBoundedSMul R A] [CompleteSpace A] {f : R⟦X⟧} {x : A}
    (hx : ‖x‖ₑ < f.radius) : Summable fun n ↦ coeff n f • x ^ n :=
  (summable_norm_smul_pow_of_lt_radius hx).of_norm

/-- Strictly inside `f.radius`, the series `∑ aₙ • xⁿ` sums to `f.evalAt x` in any complete
seminormed algebra with a bounded scalar action. -/
theorem hasSum_evalAt_of_lt_radius {R A : Type*} [NormedCommRing R] [SeminormedRing A]
    [Algebra R A] [IsBoundedSMul R A] [CompleteSpace A] {f : R⟦X⟧} {x : A}
    (hx : ‖x‖ₑ < f.radius) : HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) :=
  hasSum_evalAt_of_summable_norm (summable_norm_smul_pow_of_lt_radius hx)

end Interior

section Ultrametric

/-- In a complete ultrametric seminormed target with bounded scalar action, a series `f` restricted
at `r` is summable at every point `y` of the closed ball `{y | ‖y‖ ≤ r}`. -/
theorem IsRestricted.summable_smul_pow {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMulZeroClass R A] [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A]
    {f : R⟦X⟧} {r : ℝ} (hf : f.IsRestricted r) {y : A} (hy : ‖y‖ ≤ r) :
    Summable fun n ↦ coeff n f • y ^ n := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm' ?_ ((isRestricted_iff' r f).mp hf)
  -- `‖yⁿ‖ ≤ ‖y‖ⁿ` holds for `n ≥ 1`, so `n = 0` is excluded on `atTop`.
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (norm_smul_le _ _).trans <| mul_le_mul_of_nonneg_left
    ((norm_pow_le' y (Nat.pos_of_ne_zero hn)).trans (pow_le_pow_left₀ (norm_nonneg y) hy n))
    (norm_nonneg _)

/-- In an ultrametric normed algebra with `‖1‖ = 1`, the value of a series restricted at `r` on the
closed ball `{y | ‖y‖ ≤ r}` is bounded in norm by the Gauss norm at `r`. -/
theorem IsRestricted.norm_evalAt_le_gaussNorm {R A : Type*} [NormedCommRing R] [NormedRing A]
    [NormOneClass A] [Algebra R A] [IsBoundedSMul R A] [IsUltrametricDist A]
    {f : R⟦X⟧} {r : ℝ} (hf : f.IsRestricted r) {y : A} (hy : ‖y‖ ≤ r) :
    ‖f.evalAt y‖ ≤ gaussNorm norm r f :=
  PowerSeries.norm_evalAt_le_gaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf) hy

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [Module R A]
  [NormSMulClass R A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
  {f : R⟦X⟧} {x : A} {r : ℝ}

/-- **Ultrametric pointwise convergence criterion.** In a complete ultrametric target in which
scalar multiplication and powers preserve norms, `∑ aₙ • xⁿ` is summable at `x` if and only if `f`
is restricted at `‖x‖`. -/
theorem summable_smul_pow_iff_isRestricted :
    (Summable fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted ‖x‖ :=
  ⟨isRestricted_of_summable_smul_pow, fun hf ↦ hf.summable_smul_pow le_rfl⟩

/-- **Ultrametric convergence at a point of prescribed norm.** For `x : A` with `‖x‖ = r`,
`∑ aₙ • xⁿ` is summable if and only if `f` is restricted at `r`. -/
theorem summable_smul_pow_iff_isRestricted_of_norm_eq (hx : ‖x‖ = r) :
    (Summable fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted r :=
  hx ▸ summable_smul_pow_iff_isRestricted

/-- **Closed-ball convergence characterization.** When the radius `r` is attained by a norm in a
complete ultrametric target `A`, `∑ aₙ • yⁿ` is summable throughout `{y : A | ‖y‖ ≤ r}` if and only
if `f` is restricted at `r`. -/
theorem forall_norm_le_summable_iff_isRestricted (hr : ∃ x : A, ‖x‖ = r) :
    (∀ y : A, ‖y‖ ≤ r → Summable fun n ↦ coeff n f • y ^ n) ↔ f.IsRestricted r :=
  ⟨fun h ↦ isRestricted_of_forall_norm_le_summable h hr, fun hf _ hy ↦ hf.summable_smul_pow hy⟩

/-- When the radius `r` is attained by a norm in a complete ultrametric normed algebra `A`, the
series `∑ aₙ • yⁿ` sums to `f.evalAt y` throughout `{y : A | ‖y‖ ≤ r}` if and only if `f` is
restricted at `r`. -/
theorem forall_norm_le_hasSum_evalAt_iff_isRestricted {R A : Type*} [NormedCommRing R]
    [NormedRing A] [Algebra R A] [NormSMulClass R A] [NormMulClass A]
    [IsUltrametricDist A] [CompleteSpace A] {f : R⟦X⟧} {r : ℝ} (hr : ∃ x : A, ‖x‖ = r) :
    (∀ y : A, ‖y‖ ≤ r → HasSum (fun n ↦ coeff n f • y ^ n) (f.evalAt y)) ↔ f.IsRestricted r :=
  ⟨fun h ↦ isRestricted_of_forall_norm_le_summable (fun y hy ↦ (h y hy).summable) hr,
    fun hf _ hy ↦ hf.hasSum_evalAt hy⟩

end Ultrametric

end Pointwise

section ConvergenceRadius

section Semiring

variable {R : Type*} [Semiring R]

/-- The *convergence-point radius* of a power series `f = ∑ aₙ Xⁿ` in a seminormed target `A`: the
supremum, in `ℝ≥0∞`, of `‖x‖ₑ` over the points `x : A` at which `∑ aₙ • xⁿ` is summable. Unlike
`PowerSeries.radius`, this quantity depends on the norms attained in `A`. -/
noncomputable def convergenceRadius (A : Type*) [SeminormedRing A] [SMul R A] (f : R⟦X⟧) :
    ℝ≥0∞ :=
  ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ

/-- The convergence-point radius as the supremum of `‖x‖ₑ` over convergence points `x : A`. -/
theorem convergenceRadius_def (A : Type*) [SeminormedRing A] [SMul R A] (f : R⟦X⟧) :
    f.convergenceRadius A = ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ :=
  (rfl)

/-- Every convergence point `x : A` of `f` has extended norm at most `f.convergenceRadius A`. -/
theorem le_convergenceRadius_of_summable {A : Type*} [SeminormedRing A] [SMul R A] {f : R⟦X⟧}
    {x : A} (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.convergenceRadius A :=
  le_iSup₂ (f := fun (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n) ↦ ‖x‖ₑ) x h

/-- Extending scalars along an algebra homomorphism does not change the convergence-point radius in
any target algebra over the extension. -/
@[simp]
theorem convergenceRadius_map_algebraMap {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Type*) [SeminormedRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] (f : R⟦X⟧) :
    (f.map (algebraMap R S)).convergenceRadius A = f.convergenceRadius A := by
  simp [convergenceRadius, coeff_map, algebraMap_smul]

/-- The zero series converges at every point of `A`, so its convergence-point radius is
`⨆ x : A, ‖x‖ₑ`. -/
theorem convergenceRadius_zero_eq_iSup (A : Type*) [SeminormedRing A] [Module R A] :
    (0 : R⟦X⟧).convergenceRadius A = ⨆ x : A, ‖x‖ₑ := by
  refine iSup_congr fun x ↦ iSup_pos ?_
  simp

/-- A polynomial converges at every point of `A`, so its convergence-point radius is
`⨆ x : A, ‖x‖ₑ`. -/
theorem convergenceRadius_coe_eq_iSup (A : Type*) [SeminormedRing A] [Module R A]
    (p : Polynomial R) : (p : R⟦X⟧).convergenceRadius A = ⨆ x : A, ‖x‖ₑ := by
  refine iSup_congr fun x ↦ iSup_pos <|
    summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn ↦ ?_
  rw [Finset.mem_range, not_lt] at hn
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- Over a nontrivially normed field `L`, the zero series has infinite convergence-point radius. -/
@[simp]
theorem convergenceRadius_zero (L : Type*) [NontriviallyNormedField L] [Module R L] :
    (0 : R⟦X⟧).convergenceRadius L = ⊤ := by
  rw [convergenceRadius_zero_eq_iSup]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨x, hx⟩ := NormedField.exists_lt_nnNorm L r
  exact (by simpa [eNorm_eq_nnNorm] using hx.le : (r : ℝ≥0∞) ≤ ‖x‖ₑ).trans (le_iSup _ x)

/-- Over a nontrivially normed field `L`, polynomials have infinite convergence-point radius. -/
@[simp]
theorem convergenceRadius_coe (L : Type*) [NontriviallyNormedField L] [Module R L]
    (p : Polynomial R) : (p : R⟦X⟧).convergenceRadius L = ⊤ := by
  rw [convergenceRadius_coe_eq_iSup, ← convergenceRadius_zero_eq_iSup (R := R),
    convergenceRadius_zero]

end Semiring

/-- Negating a power series preserves its convergence-point radius. -/
theorem convergenceRadius_neg {R A : Type*} [Ring R] [SeminormedRing A] [Module R A] (f : R⟦X⟧) :
    (-f).convergenceRadius A = f.convergenceRadius A := by
  simp only [convergenceRadius, map_neg, neg_smul, summable_neg_iff]

section Comparison

variable {R A : Type*} [NormedRing R] [SeminormedRing A] {f : R⟦X⟧}

/-- **Upper bound by the intrinsic radius.** When scalar multiplication and powers preserve norms,
the convergence-point radius in `A` is at most `f.radius`. -/
theorem convergenceRadius_le_radius [SMulZeroClass R A] [NormSMulClass R A] [NormMulClass A] :
    f.convergenceRadius A ≤ f.radius :=
  iSup₂_le fun _ hx ↦ le_radius_of_summable_smul_pow hx

/-- **Lower bound from dense positive norms.** In a complete target `A` with bounded scalar action
whose norms separate any two radii `0 ≤ r₁ < r₂`, `f.radius ≤ f.convergenceRadius A`. -/
theorem le_convergenceRadius_of_forall_exists_lt_norm_lt [SMulZeroClass R A] [IsBoundedSMul R A]
    [CompleteSpace A]
    (hdense : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → r₁ < r₂ → ∃ x : A, r₁ < ‖x‖ ∧ ‖x‖ < r₂) :
    f.radius ≤ f.convergenceRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨s, hrs, hsf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  obtain ⟨x, hrx, hxs⟩ := hdense r s r.coe_nonneg (mod_cast hrs)
  have hx_lt : ‖x‖ₑ < f.radius := by
    refine (eNorm_lt_coe.mpr ?_).trans hsf
    exact_mod_cast hxs
  have hrx' : (r : ℝ≥0∞) ≤ ‖x‖ₑ := by
    rw [eNorm_eq_nnNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
    exact hrx.le
  exact hrx'.trans (le_convergenceRadius_of_summable (summable_smul_pow_of_lt_radius hx_lt))

/-- **Equality for dense positive norms**, interval form. In a complete target `A` in which scalar
multiplication and powers preserve norms and every interval `(r₁, r₂)` with `0 ≤ r₁ < r₂` contains
a norm of `A`, the convergence-point radius equals `f.radius`. -/
theorem convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt [Module R A] [NormSMulClass R A]
    [NormMulClass A] [CompleteSpace A]
    (hdense : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → r₁ < r₂ → ∃ x : A, r₁ < ‖x‖ ∧ ‖x‖ < r₂) :
    f.convergenceRadius A = f.radius :=
  le_antisymm convergenceRadius_le_radius (le_convergenceRadius_of_forall_exists_lt_norm_lt hdense)

/-- **Equality for dense positive norms**, closure form. When `A` is complete, scalar multiplication
and powers preserve norms, and the nonzero norms of `A` are dense in `(0, ∞)`,
`f.convergenceRadius A = f.radius`. -/
theorem convergenceRadius_eq_radius_of_Ioi_subset_closure [Module R A] [NormSMulClass R A]
    [NormMulClass A] [CompleteSpace A]
    (hdense : Set.Ioi (0 : ℝ) ⊆ closure (Set.range (norm : A → ℝ) \ {0})) :
    f.convergenceRadius A = f.radius := by
  refine convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt fun r₁ r₂ hr₀ hr ↦ ?_
  have hm : (r₁ + r₂) / 2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  obtain ⟨_, ⟨⟨x, rfl⟩, -⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (hdense hm) ((r₂ - r₁) / 2) (by linarith)
  rw [Real.dist_eq, abs_sub_lt_iff] at hdist
  exact ⟨x, by linarith, by linarith⟩

/-- **Equality over a complete densely normed field.** In any complete densely normed field `L`
on which `R` acts linearly with norm-preserving scalar multiplication (for instance `ℂ` or
`ℂ_[p]`), the convergence-point radius equals `f.radius`. -/
@[simp]
theorem convergenceRadius_eq_radius (L : Type*) [DenselyNormedField L] [Module R L]
    [NormSMulClass R L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergenceRadius L = f.radius :=
  convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt fun _ _ hr₀ hr ↦
    DenselyNormedField.lt_norm_lt _ _ hr₀ hr

/-- **Gap bound on the convergence-point radius.** If no element of `A` has extended norm in the
open interval `(r₁, r₂)` and `f.radius < r₂`, every convergence point of `f` in `A` has extended
norm at most `r₁`, so `f.convergenceRadius A ≤ r₁`. -/
theorem convergenceRadius_le_of_radius_lt [SMulZeroClass R A] [NormSMulClass R A] [NormMulClass A]
    {r₁ r₂ : ℝ≥0∞} (hgap : ∀ x : A, r₁ < ‖x‖ₑ → r₂ ≤ ‖x‖ₑ) (hr : f.radius < r₂) :
    f.convergenceRadius A ≤ r₁ :=
  iSup₂_le fun x hx ↦ le_of_not_gt fun hrx ↦
    ((hgap x hrx).trans (le_radius_of_summable_smul_pow hx)).not_gt hr

/-- **Strict inequality across a norm gap.** If no element of `A` has extended norm in `(r₁, r₂)`
and `r₁ < f.radius < r₂`, then `f.convergenceRadius A < f.radius`. -/
theorem convergenceRadius_lt_radius_of_mem_Ioo [SMulZeroClass R A] [NormSMulClass R A]
    [NormMulClass A] {r₁ r₂ : ℝ≥0∞} (hgap : ∀ x : A, r₁ < ‖x‖ₑ → r₂ ≤ ‖x‖ₑ)
    (hr₁ : r₁ < f.radius) (hr₂ : f.radius < r₂) :
    f.convergenceRadius A < f.radius :=
  (convergenceRadius_le_of_radius_lt hgap hr₂).trans_lt hr₁

end Comparison

section UltrametricConvergenceRadius

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [Module R A]
  [NormSMulClass R A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
  {f g : R⟦X⟧} {x : A}

/-- In a complete ultrametric target, `f.convergenceRadius A` is the supremum of `‖x‖ₑ` over the
points `x : A` at which `f` is restricted at `‖x‖`. -/
theorem convergenceRadius_eq_iSup_isRestricted :
    f.convergenceRadius A = ⨆ (x : A) (_ : f.IsRestricted ‖x‖), ‖x‖ₑ := by
  simp only [convergenceRadius, summable_smul_pow_iff_isRestricted]

/-- In a complete ultrametric target, `∑ aₙ • xⁿ` is summable at every `x : A` with
`‖x‖ₑ < f.convergenceRadius A`. -/
theorem summable_smul_pow_of_lt_convergenceRadius (hx : ‖x‖ₑ < f.convergenceRadius A) :
    Summable fun n ↦ coeff n f • x ^ n := by
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp hx
  obtain ⟨hsum, hxy⟩ := lt_iSup_iff.mp hy
  rw [eNorm_eq_nnNorm, eNorm_eq_nnNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hxy
  exact (isRestricted_of_summable_smul_pow hsum).summable_smul_pow hxy.le

/-- In a complete ultrametric target, the convergence-point radius of a sum is at least the minimum
of the two convergence-point radii. -/
theorem min_convergenceRadius_le_convergenceRadius_add (f g : R⟦X⟧) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ (f + g).convergenceRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨hrf, hrg⟩ := lt_min_iff.mp hr
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp hrf
  obtain ⟨hsf, hrx⟩ := lt_iSup_iff.mp hx
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp hrg
  obtain ⟨hsg, hry⟩ := lt_iSup_iff.mp hy
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · have hsg' := (isRestricted_of_summable_smul_pow hsg).summable_smul_pow hxy
    have hadd : Summable fun n ↦ coeff n (f + g) • x ^ n := by
      simpa only [map_add, add_smul] using hsf.add hsg'
    exact hrx.le.trans (le_convergenceRadius_of_summable hadd)
  · have hsf' := (isRestricted_of_summable_smul_pow hsf).summable_smul_pow hyx
    have hadd : Summable fun n ↦ coeff n (f + g) • y ^ n := by
      simpa only [map_add, add_smul] using hsf'.add hsg
    exact hry.le.trans (le_convergenceRadius_of_summable hadd)

/-- Over an ultrametric normed coefficient ring and in a complete ultrametric target, the
convergence-point radius of a product is at least the minimum of the two convergence-point
radii. -/
theorem min_convergenceRadius_le_convergenceRadius_mul [IsUltrametricDist R] (f g : R⟦X⟧) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ (f * g).convergenceRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨hrf, hrg⟩ := lt_min_iff.mp hr
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp hrf
  obtain ⟨hsf, hrx⟩ := lt_iSup_iff.mp hx
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp hrg
  obtain ⟨hsg, hry⟩ := lt_iSup_iff.mp hy
  have hrf' := isRestricted_of_summable_smul_pow hsf
  have hrg' := isRestricted_of_summable_smul_pow hsg
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · have hg_x :=
      TauCeti.PowerSeries.isRestricted_of_abs_le (c := ‖x‖) hrg' (by simpa [abs_norm] using hxy)
    have hmul : (f * g).IsRestricted ‖x‖ := hrf'.mul hg_x
    exact hrx.le.trans (le_convergenceRadius_of_summable (hmul.summable_smul_pow le_rfl))
  · have hf_y :=
      TauCeti.PowerSeries.isRestricted_of_abs_le (c := ‖y‖) hrf' (by simpa [abs_norm] using hyx)
    have hmul : (f * g).IsRestricted ‖y‖ := hf_y.mul hrg'
    exact hry.le.trans (le_convergenceRadius_of_summable (hmul.summable_smul_pow le_rfl))

end UltrametricConvergenceRadius

end ConvergenceRadius

end PowerSeries
