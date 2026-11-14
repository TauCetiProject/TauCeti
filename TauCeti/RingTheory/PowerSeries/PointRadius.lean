/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval
public import TauCeti.RingTheory.PowerSeries.Radius
import TauCeti.Analysis.Normed.Field.Basic

/-!
# Convergence of power series in extensions and the point-convergence radius

Let `f = ∑ aₙ Xⁿ` be a power series over a normed ring `R`, and let `A` be a seminormed ring on
which `R` acts with multiplicative scalar and power norms (`NormSMulClass R A` and
`NormMulClass A`), such as a normed field extension `L / K` or a normed division algebra. For
`n ≥ 1`, the individual term at `x : A` has norm `‖aₙ • xⁿ‖ = ‖aₙ‖ ‖x‖ⁿ`. Consequently the terms
`aₙ • xⁿ` tend to zero if and only if `f` is restricted at the numerical radius `‖x‖`, without any
completeness or ultrametric hypothesis
(`PowerSeries.tendsto_coeff_smul_pow_zero_iff_isRestricted`). In particular, summability of
`∑ aₙ • xⁿ` at `x` always forces `f.IsRestricted ‖x‖` and hence `‖x‖ₑ ≤ f.radius`
(`PowerSeries.isRestricted_norm_of_summable`, `PowerSeries.le_radius_of_summable`), and summability
throughout a closed ball `{y : A | ‖y‖ ≤ r}` implies `f.IsRestricted r` whenever `r` is attained
by the norm of a point of `A` (`PowerSeries.isRestricted_of_forall_norm_le_summable`).

When `A` is complete and ultrametric, a series in `A` is summable if and only if its terms tend to
zero, so convergence at `x` is *equivalent* to `f.IsRestricted ‖x‖`
(`PowerSeries.summable_coeff_smul_pow_iff_isRestricted`). Convergence at a single point `x`
therefore implies convergence to `f.evalAt y` and the Gauss-norm bound
`‖f.evalAt y‖ ≤ gaussNorm norm ‖x‖ f` throughout the closed disc `‖y‖ ≤ ‖x‖`.

The *point-convergence radius* `PowerSeries.pointRadius f A` is the supremum in `ℝ≥0∞` of `‖x‖ₑ`
over the convergence points `x : A` of `f`. Unlike the intrinsic coefficient radius
`PowerSeries.radius f`, it depends on the value group of `A`:

* `f.pointRadius A ≤ f.radius` always holds (`PowerSeries.pointRadius_le_radius`).
* When `A` is complete and its positive norms are dense in `(0, ∞)` (for instance when `A` is a
  complete `DenselyNormedField` such as `ℝ`, `ℂ`, or `ℂ_[p]`), `f.pointRadius A = f.radius`
  (`PowerSeries.pointRadius_eq_radius_of_forall_exists_lt_norm_lt`,
  `PowerSeries.pointRadius_eq_radius`), even without an ultrametric hypothesis.
* When the nonzero norms of `A` form a discrete group `{b ^ m | m : ℤ}` (`b > 1`) and `f.radius`
  lies strictly between consecutive powers `b ^ k` and `b ^ (k + 1)`, the supremum drops to
  `b ^ k < f.radius` (`PowerSeries.pointRadius_eq_ofReal_zpow_of_lt_radius_lt`).

## Main definitions

* `PowerSeries.pointRadius f A`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over `x : A` for which
  `∑ₙ coeff n f • x ^ n` is summable.

## Main results

* `PowerSeries.tendsto_coeff_smul_pow_zero_iff_isRestricted`: `coeff n f • x ^ n → 0` if and only
  if `f.IsRestricted ‖x‖`.
* `PowerSeries.isRestricted_norm_of_summable` and `PowerSeries.le_radius_of_summable`: convergence
  at `x` implies `f.IsRestricted ‖x‖` and `‖x‖ₑ ≤ f.radius`.
* `PowerSeries.summable_coeff_smul_pow_iff_isRestricted`: in a complete ultrametric target,
  convergence at `x` is equivalent to `f.IsRestricted ‖x‖`.
* `PowerSeries.forall_norm_le_summable_iff_isRestricted` and
  `PowerSeries.forall_norm_le_hasSum_evalAt_iff_isRestricted`: closed-disc characterizations when
  the radius is attained by a norm.
* `PowerSeries.norm_evalAt_le_gaussNorm_of_isRestricted`,
  `PowerSeries.hasSum_evalAt_of_summable_of_norm_le`, and
  `PowerSeries.norm_evalAt_le_gaussNorm_of_summable_of_norm_le`: closed-disc convergence and
  Gauss-norm bound deduced from restrictedness or convergence at one boundary point.
* `PowerSeries.pointRadius_le_radius`: `f.pointRadius A ≤ f.radius`.
* `PowerSeries.pointRadius_eq_radius_of_forall_exists_lt_norm_lt`,
  `PowerSeries.pointRadius_eq_radius_of_Ioi_subset_closure`, and
  `PowerSeries.pointRadius_eq_radius`: equality when `A` is complete and its positive norms are
  dense in `(0, ∞)`.
* `PowerSeries.pointRadius_eq_ofReal_zpow_of_lt_radius_lt` and
  `PowerSeries.pointRadius_eq_one_of_one_lt_radius_lt`: exact value and strict inequality for
  discretely normed targets when `f.radius` lies strictly between consecutive value-group powers.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV, §§1, 4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 6, §1.
-/

public section

namespace PowerSeries

open Filter
open scoped NNReal ENNReal Topology

section Terms

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMul R A] [NormSMulClass R A]
  [NormMulClass A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- Multiplicativity of the norm gives `‖x ^ (n + 1)‖ = ‖x‖ ^ (n + 1)` without assuming
`NormOneClass A`. -/
private theorem norm_pow_succ (x : A) (n : ℕ) : ‖x ^ (n + 1)‖ = ‖x‖ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ x (n + 1), norm_mul, ih, ← pow_succ]

/-- For `n ≥ 1`, the norm of `coeff n f • x ^ n` is `‖coeff n f‖ * ‖x‖ ^ n`. -/
theorem norm_coeff_smul_pow_succ (f : R⟦X⟧) (x : A) (n : ℕ) :
    ‖coeff (n + 1) f • x ^ (n + 1)‖ = ‖coeff (n + 1) f‖ * ‖x‖ ^ (n + 1) := by
  rw [norm_smul, norm_pow_succ]

/-- The terms `coeff n f • x ^ n` tend to zero if and only if `f` is restricted at `‖x‖`. -/
theorem tendsto_coeff_smul_pow_zero_iff_isRestricted :
    Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0) ↔ f.IsRestricted ‖x‖ := by
  rw [tendsto_zero_iff_norm_tendsto_zero, ← tendsto_add_atTop_iff_nat 1, isRestricted_iff']
  simp only [norm_coeff_smul_pow_succ]
  exact tendsto_add_atTop_iff_nat (f := fun t ↦ ‖coeff t f‖ * ‖x‖ ^ t) 1

/-- At a point `x` of norm `r`, the terms `coeff n f • x ^ n` tend to zero if and only if `f` is
restricted at `r`. -/
theorem tendsto_coeff_smul_pow_zero_iff_isRestricted_of_norm_eq (hr : ‖x‖ = r) :
    Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0) ↔ f.IsRestricted r :=
  hr ▸ tendsto_coeff_smul_pow_zero_iff_isRestricted

end Terms

section Necessary

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMul R A] [NormSMulClass R A]
  [NormMulClass A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- If `∑ₙ coeff n f • x ^ n` is summable, then `f` is restricted at `‖x‖`. Neither completeness
nor an ultrametric norm is required. -/
theorem isRestricted_norm_of_summable (h : Summable fun n ↦ coeff n f • x ^ n) :
    f.IsRestricted ‖x‖ :=
  tendsto_coeff_smul_pow_zero_iff_isRestricted.mp h.tendsto_atTop_zero

/-- If `∑ₙ coeff n f • x ^ n` is summable at a point `x` of norm `r`, then `f` is restricted at
`r`. -/
theorem isRestricted_of_summable_of_norm_eq (h : Summable fun n ↦ coeff n f • x ^ n)
    (hr : ‖x‖ = r) : f.IsRestricted r :=
  hr ▸ isRestricted_norm_of_summable h

/-- Any convergence point `x` of `f` has extended norm at most `f.radius`. -/
theorem le_radius_of_summable (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.radius := by
  simpa only [eNorm_norm] using le_radius_of_isRestricted (isRestricted_norm_of_summable h)

/-- `f` does not converge at any point `x` with `f.radius < ‖x‖ₑ`. -/
theorem not_summable_of_radius_lt (h : f.radius < ‖x‖ₑ) :
    ¬Summable fun n ↦ coeff n f • x ^ n :=
  fun hs ↦ (le_radius_of_summable hs).not_gt h

/-- Convergence on all points of norm at most `r` implies `f.IsRestricted r` whenever `r` is
attained by the norm of a point. -/
theorem isRestricted_of_forall_norm_le_summable (hx : ∃ x : A, ‖x‖ = r)
    (h : ∀ y : A, ‖y‖ ≤ r → Summable fun n ↦ coeff n f • y ^ n) : f.IsRestricted r := by
  obtain ⟨x, rfl⟩ := hx
  exact isRestricted_norm_of_summable (h x le_rfl)

/-- Convergence throughout `Metric.closedBall 0 r` implies `f.IsRestricted r` whenever `r` is
attained by the norm of a point. -/
theorem isRestricted_of_forall_mem_closedBall_summable (hx : ∃ x : A, ‖x‖ = r)
    (h : ∀ y ∈ Metric.closedBall (0 : A) r, Summable fun n ↦ coeff n f • y ^ n) :
    f.IsRestricted r :=
  isRestricted_of_forall_norm_le_summable hx fun y hy ↦ h y (mem_closedBall_zero_iff.mpr hy)

end Necessary

section Ultrametric

/-- In a complete ultrametric seminormed target with bounded scalar action, a series `f` restricted
at `r` has summable terms `coeff n f • x ^ n` at every `x` with `‖x‖ ≤ r`. -/
theorem IsRestricted.summable_coeff_smul_pow {R A : Type*} [NormedRing R] [SeminormedRing A]
    [IsUltrametricDist A] [CompleteSpace A] [SMulZeroClass R A] [IsBoundedSMul R A] {f : R⟦X⟧}
    {r : ℝ} (hf : f.IsRestricted r) {x : A} (hx : ‖x‖ ≤ r) :
    Summable fun n ↦ coeff n f • x ^ n := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm' ?_ ((isRestricted_iff' r f).mp hf)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (norm_smul_le _ _).trans <| mul_le_mul_of_nonneg_left
    ((norm_pow_le' x hn).trans (pow_le_pow_left₀ (norm_nonneg x) hx n)) (norm_nonneg _)

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [IsUltrametricDist A] [CompleteSpace A]
  [Module R A] [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- **Pointwise convergence characterization.** In a complete ultrametric target with
multiplicative scalar and power norms, `∑ₙ coeff n f • x ^ n` converges if and only if `f` is
restricted at `‖x‖`. -/
theorem summable_coeff_smul_pow_iff_isRestricted :
    Summable (fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted ‖x‖ := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    tendsto_coeff_smul_pow_zero_iff_isRestricted]

/-- At a point `x` of norm `r` in a complete ultrametric target, `∑ₙ coeff n f • x ^ n` converges
if and only if `f` is restricted at `r`. -/
theorem summable_coeff_smul_pow_iff_isRestricted_of_norm_eq (hr : ‖x‖ = r) :
    Summable (fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted r :=
  hr ▸ summable_coeff_smul_pow_iff_isRestricted

/-- **Closed-disc convergence characterization.** When `r` is attained by the norm of a point of
`A`, `f` converges at every point of norm at most `r` if and only if `f.IsRestricted r`. -/
theorem forall_norm_le_summable_iff_isRestricted (hx : ∃ x : A, ‖x‖ = r) :
    (∀ y : A, ‖y‖ ≤ r → Summable fun n ↦ coeff n f • y ^ n) ↔ f.IsRestricted r :=
  ⟨isRestricted_of_forall_norm_le_summable hx, fun hf _ hy ↦ hf.summable_coeff_smul_pow hy⟩

/-- When `r` is attained by the norm of a point of `A`, `f` converges throughout
`Metric.closedBall 0 r` if and only if `f.IsRestricted r`. -/
theorem forall_mem_closedBall_summable_iff_isRestricted (hx : ∃ x : A, ‖x‖ = r) :
    (∀ y ∈ Metric.closedBall (0 : A) r, Summable fun n ↦ coeff n f • y ^ n) ↔ f.IsRestricted r := by
  simpa only [mem_closedBall_zero_iff] using forall_norm_le_summable_iff_isRestricted hx

end Ultrametric

section UltrametricEval

/-- In an ultrametric normed algebra with `‖1‖ = 1`, a series `f` restricted at `r` satisfies the
Gauss-norm bound `‖f.evalAt b‖ ≤ gaussNorm norm r f` on the closed disc `‖b‖ ≤ r`. -/
theorem norm_evalAt_le_gaussNorm_of_isRestricted {R A : Type*} [NormedCommRing R] [NormedRing A]
    [Algebra R A] [IsBoundedSMul R A] [IsUltrametricDist A] [NormOneClass A] {f : R⟦X⟧} {r : ℝ}
    (hf : f.IsRestricted r) {b : A} (hb : ‖b‖ ≤ r) :
    ‖f.evalAt b‖ ≤ gaussNorm norm r f :=
  norm_evalAt_le_gaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf) hb

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [IsUltrametricDist A] [CompleteSpace A]
  [Algebra R A] [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {x y : A} {r : ℝ}

/-- In a complete ultrametric algebra with multiplicative scalar and power norms, convergence at a
single point `x` gives convergence to `f.evalAt y` at every `y` in the closed disc `‖y‖ ≤ ‖x‖`. -/
theorem hasSum_evalAt_of_summable_of_norm_le (hx : Summable fun n ↦ coeff n f • x ^ n)
    (hy : ‖y‖ ≤ ‖x‖) : HasSum (fun n ↦ coeff n f • y ^ n) (f.evalAt y) :=
  (isRestricted_norm_of_summable hx).hasSum_evalAt hy

omit [CompleteSpace A] in
/-- In an ultrametric algebra with `‖1‖ = 1` and multiplicative scalar and power norms,
convergence at `x` bounds `‖f.evalAt y‖` by `gaussNorm norm ‖x‖ f` for every `y` with
`‖y‖ ≤ ‖x‖`. -/
theorem norm_evalAt_le_gaussNorm_of_summable_of_norm_le [NormOneClass A]
    (hx : Summable fun n ↦ coeff n f • x ^ n) (hy : ‖y‖ ≤ ‖x‖) :
    ‖f.evalAt y‖ ≤ gaussNorm norm ‖x‖ f :=
  norm_evalAt_le_gaussNorm_of_isRestricted (isRestricted_norm_of_summable hx) hy

/-- When `r` is attained by the norm of a point of `A`, `∑ₙ coeff n f • y ^ n` sums to `f.evalAt y`
throughout `‖y‖ ≤ r` if and only if `f.IsRestricted r`. -/
theorem forall_norm_le_hasSum_evalAt_iff_isRestricted (hx : ∃ x : A, ‖x‖ = r) :
    (∀ y : A, ‖y‖ ≤ r → HasSum (fun n ↦ coeff n f • y ^ n) (f.evalAt y)) ↔ f.IsRestricted r :=
  ⟨fun h ↦ isRestricted_of_forall_norm_le_summable hx fun y hy ↦ (h y hy).summable,
    fun hf _ hy ↦ hf.hasSum_evalAt hy⟩

end UltrametricEval

section PointRadiusDef

variable {R : Type*} [Semiring R]

/-- The *point-convergence radius* of a power series `f = ∑ aₙ Xⁿ` in `A`: the supremum in `ℝ≥0∞`
of the extended norms `‖x‖ₑ` of points `x : A` at which `∑ₙ aₙ • xⁿ` is summable. Unlike
`PowerSeries.radius`, this quantity depends on the norms attained in `A`. -/
noncomputable def pointRadius (f : R⟦X⟧) (A : Type*) [SeminormedRing A] [SMul R A] : ℝ≥0∞ :=
  ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ

/-- Explicit `iSup` formula for `PowerSeries.pointRadius`. -/
theorem pointRadius_def (f : R⟦X⟧) (A : Type*) [SeminormedRing A] [SMul R A] :
    f.pointRadius A = ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ :=
  (rfl)

/-- Every convergence point `x : A` of `f` satisfies `‖x‖ₑ ≤ f.pointRadius A`. -/
theorem le_pointRadius_of_summable {A : Type*} [SeminormedRing A] [SMul R A] {f : R⟦X⟧} {x : A}
    (h : Summable fun n ↦ coeff n f • x ^ n) : ‖x‖ₑ ≤ f.pointRadius A :=
  le_iSup₂ (f := fun (y : A) (_ : Summable fun n ↦ coeff n f • y ^ n) ↦ ‖y‖ₑ) x h

/-- `f` diverges at every point `x : A` with `f.pointRadius A < ‖x‖ₑ`. -/
theorem not_summable_of_pointRadius_lt {A : Type*} [SeminormedRing A] [SMul R A] {f : R⟦X⟧}
    {x : A} (h : f.pointRadius A < ‖x‖ₑ) : ¬Summable fun n ↦ coeff n f • x ^ n :=
  fun hs ↦ (le_pointRadius_of_summable hs).not_gt h

/-- Every power series converges at `0 : A`. -/
theorem summable_coeff_smul_zero_pow {A : Type*} [SeminormedRing A] [SMulZeroClass R A]
    (f : R⟦X⟧) : Summable fun n ↦ coeff n f • (0 : A) ^ n :=
  summable_of_ne_finset_zero (s := {0}) fun n hn ↦ by
    rw [zero_pow (Finset.notMem_singleton.mp hn), smul_zero]

/-- Every polynomial converges at every point of `A`. -/
theorem summable_coeff_coe_smul_pow {A : Type*} [SeminormedRing A] [Module R A]
    (p : Polynomial R) (x : A) : Summable fun n ↦ coeff n (p : R⟦X⟧) • x ^ n :=
  summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn ↦ by
    rw [Finset.mem_range, not_lt] at hn
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- A polynomial converges everywhere on `A`, so its point-convergence radius is `⨆ x : A, ‖x‖ₑ`. -/
theorem pointRadius_coe_eq_iSup (p : Polynomial R) (A : Type*) [SeminormedRing A] [Module R A] :
    (p : R⟦X⟧).pointRadius A = ⨆ x : A, ‖x‖ₑ := by
  rw [pointRadius_def]
  exact iSup_congr fun x ↦ ciSup_pos (summable_coeff_coe_smul_pow p x)

/-- The point-convergence radius of `0` in `A` is `⨆ x : A, ‖x‖ₑ`. -/
theorem pointRadius_zero_eq_iSup (A : Type*) [SeminormedRing A] [Module R A] :
    (0 : R⟦X⟧).pointRadius A = ⨆ x : A, ‖x‖ₑ := by
  simpa using pointRadius_coe_eq_iSup (0 : Polynomial R) A

/-- The point-convergence radius of a constant series `C a` in `A` is `⨆ x : A, ‖x‖ₑ`. -/
theorem pointRadius_C_eq_iSup (a : R) (A : Type*) [SeminormedRing A] [Module R A] :
    (C a : R⟦X⟧).pointRadius A = ⨆ x : A, ‖x‖ₑ := by
  simpa using pointRadius_coe_eq_iSup (Polynomial.C a) A

/-- The point-convergence radius of a monomial `monomial n a` in `A` is `⨆ x : A, ‖x‖ₑ`. -/
theorem pointRadius_monomial_eq_iSup (n : ℕ) (a : R) (A : Type*) [SeminormedRing A]
    [Module R A] :
    (monomial n a : R⟦X⟧).pointRadius A = ⨆ x : A, ‖x‖ₑ := by
  simpa using pointRadius_coe_eq_iSup (Polynomial.monomial n a) A

/-- Over a nontrivially normed field `L`, the supremum of all extended norms is `⊤`. -/
private theorem iSup_eNorm_eq_top (L : Type*) [NontriviallyNormedField L] :
    (⨆ x : L, ‖x‖ₑ) = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm L r
  exact (ENNReal.ofReal_coe_nnreal ▸ ENNReal.ofReal_le_ofReal hx.le).trans
    (ofReal_norm x ▸ le_iSup (fun y : L ↦ ‖y‖ₑ) x)

/-- Over a nontrivially normed field `L`, polynomials have infinite point-convergence radius. -/
@[simp]
theorem pointRadius_coe (p : Polynomial R) (L : Type*) [NontriviallyNormedField L] [Module R L] :
    (p : R⟦X⟧).pointRadius L = ⊤ := by
  rw [pointRadius_coe_eq_iSup, iSup_eNorm_eq_top]

/-- Over a nontrivially normed field `L`, the zero series has infinite point-convergence radius. -/
@[simp]
theorem pointRadius_zero (L : Type*) [NontriviallyNormedField L] [Module R L] :
    (0 : R⟦X⟧).pointRadius L = ⊤ := by
  simpa using pointRadius_coe (0 : Polynomial R) L

/-- Over a nontrivially normed field `L`, constant series have infinite point-convergence
radius. -/
@[simp]
theorem pointRadius_C (a : R) (L : Type*) [NontriviallyNormedField L] [Module R L] :
    (C a : R⟦X⟧).pointRadius L = ⊤ := by
  simpa using pointRadius_coe (Polynomial.C a) L

/-- Over a nontrivially normed field `L`, `1` has infinite point-convergence radius. -/
@[simp]
theorem pointRadius_one (L : Type*) [NontriviallyNormedField L] [Module R L] :
    (1 : R⟦X⟧).pointRadius L = ⊤ := by
  simpa using pointRadius_coe (1 : Polynomial R) L

/-- Over a nontrivially normed field `L`, monomials have infinite point-convergence radius. -/
@[simp]
theorem pointRadius_monomial (n : ℕ) (a : R) (L : Type*) [NontriviallyNormedField L]
    [Module R L] :
    (monomial n a : R⟦X⟧).pointRadius L = ⊤ := by
  simpa using pointRadius_coe (Polynomial.monomial n a) L

/-- Over a nontrivially normed field `L`, `X` has infinite point-convergence radius. -/
@[simp]
theorem pointRadius_X (L : Type*) [NontriviallyNormedField L] [Module R L] :
    (X : R⟦X⟧).pointRadius L = ⊤ := by
  simpa using pointRadius_coe (Polynomial.X : Polynomial R) L

/-- Extension of scalars along `algebraMap R S` preserves the point-convergence radius in any
`S`-algebra `A`. -/
@[simp]
theorem pointRadius_map_algebraMap {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (f : R⟦X⟧) (A : Type*) [SeminormedRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] :
    (f.map (algebraMap R S)).pointRadius A = f.pointRadius A := by
  simp [pointRadius_def]

end PointRadiusDef

section EntirePointRadius

/-- An entire series converges everywhere in any complete seminormed target `A` with a bounded
scalar action, so its point-convergence radius in `A` is `⨆ x : A, ‖x‖ₑ`. -/
theorem IsEntire.pointRadius_eq_iSup {R : Type*} [NormedRing R] {f : R⟦X⟧} (hf : f.IsEntire)
    (A : Type*) [SeminormedRing A] [CompleteSpace A] [SMulZeroClass R A] [IsBoundedSMul R A] :
    f.pointRadius A = ⨆ x : A, ‖x‖ₑ := by
  have hs (x : A) : Summable fun n ↦ coeff n f • x ^ n :=
    ((hf.onOpenDisc (‖x‖ + 1)).summable_norm_smul_pow (lt_add_one ‖x‖)).of_norm
  simp [pointRadius_def, hs]

/-- An entire series converges everywhere in any complete nontrivially normed field `L` with a
bounded scalar action, so its point-convergence radius in `L` is `⊤`. -/
theorem IsEntire.pointRadius_eq_top {R : Type*} [NormedRing R] {f : R⟦X⟧} (hf : f.IsEntire)
    (L : Type*) [NontriviallyNormedField L] [CompleteSpace L] [SMulZeroClass R L]
    [IsBoundedSMul R L] :
    f.pointRadius L = ⊤ := by
  rw [hf.pointRadius_eq_iSup, iSup_eNorm_eq_top]

end EntirePointRadius

section PointRadiusUltrametric

/-- Any radius strictly below `f.pointRadius A` is a radius of restrictedness of `f`. -/
theorem isRestricted_of_lt_pointRadius {R A : Type*} [NormedRing R] [SeminormedRing A] [SMul R A]
    [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {r : ℝ} (h : ‖r‖ₑ < f.pointRadius A) :
    f.IsRestricted r := by
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp h
  obtain ⟨hs, hrx⟩ := lt_iSup_iff.mp hx
  rw [eNorm_eq_nnNorm, eNorm_eq_nnNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm,
    coe_nnNorm, Real.norm_eq_abs] at hrx
  exact TauCeti.PowerSeries.isRestricted_of_abs_le (isRestricted_norm_of_summable hs)
    (hrx.le.trans (le_abs_self _))

variable {R S A : Type*} [NormedRing R] [NormedRing S] [SeminormedRing A] [IsUltrametricDist A]
  [CompleteSpace A] [Module R A] [Module S A] [NormSMulClass R A] [NormSMulClass S A]
  [NormMulClass A] {f g : R⟦X⟧}

/-- In a complete ultrametric target, `f` converges at every point `x : A` with
`‖x‖ₑ < f.pointRadius A`. -/
theorem summable_of_lt_pointRadius {x : A} (hx : ‖x‖ₑ < f.pointRadius A) :
    Summable fun n ↦ coeff n f • x ^ n :=
  summable_coeff_smul_pow_iff_isRestricted.mpr
    (isRestricted_of_lt_pointRadius (by simpa only [eNorm_norm] using hx))

/-- In a complete ultrametric normed algebra, `∑ₙ coeff n f • x ^ n` sums to `f.evalAt x` at every
point `x` with `‖x‖ₑ < f.pointRadius A`. -/
theorem hasSum_evalAt_of_lt_pointRadius {R A : Type*} [NormedCommRing R] [NormedRing A]
    [IsUltrametricDist A] [CompleteSpace A] [Algebra R A] [NormSMulClass R A] [NormMulClass A]
    {f : R⟦X⟧} {x : A} (hx : ‖x‖ₑ < f.pointRadius A) :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) :=
  (isRestricted_of_lt_pointRadius (r := ‖x‖) (by simpa only [eNorm_norm] using hx)).hasSum_evalAt
    le_rfl

/-- If the coefficients of `h` are no larger in norm than those of `f`, then in a complete
ultrametric target `f.pointRadius A ≤ h.pointRadius A`. -/
theorem pointRadius_le_pointRadius_of_norm_coeff_le {h : S⟦X⟧}
    (hle : ∀ n, ‖coeff n h‖ ≤ ‖coeff n f‖) :
    f.pointRadius A ≤ h.pointRadius A := by
  refine iSup₂_le fun x hx ↦ le_pointRadius_of_summable ?_
  rw [summable_coeff_smul_pow_iff_isRestricted] at hx ⊢
  rw [isRestricted_iff'] at hx ⊢
  exact squeeze_zero (fun n ↦ by positivity)
    (fun n ↦ mul_le_mul_of_nonneg_right (hle n) (pow_nonneg (norm_nonneg x) n)) hx

/-- Isometric coefficient ring homomorphisms preserve the point-convergence radius in any complete
ultrametric target. -/
theorem pointRadius_map (φ : R →+* S) (hφ : ∀ a, ‖φ a‖ = ‖a‖) :
    (f.map φ).pointRadius A = f.pointRadius A :=
  le_antisymm (pointRadius_le_pointRadius_of_norm_coeff_le fun n ↦ by simp [hφ])
    (pointRadius_le_pointRadius_of_norm_coeff_le fun n ↦ by simp [hφ])

/-- In a complete ultrametric target, the point-convergence radius of a sum is at least the minimum
of the two point-convergence radii. -/
theorem min_pointRadius_le_pointRadius_add (f g : R⟦X⟧) (A : Type*) [SeminormedRing A]
    [IsUltrametricDist A] [CompleteSpace A] [Module R A] [NormSMulClass R A] [NormMulClass A] :
    min (f.pointRadius A) (g.pointRadius A) ≤ (f + g).pointRadius A := by
  refine le_of_forall_lt fun c hc ↦ ?_
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp (lt_min_iff.mp hc).1
  obtain ⟨hfx, hcx⟩ := lt_iSup_iff.mp hx
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp (lt_min_iff.mp hc).2
  obtain ⟨hgy, hcy⟩ := lt_iSup_iff.mp hy
  by_cases hxy : ‖x‖ ≤ ‖y‖
  · have hgx : Summable fun n ↦ coeff n g • x ^ n :=
      summable_coeff_smul_pow_iff_isRestricted.mpr
        (TauCeti.PowerSeries.isRestricted_of_abs_le (isRestricted_norm_of_summable hgy)
          (by simpa only [abs_norm] using hxy))
    have hfg : Summable fun n ↦ coeff n (f + g) • x ^ n := by
      simpa only [map_add, add_smul] using hfx.add hgx
    exact hcx.trans_le (le_pointRadius_of_summable hfg)
  · have hyx : ‖y‖ ≤ ‖x‖ := le_of_not_ge hxy
    have hfy : Summable fun n ↦ coeff n f • y ^ n :=
      summable_coeff_smul_pow_iff_isRestricted.mpr
        (TauCeti.PowerSeries.isRestricted_of_abs_le (isRestricted_norm_of_summable hfx)
          (by simpa only [abs_norm] using hyx))
    have hfg : Summable fun n ↦ coeff n (f + g) • y ^ n := by
      simpa only [map_add, add_smul] using hfy.add hgy
    exact hcy.trans_le (le_pointRadius_of_summable hfg)

/-- Over an ultrametric coefficient ring, the point-convergence radius of a product in a complete
ultrametric target is at least the minimum of the two point-convergence radii. -/
theorem min_pointRadius_le_pointRadius_mul [IsUltrametricDist R] (f g : R⟦X⟧) (A : Type*)
    [SeminormedRing A] [IsUltrametricDist A] [CompleteSpace A] [Module R A] [NormSMulClass R A]
    [NormMulClass A] :
    min (f.pointRadius A) (g.pointRadius A) ≤ (f * g).pointRadius A := by
  refine le_of_forall_lt fun c hc ↦ ?_
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp (lt_min_iff.mp hc).1
  obtain ⟨hfx, hcx⟩ := lt_iSup_iff.mp hx
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp (lt_min_iff.mp hc).2
  obtain ⟨hgy, hcy⟩ := lt_iSup_iff.mp hy
  by_cases hxy : ‖x‖ ≤ ‖y‖
  · have hgx : g.IsRestricted ‖x‖ :=
      TauCeti.PowerSeries.isRestricted_of_abs_le (isRestricted_norm_of_summable hgy)
        (by simpa only [abs_norm] using hxy)
    have hfg : Summable fun n ↦ coeff n (f * g) • x ^ n :=
      summable_coeff_smul_pow_iff_isRestricted.mpr ((isRestricted_norm_of_summable hfx).mul hgx)
    exact hcx.trans_le (le_pointRadius_of_summable hfg)
  · have hyx : ‖y‖ ≤ ‖x‖ := le_of_not_ge hxy
    have hfy : f.IsRestricted ‖y‖ :=
      TauCeti.PowerSeries.isRestricted_of_abs_le (isRestricted_norm_of_summable hfx)
        (by simpa only [abs_norm] using hyx)
    have hfg : Summable fun n ↦ coeff n (f * g) • y ^ n :=
      summable_coeff_smul_pow_iff_isRestricted.mpr (hfy.mul (isRestricted_norm_of_summable hgy))
    exact hcy.trans_le (le_pointRadius_of_summable hfg)

end PointRadiusUltrametric

section ComparisonWithRadius

/-- **Comparison with the intrinsic radius.** The point-convergence radius of `f` in `A` never
exceeds the intrinsic coefficient radius `f.radius`. Neither completeness nor an ultrametric norm
is needed. -/
theorem pointRadius_le_radius {R : Type*} [NormedRing R] (f : R⟦X⟧) (A : Type*)
    [SeminormedRing A] [SMul R A] [NormSMulClass R A] [NormMulClass A] :
    f.pointRadius A ≤ f.radius :=
  iSup₂_le fun _ hx ↦ le_radius_of_summable hx

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [Module R A] [NormSMulClass R A]
  [NormMulClass A]

/-- **Equality when positive norms separate positive open intervals.** If `A` is complete and every
interval `(r₁, r₂)` with `0 < r₁ < r₂` contains the norm of an element of `A`, then
`f.pointRadius A = f.radius`. No ultrametric hypothesis is needed: strictly inside `f.radius`, the
terms are geometrically dominated and hence absolutely summable. -/
theorem pointRadius_eq_radius_of_forall_exists_lt_norm_lt [CompleteSpace A]
    (hdense : ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → ∃ x : A, r₁ < ‖x‖ ∧ ‖x‖ < r₂) (f : R⟦X⟧) :
    f.pointRadius A = f.radius := by
  refine le_antisymm (f.pointRadius_le_radius A) (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
  rcases eq_or_ne r 0 with rfl | hr₀
  · simp
  have hr_pos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr₀)
  obtain ⟨t, hrt, htR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have hrt' : (r : ℝ) < (t : ℝ) := by exact_mod_cast hrt
  obtain ⟨x, hrx, hxt⟩ := hdense r t hr_pos hrt'
  have hft : f.IsRestricted (t : ℝ) := isRestricted_of_lt_radius (by simpa using htR)
  have hs : Summable fun n ↦ coeff n f • x ^ n :=
    (hft.onOpenDisc.summable_norm_smul_pow hxt).of_norm
  exact (ENNReal.ofReal_coe_nnreal ▸ ENNReal.ofReal_le_ofReal hrx.le).trans
    (ofReal_norm x ▸ le_pointRadius_of_summable hs)

/-- **Equality when positive norms are dense in `(0, ∞)`.** If `A` is complete and
`Set.Ioi (0 : ℝ) ⊆ closure ((‖·‖) '' {x : A | 0 < ‖x‖})`, then `f.pointRadius A = f.radius`. -/
theorem pointRadius_eq_radius_of_Ioi_subset_closure [CompleteSpace A]
    (hdense : Set.Ioi (0 : ℝ) ⊆ closure ((‖·‖) '' {x : A | 0 < ‖x‖})) (f : R⟦X⟧) :
    f.pointRadius A = f.radius :=
  pointRadius_eq_radius_of_forall_exists_lt_norm_lt
    (NormedField.forall_exists_lt_norm_lt_iff_Ioi_subset_closure.mpr hdense) f

/-- In any complete densely normed field `L` (such as `ℝ`, `ℂ`, or `ℂ_[p]`), the point-convergence
radius of `f` equals its intrinsic radius `f.radius`. -/
@[simp]
theorem pointRadius_eq_radius (f : R⟦X⟧) (L : Type*) [DenselyNormedField L] [CompleteSpace L]
    [Module R L] [NormSMulClass R L] :
    f.pointRadius L = f.radius :=
  pointRadius_eq_radius_of_forall_exists_lt_norm_lt
    (fun _ _ hr₁ ↦ NormedField.exists_lt_norm_lt L hr₁.le) f

/-- In any complete algebraically closed nontrivially normed field `L`, the point-convergence
radius of `f` equals its intrinsic radius `f.radius`. -/
theorem pointRadius_eq_radius_of_isAlgClosed (f : R⟦X⟧) (L : Type*) [NontriviallyNormedField L]
    [IsAlgClosed L] [CompleteSpace L] [Module R L] [NormSMulClass R L] :
    f.pointRadius L = f.radius :=
  pointRadius_eq_radius_of_forall_exists_lt_norm_lt
    (fun _ _ hr₁ ↦ NormedField.exists_lt_norm_lt_of_isAlgClosed L hr₁.le) f

end ComparisonWithRadius

section DiscreteValueGroup

/-- If every nonzero norm in `A` is an integer power of `b > 1` and `f.radius < b ^ (k + 1)`, then
every convergence point of `f` in `A` has norm at most `b ^ k`, so
`f.pointRadius A ≤ ENNReal.ofReal (b ^ k)`. -/
theorem pointRadius_le_ofReal_zpow_of_radius_lt {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMul R A] [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {b : ℝ} {k : ℤ} (hb : 1 < b)
    (hval : ∀ x : A, ‖x‖ ≠ 0 → ∃ m : ℤ, ‖x‖ = b ^ m)
    (hhi : f.radius < ENNReal.ofReal (b ^ (k + 1))) :
    f.pointRadius A ≤ ENNReal.ofReal (b ^ k) := by
  refine iSup₂_le fun x hx ↦ ?_
  rw [← ofReal_norm]
  rcases eq_or_ne ‖x‖ 0 with hx₀ | hx₀
  · simp [hx₀]
  obtain ⟨m, hm⟩ := hval x hx₀
  have hmk : m ≤ k := by
    by_contra! hkm
    have hpow : b ^ (k + 1) ≤ ‖x‖ := hm ▸ zpow_le_zpow_right₀ hb.le hkm
    have hle : ENNReal.ofReal (b ^ (k + 1)) ≤ f.radius :=
      (ENNReal.ofReal_le_ofReal hpow).trans (ofReal_norm x ▸ le_radius_of_summable hx)
    exact hle.not_gt hhi
  exact ENNReal.ofReal_le_ofReal (hm ▸ zpow_le_zpow_right₀ hb.le hmk)

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [Module R A] [NormSMulClass R A]
  [NormMulClass A] {f : R⟦X⟧} {b : ℝ} {k : ℤ}

/-- **Discrete-value-group drop of the point-convergence radius.** Let `A` be complete and suppose
every nonzero norm in `A` is an integer power of `b > 1`, with `b ^ k` attained by the norm of an
element of `A`. If `b ^ k < f.radius < b ^ (k + 1)`, then `f.pointRadius A = b ^ k`. -/
theorem pointRadius_eq_ofReal_zpow_of_lt_radius_lt [CompleteSpace A] (hb : 1 < b)
    (hval : ∀ x : A, ‖x‖ ≠ 0 → ∃ m : ℤ, ‖x‖ = b ^ m) (hx₀ : ∃ x₀ : A, ‖x₀‖ = b ^ k)
    (hlo : ENNReal.ofReal (b ^ k) < f.radius)
    (hhi : f.radius < ENNReal.ofReal (b ^ (k + 1))) :
    f.pointRadius A = ENNReal.ofReal (b ^ k) := by
  refine le_antisymm (pointRadius_le_ofReal_zpow_of_radius_lt hb hval hhi) ?_
  obtain ⟨x₀, hx₀⟩ := hx₀
  have hx₀R : ‖x₀‖ₑ < f.radius := by rwa [← ofReal_norm, hx₀]
  obtain ⟨t, hxt, htR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hx₀R
  have hxt' : ‖x₀‖ < (t : ℝ) := by
    rw [eNorm_eq_nnNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm] at hxt
    exact hxt
  have hft : f.IsRestricted (t : ℝ) := isRestricted_of_lt_radius (by simpa using htR)
  have hs : Summable fun n ↦ coeff n f • x₀ ^ n :=
    (hft.onOpenDisc.summable_norm_smul_pow hxt').of_norm
  simpa only [← ofReal_norm, hx₀] using le_pointRadius_of_summable hs

/-- Under the hypotheses of `pointRadius_eq_ofReal_zpow_of_lt_radius_lt`, the inequality
`f.pointRadius A < f.radius` is strict. -/
theorem pointRadius_lt_radius_of_lt_radius_lt [CompleteSpace A] (hb : 1 < b)
    (hval : ∀ x : A, ‖x‖ ≠ 0 → ∃ m : ℤ, ‖x‖ = b ^ m) (hx₀ : ∃ x₀ : A, ‖x₀‖ = b ^ k)
    (hlo : ENNReal.ofReal (b ^ k) < f.radius)
    (hhi : f.radius < ENNReal.ofReal (b ^ (k + 1))) :
    f.pointRadius A < f.radius := by
  rwa [pointRadius_eq_ofReal_zpow_of_lt_radius_lt hb hval hx₀ hlo hhi]

/-- Special case `k = 0`: when `A` is complete with `‖(1 : A)‖ = 1` and every nonzero norm in `A`
is an integer power of `b > 1`, any series with `1 < f.radius < b` has `f.pointRadius A = 1`. -/
theorem pointRadius_eq_one_of_one_lt_radius_lt [CompleteSpace A] [NormOneClass A] (hb : 1 < b)
    (hval : ∀ x : A, ‖x‖ ≠ 0 → ∃ m : ℤ, ‖x‖ = b ^ m)
    (hlo : 1 < f.radius) (hhi : f.radius < ENNReal.ofReal b) :
    f.pointRadius A = 1 := by
  simpa using pointRadius_eq_ofReal_zpow_of_lt_radius_lt (k := 0) hb hval
    ⟨1, by simp⟩ (by simpa using hlo) (by simpa using hhi)

end DiscreteValueGroup

end PowerSeries
