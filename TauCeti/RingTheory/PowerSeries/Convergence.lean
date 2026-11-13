/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Radius
import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Pointwise convergence of power series in normed extensions

Let `f = ∑ aₙ Xⁿ` be a power series over a normed ring `R` acting isometrically on a seminormed
ring `A` with multiplicative norm (`[NormSMulClass R A] [NormMulClass A]`), such as a normed field
extension `L/K` (`[NormedField K] [NormedField L] [NormedAlgebra K L]`). In positive degree the
individual terms satisfy `‖aₙ • xⁿ‖ = ‖aₙ‖ ‖x‖ⁿ` (and in degree `0` as well when `‖(1 : A)‖ = 1`),
so `aₙ • xⁿ → 0` if and only if `f` is restricted at the radius `‖x‖`. In particular, without any
completeness or ultrametric assumption, summability of `∑ aₙ • xⁿ` forces `f.IsRestricted ‖x‖` and
hence `‖x‖ₑ ≤ f.radius`.

When `A` is complete and ultrametric, summability is equivalent to the vanishing of the terms
(`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`), so convergence of `f` at `x : A` is
equivalent to `f.IsRestricted ‖x‖`. Consequently, convergence on the closed ball
`Metric.closedBall 0 r` is equivalent to `f.IsRestricted r` whenever `r` is attained as the norm of
a point of `A` (`PowerSeries.forall_mem_closedBall_summable_iff_isRestricted`), complementing
closed-disc convergence and the Gauss-norm bound (`PowerSeries.IsRestricted.summable_smul_pow`,
`PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm`) from `EvalAt`.

To separate what points of `A` witness from the coefficient invariant `PowerSeries.radius`, this
file defines the *pointwise convergence radius*
`PowerSeries.convergenceRadius f A = ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ`
in `ℝ≥0∞`. It always satisfies `f.convergenceRadius A ≤ f.radius`, and over any complete
nontrivially normed field `L` it is `0` (resp. `⊤`) if and only if `f.radius = 0` (resp. `f` is
entire). When `A` is complete and its positive norms are dense in `(0, ∞)` — for instance for any
complete `DenselyNormedField` such as `ℂ_[p]`, or any complete algebraically closed nontrivially
normed field — equality `f.convergenceRadius A = f.radius` holds, even without an ultrametric
hypothesis. Over a discretely normed ultrametric extension whose nonzero norms are integer powers
`b ^ m` (`b > 1`), by contrast, `f.convergenceRadius A` is strictly smaller than `f.radius`
whenever `b ^ k` is attained as a norm in `A` and `f.radius` falls strictly above `b ^ k` while `f`
is not restricted at `b ^ (k + 1)`.

## Main definitions

* `PowerSeries.convergenceRadius f A`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over the points `x : A` at
  which `∑ coeff n f • x ^ n` is summable.

## Main results

* `PowerSeries.norm_coeff_smul_pow` and `PowerSeries.tendsto_smul_pow_cofinite_iff_isRestricted`:
  exact term norms `‖aₙ • xⁿ‖ = ‖aₙ‖ ‖x‖ⁿ`, and equivalence between `aₙ • xⁿ → 0` and
  `f.IsRestricted ‖x‖`.
* `PowerSeries.isRestricted_norm_of_summable` and `PowerSeries.le_radius_of_summable`: summability
  at `x` implies `f.IsRestricted ‖x‖` and `‖x‖ₑ ≤ f.radius`.
* `PowerSeries.summable_smul_pow_iff_isRestricted`, `PowerSeries.hasSum_evalAt_iff_isRestricted`
  and `PowerSeries.forall_mem_closedBall_summable_iff_isRestricted`: in a complete ultrametric
  extension, convergence at `x` (and on a closed ball of attained radius `r`) is equivalent to
  restrictedness.
* `PowerSeries.convergenceRadius_le_radius`, `PowerSeries.convergenceRadius_pos_iff_radius_pos`,
  `PowerSeries.convergenceRadius_eq_zero_iff_radius_eq_zero` and
  `PowerSeries.convergenceRadius_eq_top_iff`: upper bound by `f.radius`, and characterizations of
  vanishing and infinite pointwise convergence radius over complete nontrivially normed fields.
* `PowerSeries.radius_le_convergenceRadius_of_forall_exists_lt_norm_lt`,
  `PowerSeries.convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt`,
  `PowerSeries.convergenceRadius_eq_radius` and
  `PowerSeries.convergenceRadius_eq_radius_of_isAlgClosed`: equality `f.convergenceRadius A =
  f.radius` when positive norms separate every open interval in `(0, ∞)`.
* `PowerSeries.convergenceRadius_eq_ofReal_zpow` and
  `PowerSeries.convergenceRadius_lt_radius_of_zpow`: exact formula and strict inequality
  `f.convergenceRadius A < f.radius` when nonzero norms are integer powers of `b > 1`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §§1, 4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 6 §1.
-/

public section

namespace PowerSeries

open Filter
open scoped NNReal ENNReal Topology

section TermNorm

/-- In positive degree, the `n`-th term `aₙ • xⁿ` has norm `‖aₙ‖ ‖x‖ⁿ`, without assuming
`‖(1 : A)‖ = 1`. -/
theorem norm_coeff_smul_pow_succ {R A : Type*} [SeminormedRing R] [SeminormedRing A] [SMul R A]
    [NormSMulClass R A] [NormMulClass A] (f : R⟦X⟧) (x : A) (n : ℕ) :
    ‖coeff (n + 1) f • x ^ (n + 1)‖ = ‖coeff (n + 1) f‖ * ‖x‖ ^ (n + 1) := by
  rw [norm_smul, TauCeti.norm_pow_succ]

/-- When `‖(1 : A)‖ = 1`, every term `aₙ • xⁿ` of `f` at `x` has norm `‖aₙ‖ ‖x‖ⁿ`. -/
theorem norm_coeff_smul_pow {R A : Type*} [SeminormedRing R] [SeminormedRing A] [SMul R A]
    [NormSMulClass R A] [NormMulClass A] [NormOneClass A] (f : R⟦X⟧) (x : A) (n : ℕ) :
    ‖coeff n f • x ^ n‖ = ‖coeff n f‖ * ‖x‖ ^ n := by
  rw [norm_smul, norm_pow]

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMul R A] [NormSMulClass R A]
  [NormMulClass A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- The terms `aₙ • xⁿ` tend to zero along the cofinite filter if and only if `f` is restricted at
the radius `‖x‖`. -/
theorem tendsto_smul_pow_cofinite_iff_isRestricted :
    Tendsto (fun n ↦ coeff n f • x ^ n) cofinite (𝓝 0) ↔ f.IsRestricted ‖x‖ := by
  rw [tendsto_zero_iff_norm_tendsto_zero, isRestricted_iff]
  refine tendsto_congr' ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Set.mem_compl_singleton_iff.mp hn)
  exact norm_coeff_smul_pow_succ f x m

/-- The terms `aₙ • xⁿ` tend to zero as `n → ∞` if and only if `f` is restricted at `‖x‖`. -/
theorem tendsto_smul_pow_atTop_iff_isRestricted :
    Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0) ↔ f.IsRestricted ‖x‖ := by
  rw [← Nat.cofinite_eq_atTop, tendsto_smul_pow_cofinite_iff_isRestricted]

/-- **Summability implies restrictedness.** If `∑ aₙ • xⁿ` is summable, then `f` is restricted at
`‖x‖`. Neither completeness nor an ultrametric norm is needed. -/
theorem isRestricted_norm_of_summable (h : Summable fun n ↦ coeff n f • x ^ n) :
    f.IsRestricted ‖x‖ :=
  tendsto_smul_pow_cofinite_iff_isRestricted.mp h.tendsto_cofinite_zero

/-- If `∑ aₙ • xⁿ` is summable at a point `x` with `‖x‖ = |r|`, then `f` is restricted at `r`. -/
theorem isRestricted_of_summable_of_norm_eq_abs (h : Summable fun n ↦ coeff n f • x ^ n)
    (hx : ‖x‖ = |r|) : f.IsRestricted r := by
  rw [← isRestricted_abs_iff, ← hx]
  exact isRestricted_norm_of_summable h

/-- If `∑ aₙ • xⁿ` is summable at a point `x` of norm `r`, then `f` is restricted at `r`. -/
theorem isRestricted_of_summable_of_norm_eq (h : Summable fun n ↦ coeff n f • x ^ n)
    (hx : ‖x‖ = r) : f.IsRestricted r :=
  hx ▸ isRestricted_norm_of_summable h

/-- **Pointwise convergence is bounded by the coefficient radius.** If `∑ aₙ • xⁿ` is summable,
then `‖x‖ₑ ≤ f.radius`. -/
theorem le_radius_of_summable (h : Summable fun n ↦ coeff n f • x ^ n) : ‖x‖ₑ ≤ f.radius := by
  simpa using le_radius_of_isRestricted (isRestricted_norm_of_summable h)

/-- **Convergence on a closed ball implies restrictedness at an attained radius.** If `r` is the
norm of a point of `A` and `f` is summable at every point of `Metric.closedBall (0 : A) r`, then
`f` is restricted at `r`. -/
theorem isRestricted_of_forall_mem_closedBall_summable (hr : ∃ x : A, ‖x‖ = r)
    (h : ∀ y ∈ Metric.closedBall (0 : A) r, Summable fun n ↦ coeff n f • y ^ n) :
    f.IsRestricted r := by
  obtain ⟨x, rfl⟩ := hr
  exact isRestricted_norm_of_summable (h x (mem_closedBall_zero_iff.mpr le_rfl))

omit [NormMulClass A] in
/-- Strictly inside a restricted radius `r`, the term norms `‖aₙ • xⁿ‖` are summable, without any
completeness or ultrametric assumption. -/
theorem IsRestricted.summable_norm_smul_pow (hf : f.IsRestricted r) (hx : ‖x‖ < |r|) :
    Summable fun n ↦ ‖coeff n f • x ^ n‖ := by
  have hmul := hf.summable_norm_coeff_mul_pow (by rwa [abs_norm x])
  rw [← summable_nat_add_iff 1]
  refine ((summable_nat_add_iff 1).mpr hmul).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x n.succ_pos) (norm_nonneg _)

end TermNorm

section Ultrametric

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMul R A] [NormSMulClass R A]
  [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] {f : R⟦X⟧} {x y : A} {r : ℝ}

/-- **Pointwise convergence versus restrictedness.** In a complete ultrametric extension `A` with
multiplicative norm and isometric `R`-action, `∑ aₙ • xⁿ` converges at `x : A` if and only if `f`
is restricted at the radius `‖x‖`. -/
theorem summable_smul_pow_iff_isRestricted :
    Summable (fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted ‖x‖ := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
    tendsto_smul_pow_cofinite_iff_isRestricted]

/-- At a point `x : A` of norm `r`, convergence of `∑ aₙ • xⁿ` is equivalent to restrictedness of
`f` at `r`. -/
theorem summable_smul_pow_iff_isRestricted_of_norm_eq (hx : ‖x‖ = r) :
    Summable (fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted r :=
  hx ▸ summable_smul_pow_iff_isRestricted

/-- In a complete ultrametric extension, convergence at one point `x` implies convergence at every
point `y` of the closed disc `‖y‖ ≤ ‖x‖`. -/
theorem summable_smul_pow_of_summable_of_norm_le (hx : Summable fun n ↦ coeff n f • x ^ n)
    (hy : ‖y‖ ≤ ‖x‖) : Summable fun n ↦ coeff n f • y ^ n :=
  summable_smul_pow_iff_isRestricted.mpr
    (TauCeti.PowerSeries.isRestricted_of_abs_le (isRestricted_norm_of_summable hx)
      (by rwa [abs_norm, abs_norm]))

/-- **Closed-ball convergence characterization.** When the radius `r` is attained as the norm of a
point of `A`, summability of `f` throughout `Metric.closedBall (0 : A) r` is equivalent to
`f.IsRestricted r`. -/
theorem forall_mem_closedBall_summable_iff_isRestricted (hr : ∃ x : A, ‖x‖ = r) :
    (∀ y ∈ Metric.closedBall (0 : A) r, Summable fun n ↦ coeff n f • y ^ n) ↔ f.IsRestricted r := by
  refine ⟨isRestricted_of_forall_mem_closedBall_summable hr, fun hf y hy ↦ ?_⟩
  exact summable_smul_pow_iff_isRestricted.mpr
    (TauCeti.PowerSeries.isRestricted_of_abs_le hf
      (by rw [abs_norm]; exact (mem_closedBall_zero_iff.mp hy).trans (le_abs_self r)))

end Ultrametric

section UltrametricEval

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A] [NormSMulClass R A]
  [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] {f : R⟦X⟧} {x : A}

/-- In a complete ultrametric normed algebra with isometric scalar action and multiplicative norm,
`∑ aₙ • xⁿ` sums to `f.evalAt x` if and only if `f` is restricted at `‖x‖`. -/
theorem hasSum_evalAt_iff_isRestricted :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) ↔ f.IsRestricted ‖x‖ :=
  ⟨fun h ↦ isRestricted_norm_of_summable h.summable, fun h ↦ h.hasSum_evalAt le_rfl⟩

end UltrametricEval

section ConvergenceRadiusDef

variable {R : Type*} [Semiring R]

/-- The *pointwise convergence radius* of a power series `f = ∑ aₙ Xⁿ` in a seminormed `R`-action
`A`: the supremum, in `ℝ≥0∞`, of `‖x‖ₑ` over the points `x : A` at which `∑ aₙ • xⁿ` is summable.
Unlike `PowerSeries.radius`, it depends on the norms realised by points of `A`. -/
noncomputable def convergenceRadius (f : R⟦X⟧) (A : Type*) [SeminormedRing A] [SMul R A] :
    ℝ≥0∞ :=
  ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ

/-- The pointwise convergence radius as the supremum of `‖x‖ₑ` over convergence points `x : A`. -/
theorem convergenceRadius_def (f : R⟦X⟧) (A : Type*) [SeminormedRing A] [SMul R A] :
    f.convergenceRadius A = ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ :=
  (rfl)

variable {A : Type*} [SeminormedRing A] [SMul R A] {f : R⟦X⟧} {x : A} {r : ℝ≥0∞}

/-- Every convergence point `x : A` of `f` has extended norm at most `f.convergenceRadius A`. -/
theorem le_convergenceRadius_of_summable (hx : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.convergenceRadius A :=
  le_iSup₂ (f := fun (y : A) (_ : Summable fun n ↦ coeff n f • y ^ n) ↦ ‖y‖ₑ) x hx

/-- `f` is not summable at any point of extended norm strictly above `f.convergenceRadius A`. -/
theorem not_summable_of_convergenceRadius_lt (hx : f.convergenceRadius A < ‖x‖ₑ) :
    ¬Summable fun n ↦ coeff n f • x ^ n :=
  fun h ↦ (le_convergenceRadius_of_summable h).not_gt hx

/-- Universal property of `convergenceRadius`: `f.convergenceRadius A ≤ r` exactly when every
convergence point of `f` in `A` has extended norm at most `r`. -/
theorem convergenceRadius_le_iff :
    f.convergenceRadius A ≤ r ↔ ∀ x : A, Summable (fun n ↦ coeff n f • x ^ n) → ‖x‖ₑ ≤ r := by
  simp [convergenceRadius_def]

/-- `r < f.convergenceRadius A` exactly when `f` converges at some `x : A` with `r < ‖x‖ₑ`. -/
theorem lt_convergenceRadius_iff :
    r < f.convergenceRadius A ↔ ∃ x : A, Summable (fun n ↦ coeff n f • x ^ n) ∧ r < ‖x‖ₑ := by
  simp [convergenceRadius_def, lt_iSup_iff, and_comm]

/-- `0 < f.convergenceRadius A` exactly when `f` converges at some point of positive norm in `A`. -/
theorem convergenceRadius_pos_iff :
    0 < f.convergenceRadius A ↔ ∃ x : A, 0 < ‖x‖ ∧ Summable fun n ↦ coeff n f • x ^ n := by
  rw [lt_convergenceRadius_iff]
  refine ⟨fun ⟨x, hx, h0⟩ ↦ ⟨x, ?_, hx⟩, fun ⟨x, h0, hx⟩ ↦ ⟨x, hx, ?_⟩⟩
  · simpa only [eNorm_eq_nnNorm, ENNReal.coe_pos, ← NNReal.coe_pos, coe_nnNorm] using h0
  · simpa only [eNorm_eq_nnNorm, ENNReal.coe_pos, ← NNReal.coe_pos, coe_nnNorm] using h0

/-- Extension of scalars preserves the pointwise convergence radius in a tower of algebras. -/
@[simp]
theorem convergenceRadius_map_algebraMap {R S : Type*} [CommSemiring R] [CommSemiring S]
    (A : Type*) [SeminormedRing A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] (f : R⟦X⟧) :
    (f.map (algebraMap R S)).convergenceRadius A = f.convergenceRadius A := by
  simp [convergenceRadius_def]

end ConvergenceRadiusDef

section ConvergenceRadiusAlgebraic

/-- A polynomial converges at every point of `A`, so its pointwise convergence radius in `A` is
the supremum `⨆ x : A, ‖x‖ₑ` of all norms in `A`. -/
theorem convergenceRadius_coe_eq_iSup {R : Type*} [Semiring R] (p : Polynomial R) (A : Type*)
    [SeminormedRing A] [MulActionWithZero R A] :
    (p : R⟦X⟧).convergenceRadius A = ⨆ x : A, ‖x‖ₑ := by
  refine le_antisymm (convergenceRadius_le_iff.mpr fun x _ ↦ le_iSup (fun y : A ↦ ‖y‖ₑ) x)
    (iSup_le fun x ↦ le_convergenceRadius_of_summable ?_)
  refine summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn ↦ ?_
  rw [Finset.mem_range, not_lt] at hn
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- Over a nontrivially normed field `L`, every polynomial has infinite pointwise convergence
radius, regardless of the norms of its roots. -/
@[simp]
theorem convergenceRadius_coe {R : Type*} [Semiring R] (p : Polynomial R) (L : Type*)
    [NontriviallyNormedField L] [MulActionWithZero R L] :
    (p : R⟦X⟧).convergenceRadius L = ⊤ := by
  rw [convergenceRadius_coe_eq_iSup, NormedField.iSup_eNorm_eq_top]

/-- Over a nontrivially normed field `L`, the zero series has infinite pointwise convergence
radius. -/
@[simp]
theorem convergenceRadius_zero {R : Type*} [Semiring R] (L : Type*) [NontriviallyNormedField L]
    [MulActionWithZero R L] : (0 : R⟦X⟧).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe (0 : Polynomial R) L

/-- Over a nontrivially normed field `L`, `1` has infinite pointwise convergence radius. -/
@[simp]
theorem convergenceRadius_one {R : Type*} [Semiring R] (L : Type*) [NontriviallyNormedField L]
    [MulActionWithZero R L] : (1 : R⟦X⟧).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe (1 : Polynomial R) L

/-- Over a nontrivially normed field `L`, constant series have infinite pointwise convergence
radius. -/
@[simp]
theorem convergenceRadius_C {R : Type*} [Semiring R] (L : Type*) [NontriviallyNormedField L]
    [MulActionWithZero R L] (a : R) : (C a).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe (Polynomial.C a) L

/-- Over a nontrivially normed field `L`, every monomial has infinite pointwise convergence
radius. -/
@[simp]
theorem convergenceRadius_monomial {R : Type*} [Semiring R] (L : Type*) [NontriviallyNormedField L]
    [MulActionWithZero R L] (n : ℕ) (a : R) : (monomial n a).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe (Polynomial.monomial n a) L

/-- Over a nontrivially normed field `L`, `X` has infinite pointwise convergence radius. -/
@[simp]
theorem convergenceRadius_X {R : Type*} [Semiring R] (L : Type*) [NontriviallyNormedField L]
    [MulActionWithZero R L] : (X : R⟦X⟧).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe (Polynomial.X : Polynomial R) L

/-- Negating a series preserves its pointwise convergence radius. -/
@[simp]
theorem convergenceRadius_neg {R : Type*} [Ring R] (f : R⟦X⟧) (A : Type*) [SeminormedRing A]
    [Module R A] : (-f).convergenceRadius A = f.convergenceRadius A := by
  have hneg (g : R⟦X⟧) : g.convergenceRadius A ≤ (-g).convergenceRadius A :=
    convergenceRadius_le_iff.mpr fun x hx ↦
      le_convergenceRadius_of_summable (by simpa [neg_smul] using hx.neg)
  exact le_antisymm (by simpa using hneg (-f)) (hneg f)

/-- An entire series converges at every point of a complete extension `A`, so its pointwise
convergence radius in `A` is `⨆ x : A, ‖x‖ₑ`. -/
theorem IsEntire.convergenceRadius_eq_iSup {R : Type*} [NormedRing R] {f : R⟦X⟧} (hf : f.IsEntire)
    (A : Type*) [SeminormedRing A] [SMulZeroClass R A] [IsBoundedSMul R A] [CompleteSpace A] :
    f.convergenceRadius A = ⨆ x : A, ‖x‖ₑ := by
  refine le_antisymm (convergenceRadius_le_iff.mpr fun x _ ↦ le_iSup (fun y : A ↦ ‖y‖ₑ) x)
    (iSup_le fun x ↦ le_convergenceRadius_of_summable ?_)
  exact (summable_norm_smul_pow_of_summable_norm_mul_pow
    (hf.summable_norm_coeff_mul_pow ‖x‖)).of_norm

/-- Over a complete nontrivially normed field `L`, every entire series has infinite pointwise
convergence radius. -/
theorem IsEntire.convergenceRadius_eq_top {R : Type*} [NormedRing R] {f : R⟦X⟧} (hf : f.IsEntire)
    (L : Type*) [NontriviallyNormedField L] [SMulZeroClass R L] [IsBoundedSMul R L]
    [CompleteSpace L] : f.convergenceRadius L = ⊤ := by
  rw [hf.convergenceRadius_eq_iSup L, NormedField.iSup_eNorm_eq_top]

end ConvergenceRadiusAlgebraic

section ConvergenceRadiusUltrametric

variable {R A : Type*} [NormedRing R] [SeminormedRing A]

/-- In a complete ultrametric extension, `f.convergenceRadius A` is the supremum of `‖x‖ₑ` over the
points `x : A` whose norm is a restricted radius of `f`. -/
theorem convergenceRadius_eq_iSup_isRestricted [SMul R A] [NormSMulClass R A] [NormMulClass A]
    [IsUltrametricDist A] [CompleteSpace A] (f : R⟦X⟧) :
    f.convergenceRadius A = ⨆ (x : A) (_ : f.IsRestricted ‖x‖), ‖x‖ₑ := by
  simp_rw [convergenceRadius_def, summable_smul_pow_iff_isRestricted]

/-- In a complete ultrametric extension, the pointwise convergence radius of `f + g` is at least
`min (f.convergenceRadius A) (g.convergenceRadius A)`. -/
theorem min_convergenceRadius_le_convergenceRadius_add [Module R A] [NormSMulClass R A]
    [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] (f g : R⟦X⟧) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ (f + g).convergenceRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨x₁, hf₁, hr₁⟩ := lt_convergenceRadius_iff.mp (lt_min_iff.mp hr).1
  obtain ⟨x₂, hg₂, hr₂⟩ := lt_convergenceRadius_iff.mp (lt_min_iff.mp hr).2
  obtain ⟨x, hx₁, hx₂, hrx⟩ : ∃ x : A, ‖x‖ ≤ ‖x₁‖ ∧ ‖x‖ ≤ ‖x₂‖ ∧ (r : ℝ≥0∞) ≤ ‖x‖ₑ :=
    if h : ‖x₁‖ ≤ ‖x₂‖ then ⟨x₁, le_rfl, h, hr₁.le⟩ else ⟨x₂, le_of_not_ge h, le_rfl, hr₂.le⟩
  have hf := summable_smul_pow_of_summable_of_norm_le hf₁ hx₁
  have hg := summable_smul_pow_of_summable_of_norm_le hg₂ hx₂
  exact hrx.trans (le_convergenceRadius_of_summable (by simpa [add_smul] using hf.add hg))

/-- In a complete ultrametric extension over an ultrametric ring, the pointwise convergence radius
of `f * g` is at least `min (f.convergenceRadius A) (g.convergenceRadius A)`. -/
theorem min_convergenceRadius_le_convergenceRadius_mul [IsUltrametricDist R] [SMul R A]
    [NormSMulClass R A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] (f g : R⟦X⟧) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ (f * g).convergenceRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨x₁, hf₁, hr₁⟩ := lt_convergenceRadius_iff.mp (lt_min_iff.mp hr).1
  obtain ⟨x₂, hg₂, hr₂⟩ := lt_convergenceRadius_iff.mp (lt_min_iff.mp hr).2
  obtain ⟨x, hx₁, hx₂, hrx⟩ : ∃ x : A, ‖x‖ ≤ ‖x₁‖ ∧ ‖x‖ ≤ ‖x₂‖ ∧ (r : ℝ≥0∞) ≤ ‖x‖ₑ :=
    if h : ‖x₁‖ ≤ ‖x₂‖ then ⟨x₁, le_rfl, h, hr₁.le⟩ else ⟨x₂, le_of_not_ge h, le_rfl, hr₂.le⟩
  have hf := isRestricted_norm_of_summable (summable_smul_pow_of_summable_of_norm_le hf₁ hx₁)
  have hg := isRestricted_norm_of_summable (summable_smul_pow_of_summable_of_norm_le hg₂ hx₂)
  exact hrx.trans (le_convergenceRadius_of_summable
    ((summable_smul_pow_iff_isRestricted (R := R)).mpr (hf.mul hg)))

end ConvergenceRadiusUltrametric

section Comparison

/-- **Inside the pointwise convergence disc, terms are absolutely summable.** If
`‖x‖ₑ < f.convergenceRadius A`, then `∑ ‖aₙ • xⁿ‖` is summable. Neither completeness nor an
ultrametric norm is needed. -/
theorem summable_norm_of_lt_convergenceRadius {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMul R A] [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {x : A}
    (hx : ‖x‖ₑ < f.convergenceRadius A) :
    Summable fun n ↦ ‖coeff n f • x ^ n‖ := by
  obtain ⟨y, hy, hxy⟩ := lt_convergenceRadius_iff.mp hx
  have hlt : ‖x‖ < |‖y‖| := by
    rw [abs_norm]
    exact_mod_cast (by simpa only [eNorm_eq_nnNorm, ENNReal.coe_lt_coe] using hxy : ‖x‖₊ < ‖y‖₊)
  exact (isRestricted_norm_of_summable hy).summable_norm_smul_pow hlt

/-- In a complete extension, `f` is summable at every point `x : A` with
`‖x‖ₑ < f.convergenceRadius A`. -/
theorem summable_of_lt_convergenceRadius {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMul R A] [NormSMulClass R A] [NormMulClass A] [CompleteSpace A] {f : R⟦X⟧} {x : A}
    (hx : ‖x‖ₑ < f.convergenceRadius A) :
    Summable fun n ↦ coeff n f • x ^ n :=
  (summable_norm_of_lt_convergenceRadius hx).of_norm

/-- In a complete normed algebra with isometric scalar action and multiplicative norm, `f` sums to
`f.evalAt x` at every point `x : A` with `‖x‖ₑ < f.convergenceRadius A`. -/
theorem hasSum_evalAt_of_lt_convergenceRadius {R A : Type*} [NormedCommRing R] [SeminormedRing A]
    [Algebra R A] [NormSMulClass R A] [NormMulClass A] [CompleteSpace A] {f : R⟦X⟧} {x : A}
    (hx : ‖x‖ₑ < f.convergenceRadius A) :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) :=
  hasSum_evalAt_of_summable_norm (summable_norm_of_lt_convergenceRadius hx)

/-- **Comparison with the coefficient radius.** The pointwise convergence radius
`f.convergenceRadius A` never exceeds the intrinsic coefficient radius `f.radius`. Neither
completeness nor an ultrametric norm is needed. -/
theorem convergenceRadius_le_radius {R : Type*} [NormedRing R] (f : R⟦X⟧) (A : Type*)
    [SeminormedRing A] [SMul R A] [NormSMulClass R A] [NormMulClass A] :
    f.convergenceRadius A ≤ f.radius :=
  convergenceRadius_le_iff.mpr fun _ hx ↦ le_radius_of_summable hx

/-- If `f` has infinite pointwise convergence radius in `A`, then `f` is entire. -/
theorem isEntire_of_convergenceRadius_eq_top {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMul R A] [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧}
    (h : f.convergenceRadius A = ⊤) : f.IsEntire :=
  radius_eq_top_iff.mp (top_unique (h ▸ f.convergenceRadius_le_radius A))

/-- Over any complete nontrivially normed field `L` with isometric `R`-action, `f` has infinite
pointwise convergence radius if and only if `f` is entire. -/
@[simp]
theorem convergenceRadius_eq_top_iff {R : Type*} [NormedRing R] (f : R⟦X⟧) (L : Type*)
    [NontriviallyNormedField L] [SMul R L] [NormSMulClass R L] [CompleteSpace L] :
    f.convergenceRadius L = ⊤ ↔ f.IsEntire := by
  refine ⟨isEntire_of_convergenceRadius_eq_top, fun hf ↦ ?_⟩
  rw [← NormedField.iSup_eNorm_eq_top L]
  refine le_antisymm (convergenceRadius_le_iff.mpr fun x _ ↦ le_iSup (fun y : L ↦ ‖y‖ₑ) x)
    (iSup_le fun x ↦ le_convergenceRadius_of_summable ?_)
  exact ((hf.isRestricted (‖x‖ + 1)).summable_norm_smul_pow
    ((lt_add_one ‖x‖).trans_le (le_abs_self _))).of_norm

/-- Over any complete nontrivially normed field `L`, `f` has positive pointwise convergence radius
in `L` if and only if `0 < f.radius`, because `L` contains elements of arbitrarily small positive
norm. -/
theorem convergenceRadius_pos_iff_radius_pos {R : Type*} [NormedRing R] (f : R⟦X⟧) (L : Type*)
    [NontriviallyNormedField L] [SMul R L] [NormSMulClass R L] [CompleteSpace L] :
    0 < f.convergenceRadius L ↔ 0 < f.radius := by
  refine ⟨fun h ↦ h.trans_le (f.convergenceRadius_le_radius L), fun h ↦ ?_⟩
  obtain ⟨r, hr0, hfr⟩ := radius_pos_iff.mp h
  obtain ⟨x, hx0, hxr⟩ := NormedField.exists_norm_lt L hr0
  have hnorm : Summable fun n ↦ ‖coeff n f • x ^ n‖ :=
    hfr.summable_norm_smul_pow (by rwa [abs_of_pos hr0])
  exact convergenceRadius_pos_iff.mpr ⟨x, hx0, hnorm.of_norm⟩

/-- Over any complete nontrivially normed field `L`, `f.convergenceRadius L = 0` if and only if
`f.radius = 0`. -/
theorem convergenceRadius_eq_zero_iff_radius_eq_zero {R : Type*} [NormedRing R] (f : R⟦X⟧)
    (L : Type*) [NontriviallyNormedField L] [SMul R L] [NormSMulClass R L] [CompleteSpace L] :
    f.convergenceRadius L = 0 ↔ f.radius = 0 := by
  rw [← not_iff_not, ← ne_eq, ← ne_eq, ← pos_iff_ne_zero, ← pos_iff_ne_zero,
    convergenceRadius_pos_iff_radius_pos]

/-- **Lower bound under dense positive norms.** In a complete seminormed ring `A` with a contractive
`R`-action (`‖a • x‖ ≤ ‖a‖ * ‖x‖`), if every open subinterval `(r₁, r₂) ⊆ (0, ∞)` contains the norm
of a point of `A`, then `f.radius ≤ f.convergenceRadius A`. -/
theorem radius_le_convergenceRadius_of_forall_exists_lt_norm_lt {R : Type*} [NormedRing R]
    (f : R⟦X⟧) (A : Type*) [SeminormedRing A] [SMul R A] [CompleteSpace A]
    (hsmul : ∀ (a : R) (x : A), ‖a • x‖ ≤ ‖a‖ * ‖x‖)
    (hdense : ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → ∃ x : A, r₁ < ‖x‖ ∧ ‖x‖ < r₂) :
    f.radius ≤ f.convergenceRadius A := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr₀ hr ↦ ?_
  obtain ⟨s, hrs, hsr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  obtain ⟨x, hrx, hxs⟩ := hdense r s (NNReal.coe_pos.mpr hr₀) (ENNReal.coe_lt_coe.mp hrs)
  have hs : f.IsRestricted s := isRestricted_of_lt_radius (by simpa using hsr)
  have hmul := hs.summable_norm_coeff_mul_pow (t := ‖x‖)
    (by rwa [abs_norm, abs_of_nonneg s.coe_nonneg])
  have hnorm : Summable fun n ↦ ‖coeff n f • x ^ n‖ := by
    rw [← summable_nat_add_iff 1]
    refine ((summable_nat_add_iff 1).mpr hmul).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦
      (hsmul _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le' x n.succ_pos) (norm_nonneg _))
  have hle : (r : ℝ≥0∞) ≤ ‖x‖ₑ := by simpa [← ofReal_norm] using ENNReal.ofReal_le_ofReal hrx.le
  exact hle.trans (le_convergenceRadius_of_summable hnorm.of_norm)

/-- **Equality of pointwise and intrinsic radii under interval separation.** If `A` is complete and
every interval `(r₁, r₂) ⊆ (0, ∞)` contains the norm of a point of `A`, then
`f.convergenceRadius A = f.radius`. -/
theorem convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt {R : Type*} [NormedRing R]
    (f : R⟦X⟧) (A : Type*) [SeminormedRing A] [SMul R A] [NormSMulClass R A] [NormMulClass A]
    [CompleteSpace A] (hdense : ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → ∃ x : A, r₁ < ‖x‖ ∧ ‖x‖ < r₂) :
    f.convergenceRadius A = f.radius :=
  le_antisymm (f.convergenceRadius_le_radius A)
    (f.radius_le_convergenceRadius_of_forall_exists_lt_norm_lt A (fun a x ↦ (norm_smul a x).le)
      hdense)

/-- **Over a complete densely normed extension field `L` (such as `ℂ_[p]`), the pointwise
convergence radius equals the intrinsic radius.** -/
theorem convergenceRadius_eq_radius {R : Type*} [NormedRing R] (f : R⟦X⟧) (L : Type*)
    [DenselyNormedField L] [SMul R L] [NormSMulClass R L] [CompleteSpace L] :
    f.convergenceRadius L = f.radius :=
  f.convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt L fun _ _ hr₁ hr ↦
    NormedField.exists_lt_norm_lt L hr₁.le hr

/-- **Over a complete algebraically closed nontrivially normed extension field `L`, the pointwise
convergence radius equals the intrinsic radius.** -/
theorem convergenceRadius_eq_radius_of_isAlgClosed {R : Type*} [NormedRing R] (f : R⟦X⟧)
    (L : Type*) [NontriviallyNormedField L] [IsAlgClosed L] [SMul R L] [NormSMulClass R L]
    [CompleteSpace L] :
    f.convergenceRadius L = f.radius :=
  f.convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt L fun _ _ hr₁ hr ↦
    NormedField.exists_lt_norm_lt_of_isAlgClosed L hr₁.le hr

end Comparison

section DiscreteValueGroup

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMul R A] [NormSMulClass R A]
  [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] {f : R⟦X⟧} {b : ℝ} {k : ℤ}

/-- **Pointwise convergence radius in a discretely normed extension.** Suppose `b > 1` and every
nonzero norm in `A` is an integer power `b ^ m` (`m ∈ ℤ`). If `b ^ k` is attained as the norm of a
point in `A`, `f` is restricted at `b ^ k`, and `f` is not restricted at `b ^ (k + 1)`, then
`f.convergenceRadius A = ENNReal.ofReal (b ^ k)`. -/
theorem convergenceRadius_eq_ofReal_zpow (hb : 1 < b)
    (hdisc : ∀ y : A, ‖y‖ ≠ 0 → ∃ m : ℤ, ‖y‖ = b ^ m) (hatt : ∃ x : A, ‖x‖ = b ^ k)
    (hres : f.IsRestricted (b ^ k)) (hnres : ¬f.IsRestricted (b ^ (k + 1))) :
    f.convergenceRadius A = ENNReal.ofReal (b ^ k) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  refine le_antisymm (convergenceRadius_le_iff.mpr fun y hy ↦ ?_) ?_
  · rcases eq_or_ne ‖y‖ 0 with hy0 | hy0
    · simp [← ofReal_norm, hy0]
    · obtain ⟨m, hm⟩ := hdisc y hy0
      have hm_le : m ≤ k := by
        by_contra hlt
        have hk1 : k + 1 ≤ m := by omega
        have hpow : |b ^ (k + 1)| ≤ |b ^ m| := by
          rw [abs_of_pos (zpow_pos hb0 _), abs_of_pos (zpow_pos hb0 _)]
          exact zpow_le_zpow_right₀ hb.le hk1
        exact hnres (TauCeti.PowerSeries.isRestricted_of_abs_le
          (hm ▸ isRestricted_norm_of_summable hy) hpow)
      rw [← ofReal_norm, hm]
      exact ENNReal.ofReal_le_ofReal (zpow_le_zpow_right₀ hb.le hm_le)
  · obtain ⟨x, hx⟩ := hatt
    rw [← hx, ofReal_norm]
    exact le_convergenceRadius_of_summable
      ((summable_smul_pow_iff_isRestricted_of_norm_eq hx).mpr hres)

/-- **Strict inequality `f.convergenceRadius A < f.radius` in a discretely normed extension.**
Suppose `b > 1`, every nonzero norm in `A` is an integer power of `b`, and `b ^ k` is attained in
`A`. Whenever `ENNReal.ofReal (b ^ k) < f.radius` and `f` is not restricted at `b ^ (k + 1)` — in
particular whenever `ENNReal.ofReal (b ^ k) < f.radius < ENNReal.ofReal (b ^ (k + 1))` — the
pointwise convergence radius `f.convergenceRadius A` is strictly smaller than `f.radius`. -/
theorem convergenceRadius_lt_radius_of_zpow (hb : 1 < b)
    (hdisc : ∀ y : A, ‖y‖ ≠ 0 → ∃ m : ℤ, ‖y‖ = b ^ m) (hatt : ∃ x : A, ‖x‖ = b ^ k)
    (hlt : ENNReal.ofReal (b ^ k) < f.radius) (hnres : ¬f.IsRestricted (b ^ (k + 1))) :
    f.convergenceRadius A < f.radius := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hres : f.IsRestricted (b ^ k) := isRestricted_of_lt_radius <| by
    rwa [Real.eNorm_eq_ofReal (zpow_pos hb0 k).le]
  exact convergenceRadius_eq_ofReal_zpow hb hdisc hatt hres hnres ▸ hlt

end DiscreteValueGroup

end PowerSeries
