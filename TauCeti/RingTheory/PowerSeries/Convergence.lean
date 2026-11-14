/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.Analysis.Normed.Field.Basic
public import TauCeti.RingTheory.PowerSeries.Entire.Eval
public import TauCeti.RingTheory.PowerSeries.Radius
import TauCeti.RingTheory.PowerSeries.Exp
import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Pointwise convergence of power series in normed algebras and extensions

A formal power series `f = ∑ aₙ Xⁿ` over a normed ring `R` has an intrinsic coefficient radius
`PowerSeries.radius f : ℝ≥0∞`, the supremum of the nonnegative real radii `r` at which
`‖aₙ‖ rⁿ → 0`. When `f` is evaluated in a normed `R`-algebra `A`, there is a second invariant:
`PowerSeries.convergenceRadius A f : ℝ≥0∞`, the supremum of `‖x‖ₑ` over the points `x : A` at
which `∑ₙ aₙ • xⁿ` converges.

When scalar multiplication is isometric and `A` has multiplicative norm (as in any normed field
extension `L / K`), individual terms satisfy `‖aₙ • xⁿ‖ = ‖aₙ‖ ‖x‖ⁿ` for `n ≥ 1`. Hence term
decay or summability at `x` forces `f` to be restricted at `‖x‖`, without any ultrametric or
completeness assumption (`PowerSeries.isRestricted_norm_of_summable`). Consequently
`f.convergenceRadius A ≤ f.radius` always holds (`PowerSeries.convergenceRadius_le_radius`).

When `A` is in addition a complete ultrametric normed `R`-algebra, ultrametric summability gives
the converse: `∑ₙ aₙ • xⁿ` converges if and only if `f` is restricted at `‖x‖`
(`PowerSeries.summable_smul_pow_iff_isRestricted_norm`). Thus restrictedness at `r` is equivalent
to convergence throughout the closed ball of radius `r` whenever `r` is attained as the norm of
an element of `A` (`PowerSeries.forall_closedBall_summable_iff_isRestricted`), with the Gauss-norm
evaluation bound `‖f.evalAt b‖ ≤ gaussNorm norm r f` on that closed ball. Moreover, when the
positive norms of `A` are dense in `(0, ∞)` — in particular over any `DenselyNormedField` or
algebraically closed nontrivially normed field — the pointwise convergence radius equals the
intrinsic radius (`PowerSeries.convergenceRadius_eq_radius`). When the norms of `A` have gaps,
`PowerSeries.convergenceRadius_eq_ofReal_of_forall_norm_le` and
`PowerSeries.convergenceRadius_eq_ofReal_of_not_isRestricted` compute the smaller pointwise
convergence radius.

Finally, the formal identity `exp X * exp (-X) = 1` evaluates to `f(x) f(-x) = 1` wherever the
exponential series is restricted at `‖x‖` in a complete ultrametric algebra, showing that
`PowerSeries.exp` has no zeros inside its disc of convergence
(`PowerSeries.evalAt_exp_ne_zero_of_lt_radius`).

## Main definitions

* `PowerSeries.convergenceRadius A f`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over all `x : A` at which
  `∑ₙ coeff n f • x ^ n` is summable.

## Main results

* `PowerSeries.isRestricted_norm_of_summable` and `PowerSeries.le_radius_of_summable`: under an
  isometric scalar action and multiplicative norm, convergence at `x` implies restrictedness at
  `‖x‖` and `‖x‖ₑ ≤ f.radius`.
* `PowerSeries.summable_smul_pow_iff_isRestricted_norm` and
  `PowerSeries.summable_smul_pow_iff_isRestricted`: in a complete ultrametric algebra with
  isometric scalar action and multiplicative norm, convergence at `x` is equivalent to
  restrictedness at `‖x‖`.
* `PowerSeries.forall_closedBall_summable_iff_isRestricted`: when `r` is attained as `‖x‖ = r`,
  convergence on `Metric.closedBall 0 r` is equivalent to `f.IsRestricted r`.
* `PowerSeries.convergenceRadius_le_radius`: `f.convergenceRadius A ≤ f.radius`.
* `PowerSeries.convergenceRadius_eq_radius_of_Ioi_subset_closure_range_norm`,
  `PowerSeries.convergenceRadius_eq_radius`, and
  `PowerSeries.convergenceRadius_eq_radius_of_isAlgClosed`: equality when positive norms are
  dense in `(0, ∞)`.
* `PowerSeries.convergenceRadius_eq_ofReal_of_forall_norm_le` and
  `PowerSeries.convergenceRadius_eq_ofReal_of_not_isRestricted`: exact pointwise convergence
  radius across a norm gap.
* `PowerSeries.isUnit_evalAt_exp_of_lt_radius` and
  `PowerSeries.evalAt_exp_ne_zero_of_lt_radius`: `PowerSeries.exp` is unit-valued and nonzero
  throughout its open disc of convergence in a complete ultrametric algebra.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §1 and §4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace PowerSeries

open Filter
open scoped NNReal ENNReal Topology

section Necessity

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [NormMulClass A] [SMul R A]
  [NormSMulClass R A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- In a seminormed ring with multiplicative norm, positive powers preserve norms even without
`NormOneClass`. -/
private theorem norm_pow_succ (x : A) (n : ℕ) : ‖x ^ (n + 1)‖ = ‖x‖ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [_root_.pow_succ x (n + 1), norm_mul, ih, _root_.pow_succ ‖x‖ (n + 1)]

/-- If the terms `aₙ • xⁿ` of `f` at `x` tend to zero, and scalar multiplication and multiplication
in `A` preserve norms, then `f` is restricted at `‖x‖`. Neither completeness nor ultrametricity is
needed. -/
theorem isRestricted_norm_of_tendsto_smul_pow_zero
    (hx : Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0)) : f.IsRestricted ‖x‖ := by
  rw [isRestricted_iff', ← tendsto_add_atTop_iff_nat 1]
  have hnorm : Tendsto (fun n ↦ ‖coeff (n + 1) f • x ^ (n + 1)‖) atTop (𝓝 0) := by
    simpa using ((tendsto_add_atTop_iff_nat 1).mpr hx).norm
  refine hnorm.congr fun n ↦ ?_
  rw [norm_smul, norm_pow_succ]

/-- If the terms `aₙ • xⁿ` tend to zero and `|r| ≤ ‖x‖`, then `f` is restricted at `r`. -/
theorem isRestricted_of_tendsto_smul_pow_zero
    (hx : Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0)) (hr : |r| ≤ ‖x‖) :
    f.IsRestricted r :=
  TauCeti.PowerSeries.isRestricted_of_abs_le (isRestricted_norm_of_tendsto_smul_pow_zero hx)
    (by simpa using hr)

/-- **Convergence implies restrictedness.** If `∑ₙ aₙ • xⁿ` is summable in a seminormed ring with
multiplicative norm and isometric `R`-action, then `f` is restricted at `‖x‖`. -/
theorem isRestricted_norm_of_summable (hx : Summable fun n ↦ coeff n f • x ^ n) :
    f.IsRestricted ‖x‖ :=
  isRestricted_norm_of_tendsto_smul_pow_zero hx.tendsto_atTop_zero

/-- If `∑ₙ aₙ • xⁿ` is summable and `|r| ≤ ‖x‖`, then `f` is restricted at `r`. -/
theorem isRestricted_of_summable_of_abs_le (hx : Summable fun n ↦ coeff n f • x ^ n)
    (hr : |r| ≤ ‖x‖) : f.IsRestricted r :=
  isRestricted_of_tendsto_smul_pow_zero hx.tendsto_atTop_zero hr

/-- If `∑ₙ aₙ • xⁿ` is summable at a point of norm `r`, then `f` is restricted at `r`. -/
theorem isRestricted_of_summable_of_norm_eq (hx : Summable fun n ↦ coeff n f • x ^ n)
    (hr : ‖x‖ = r) : f.IsRestricted r :=
  hr ▸ isRestricted_norm_of_summable hx

/-- If `f` converges at every point of `Metric.closedBall 0 r` and `r` is attained as the norm of
some point of `A`, then `f` is restricted at `r`. -/
theorem isRestricted_of_forall_closedBall_summable (hx : ∃ x : A, ‖x‖ = r)
    (hball : ∀ y ∈ Metric.closedBall (0 : A) r, Summable fun n ↦ coeff n f • y ^ n) :
    f.IsRestricted r := by
  obtain ⟨x, rfl⟩ := hx
  exact isRestricted_norm_of_summable (hball x (by simp))

/-- Every point at which `∑ₙ aₙ • xⁿ` is summable has extended norm at most `f.radius`. -/
theorem le_radius_of_summable (hx : Summable fun n ↦ coeff n f • x ^ n) : ‖x‖ₑ ≤ f.radius := by
  simpa using le_radius_of_isRestricted (isRestricted_norm_of_summable hx)

/-- Outside the intrinsic radius, `∑ₙ aₙ • xⁿ` diverges. -/
theorem not_summable_smul_pow_of_radius_lt (hx : f.radius < ‖x‖ₑ) :
    ¬Summable fun n ↦ coeff n f • x ^ n :=
  fun h ↦ (le_radius_of_summable h).not_gt hx

end Necessity

section Ultrametric

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A]
  {f g : R⟦X⟧} {b x : A} {c r : ℝ}

/-- In an ultrametric normed algebra with `‖1‖ = 1` and bounded scalar action, a series restricted
at `r` satisfies the Gauss-norm bound `‖f.evalAt b‖ ≤ gaussNorm norm r f` throughout `‖b‖ ≤ r`. -/
theorem IsRestricted.norm_evalAt_le_gaussNorm [IsBoundedSMul R A] [IsUltrametricDist A]
    [NormOneClass A] (hf : f.IsRestricted r) (hb : ‖b‖ ≤ r) :
    ‖f.evalAt b‖ ≤ gaussNorm norm r f :=
  PowerSeries.norm_evalAt_le_gaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf) hb

section BoundedSMul

variable [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A]

/-- In a complete ultrametric normed algebra, a series restricted at `c` is summable at every
point `b` with `‖b‖ ≤ c`. -/
theorem IsRestricted.summable_smul_pow (hf : f.IsRestricted c) (hb : ‖b‖ ≤ c) :
    Summable fun n ↦ coeff n f • b ^ n :=
  (hf.hasSum_evalAt hb).summable

/-- Strictly inside the intrinsic radius, `∑ₙ aₙ • bⁿ` converges to `f.evalAt b` in any complete
ultrametric normed algebra. -/
theorem hasSum_evalAt_of_lt_radius (hb : ‖b‖ₑ < f.radius) :
    HasSum (fun n ↦ coeff n f • b ^ n) (f.evalAt b) :=
  (isRestricted_of_lt_radius (r := ‖b‖) (by simpa using hb)).hasSum_evalAt le_rfl

/-- Strictly inside the intrinsic radius, `∑ₙ aₙ • bⁿ` is summable in any complete ultrametric
normed algebra. -/
theorem summable_smul_pow_of_lt_radius (hb : ‖b‖ₑ < f.radius) :
    Summable fun n ↦ coeff n f • b ^ n :=
  (hasSum_evalAt_of_lt_radius hb).summable

end BoundedSMul

section Isometric

variable [NormMulClass A] [NormSMulClass R A] [IsUltrametricDist A] [CompleteSpace A]

/-- **Convergence vs. restrictedness.** In a complete ultrametric normed `R`-algebra with
multiplicative norm and isometric scalar action (such as any complete ultrametric normed field
extension), `∑ₙ aₙ • xⁿ` converges if and only if `f` is restricted at `‖x‖`. -/
theorem summable_smul_pow_iff_isRestricted_norm :
    Summable (fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted ‖x‖ :=
  ⟨isRestricted_norm_of_summable, fun hf ↦ hf.summable_smul_pow le_rfl⟩

/-- At a point `x` of norm `r`, `∑ₙ aₙ • xⁿ` converges if and only if `f` is restricted at `r`. -/
theorem summable_smul_pow_iff_isRestricted (hr : ‖x‖ = r) :
    Summable (fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted r := by
  subst hr
  exact summable_smul_pow_iff_isRestricted_norm

/-- If `f` converges at a point `x`, then `f` converges throughout `‖b‖ ≤ ‖x‖`. -/
theorem hasSum_evalAt_of_summable_of_norm_le (hx : Summable fun n ↦ coeff n f • x ^ n)
    (hb : ‖b‖ ≤ ‖x‖) : HasSum (fun n ↦ coeff n f • b ^ n) (f.evalAt b) :=
  (isRestricted_norm_of_summable hx).hasSum_evalAt hb

/-- **Closed-disc convergence characterisation.** When `r` is attained as the norm of some point
of `A`, convergence on all of `Metric.closedBall 0 r` is equivalent to `f.IsRestricted r`. -/
theorem forall_closedBall_summable_iff_isRestricted (hx : ∃ x : A, ‖x‖ = r) :
    (∀ y ∈ Metric.closedBall (0 : A) r, Summable fun n ↦ coeff n f • y ^ n) ↔ f.IsRestricted r := by
  refine ⟨isRestricted_of_forall_closedBall_summable hx, fun hf y hy ↦ ?_⟩
  exact hf.summable_smul_pow (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)

end Isometric

end Ultrametric

section ConvergenceRadius

/-- The *pointwise convergence radius* of a power series `f = ∑ aₙ Xⁿ` in a seminormed ring `A`
acted on by `R`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over the points `x : A` at which `∑ₙ aₙ • xⁿ`
is summable. Unlike `PowerSeries.radius`, this invariant depends on the norms realized in `A`. -/
noncomputable def convergenceRadius {R : Type*} [Semiring R] (A : Type*) [SeminormedRing A]
    [SMul R A] (f : R⟦X⟧) : ℝ≥0∞ :=
  ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ

section Basic

variable {R : Type*} [Semiring R] {A : Type*} [SeminormedRing A] [SMul R A] {f : R⟦X⟧}

/-- Unfolding definition of `PowerSeries.convergenceRadius`. -/
theorem convergenceRadius_def (A : Type*) [SeminormedRing A] [SMul R A] (f : R⟦X⟧) :
    f.convergenceRadius A = ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ :=
  (rfl)

/-- Every convergence point `x : A` of `f` satisfies `‖x‖ₑ ≤ f.convergenceRadius A`. -/
theorem le_convergenceRadius_of_summable {x : A} (hx : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.convergenceRadius A :=
  le_iSup₂ (f := fun (y : A) (_ : Summable fun n ↦ coeff n f • y ^ n) ↦ ‖y‖ₑ) x hx

/-- `f.convergenceRadius A ≤ r` if and only if every convergence point `x : A` has `‖x‖ₑ ≤ r`. -/
theorem convergenceRadius_le_iff {r : ℝ≥0∞} :
    f.convergenceRadius A ≤ r ↔ ∀ x : A, Summable (fun n ↦ coeff n f • x ^ n) → ‖x‖ₑ ≤ r :=
  iSup₂_le_iff

/-- `r < f.convergenceRadius A` if and only if `f` converges at some `x : A` with `r < ‖x‖ₑ`. -/
theorem lt_convergenceRadius_iff {r : ℝ≥0∞} :
    r < f.convergenceRadius A ↔ ∃ x : A, Summable (fun n ↦ coeff n f • x ^ n) ∧ r < ‖x‖ₑ := by
  simp [convergenceRadius_def, lt_iSup_iff]

/-- Negating a power series preserves its pointwise convergence radius. -/
@[simp]
theorem convergenceRadius_neg {R : Type*} [Ring R] (A : Type*) [SeminormedRing A] [Module R A]
    (f : R⟦X⟧) : (-f).convergenceRadius A = f.convergenceRadius A := by
  have hle (g : R⟦X⟧) : (-g).convergenceRadius A ≤ g.convergenceRadius A :=
    convergenceRadius_le_iff.mpr fun x hx ↦
      le_convergenceRadius_of_summable (by simpa [neg_smul] using hx.neg)
  exact le_antisymm (hle f) (by simpa using hle (-f))

end Basic

section ZeroAndPoly

/-- At `0 : A`, the terms `coeff n f • 0 ^ n` vanish for `n ≥ 1`, so they are summable. -/
theorem summable_smul_pow_zero {R A : Type*} [Semiring R] [SeminormedRing A] [SMulZeroClass R A]
    (f : R⟦X⟧) : Summable fun n ↦ coeff n f • (0 : A) ^ n :=
  summable_of_ne_finset_zero (s := {0}) fun n hn ↦ by
    rw [Finset.mem_singleton] at hn
    simp [zero_pow hn]

/-- For a polynomial `p`, the series `∑ₙ coeff n p • x ^ n` has finitely many nonzero terms and so
is summable at every `x : A`. -/
theorem summable_smul_pow_coe {R A : Type*} [CommSemiring R] [SeminormedRing A] [Module R A]
    (p : Polynomial R) (x : A) : Summable fun n ↦ coeff n (p : R⟦X⟧) • x ^ n :=
  summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn ↦ by
    rw [Finset.mem_range, not_lt] at hn
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- The pointwise convergence radius of a polynomial in `A` is the supremum of all extended norms
in `A`. -/
theorem convergenceRadius_coe {R : Type*} [CommSemiring R] (A : Type*) [SeminormedRing A]
    [Module R A] (p : Polynomial R) :
    (p : R⟦X⟧).convergenceRadius A = ⨆ x : A, ‖x‖ₑ := by
  refine le_antisymm (convergenceRadius_le_iff.mpr fun x _ ↦ le_iSup (fun y : A ↦ ‖y‖ₑ) x) ?_
  exact iSup_le fun x ↦ le_convergenceRadius_of_summable (summable_smul_pow_coe p x)

/-- The pointwise convergence radius of `0` in `A` is the supremum of all extended norms in `A`. -/
theorem convergenceRadius_zero {R : Type*} [CommSemiring R] (A : Type*) [SeminormedRing A]
    [Module R A] : (0 : R⟦X⟧).convergenceRadius A = ⨆ x : A, ‖x‖ₑ := by
  simpa using convergenceRadius_coe A (0 : Polynomial R)

/-- Over a nontrivial normed ring with an isometric action by a nontrivially normed field, any
polynomial has infinite pointwise convergence radius. -/
theorem convergenceRadius_coe_eq_top_of_normSMulClass {R : Type*} [CommSemiring R]
    (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NormedRing A] [Module R A] [SMul 𝕜 A]
    [NormSMulClass 𝕜 A] [Nontrivial A] (p : Polynomial R) :
    (p : R⟦X⟧).convergenceRadius A = ⊤ := by
  rw [convergenceRadius_coe, NormedField.iSup_eNorm_eq_top_of_normSMulClass 𝕜 A]

/-- Over a nontrivially normed field `L`, every polynomial has pointwise convergence radius `⊤`. -/
@[simp]
theorem convergenceRadius_coe_eq_top {R : Type*} [CommSemiring R] (L : Type*)
    [NontriviallyNormedField L] [Module R L] (p : Polynomial R) :
    (p : R⟦X⟧).convergenceRadius L = ⊤ :=
  convergenceRadius_coe_eq_top_of_normSMulClass L L p

/-- Over a nontrivially normed field `L`, the zero series has pointwise convergence radius `⊤`. -/
@[simp]
theorem convergenceRadius_zero_eq_top {R : Type*} [CommSemiring R] (L : Type*)
    [NontriviallyNormedField L] [Module R L] :
    (0 : R⟦X⟧).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe_eq_top L (0 : Polynomial R)

/-- An entire series converges at every point of a complete seminormed ring with bounded scalar
action, so its pointwise convergence radius is `⨆ x : A, ‖x‖ₑ`. -/
theorem IsEntire.convergenceRadius_eq_iSup_eNorm {R : Type*} [NormedRing R] (A : Type*)
    [SeminormedRing A] [SMulZeroClass R A] [IsBoundedSMul R A] [CompleteSpace A]
    {f : R⟦X⟧} (hf : f.IsEntire) :
    f.convergenceRadius A = ⨆ x : A, ‖x‖ₑ := by
  refine le_antisymm (convergenceRadius_le_iff.mpr fun x _ ↦ le_iSup (fun y : A ↦ ‖y‖ₑ) x) ?_
  exact iSup_le fun x ↦ le_convergenceRadius_of_summable (hf.summable_smul_pow x)

/-- Over a complete nontrivially normed field, an entire series has pointwise convergence radius
`⊤`. -/
theorem IsEntire.convergenceRadius_eq_top {R : Type*} [NormedRing R] (L : Type*)
    [NontriviallyNormedField L] [SMulZeroClass R L] [IsBoundedSMul R L] [CompleteSpace L]
    {f : R⟦X⟧} (hf : f.IsEntire) :
    f.convergenceRadius L = ⊤ := by
  rw [hf.convergenceRadius_eq_iSup_eNorm L, NormedField.iSup_eNorm_eq_top L]

end ZeroAndPoly

section Functoriality

/-- Extending scalars along `algebraMap R S` preserves the pointwise convergence radius in any
`S`-algebra `A` forming a scalar tower. -/
@[simp]
theorem convergenceRadius_map_algebraMap {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Type*) [SeminormedRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (f : R⟦X⟧) :
    (f.map (algebraMap R S)).convergenceRadius A = f.convergenceRadius A := by
  simp [convergenceRadius_def]

/-- An isometric continuous ring homomorphism `φ : A →+* B` commuting with the `R`-action can only
increase the pointwise convergence radius: every convergence point in `A` maps to a convergence
point of the same norm in `B`. -/
theorem convergenceRadius_le_convergenceRadius_of_isometry {R A B : Type*} [Semiring R]
    [SeminormedRing A] [SeminormedRing B] [SMul R A] [SMul R B] {f : R⟦X⟧} (φ : A →+* B)
    (hcont : Continuous φ) (hsmul : ∀ (r : R) (x : A), φ (r • x) = r • φ x)
    (hnorm : ∀ x : A, ‖φ x‖ = ‖x‖) :
    f.convergenceRadius A ≤ f.convergenceRadius B := by
  refine convergenceRadius_le_iff.mpr fun x hx ↦ ?_
  have hsum : Summable fun n ↦ coeff n f • (φ x) ^ n := by
    simpa [Function.comp_def, hsmul, map_pow] using hx.map φ.toAddMonoidHom hcont
  have henorm : ‖φ x‖ₑ = ‖x‖ₑ := by simp [eNorm_eq_nnNorm, ← NNReal.coe_inj, hnorm]
  exact henorm ▸ le_convergenceRadius_of_summable hsum

end Functoriality

section ComparisonWithRadius

/-- **The pointwise convergence radius never exceeds the intrinsic radius.** Under an isometric
scalar action and multiplicative norm on `A`, `f.convergenceRadius A ≤ f.radius`. -/
theorem convergenceRadius_le_radius {R : Type*} [NormedRing R] (A : Type*) [SeminormedRing A]
    [NormMulClass A] [SMul R A] [NormSMulClass R A] (f : R⟦X⟧) :
    f.convergenceRadius A ≤ f.radius :=
  convergenceRadius_le_iff.mpr fun _ hx ↦ le_radius_of_summable hx

section CompleteUltrametric

variable {R : Type*} [NormedCommRing R] {A : Type*} [NormedRing A] [NormMulClass A]
  [Algebra R A] [NormSMulClass R A] [IsUltrametricDist A] [CompleteSpace A] {f g : R⟦X⟧}

/-- In a complete ultrametric algebra with isometric action and multiplicative norm, the pointwise
convergence radius is the supremum of `‖x‖ₑ` over the points `x : A` with `f.IsRestricted ‖x‖`. -/
theorem convergenceRadius_eq_iSup_isRestricted (A : Type*) [NormedRing A] [NormMulClass A]
    [Algebra R A] [NormSMulClass R A] [IsUltrametricDist A] [CompleteSpace A] (f : R⟦X⟧) :
    f.convergenceRadius A = ⨆ (x : A) (_ : f.IsRestricted ‖x‖), ‖x‖ₑ := by
  simp_rw [convergenceRadius_def, summable_smul_pow_iff_isRestricted_norm]

/-- Strictly inside `f.convergenceRadius A`, `f` converges at every point of `A` to `f.evalAt b`. -/
theorem hasSum_evalAt_of_lt_convergenceRadius {b : A} (hb : ‖b‖ₑ < f.convergenceRadius A) :
    HasSum (fun n ↦ coeff n f • b ^ n) (f.evalAt b) :=
  hasSum_evalAt_of_lt_radius (hb.trans_le (convergenceRadius_le_radius A f))

/-- Shared comparison bound for binary operations preserving `PowerSeries.IsRestricted` at every
radius. -/
private theorem min_convergenceRadius_le_of_isRestricted {f g h : R⟦X⟧}
    (hop : ∀ r : ℝ, f.IsRestricted r → g.IsRestricted r → h.IsRestricted r) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ h.convergenceRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨x, hx, hrx⟩ := lt_convergenceRadius_iff.mp (lt_min_iff.mp hr).1
  obtain ⟨y, hy, hry⟩ := lt_convergenceRadius_iff.mp (lt_min_iff.mp hr).2
  have hfx := isRestricted_norm_of_summable hx
  have hgy := isRestricted_norm_of_summable hy
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · have hg_at_x : g.IsRestricted ‖x‖ :=
      TauCeti.PowerSeries.isRestricted_of_abs_le (c := ‖x‖) hgy (by simpa using hxy)
    have hsum := (summable_smul_pow_iff_isRestricted_norm (f := h) (x := x)).mpr
      (hop ‖x‖ hfx hg_at_x)
    exact hrx.le.trans (le_convergenceRadius_of_summable hsum)
  · have hf_at_y : f.IsRestricted ‖y‖ :=
      TauCeti.PowerSeries.isRestricted_of_abs_le (c := ‖y‖) hfx (by simpa using hyx)
    have hsum := (summable_smul_pow_iff_isRestricted_norm (f := h) (x := y)).mpr
      (hop ‖y‖ hf_at_y hgy)
    exact hry.le.trans (le_convergenceRadius_of_summable hsum)

/-- The pointwise convergence radius of a sum is at least the minimum of the two pointwise
convergence radii. -/
theorem min_convergenceRadius_le_convergenceRadius_add (f g : R⟦X⟧) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ (f + g).convergenceRadius A :=
  min_convergenceRadius_le_of_isRestricted fun _ hf hg ↦ hf.add hg

/-- The pointwise convergence radius of a product is at least the minimum of the two pointwise
convergence radii. -/
theorem min_convergenceRadius_le_convergenceRadius_mul [IsUltrametricDist R] (f g : R⟦X⟧) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ (f * g).convergenceRadius A :=
  min_convergenceRadius_le_of_isRestricted fun _ hf hg ↦ hf.mul hg

/-- **Pointwise convergence radius equals intrinsic radius when positive norms are dense.**
If `Set.Ioi 0 ⊆ closure (Set.range norm)` in a complete ultrametric normed `R`-algebra `A` with
multiplicative norm and isometric scalar action, then `f.convergenceRadius A = f.radius`. -/
theorem convergenceRadius_eq_radius_of_Ioi_subset_closure_range_norm
    (hdense : Set.Ioi (0 : ℝ) ⊆ closure (Set.range (norm : A → ℝ))) (f : R⟦X⟧) :
    f.convergenceRadius A = f.radius := by
  refine le_antisymm (convergenceRadius_le_radius A f)
    (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
  obtain ⟨s, hrs, hsr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have hrs' : (r : ℝ) < (s : ℝ) := by exact_mod_cast ENNReal.coe_lt_coe.mp hrs
  have hm : ((r : ℝ) + (s : ℝ)) / 2 ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]
    linarith [r.coe_nonneg]
  have hopen : Set.Ioo (r : ℝ) (s : ℝ) ∈ 𝓝 (((r : ℝ) + (s : ℝ)) / 2) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  obtain ⟨_, ⟨hmem, x, rfl⟩⟩ := mem_closure_iff_nhds.mp (hdense hm) _ hopen
  have hxs : ‖x‖ₑ < (s : ℝ≥0∞) := by
    rw [eNorm_eq_nnNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm]
    exact hmem.2
  have hrx : (r : ℝ≥0∞) ≤ ‖x‖ₑ := by
    rw [eNorm_eq_nnNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
    exact hmem.1.le
  exact hrx.trans <|
    le_convergenceRadius_of_summable (summable_smul_pow_of_lt_radius (hxs.trans hsr))

/-- **Over a complete ultrametric densely normed field, the pointwise convergence radius equals the
intrinsic radius.** -/
theorem convergenceRadius_eq_radius (L : Type*) [DenselyNormedField L] [Algebra R L]
    [NormSMulClass R L] [IsUltrametricDist L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergenceRadius L = f.radius :=
  convergenceRadius_eq_radius_of_Ioi_subset_closure_range_norm
    (NormedField.Ioi_subset_closure_range_norm L) f

/-- **Over a complete ultrametric algebraically closed nontrivially normed field, the pointwise
convergence radius equals the intrinsic radius.** -/
theorem convergenceRadius_eq_radius_of_isAlgClosed (L : Type*) [NontriviallyNormedField L]
    [IsAlgClosed L] [Algebra R L] [NormSMulClass R L] [IsUltrametricDist L] [CompleteSpace L]
    (f : R⟦X⟧) :
    f.convergenceRadius L = f.radius :=
  convergenceRadius_eq_radius_of_Ioi_subset_closure_range_norm
    (NormedField.Ioi_subset_closure_range_norm_of_isAlgClosed L) f

end CompleteUltrametric

section NormGap

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [NormMulClass A] [SMul R A]
  [NormSMulClass R A] {f : R⟦X⟧} {r s : ℝ}

/-- If `f.radius ≤ ENNReal.ofReal s` and every element of `A` of norm at most `s` in fact has norm
at most `r` (so `A` has no norms in `(r, s]`), then `f.convergenceRadius A ≤ ENNReal.ofReal r`. -/
theorem convergenceRadius_le_ofReal_of_forall_norm_le (hs : 0 ≤ s)
    (hf : f.radius ≤ ENNReal.ofReal s) (hgap : ∀ x : A, ‖x‖ ≤ s → ‖x‖ ≤ r) :
    f.convergenceRadius A ≤ ENNReal.ofReal r := by
  refine convergenceRadius_le_iff.mpr fun x hx ↦ ?_
  have hxs : ‖x‖ ≤ s := by
    have h := (le_radius_of_summable hx).trans hf
    rwa [eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal hs, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe, coe_nnNorm] at h
  have hxr : ‖x‖ ≤ r := hgap x hxs
  rw [eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal ((norm_nonneg x).trans hxr),
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
  exact hxr

/-- If `f.radius ≤ ENNReal.ofReal s`, `f` is not restricted at `s`, and every element of `A` of
norm strictly below `s` has norm at most `r` (so `A` has no norms in `(r, s)`), then
`f.convergenceRadius A ≤ ENNReal.ofReal r`. -/
theorem convergenceRadius_le_ofReal_of_not_isRestricted (hs : 0 ≤ s)
    (hf : f.radius ≤ ENNReal.ofReal s) (hns : ¬f.IsRestricted s)
    (hgap : ∀ x : A, ‖x‖ < s → ‖x‖ ≤ r) :
    f.convergenceRadius A ≤ ENNReal.ofReal r := by
  refine convergenceRadius_le_iff.mpr fun x hx ↦ ?_
  have hxs : ‖x‖ ≤ s := by
    have h := (le_radius_of_summable hx).trans hf
    rwa [eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal hs, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe, coe_nnNorm] at h
  have hlt : ‖x‖ < s := hxs.lt_of_ne fun heq ↦ hns (isRestricted_of_summable_of_norm_eq hx heq)
  have hxr : ‖x‖ ≤ r := hgap x hlt
  rw [eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal ((norm_nonneg x).trans hxr),
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
  exact hxr

/-- Exact pointwise convergence radius across a half-closed norm gap `(r, s]`: if `r` is attained
by the norm of an element of a complete ultrametric algebra `A`, `ENNReal.ofReal r < f.radius ≤
ENNReal.ofReal s`, and `A` has no norms in `(r, s]`, then
`f.convergenceRadius A = ENNReal.ofReal r`. -/
theorem convergenceRadius_eq_ofReal_of_forall_norm_le {R A : Type*} [NormedCommRing R]
    [NormedRing A] [NormMulClass A] [Algebra R A] [NormSMulClass R A] [IsUltrametricDist A]
    [CompleteSpace A] {f : R⟦X⟧} {r s : ℝ} (hr : ∃ x : A, ‖x‖ = r) (hs : 0 ≤ s)
    (hlb : ENNReal.ofReal r < f.radius) (hub : f.radius ≤ ENNReal.ofReal s)
    (hgap : ∀ x : A, ‖x‖ ≤ s → ‖x‖ ≤ r) :
    f.convergenceRadius A = ENNReal.ofReal r := by
  refine le_antisymm (convergenceRadius_le_ofReal_of_forall_norm_le hs hub hgap) ?_
  obtain ⟨x, rfl⟩ := hr
  have hx : ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
    rw [eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg x)]
    rfl
  exact hx ▸ le_convergenceRadius_of_summable (summable_smul_pow_of_lt_radius (hx.trans_lt hlb))

/-- Exact pointwise convergence radius across an open norm gap `(r, s)` when `f` is not restricted
at the upper endpoint `s`. -/
theorem convergenceRadius_eq_ofReal_of_not_isRestricted {R A : Type*} [NormedCommRing R]
    [NormedRing A] [NormMulClass A] [Algebra R A] [NormSMulClass R A] [IsUltrametricDist A]
    [CompleteSpace A] {f : R⟦X⟧} {r s : ℝ} (hr : ∃ x : A, ‖x‖ = r) (hs : 0 ≤ s)
    (hlb : ENNReal.ofReal r < f.radius) (hub : f.radius ≤ ENNReal.ofReal s)
    (hns : ¬f.IsRestricted s) (hgap : ∀ x : A, ‖x‖ < s → ‖x‖ ≤ r) :
    f.convergenceRadius A = ENNReal.ofReal r := by
  refine le_antisymm (convergenceRadius_le_ofReal_of_not_isRestricted hs hub hns hgap) ?_
  obtain ⟨x, rfl⟩ := hr
  have hx : ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
    rw [eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg x)]
    rfl
  exact hx ▸ le_convergenceRadius_of_summable (summable_smul_pow_of_lt_radius (hx.trans_lt hlb))

end NormGap

end ComparisonWithRadius

end ConvergenceRadius

section Exp

variable {R A : Type*} [NormedCommRing R] [NormOneClass R] [Algebra ℚ R]
  [NormedRing A] [Algebra R A] [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A]

/-- Wherever `PowerSeries.exp R` is restricted at `‖x‖` in a complete ultrametric normed
`R`-algebra, the evaluated exponential identity gives `(exp R).evalAt x * (exp R).evalAt (-x) = 1`.
The target algebra `A` need not be commutative. -/
theorem evalAt_exp_mul_evalAt_exp_neg_of_isRestricted {x : A}
    (hx : (exp R).IsRestricted ‖x‖) :
    (exp R).evalAt x * (exp R).evalAt (-x) = 1 := by
  have hneg : (rescale (-1 : R) (exp R)).IsRestricted ‖x‖ :=
    IsRestricted.rescale (by simpa using hx)
  have hmul := hx.evalAt_mul hneg (le_rfl : ‖x‖ ≤ ‖x‖)
  have hid : exp R * rescale (-1 : R) (exp R) = 1 := by
    simpa using rescale_exp_mul_rescale_neg_exp (1 : R)
  rw [hid, evalAt_one, evalAt_rescale, neg_one_smul] at hmul
  exact hmul.symm

/-- Wherever `PowerSeries.exp R` is restricted at `‖x‖` in a complete ultrametric normed
`R`-algebra, `(exp R).evalAt x` is a unit with two-sided inverse `(exp R).evalAt (-x)`. -/
theorem isUnit_evalAt_exp_of_isRestricted {x : A} (hx : (exp R).IsRestricted ‖x‖) :
    IsUnit ((exp R).evalAt x) := by
  refine ⟨⟨(exp R).evalAt x, (exp R).evalAt (-x), evalAt_exp_mul_evalAt_exp_neg_of_isRestricted hx,
    ?_⟩, rfl⟩
  simpa only [neg_neg] using
    evalAt_exp_mul_evalAt_exp_neg_of_isRestricted (x := -x) (by simpa using hx)

/-- Wherever `PowerSeries.exp R` is restricted at `‖x‖` in a nontrivial complete ultrametric normed
`R`-algebra, `(exp R).evalAt x ≠ 0`. -/
theorem evalAt_exp_ne_zero_of_isRestricted [Nontrivial A] {x : A}
    (hx : (exp R).IsRestricted ‖x‖) : (exp R).evalAt x ≠ 0 :=
  (isUnit_evalAt_exp_of_isRestricted hx).ne_zero

/-- Throughout the open disc `‖x‖ₑ < (exp R).radius` in a complete ultrametric normed `R`-algebra,
`(exp R).evalAt x` is a unit. -/
theorem isUnit_evalAt_exp_of_lt_radius {x : A} (hx : ‖x‖ₑ < (exp R).radius) :
    IsUnit ((exp R).evalAt x) :=
  isUnit_evalAt_exp_of_isRestricted (isRestricted_of_lt_radius (by simpa using hx))

/-- **Nonvanishing of the ultrametric exponential.** Throughout the open disc
`‖x‖ₑ < (exp R).radius` in a nontrivial complete ultrametric normed `R`-algebra,
`(exp R).evalAt x ≠ 0`. -/
theorem evalAt_exp_ne_zero_of_lt_radius [Nontrivial A] {x : A} (hx : ‖x‖ₑ < (exp R).radius) :
    (exp R).evalAt x ≠ 0 :=
  (isUnit_evalAt_exp_of_lt_radius hx).ne_zero

end Exp

end PowerSeries
