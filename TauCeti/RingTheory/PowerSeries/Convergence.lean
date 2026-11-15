/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Radius

/-!
# Pointwise convergence of power series in normed algebras and extensions

Let `f = ∑ aₙ Xⁿ` be a power series over a commutative normed ring `R` and `A` a normed `R`-algebra
whose scalar action and multiplication preserve norms (`NormSMulClass R A`, `NormMulClass A`), such
as any isometric normed field extension `L / K`. For `n ≥ 1` the individual term `aₙ • x ^ n` at
`x : A` has norm `‖aₙ‖ * ‖x‖ ^ n`. Consequently the terms at `x` tend to zero if and only if `f` is
restricted at the numerical radius `‖x‖`, and convergence of `∑ aₙ • x ^ n` forces restrictedness
at `‖x‖` (hence `‖x‖ₑ ≤ f.radius`) without any completeness or ultrametric hypothesis.

When `A` is complete and ultrametric, summability is equivalent to decay of the individual terms,
so convergence of `∑ aₙ • x ^ n` at `x` is equivalent to `f.IsRestricted ‖x‖`. Convergence at a
single point of norm `r` therefore implies convergence throughout the closed disc
`{y : A | ‖y‖ ≤ r}`, bounded in norm by `gaussNorm norm r f` when `‖1‖ = 1`; conversely,
convergence throughout `{y : A | ‖y‖ ≤ r}` implies `f.IsRestricted r` provided the numerical
radius `r` is attained as the norm of an element of `A`.

To compare pointwise convergence in a specific target algebra `A` with the coefficient-intrinsic
radius `PowerSeries.radius f`, this file defines `PowerSeries.convergenceRadius A f`, the supremum
in `ℝ≥0∞` of `‖x‖ₑ` over the points `x : A` at which `∑ aₙ • x ^ n` is summable. It satisfies
`f.convergenceRadius A ≤ f.radius`, agrees with `⨆ (x : A) (_ : f.IsRestricted ‖x‖), ‖x‖ₑ` when `A`
is complete and ultrametric, and equals `f.radius` whenever the positive norms of `A` are dense in
`(0, ∞)` — in particular over any complete ultrametric `DenselyNormedField` such as `ℂ_[p]`. When
the norms of `A` omit an interval `(r, c)` containing `f.radius`, as happens over discretely valued
fields, the inequality `f.convergenceRadius A < f.radius` is strict.

## Main definitions

* `PowerSeries.convergenceRadius A f`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over the points `x : A` at
  which `∑ aₙ • x ^ n` converges.

## Main results

* `PowerSeries.tendsto_smul_pow_cofinite_nhds_zero_iff_isRestricted` and
  `PowerSeries.isRestricted_of_summable_smul_pow`: decay or summability of the terms at `x` gives
  `f.IsRestricted ‖x‖`, hence `‖x‖ₑ ≤ f.radius` (`PowerSeries.le_radius_of_summable_smul_pow`).
* `PowerSeries.summable_smul_pow_iff_isRestricted` and `PowerSeries.hasSum_evalAt_iff_isRestricted`:
  in a complete ultrametric algebra with multiplicative scalar and ring norms, convergence at `x`
  is equivalent to restrictedness at `‖x‖`.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm`,
  `PowerSeries.hasSum_evalAt_of_norm_le_of_summable_smul_pow`, and
  `PowerSeries.forall_norm_le_summable_smul_pow_iff_isRestricted`: closed-disc convergence and
  Gauss-norm bounds, and restrictedness from closed-ball convergence at an attained radius.
* `PowerSeries.convergenceRadius_le_radius`, `PowerSeries.convergenceRadius_eq_iSup_isRestricted`,
  `PowerSeries.convergenceRadius_eq_top_iff`, `PowerSeries.convergenceRadius_pos_iff`,
  `PowerSeries.convergenceRadius_eq_radius_of_Ioi_subset_closure`, and
  `PowerSeries.convergenceRadius_eq_radius`: comparison between the convergence-point supremum and
  the intrinsic radius, matching top and positivity over any complete ultrametric nontrivially
  normed field and full equality under dense positive norms.
* `PowerSeries.convergenceRadius_eq_ofReal_of_norm_le_or_le` and
  `PowerSeries.convergenceRadius_lt_radius_of_norm_le_or_le`: exact value and strict inequality in
  the presence of a gap `(r, c)` in the norms of `A`.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren der mathematischen
  Wissenschaften 261, Springer, 1984, §5.1.4.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Graduate Texts in
  Mathematics 58, Springer, 1984, Chapter IV, §§1, 4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace PowerSeries

open Filter
open scoped NNReal ENNReal Topology

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The **convergence-point radius** of a power series `f = ∑ aₙ Xⁿ` in a seminormed `R`-algebra
`A`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over the points `x : A` at which `∑ₙ aₙ • x ^ n` is summable.
Unlike `PowerSeries.radius`, this supremum ranges only over norms attained in `A`. -/
noncomputable def convergenceRadius (A : Type*) [SeminormedRing A] [Algebra R A] (f : R⟦X⟧) :
    ℝ≥0∞ :=
  ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ

/-- `PowerSeries.convergenceRadius A f` as the supremum of extended norms of convergence points in
`A`. -/
theorem convergenceRadius_def (A : Type*) [SeminormedRing A] [Algebra R A] (f : R⟦X⟧) :
    f.convergenceRadius A = ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ :=
  (rfl)

section SeminormedRing

variable {A : Type*} [SeminormedRing A] [Algebra R A] {f : R⟦X⟧} {x : A}

/-- Every point at which `f` is summable bounds `f.convergenceRadius A` from below. -/
theorem le_convergenceRadius_of_summable (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.convergenceRadius A :=
  le_iSup₂ (f := fun (y : A) (_ : Summable fun n ↦ coeff n f • y ^ n) ↦ ‖y‖ₑ) x h

/-- Every point at which `f` has a sum bounds `f.convergenceRadius A` from below. -/
theorem le_convergenceRadius_of_hasSum {y : A} (h : HasSum (fun n ↦ coeff n f • x ^ n) y) :
    ‖x‖ₑ ≤ f.convergenceRadius A :=
  f.le_convergenceRadius_of_summable h.summable

/-- `f.convergenceRadius A` is at most `r` exactly when every convergence point has extended norm
at most `r`. -/
theorem convergenceRadius_le_iff {r : ℝ≥0∞} :
    f.convergenceRadius A ≤ r ↔ ∀ x : A, (Summable fun n ↦ coeff n f • x ^ n) → ‖x‖ₑ ≤ r :=
  iSup₂_le_iff

/-- A radius `r` is strictly below `f.convergenceRadius A` exactly when `f` is summable at some
point `x : A` with `r < ‖x‖ₑ`. -/
theorem lt_convergenceRadius_iff {r : ℝ≥0∞} :
    r < f.convergenceRadius A ↔ ∃ x : A, (Summable fun n ↦ coeff n f • x ^ n) ∧ r < ‖x‖ₑ := by
  simp [convergenceRadius_def, lt_iSup_iff]

/-- A polynomial converges at every point of `A`, so its convergence-point radius in `A` is the
supremum of all extended norms in `A`. -/
theorem convergenceRadius_coe_eq_iSup (A : Type*) [SeminormedRing A] [Algebra R A]
    (p : Polynomial R) : (p : R⟦X⟧).convergenceRadius A = ⨆ x : A, ‖x‖ₑ := by
  have hsum (x : A) : Summable fun n ↦ p.coeff n • x ^ n :=
    summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn ↦ by
      rw [Finset.mem_range, not_lt] at hn
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  simp [convergenceRadius_def, hsum]

/-- Extension of scalars preserves the convergence-point radius. -/
@[simp]
theorem convergenceRadius_map_algebraMap {S : Type*} [CommSemiring S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] (f : R⟦X⟧) :
    (f.map (algebraMap R S)).convergenceRadius A = f.convergenceRadius A := by
  simp [convergenceRadius_def]

end SeminormedRing

section NontriviallyNormedField

variable (L : Type*) [NontriviallyNormedField L] [Algebra R L]

/-- Over a nontrivially normed field `L`, every polynomial has infinite convergence-point radius,
regardless of the norms of its roots. -/
@[simp]
theorem convergenceRadius_coe (p : Polynomial R) : (p : R⟦X⟧).convergenceRadius L = ⊤ := by
  rw [convergenceRadius_coe_eq_iSup]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨x, hx⟩ := NormedField.exists_lt_eNorm L (ENNReal.coe_ne_top : (r : ℝ≥0∞) ≠ ⊤)
  exact hx.le.trans (le_iSup (fun y : L ↦ ‖y‖ₑ) x)

/-- Over a nontrivially normed field `L`, the zero series has infinite convergence-point radius. -/
@[simp]
theorem convergenceRadius_zero : (0 : R⟦X⟧).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe L (0 : Polynomial R)

/-- Over a nontrivially normed field `L`, the constant series `1` has infinite convergence-point
radius. -/
@[simp]
theorem convergenceRadius_one : (1 : R⟦X⟧).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe L (1 : Polynomial R)

/-- Over a nontrivially normed field `L`, every constant series has infinite convergence-point
radius. -/
@[simp]
theorem convergenceRadius_C (a : R) : (C a : R⟦X⟧).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe L (Polynomial.C a)

/-- Over a nontrivially normed field `L`, `X` has infinite convergence-point radius. -/
@[simp]
theorem convergenceRadius_X : (X : R⟦X⟧).convergenceRadius L = ⊤ := by
  simpa using convergenceRadius_coe L (Polynomial.X : Polynomial R)

end NontriviallyNormedField

end Semiring

section Ring

variable {R A B : Type*} [CommRing R] [SeminormedRing A] [SeminormedRing B]
  [Algebra R A] [Algebra R B]

/-- Negating a power series preserves its convergence-point radius. -/
@[simp]
theorem convergenceRadius_neg (f : R⟦X⟧) : (-f).convergenceRadius A = f.convergenceRadius A := by
  simp only [convergenceRadius_def, map_neg, neg_smul, summable_neg_iff]

/-- An isometric `R`-algebra homomorphism `A →ₐ[R] B` can only enlarge the convergence-point
radius: every convergence point in `A` pushes forward to a convergence point of the same norm in
`B`. -/
theorem convergenceRadius_le_convergenceRadius_of_norm_eq (ψ : A →ₐ[R] B)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (f : R⟦X⟧) :
    f.convergenceRadius A ≤ f.convergenceRadius B := by
  have hisom : Isometry ψ := AddMonoidHomClass.isometry_of_norm ψ hψ
  refine iSup₂_le fun x hx ↦ ?_
  have hsum : Summable fun n ↦ coeff n f • (ψ x) ^ n := by
    simpa only [Function.comp_def, map_smul, map_pow] using hx.map ψ hisom.continuous
  have hnorm : ‖ψ x‖ₑ = ‖x‖ₑ := by simp [eNorm_eq_nnNorm, ← NNReal.coe_inj, hψ]
  exact hnorm ▸ f.le_convergenceRadius_of_summable hsum

/-- Isometric `R`-algebra equivalences preserve the convergence-point radius. -/
theorem convergenceRadius_congr_algEquiv (ψ : A ≃ₐ[R] B) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (f : R⟦X⟧) :
    f.convergenceRadius A = f.convergenceRadius B :=
  le_antisymm (f.convergenceRadius_le_convergenceRadius_of_norm_eq ψ.toAlgHom hψ)
    (f.convergenceRadius_le_convergenceRadius_of_norm_eq ψ.symm.toAlgHom fun y ↦ by
      simpa using (hψ (ψ.symm y)).symm)

end Ring

section TermNorms

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A]
  [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- Positive powers preserve the norm in any ring with `NormMulClass`, without assuming
`NormOneClass`. -/
private theorem norm_pow_succ (x : A) (n : ℕ) : ‖x ^ (n + 1)‖ = ‖x‖ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ x (n + 1), norm_mul, ih, pow_succ ‖x‖ (n + 1)]

/-- For `n ≠ 0`, the `n`-th term `aₙ • x ^ n` has norm `‖aₙ‖ * ‖x‖ ^ n`. -/
theorem norm_coeff_smul_pow {n : ℕ} (hn : n ≠ 0) :
    ‖coeff n f • x ^ n‖ = ‖coeff n f‖ * ‖x‖ ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [norm_smul, norm_pow_succ]

/-- **Term decay vs restrictedness.** The terms `aₙ • x ^ n` tend to zero along `cofinite` if and
only if `f` is restricted at `‖x‖`. -/
theorem tendsto_smul_pow_cofinite_nhds_zero_iff_isRestricted :
    Tendsto (fun n ↦ coeff n f • x ^ n) cofinite (𝓝 0) ↔ f.IsRestricted ‖x‖ := by
  rw [tendsto_zero_iff_norm_tendsto_zero, isRestricted_iff]
  refine tendsto_congr' ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
  exact f.norm_coeff_smul_pow (Set.mem_compl_singleton_iff.mp hn)

/-- **Term decay vs restrictedness (`atTop` form).** The terms `aₙ • x ^ n` tend to zero as
`n → ∞` if and only if `f` is restricted at `‖x‖`. -/
theorem tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted :
    Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0) ↔ f.IsRestricted ‖x‖ := by
  rw [← Nat.cofinite_eq_atTop, tendsto_smul_pow_cofinite_nhds_zero_iff_isRestricted]

/-- If `∑ aₙ • x ^ n` is summable, then `f` is restricted at `‖x‖`. Neither completeness nor an
ultrametric norm is needed. -/
theorem isRestricted_of_summable_smul_pow (h : Summable fun n ↦ coeff n f • x ^ n) :
    f.IsRestricted ‖x‖ :=
  tendsto_smul_pow_cofinite_nhds_zero_iff_isRestricted.mp h.tendsto_cofinite_zero

/-- If `∑ aₙ • x ^ n` is summable and `|r| ≤ ‖x‖`, then `f` is restricted at `r`. -/
theorem isRestricted_of_abs_le_norm_of_summable_smul_pow (hr : |r| ≤ ‖x‖)
    (h : Summable fun n ↦ coeff n f • x ^ n) : f.IsRestricted r :=
  TauCeti.PowerSeries.isRestricted_of_abs_le (f.isRestricted_of_summable_smul_pow h)
    (by rwa [abs_norm])

/-- Convergence on all points of the closed ball `{y : A | ‖y‖ ≤ r}` implies restrictedness at `r`
whenever `r` is attained as the norm of an element `x : A`. -/
theorem isRestricted_of_forall_norm_le_summable_smul_pow (hx : ‖x‖ = r)
    (h : ∀ y : A, ‖y‖ ≤ r → Summable fun n ↦ coeff n f • y ^ n) : f.IsRestricted r :=
  hx ▸ f.isRestricted_of_summable_smul_pow (h x hx.le)

/-- Every convergence point of `f` in `A` has extended norm at most the intrinsic radius of `f`. -/
theorem le_radius_of_summable_smul_pow (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.radius := by
  simpa [eNorm_eq_nnNorm] using le_radius_of_isRestricted (f.isRestricted_of_summable_smul_pow h)

/-- **Upper bound by the intrinsic radius.** The convergence-point supremum in `A` never exceeds
the intrinsic radius `f.radius`. -/
theorem convergenceRadius_le_radius (A : Type*) [NormedRing A] [Algebra R A]
    [NormSMulClass R A] [NormMulClass A] (f : R⟦X⟧) :
    f.convergenceRadius A ≤ f.radius :=
  iSup₂_le fun _ hx ↦ f.le_radius_of_summable_smul_pow hx

/-- If every element of `A` has norm at most `r` or at least `c ≥ 0` (so the open interval `(r, c)`
contains no norms of `A`), and `f` is not restricted at `c`, then `f.convergenceRadius A` is at
most `ENNReal.ofReal r`. -/
theorem convergenceRadius_le_ofReal_of_norm_le_or_le {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ y : A, ‖y‖ ≤ r ∨ c ≤ ‖y‖) (hnc : ¬f.IsRestricted c) :
    f.convergenceRadius A ≤ ENNReal.ofReal r := by
  refine iSup₂_le fun y hy ↦ ?_
  have hres := f.isRestricted_of_summable_smul_pow hy
  rcases hgap y with hyr | hcy
  · rw [eNorm_eq_nnNorm, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
    exact ENNReal.ofReal_le_ofReal hyr
  · refine (hnc (TauCeti.PowerSeries.isRestricted_of_abs_le hres ?_)).elim
    rwa [abs_of_nonneg hc, abs_norm]

end TermNorms

section BoundedSMulUltrametric

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A]
  [IsBoundedSMul R A] [IsUltrametricDist A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- **Closed-disc evaluation bound.** In an ultrametric normed algebra with `‖1‖ = 1`, if `f` is
restricted at `r`, then at every point `b` with `‖b‖ ≤ r` the value `f.evalAt b` has norm at most
`gaussNorm norm r f`. -/
theorem IsRestricted.norm_evalAt_le_gaussNorm [NormOneClass A] (hf : f.IsRestricted r) {b : A}
    (hb : ‖b‖ ≤ r) : ‖f.evalAt b‖ ≤ gaussNorm norm r f :=
  PowerSeries.norm_evalAt_le_gaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf) hb

variable [CompleteSpace A]

/-- In a complete ultrametric normed algebra, `f` converges to `f.evalAt x` at every point strictly
inside `f.radius`. -/
theorem hasSum_evalAt_of_lt_radius (hx : ‖x‖ₑ < f.radius) :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) :=
  (isRestricted_of_lt_radius (by simpa [eNorm_eq_nnNorm] using hx)).hasSum_evalAt le_rfl

/-- In a complete ultrametric normed algebra, the terms of `f` at `x` are summable whenever
`‖x‖ₑ < f.radius`. -/
theorem summable_smul_pow_of_lt_radius (hx : ‖x‖ₑ < f.radius) :
    Summable fun n ↦ coeff n f • x ^ n :=
  (f.hasSum_evalAt_of_lt_radius hx).summable

/-- In a complete ultrametric normed algebra, restrictedness at `‖x‖` gives
`‖x‖ₑ ≤ f.convergenceRadius A`. -/
theorem le_convergenceRadius_of_isRestricted (hf : f.IsRestricted ‖x‖) :
    ‖x‖ₑ ≤ f.convergenceRadius A :=
  f.le_convergenceRadius_of_hasSum (hf.hasSum_evalAt le_rfl)

/-- In a complete ultrametric normed algebra, every point with `‖x‖ₑ < f.radius` has extended norm
at most `f.convergenceRadius A`. -/
theorem le_convergenceRadius_of_lt_radius (hx : ‖x‖ₑ < f.radius) :
    ‖x‖ₑ ≤ f.convergenceRadius A :=
  f.le_convergenceRadius_of_summable (f.summable_smul_pow_of_lt_radius hx)

/-- Over any complete ultrametric nontrivially normed field `L`, an entire series has infinite
convergence-point radius. -/
theorem IsEntire.convergenceRadius_eq_top (L : Type*) [NontriviallyNormedField L] [Algebra R L]
    [IsBoundedSMul R L] [IsUltrametricDist L] [CompleteSpace L] (hf : f.IsEntire) :
    f.convergenceRadius L = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨y, hy⟩ := NormedField.exists_lt_eNorm L (ENNReal.coe_ne_top : (r : ℝ≥0∞) ≠ ⊤)
  exact hy.le.trans (f.le_convergenceRadius_of_isRestricted (hf.isRestricted ‖y‖))

end BoundedSMulUltrametric

section UltrametricEquivalence

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A]
  [NormSMulClass R A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
  {f g : R⟦X⟧} {x : A} {r : ℝ}

/-- **Convergence at a point vs restrictedness.** In a complete ultrametric normed algebra with
multiplicative scalar and ring norms, `∑ aₙ • x ^ n` is summable if and only if `f` is restricted
at `‖x‖`. -/
theorem summable_smul_pow_iff_isRestricted :
    (Summable fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted ‖x‖ :=
  ⟨f.isRestricted_of_summable_smul_pow, fun hf ↦ (hf.hasSum_evalAt le_rfl).summable⟩

/-- At a point `x` of norm `r`, `∑ aₙ • x ^ n` is summable if and only if `f` is restricted at
`r`. -/
theorem summable_smul_pow_iff_isRestricted_of_norm_eq (hx : ‖x‖ = r) :
    (Summable fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted r :=
  hx ▸ f.summable_smul_pow_iff_isRestricted

/-- In a complete ultrametric normed algebra with multiplicative scalar and ring norms,
`∑ aₙ • x ^ n` sums to `f.evalAt x` if and only if `f` is restricted at `‖x‖`. -/
theorem hasSum_evalAt_iff_isRestricted :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) ↔ f.IsRestricted ‖x‖ :=
  ⟨fun h ↦ f.isRestricted_of_summable_smul_pow h.summable, fun hf ↦ hf.hasSum_evalAt le_rfl⟩

/-- **Closed-disc convergence from convergence at one point.** If `f` converges at `x`, then `f`
converges to `f.evalAt y` at every `y : A` with `‖y‖ ≤ ‖x‖`. -/
theorem hasSum_evalAt_of_norm_le_of_summable_smul_pow {y : A} (hy : ‖y‖ ≤ ‖x‖)
    (h : Summable fun n ↦ coeff n f • x ^ n) :
    HasSum (fun n ↦ coeff n f • y ^ n) (f.evalAt y) :=
  (f.isRestricted_of_summable_smul_pow h).hasSum_evalAt hy

omit [CompleteSpace A] in
/-- **Closed-disc evaluation bound from convergence at one point.** If `f` converges at `x` and
`‖1‖ = 1` in `A`, then `‖f.evalAt y‖ ≤ gaussNorm norm ‖x‖ f` for every `y : A` with `‖y‖ ≤ ‖x‖`. -/
theorem norm_evalAt_le_gaussNorm_of_summable_smul_pow [NormOneClass A] {y : A} (hy : ‖y‖ ≤ ‖x‖)
    (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖f.evalAt y‖ ≤ gaussNorm norm ‖x‖ f :=
  (f.isRestricted_of_summable_smul_pow h).norm_evalAt_le_gaussNorm hy

/-- **Closed-ball convergence vs restrictedness.** When the numerical radius `r` is attained by the
norm of an element of `A`, summability throughout the closed ball `{y : A | ‖y‖ ≤ r}` is equivalent
to `f.IsRestricted r`. -/
theorem forall_norm_le_summable_smul_pow_iff_isRestricted (hr : ∃ x : A, ‖x‖ = r) :
    (∀ y : A, ‖y‖ ≤ r → Summable fun n ↦ coeff n f • y ^ n) ↔ f.IsRestricted r := by
  obtain ⟨x, rfl⟩ := hr
  exact ⟨f.isRestricted_of_forall_norm_le_summable_smul_pow rfl,
    fun hf _ hy ↦ (hf.hasSum_evalAt hy).summable⟩

/-- When `r` is attained by the norm of an element of `A`, convergence to `f.evalAt` throughout
`{y : A | ‖y‖ ≤ r}` is equivalent to `f.IsRestricted r`. -/
theorem forall_norm_le_hasSum_evalAt_iff_isRestricted (hr : ∃ x : A, ‖x‖ = r) :
    (∀ y : A, ‖y‖ ≤ r → HasSum (fun n ↦ coeff n f • y ^ n) (f.evalAt y)) ↔ f.IsRestricted r := by
  obtain ⟨x, rfl⟩ := hr
  refine ⟨fun h ↦ f.isRestricted_of_forall_norm_le_summable_smul_pow rfl fun y hy ↦ ?_,
    fun hf _ hy ↦ hf.hasSum_evalAt hy⟩
  exact (h y hy).summable

/-- **Restrictedness description of `convergenceRadius`.** In a complete ultrametric normed algebra
with multiplicative scalar and ring norms, `f.convergenceRadius A` is the supremum of `‖x‖ₑ` over
those `x : A` at whose norm `f` is restricted. -/
theorem convergenceRadius_eq_iSup_isRestricted (A : Type*) [NormedRing A] [Algebra R A]
    [NormSMulClass R A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] (f : R⟦X⟧) :
    f.convergenceRadius A = ⨆ (x : A) (_ : f.IsRestricted ‖x‖), ‖x‖ₑ := by
  simp_rw [convergenceRadius_def, summable_smul_pow_iff_isRestricted]

/-- In a complete ultrametric normed algebra with multiplicative scalar and ring norms, `s` is
strictly below `f.convergenceRadius A` iff `f` is restricted at `‖x‖` for some `x : A` with
`s < ‖x‖ₑ`. -/
theorem lt_convergenceRadius_iff_exists_isRestricted {s : ℝ≥0∞} :
    s < f.convergenceRadius A ↔ ∃ x : A, f.IsRestricted ‖x‖ ∧ s < ‖x‖ₑ := by
  simp [convergenceRadius_eq_iSup_isRestricted, lt_iSup_iff]

/-- If the coefficients of `g` are no larger in norm than those of `f`, then the convergence-point
radius of `g` in `A` is at least that of `f`. -/
theorem convergenceRadius_le_convergenceRadius_of_norm_coeff_le {S : Type*} [NormedCommRing S]
    [Algebra S A] [NormSMulClass S A] {g : S⟦X⟧} (h : ∀ n, ‖coeff n g‖ ≤ ‖coeff n f‖) :
    f.convergenceRadius A ≤ g.convergenceRadius A := by
  rw [convergenceRadius_eq_iSup_isRestricted, convergenceRadius_eq_iSup_isRestricted]
  refine iSup₂_le fun y hfy ↦ ?_
  have hgy : g.IsRestricted ‖y‖ := by
    rw [isRestricted_iff] at hfy ⊢
    exact squeeze_zero (fun _ ↦ by positivity)
      (fun n ↦ mul_le_mul_of_nonneg_right (h n) (by positivity)) hfy
  exact le_iSup₂ (f := fun (z : A) (_ : g.IsRestricted ‖z‖) ↦ ‖z‖ₑ) y hgy

/-- Any nonnegative radius strictly below both `f.convergenceRadius A` and `g.convergenceRadius A`
is strictly dominated by the extended norm of a single element `w : A` at whose norm both `f` and
`g` are restricted. -/
private theorem exists_isRestricted_and_lt_eNorm {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < min (f.convergenceRadius A) (g.convergenceRadius A)) :
    ∃ w : A, f.IsRestricted ‖w‖ ∧ g.IsRestricted ‖w‖ ∧ (s : ℝ≥0∞) < ‖w‖ₑ := by
  obtain ⟨y, hfy, hsy⟩ := lt_convergenceRadius_iff_exists_isRestricted.mp (lt_min_iff.mp hs).1
  obtain ⟨z, hgz, hsz⟩ := lt_convergenceRadius_iff_exists_isRestricted.mp (lt_min_iff.mp hs).2
  by_cases hyz : ‖y‖ ≤ ‖z‖
  · exact ⟨y, hfy, TauCeti.PowerSeries.isRestricted_of_abs_le hgz (by simpa using hyz), hsy⟩
  · refine ⟨z, ?_, hgz, hsz⟩
    exact TauCeti.PowerSeries.isRestricted_of_abs_le hfy (by simpa using le_of_not_ge hyz)

/-- The convergence-point radius of a sum is at least the minimum of the two convergence-point
radii. -/
theorem min_convergenceRadius_le_convergenceRadius_add (f g : R⟦X⟧) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ (f + g).convergenceRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun s hs ↦ ?_
  obtain ⟨w, hfw, hgw, hsw⟩ := exists_isRestricted_and_lt_eNorm hs
  exact hsw.le.trans ((f + g).le_convergenceRadius_of_isRestricted (hfw.add hgw))

/-- The convergence-point radius of a product is at least the minimum of the two convergence-point
radii. -/
theorem min_convergenceRadius_le_convergenceRadius_mul (f g : R⟦X⟧) :
    min (f.convergenceRadius A) (g.convergenceRadius A) ≤ (f * g).convergenceRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun s hs ↦ ?_
  obtain ⟨w, hfw, hgw, hsw⟩ := exists_isRestricted_and_lt_eNorm hs
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr fun hw ↦ by simp [hw] at hsw
  -- Positive-norm scalar action from `R` into ultrametric `A` transfers ultrametricity to `R`.
  have : IsUltrametricDist R := ⟨fun a b c ↦ le_of_mul_le_mul_right (a0 := hw0) <| by
    simpa [dist_eq_norm, ← sub_smul, norm_smul, max_mul_of_nonneg _ _ hw0.le] using
      dist_triangle_max (a • w) (b • w) (c • w)⟩
  exact hsw.le.trans ((f * g).le_convergenceRadius_of_isRestricted (hfw.mul hgw))

/-- Over any complete ultrametric nontrivially normed field `L` (even discretely valued), the
convergence-point radius is infinite if and only if `f` is entire. -/
@[simp]
theorem convergenceRadius_eq_top_iff (L : Type*) [NontriviallyNormedField L] [Algebra R L]
    [NormSMulClass R L] [IsUltrametricDist L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergenceRadius L = ⊤ ↔ f.IsEntire :=
  ⟨fun h ↦ radius_eq_top_iff.mp (top_unique (h ▸ f.convergenceRadius_le_radius L)),
    fun hf ↦ hf.convergenceRadius_eq_top L⟩

/-- Over any complete ultrametric nontrivially normed field `L` (even discretely valued), the
convergence-point radius is positive if and only if the intrinsic radius is positive. -/
theorem convergenceRadius_pos_iff (L : Type*) [NontriviallyNormedField L] [Algebra R L]
    [NormSMulClass R L] [IsUltrametricDist L] [CompleteSpace L] (f : R⟦X⟧) :
    0 < f.convergenceRadius L ↔ 0 < f.radius := by
  refine ⟨fun h ↦ h.trans_le (f.convergenceRadius_le_radius L), fun h ↦ ?_⟩
  obtain ⟨y, hy0, hyr⟩ := NormedField.exists_eNorm_lt L h
  exact hy0.trans_le (f.le_convergenceRadius_of_lt_radius hyr)

/-- Over any complete ultrametric nontrivially normed field `L` (even discretely valued), the
convergence-point radius is zero if and only if the intrinsic radius is zero. -/
theorem convergenceRadius_eq_zero_iff (L : Type*) [NontriviallyNormedField L] [Algebra R L]
    [NormSMulClass R L] [IsUltrametricDist L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergenceRadius L = 0 ↔ f.radius = 0 := by
  rw [← not_iff_not, ← ne_eq, ← ne_eq, ← pos_iff_ne_zero, ← pos_iff_ne_zero,
    convergenceRadius_pos_iff]

/-- **Equality under norm separation.** If every open interval `(r, s)` with `0 ≤ r < s` contains
the norm of an element of `A`, then the convergence-point supremum `f.convergenceRadius A` equals
the intrinsic radius `f.radius`. -/
theorem convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt
    (hdense : ∀ r s : ℝ, 0 ≤ r → r < s → ∃ x : A, r < ‖x‖ ∧ ‖x‖ < s) (f : R⟦X⟧) :
    f.convergenceRadius A = f.radius := by
  refine le_antisymm (f.convergenceRadius_le_radius A)
    (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
  obtain ⟨s, hrs, hsf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  obtain ⟨x, hrx, hxs⟩ := hdense r s r.coe_nonneg (ENNReal.coe_lt_coe.mp hrs)
  have hxs' : ‖x‖ₑ < (s : ℝ≥0∞) := by
    rw [eNorm_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm]
    exact hxs
  have hrx' : (r : ℝ≥0∞) ≤ ‖x‖ₑ := by
    rw [eNorm_eq_nnNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
    exact hrx.le
  exact hrx'.trans (f.le_convergenceRadius_of_lt_radius (hxs'.trans hsf))

/-- **Equality under dense positive norms.** When the positive norms of `A` are dense in `(0, ∞)`,
the convergence-point supremum `f.convergenceRadius A` equals the intrinsic radius `f.radius`. -/
theorem convergenceRadius_eq_radius_of_Ioi_subset_closure
    (hdense : Set.Ioi (0 : ℝ) ⊆ closure ((‖·‖ : A → ℝ) '' {x : A | x ≠ 0})) (f : R⟦X⟧) :
    f.convergenceRadius A = f.radius := by
  refine f.convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt fun r s hr hlt ↦ ?_
  have hm : (r + s) / 2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  obtain ⟨_, ⟨x, -, rfl⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (hdense hm) ((s - r) / 2) (by linarith)
  rw [Real.dist_eq, abs_lt] at hdist
  exact ⟨x, by linarith, by linarith⟩

/-- **Equality over a densely normed complete ultrametric field.** In any complete ultrametric
densely normed field `L` over `R` (for instance `ℂ_[p]` over `ℚ_[p]` or `ℂ_[p]`), the
convergence-point supremum equals the intrinsic radius. -/
theorem convergenceRadius_eq_radius (L : Type*) [DenselyNormedField L] [Algebra R L]
    [NormSMulClass R L] [IsUltrametricDist L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergenceRadius L = f.radius :=
  f.convergenceRadius_eq_radius_of_forall_exists_lt_norm_lt
    fun _ _ ↦ NormedField.exists_lt_norm_lt L

/-- **Exact convergence-point radius across a norm gap.** If `r` is attained as the norm of an
element of `A`, `f` is restricted at `r` and not at `c ≥ 0`, and no element of `A` has norm in
`(r, c)`, then `f.convergenceRadius A = ENNReal.ofReal r`. -/
theorem convergenceRadius_eq_ofReal_of_norm_le_or_le {c : ℝ} (hc : 0 ≤ c) (hf : f.IsRestricted r)
    (hx : ∃ x : A, ‖x‖ = r) (hgap : ∀ y : A, ‖y‖ ≤ r ∨ c ≤ ‖y‖) (hnc : ¬f.IsRestricted c) :
    f.convergenceRadius A = ENNReal.ofReal r := by
  refine le_antisymm (f.convergenceRadius_le_ofReal_of_norm_le_or_le hc hgap hnc) ?_
  obtain ⟨x, rfl⟩ := hx
  rw [← coe_nnNorm, ENNReal.ofReal_coe_nnreal, ← eNorm_eq_nnNorm]
  exact f.le_convergenceRadius_of_isRestricted hf

/-- **Strict inequality across a norm gap.** When `f` is restricted at an attained norm `r` and its
intrinsic radius lies strictly inside a norm-free interval `(r, c)` of `A`, the convergence-point
supremum `f.convergenceRadius A` equals `ENNReal.ofReal r` and is strictly smaller than
`f.radius`. -/
theorem convergenceRadius_lt_radius_of_norm_le_or_le {c : ℝ} (hf : f.IsRestricted r)
    (hx : ∃ x : A, ‖x‖ = r) (hgap : ∀ y : A, ‖y‖ ≤ r ∨ c ≤ ‖y‖)
    (hrf : ENNReal.ofReal r < f.radius) (hfc : f.radius < ENNReal.ofReal c) :
    f.convergenceRadius A < f.radius := by
  have hc0 : 0 ≤ c := (ENNReal.ofReal_pos.mp (pos_of_gt hfc)).le
  have hnc : ¬f.IsRestricted c := not_isRestricted_of_radius_lt <| by
    rwa [Real.eNorm_eq_ofReal hc0]
  rwa [f.convergenceRadius_eq_ofReal_of_norm_le_or_le hc0 hf hx hgap hnc]

end UltrametricEquivalence

end PowerSeries
