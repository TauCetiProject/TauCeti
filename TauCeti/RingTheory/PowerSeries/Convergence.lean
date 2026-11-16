/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Radius
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Pointwise convergence of power series in normed algebras and extensions

Let `f = ∑ aₙ Xⁿ` be a power series over a commutative normed ring `R` and `A` a seminormed
`R`-algebra whose scalar action and multiplication preserve norms (`NormSMulClass R A`,
`NormMulClass A`), such as any isometric normed field extension `L / K`. For `n ≥ 1` the individual
term `aₙ • x ^ n` at `x : A` has norm `‖aₙ‖ * ‖x‖ ^ n`. Consequently the terms at `x` tend to zero
if and only if `f` is restricted at the numerical radius `‖x‖`, and convergence of `∑ aₙ • x ^ n`
forces restrictedness at `‖x‖` (hence `‖x‖ₑ ≤ f.radius`) without any completeness or ultrametric
hypothesis.

Conversely, at every point `x : A` strictly inside `f.radius` the terms `aₙ • x ^ n` are absolutely
summable (requiring only `IsBoundedSMul R A`), and therefore sum to `f.evalAt x` whenever `A` is
complete — with no ultrametric hypothesis. To compare pointwise convergence in a specific target
algebra `A` with the coefficient-intrinsic radius `PowerSeries.radius f`, this file defines
`PowerSeries.convergencePointRadius A f`, the supremum in `ℝ≥0∞` of `‖x‖ₑ` over the points `x : A`
at which `∑ aₙ • x ^ n` is summable. It satisfies `f.convergencePointRadius A ≤ f.radius`, agrees
with `f.radius` at `⊤` and `0` over any complete nontrivially normed field (Archimedean or
non-Archimedean), and equals `f.radius` whenever the positive norms of `A` are dense in `(0, ∞)` —
in particular over any complete `DenselyNormedField` such as `ℝ`, `ℂ`, or `ℂ_[p]`. When the norms of
`A` omit an interval `(r, c)` containing `f.radius`, as happens over discretely valued fields, the
inequality `f.convergencePointRadius A < f.radius` is strict, without requiring completeness or
ultrametricity.

When `A` is complete and ultrametric, summability is equivalent to decay of the individual terms,
so convergence of `∑ aₙ • x ^ n` at `x` is equivalent to `f.IsRestricted ‖x‖`. Convergence at a
single point of norm `r` therefore implies convergence throughout the closed disc
`{y : A | ‖y‖ ≤ r}`, bounded in norm by `gaussNorm norm r f`; conversely, convergence throughout
`{y : A | ‖y‖ ≤ r}` implies `f.IsRestricted r` provided the numerical radius `r` is attained as the
norm of an element of `A`; and `f.convergencePointRadius A` agrees with
`⨆ (x : A) (_ : f.IsRestricted ‖x‖), ‖x‖ₑ`.

## Main definitions

* `PowerSeries.convergencePointRadius A f`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over the points
  `x : A` at which `∑ aₙ • x ^ n` converges.

## Main results

* `PowerSeries.tendsto_smul_pow_cofinite_nhds_zero_iff_isRestricted` and
  `PowerSeries.isRestricted_of_summable_smul_pow`: decay or summability of the terms at `x` gives
  `f.IsRestricted ‖x‖`, hence `‖x‖ₑ ≤ f.radius` (`PowerSeries.le_radius_of_summable_smul_pow`).
* `PowerSeries.summable_norm_smul_pow_of_lt_radius`, `PowerSeries.summable_smul_pow_of_lt_radius`,
  and `PowerSeries.hasSum_evalAt_of_lt_radius`: open-disc convergence in any complete seminormed
  algebra with a bounded scalar action, without ultrametricity.
* `PowerSeries.convergencePointRadius_le_radius`,
  `PowerSeries.summable_smul_pow_of_lt_convergencePointRadius`,
  `PowerSeries.not_summable_smul_pow_of_convergencePointRadius_lt`,
  `PowerSeries.convergencePointRadius_eq_top_iff`, `PowerSeries.convergencePointRadius_pos_iff`,
  `PowerSeries.convergencePointRadius_eq_radius_of_Ioi_subset_closure`, and
  `PowerSeries.convergencePointRadius_eq_radius`: comparison between the convergence-point supremum
  and the intrinsic radius, matching top and positivity over any complete nontrivially normed field
  and full equality under dense positive norms.
* `PowerSeries.convergencePointRadius_lt_radius_of_norm_le_or_le` and
  `PowerSeries.convergencePointRadius_eq_ofReal_of_norm_le_or_le`: strict inequality and exact value
  in the presence of a gap `(r, c)` in the norms of `A`.
* `PowerSeries.summable_smul_pow_iff_isRestricted`, `PowerSeries.hasSum_evalAt_iff_isRestricted`,
  `PowerSeries.hasSum_evalAt_of_norm_le_of_summable_smul_pow`,
  `PowerSeries.norm_evalAt_le_gaussNorm_of_summable_smul_pow`,
  `PowerSeries.forall_norm_le_summable_smul_pow_iff_isRestricted`, and
  `PowerSeries.convergencePointRadius_eq_iSup_isRestricted`: complete ultrametric characterization
  of pointwise and closed-disc convergence via restrictedness.

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
noncomputable def convergencePointRadius (A : Type*) [SeminormedRing A] [Algebra R A] (f : R⟦X⟧) :
    ℝ≥0∞ :=
  ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ

/-- `PowerSeries.convergencePointRadius A f` as the supremum of extended norms of convergence points
in `A`. -/
theorem convergencePointRadius_def (A : Type*) [SeminormedRing A] [Algebra R A] (f : R⟦X⟧) :
    f.convergencePointRadius A = ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ :=
  (rfl)

section SeminormedRing

variable {A : Type*} [SeminormedRing A] [Algebra R A] {f : R⟦X⟧} {x : A}

/-- Every point at which `f` is summable bounds `f.convergencePointRadius A` from below. -/
theorem le_convergencePointRadius_of_summable (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.convergencePointRadius A :=
  le_iSup₂ (f := fun (y : A) (_ : Summable fun n ↦ coeff n f • y ^ n) ↦ ‖y‖ₑ) x h

/-- Every point at which `f` has a sum bounds `f.convergencePointRadius A` from below. -/
theorem le_convergencePointRadius_of_hasSum {y : A} (h : HasSum (fun n ↦ coeff n f • x ^ n) y) :
    ‖x‖ₑ ≤ f.convergencePointRadius A :=
  f.le_convergencePointRadius_of_summable h.summable

/-- A power series cannot converge at a point whose extended norm strictly exceeds its
convergence-point radius. -/
theorem not_summable_smul_pow_of_convergencePointRadius_lt
    (hx : f.convergencePointRadius A < ‖x‖ₑ) : ¬Summable fun n ↦ coeff n f • x ^ n :=
  fun h ↦ (f.le_convergencePointRadius_of_summable h).not_gt hx

/-- `f.convergencePointRadius A` is at most `r` exactly when every convergence point has extended
norm at most `r`. -/
theorem convergencePointRadius_le_iff {r : ℝ≥0∞} :
    f.convergencePointRadius A ≤ r ↔
      ∀ x : A, (Summable fun n ↦ coeff n f • x ^ n) → ‖x‖ₑ ≤ r :=
  iSup₂_le_iff

/-- A radius `r` is strictly below `f.convergencePointRadius A` exactly when `f` is summable at some
point `x : A` with `r < ‖x‖ₑ`. -/
theorem lt_convergencePointRadius_iff {r : ℝ≥0∞} :
    r < f.convergencePointRadius A ↔ ∃ x : A, (Summable fun n ↦ coeff n f • x ^ n) ∧ r < ‖x‖ₑ := by
  simp [convergencePointRadius_def, lt_iSup_iff]

/-- A polynomial converges at every point of `A`, so its convergence-point radius in `A` is the
supremum of all extended norms in `A`. -/
theorem convergencePointRadius_coe_eq_iSup (A : Type*) [SeminormedRing A] [Algebra R A]
    (p : Polynomial R) : (p : R⟦X⟧).convergencePointRadius A = ⨆ x : A, ‖x‖ₑ := by
  have hsum (x : A) : Summable fun n ↦ p.coeff n • x ^ n :=
    summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn ↦ by
      rw [Finset.mem_range, not_lt] at hn
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  simp [convergencePointRadius_def, hsum]

/-- Extension of scalars preserves the convergence-point radius. -/
@[simp]
theorem convergencePointRadius_map_algebraMap {S : Type*} [CommSemiring S] [Algebra R S]
    [Algebra S A] [IsScalarTower R S A] (f : R⟦X⟧) :
    (f.map (algebraMap R S)).convergencePointRadius A = f.convergencePointRadius A := by
  simp [convergencePointRadius_def]

/-- An isometric `R`-algebra homomorphism `A →ₐ[R] B` (or any bundled `AlgHomClass`) can only
enlarge the convergence-point radius: every convergence point in `A` pushes forward to a
convergence point of the same norm in `B`. -/
theorem convergencePointRadius_le_convergencePointRadius_of_norm_eq {B F : Type*}
    [SeminormedRing B] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B] (ψ : F)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (f : R⟦X⟧) :
    f.convergencePointRadius A ≤ f.convergencePointRadius B := by
  have hisom : Isometry ψ := AddMonoidHomClass.isometry_of_norm ψ hψ
  refine iSup₂_le fun x hx ↦ ?_
  have hsum : Summable fun n ↦ coeff n f • (ψ x) ^ n := by
    simpa only [Function.comp_def, map_smul, map_pow] using hx.map ψ hisom.continuous
  have hnorm : ‖ψ x‖ₑ = ‖x‖ₑ := eNorm_eq_iff_norm_eq.mpr (hψ x)
  exact hnorm ▸ f.le_convergencePointRadius_of_summable hsum

/-- Isometric `R`-algebra equivalences preserve the convergence-point radius. -/
theorem convergencePointRadius_eq_convergencePointRadius_of_norm_eq {B F : Type*}
    [SeminormedRing B] [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (ψ : F)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (f : R⟦X⟧) :
    f.convergencePointRadius A = f.convergencePointRadius B := by
  let e : A ≃ₐ[R] B := AlgEquiv.ofClass ψ
  refine le_antisymm (f.convergencePointRadius_le_convergencePointRadius_of_norm_eq ψ hψ)
    (f.convergencePointRadius_le_convergencePointRadius_of_norm_eq e.symm fun y ↦ ?_)
  calc ‖e.symm y‖ = ‖ψ (e.symm y)‖ := (hψ _).symm
    _ = ‖y‖ := congrArg norm (e.apply_symm_apply y)

end SeminormedRing

section NontriviallyNormedField

variable (L : Type*) [NontriviallyNormedField L] [Algebra R L]

/-- Over a nontrivially normed field `L`, every polynomial has infinite convergence-point radius,
regardless of the norms of its roots. -/
@[simp]
theorem convergencePointRadius_coe (p : Polynomial R) :
    (p : R⟦X⟧).convergencePointRadius L = ⊤ := by
  rw [convergencePointRadius_coe_eq_iSup]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨x, hx⟩ := NormedField.exists_lt_eNorm L (ENNReal.coe_ne_top : (r : ℝ≥0∞) ≠ ⊤)
  exact hx.le.trans (le_iSup (fun y : L ↦ ‖y‖ₑ) x)

/-- Over a nontrivially normed field `L`, the zero series has infinite convergence-point radius. -/
@[simp]
theorem convergencePointRadius_zero : (0 : R⟦X⟧).convergencePointRadius L = ⊤ := by
  simpa using convergencePointRadius_coe L (0 : Polynomial R)

/-- Over a nontrivially normed field `L`, the constant series `1` has infinite convergence-point
radius. -/
@[simp]
theorem convergencePointRadius_one : (1 : R⟦X⟧).convergencePointRadius L = ⊤ := by
  simpa using convergencePointRadius_coe L (1 : Polynomial R)

/-- Over a nontrivially normed field `L`, every constant series has infinite convergence-point
radius. -/
@[simp]
theorem convergencePointRadius_C (a : R) : (C a : R⟦X⟧).convergencePointRadius L = ⊤ := by
  simpa using convergencePointRadius_coe L (Polynomial.C a)

/-- Over a nontrivially normed field `L`, `X` has infinite convergence-point radius. -/
@[simp]
theorem convergencePointRadius_X : (X : R⟦X⟧).convergencePointRadius L = ⊤ := by
  simpa using convergencePointRadius_coe L (Polynomial.X : Polynomial R)

/-- Over a nontrivially normed field `L`, every monomial has infinite convergence-point radius. -/
@[simp]
theorem convergencePointRadius_monomial (n : ℕ) (a : R) :
    (monomial n a : R⟦X⟧).convergencePointRadius L = ⊤ := by
  simpa using convergencePointRadius_coe L (Polynomial.monomial n a)

end NontriviallyNormedField

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [SeminormedRing A] [Algebra R A]

/-- Negating a power series preserves its convergence-point radius. -/
@[simp]
theorem convergencePointRadius_neg (f : R⟦X⟧) :
    (-f).convergencePointRadius A = f.convergencePointRadius A := by
  simp only [convergencePointRadius_def, map_neg, neg_smul, summable_neg_iff]

end Ring

section TermNorms

section Multiplicative

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMul R A]
  [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- For `n ≠ 0`, the `n`-th term `aₙ • x ^ n` has norm `‖aₙ‖ * ‖x‖ ^ n`. -/
theorem norm_coeff_smul_pow {n : ℕ} (hn : n ≠ 0) :
    ‖coeff n f • x ^ n‖ = ‖coeff n f‖ * ‖x‖ ^ n := by
  rw [norm_smul, TauCeti.norm_pow' x (Nat.pos_of_ne_zero hn)]

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

end Multiplicative

section Algebra

variable {R A : Type*} [NormedCommRing R] [SeminormedRing A] [Algebra R A]
  [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {r : ℝ}

/-- **Upper bound by the intrinsic radius.** The convergence-point supremum in `A` never exceeds
the intrinsic radius `f.radius`. -/
theorem convergencePointRadius_le_radius (A : Type*) [SeminormedRing A] [Algebra R A]
    [NormSMulClass R A] [NormMulClass A] (f : R⟦X⟧) :
    f.convergencePointRadius A ≤ f.radius :=
  iSup₂_le fun _ hx ↦ f.le_radius_of_summable_smul_pow hx

/-- A power series is restricted at every real radius whose extended norm is strictly smaller than
its convergence-point radius in `A`. -/
theorem isRestricted_of_lt_convergencePointRadius (hr : ‖r‖ₑ < f.convergencePointRadius A) :
    f.IsRestricted r :=
  isRestricted_of_lt_radius (hr.trans_le (f.convergencePointRadius_le_radius A))

/-- If every element of `A` has norm at most `r` or at least `c ≥ 0` (so the open interval `(r, c)`
contains no norms of `A`), and `f` is not restricted at `c`, then `f.convergencePointRadius A` is at
most `ENNReal.ofReal r`. -/
theorem convergencePointRadius_le_ofReal_of_norm_le_or_le {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ y : A, ‖y‖ ≤ r ∨ c ≤ ‖y‖) (hnc : ¬f.IsRestricted c) :
    f.convergencePointRadius A ≤ ENNReal.ofReal r := by
  refine iSup₂_le fun y hy ↦ ?_
  have hres := f.isRestricted_of_summable_smul_pow hy
  rcases hgap y with hyr | hcy
  · rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hyr
  · refine (hnc (TauCeti.PowerSeries.isRestricted_of_abs_le hres ?_)).elim
    rwa [abs_of_nonneg hc, abs_norm]

/-- **Strict inequality across a norm gap.** If no element of `A` has norm in the open interval
`(r, c)` and the intrinsic radius `f.radius` lies strictly inside `(r, c)`, then the
convergence-point supremum `f.convergencePointRadius A` is at most `ENNReal.ofReal r` and therefore
strictly smaller than `f.radius`. Neither completeness nor ultrametricity is needed. -/
theorem convergencePointRadius_lt_radius_of_norm_le_or_le {c : ℝ}
    (hgap : ∀ y : A, ‖y‖ ≤ r ∨ c ≤ ‖y‖)
    (hrf : ENNReal.ofReal r < f.radius) (hfc : f.radius < ENNReal.ofReal c) :
    f.convergencePointRadius A < f.radius := by
  have hc0 : 0 ≤ c := (ENNReal.ofReal_pos.mp (pos_of_gt hfc)).le
  have hnc : ¬f.IsRestricted c := not_isRestricted_of_radius_lt <| by
    rwa [Real.eNorm_eq_ofReal hc0]
  exact (f.convergencePointRadius_le_ofReal_of_norm_le_or_le hc0 hgap hnc).trans_lt hrf

end Algebra

end TermNorms

section OpenDisc

section BoundedSMul

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMulZeroClass R A] [IsBoundedSMul R A]
  {f : R⟦X⟧} {x : A}

/-- At every point strictly inside `f.radius`, the terms `aₙ • x ^ n` are absolutely summable.
No completeness or ultrametric hypothesis is needed. -/
theorem summable_norm_smul_pow_of_lt_radius (hx : ‖x‖ₑ < f.radius) :
    Summable fun n ↦ ‖coeff n f • x ^ n‖ := by
  obtain ⟨s, hxs, hsf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hx
  have hres : f.IsRestricted (s : ℝ) := isRestricted_of_lt_radius (by simpa using hsf)
  have hlt : |‖x‖| < |(s : ℝ)| := by
    rw [abs_norm, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast (eNorm_lt_coe.mp hxs)
  exact summable_norm_smul_pow_of_summable_norm_mul_pow (hres.summable_norm_coeff_mul_pow hlt)

/-- In a complete seminormed ring with a bounded scalar action, the terms of `f` at `x` are
summable whenever `‖x‖ₑ < f.radius`. No ultrametric hypothesis is needed. -/
theorem summable_smul_pow_of_lt_radius [CompleteSpace A] (hx : ‖x‖ₑ < f.radius) :
    Summable fun n ↦ coeff n f • x ^ n :=
  (f.summable_norm_smul_pow_of_lt_radius hx).of_norm

end BoundedSMul

section CompleteAlgebra

variable {R A : Type*} [NormedCommRing R] [SeminormedRing A] [Algebra R A]
  [IsBoundedSMul R A] [CompleteSpace A] {f : R⟦X⟧} {x : A}

/-- In a complete seminormed algebra with a bounded scalar action, `f` converges to `f.evalAt x` at
every point strictly inside `f.radius`. No ultrametric hypothesis is needed. -/
theorem hasSum_evalAt_of_lt_radius (hx : ‖x‖ₑ < f.radius) :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) :=
  hasSum_evalAt_of_summable_norm (f.summable_norm_smul_pow_of_lt_radius hx)

/-- In a complete seminormed algebra with a bounded scalar action, every point with
`‖x‖ₑ < f.radius` has extended norm at most `f.convergencePointRadius A`. -/
theorem le_convergencePointRadius_of_lt_radius (hx : ‖x‖ₑ < f.radius) :
    ‖x‖ₑ ≤ f.convergencePointRadius A :=
  f.le_convergencePointRadius_of_summable (f.summable_smul_pow_of_lt_radius hx)

/-- Over any complete nontrivially normed field `L` with a bounded scalar action (Archimedean or
non-Archimedean), an entire series has infinite convergence-point radius. -/
theorem IsEntire.convergencePointRadius_eq_top (L : Type*) [NontriviallyNormedField L] [Algebra R L]
    [IsBoundedSMul R L] [CompleteSpace L] (hf : f.IsEntire) :
    f.convergencePointRadius L = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨y, hy⟩ := NormedField.exists_lt_eNorm L (ENNReal.coe_ne_top : (r : ℝ≥0∞) ≠ ⊤)
  exact hy.le.trans (f.le_convergencePointRadius_of_lt_radius
    (by rw [radius_eq_top_iff.mpr hf]; exact eNorm_lt_top))

end CompleteAlgebra

section Comparison

variable {R A : Type*} [NormedCommRing R] [SeminormedRing A] [Algebra R A]
  [NormSMulClass R A] [NormMulClass A] [CompleteSpace A] {f : R⟦X⟧} {x : A}

/-- In a complete seminormed algebra with multiplicative scalar and ring norms, the terms of `f` at
`x` are summable whenever `‖x‖ₑ < f.convergencePointRadius A`. -/
theorem summable_smul_pow_of_lt_convergencePointRadius (hx : ‖x‖ₑ < f.convergencePointRadius A) :
    Summable fun n ↦ coeff n f • x ^ n :=
  f.summable_smul_pow_of_lt_radius (hx.trans_le (f.convergencePointRadius_le_radius A))

/-- In a complete seminormed algebra with multiplicative scalar and ring norms, `f` converges to
`f.evalAt x` at every point with `‖x‖ₑ < f.convergencePointRadius A`. -/
theorem hasSum_evalAt_of_lt_convergencePointRadius (hx : ‖x‖ₑ < f.convergencePointRadius A) :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) :=
  f.hasSum_evalAt_of_lt_radius (hx.trans_le (f.convergencePointRadius_le_radius A))

/-- Over any complete nontrivially normed field `L` (Archimedean or non-Archimedean, even
discretely valued), the convergence-point radius is infinite if and only if `f` is entire. -/
@[simp]
theorem convergencePointRadius_eq_top_iff (L : Type*) [NontriviallyNormedField L] [Algebra R L]
    [NormSMulClass R L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergencePointRadius L = ⊤ ↔ f.IsEntire :=
  ⟨fun h ↦ radius_eq_top_iff.mp (top_unique (h ▸ f.convergencePointRadius_le_radius L)),
    fun hf ↦ hf.convergencePointRadius_eq_top L⟩

/-- Over any complete nontrivially normed field `L` (Archimedean or non-Archimedean, even
discretely valued), the convergence-point radius is positive if and only if the intrinsic radius is
positive. -/
theorem convergencePointRadius_pos_iff (L : Type*) [NontriviallyNormedField L] [Algebra R L]
    [NormSMulClass R L] [CompleteSpace L] (f : R⟦X⟧) :
    0 < f.convergencePointRadius L ↔ 0 < f.radius := by
  refine ⟨fun h ↦ h.trans_le (f.convergencePointRadius_le_radius L), fun h ↦ ?_⟩
  obtain ⟨y, hy0, hyr⟩ := NormedField.exists_eNorm_lt L h
  exact hy0.trans_le (f.le_convergencePointRadius_of_lt_radius hyr)

/-- Over any complete nontrivially normed field `L` (Archimedean or non-Archimedean, even
discretely valued), the convergence-point radius is zero if and only if the intrinsic radius is
zero. -/
theorem convergencePointRadius_eq_zero_iff (L : Type*) [NontriviallyNormedField L] [Algebra R L]
    [NormSMulClass R L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergencePointRadius L = 0 ↔ f.radius = 0 := by
  rw [← not_iff_not, ← ne_eq, ← ne_eq, ← pos_iff_ne_zero, ← pos_iff_ne_zero,
    convergencePointRadius_pos_iff]

/-- **Equality under norm separation.** If every open interval `(r, s)` with `0 ≤ r < s` contains
the norm of an element of `A`, then the convergence-point supremum `f.convergencePointRadius A`
equals the intrinsic radius `f.radius`. No ultrametric hypothesis is needed. -/
theorem convergencePointRadius_eq_radius_of_forall_exists_lt_norm_lt
    (hdense : ∀ r s : ℝ, 0 ≤ r → r < s → ∃ x : A, r < ‖x‖ ∧ ‖x‖ < s) (f : R⟦X⟧) :
    f.convergencePointRadius A = f.radius := by
  refine le_antisymm (f.convergencePointRadius_le_radius A)
    (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
  obtain ⟨s, hrs, hsf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  obtain ⟨x, hrx, hxs⟩ := hdense r s r.coe_nonneg (ENNReal.coe_lt_coe.mp hrs)
  have hxs' : ‖x‖ₑ < (s : ℝ≥0∞) := by
    rw [eNorm_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm]
    exact hxs
  have hrx' : (r : ℝ≥0∞) ≤ ‖x‖ₑ := by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hrx.le
  exact hrx'.trans (f.le_convergencePointRadius_of_lt_radius (hxs'.trans hsf))

/-- **Equality under dense positive norms.** When the positive norms of `A` are dense in `(0, ∞)`,
the convergence-point supremum `f.convergencePointRadius A` equals the intrinsic radius
`f.radius`. No ultrametric hypothesis is needed. -/
theorem convergencePointRadius_eq_radius_of_Ioi_subset_closure
    (hdense : Set.Ioi (0 : ℝ) ⊆ closure ((‖·‖ : A → ℝ) '' {x : A | x ≠ 0})) (f : R⟦X⟧) :
    f.convergencePointRadius A = f.radius := by
  refine f.convergencePointRadius_eq_radius_of_forall_exists_lt_norm_lt fun r s hr hlt ↦ ?_
  have hm : (r + s) / 2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  obtain ⟨_, ⟨x, -, rfl⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (hdense hm) ((s - r) / 2) (by linarith)
  rw [Real.dist_eq, abs_lt] at hdist
  exact ⟨x, by linarith, by linarith⟩

/-- **Equality over a complete densely normed field.** In any complete densely normed field `L`
over `R` (for instance `ℝ`, `ℂ`, or `ℂ_[p]`), the convergence-point supremum equals the intrinsic
radius. -/
theorem convergencePointRadius_eq_radius (L : Type*) [DenselyNormedField L] [Algebra R L]
    [NormSMulClass R L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergencePointRadius L = f.radius :=
  f.convergencePointRadius_eq_radius_of_forall_exists_lt_norm_lt
    fun _ _ ↦ NormedField.exists_lt_norm_lt L

end Comparison

end OpenDisc

section UltrametricBoundedSMul

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A]
  [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A] {f : R⟦X⟧} {x : A}

/-- In a complete ultrametric normed algebra, restrictedness at `‖x‖` gives
`‖x‖ₑ ≤ f.convergencePointRadius A`. -/
theorem le_convergencePointRadius_of_isRestricted (hf : f.IsRestricted ‖x‖) :
    ‖x‖ₑ ≤ f.convergencePointRadius A :=
  f.le_convergencePointRadius_of_hasSum (hf.hasSum_evalAt le_rfl)

end UltrametricBoundedSMul

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
/-- **Closed-disc evaluation bound from convergence at one point.** If `f` converges at `x`, then
`‖f.evalAt y‖ ≤ gaussNorm norm ‖x‖ f` for every `y : A` with `‖y‖ ≤ ‖x‖`. -/
theorem norm_evalAt_le_gaussNorm_of_summable_smul_pow {y : A} (hy : ‖y‖ ≤ ‖x‖)
    (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖f.evalAt y‖ ≤ gaussNorm norm ‖x‖ f := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim (f.evalAt y) 0, norm_zero]
    exact gaussNorm_nonneg norm ‖x‖ f norm_nonneg
  · have : NormOneClass A := NormMulClass.toNormOneClass
    exact (f.isRestricted_of_summable_smul_pow h).norm_evalAt_le_gaussNorm hy

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

/-- **Restrictedness description of `convergencePointRadius`.** In a complete ultrametric normed
algebra with multiplicative scalar and ring norms, `f.convergencePointRadius A` is the supremum of
`‖x‖ₑ` over those `x : A` at whose norm `f` is restricted. -/
theorem convergencePointRadius_eq_iSup_isRestricted (A : Type*) [NormedRing A] [Algebra R A]
    [NormSMulClass R A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] (f : R⟦X⟧) :
    f.convergencePointRadius A = ⨆ (x : A) (_ : f.IsRestricted ‖x‖), ‖x‖ₑ := by
  simp_rw [convergencePointRadius_def, summable_smul_pow_iff_isRestricted]

/-- In a complete ultrametric normed algebra with multiplicative scalar and ring norms, `s` is
strictly below `f.convergencePointRadius A` iff `f` is restricted at `‖x‖` for some `x : A` with
`s < ‖x‖ₑ`. -/
theorem lt_convergencePointRadius_iff_exists_isRestricted {s : ℝ≥0∞} :
    s < f.convergencePointRadius A ↔ ∃ x : A, f.IsRestricted ‖x‖ ∧ s < ‖x‖ₑ := by
  simp [convergencePointRadius_eq_iSup_isRestricted, lt_iSup_iff]

/-- If the coefficients of `g` are no larger in norm than those of `f`, then the convergence-point
radius of `g` in `A` is at least that of `f`. -/
theorem convergencePointRadius_le_convergencePointRadius_of_norm_coeff_le {S : Type*}
    [NormedCommRing S] [Algebra S A] [NormSMulClass S A] {g : S⟦X⟧}
    (h : ∀ n, ‖coeff n g‖ ≤ ‖coeff n f‖) :
    f.convergencePointRadius A ≤ g.convergencePointRadius A := by
  rw [convergencePointRadius_eq_iSup_isRestricted, convergencePointRadius_eq_iSup_isRestricted]
  refine iSup₂_le fun y hfy ↦ ?_
  have hgy : g.IsRestricted ‖y‖ := by
    rw [isRestricted_iff] at hfy ⊢
    exact squeeze_zero (fun _ ↦ by positivity)
      (fun n ↦ mul_le_mul_of_nonneg_right (h n) (by positivity)) hfy
  exact le_iSup₂ (f := fun (z : A) (_ : g.IsRestricted ‖z‖) ↦ ‖z‖ₑ) y hgy

/-- Any nonnegative radius strictly below both `f.convergencePointRadius A` and
`g.convergencePointRadius A` is strictly dominated by the extended norm of a single element `w : A`
at whose norm both `f` and `g` are restricted. -/
private theorem exists_isRestricted_and_lt_eNorm {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < min (f.convergencePointRadius A) (g.convergencePointRadius A)) :
    ∃ w : A, f.IsRestricted ‖w‖ ∧ g.IsRestricted ‖w‖ ∧ (s : ℝ≥0∞) < ‖w‖ₑ := by
  obtain ⟨y, hfy, hsy⟩ := lt_convergencePointRadius_iff_exists_isRestricted.mp (lt_min_iff.mp hs).1
  obtain ⟨z, hgz, hsz⟩ := lt_convergencePointRadius_iff_exists_isRestricted.mp (lt_min_iff.mp hs).2
  by_cases hyz : ‖y‖ ≤ ‖z‖
  · exact ⟨y, hfy, TauCeti.PowerSeries.isRestricted_of_abs_le hgz (by simpa using hyz), hsy⟩
  · refine ⟨z, ?_, hgz, hsz⟩
    exact TauCeti.PowerSeries.isRestricted_of_abs_le hfy (by simpa using le_of_not_ge hyz)

/-- The convergence-point radius of a sum is at least the minimum of the two convergence-point
radii. -/
theorem min_convergencePointRadius_le_convergencePointRadius_add (f g : R⟦X⟧) :
    min (f.convergencePointRadius A) (g.convergencePointRadius A) ≤
      (f + g).convergencePointRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun s hs ↦ ?_
  obtain ⟨w, hfw, hgw, hsw⟩ := exists_isRestricted_and_lt_eNorm hs
  exact hsw.le.trans ((f + g).le_convergencePointRadius_of_isRestricted (hfw.add hgw))

/-- The convergence-point radius of a product is at least the minimum of the two convergence-point
radii. -/
theorem min_convergencePointRadius_le_convergencePointRadius_mul (f g : R⟦X⟧) :
    min (f.convergencePointRadius A) (g.convergencePointRadius A) ≤
      (f * g).convergencePointRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun s hs ↦ ?_
  obtain ⟨w, hfw, hgw, hsw⟩ := exists_isRestricted_and_lt_eNorm hs
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr fun hw ↦ by simp [hw] at hsw
  -- Positive-norm scalar action from `R` into ultrametric `A` transfers ultrametricity to `R`.
  have : IsUltrametricDist R := ⟨fun a b c ↦ le_of_mul_le_mul_right (a0 := hw0) <| by
    simpa [dist_eq_norm, ← sub_smul, norm_smul, max_mul_of_nonneg _ _ hw0.le] using
      dist_triangle_max (a • w) (b • w) (c • w)⟩
  exact hsw.le.trans ((f * g).le_convergencePointRadius_of_isRestricted (hfw.mul hgw))

/-- **Exact convergence-point radius across a norm gap.** If `r` is attained as the norm of an
element of `A`, `f` is restricted at `r` and not at `c ≥ 0`, and no element of `A` has norm in
`(r, c)`, then `f.convergencePointRadius A = ENNReal.ofReal r`. -/
theorem convergencePointRadius_eq_ofReal_of_norm_le_or_le {c : ℝ} (hc : 0 ≤ c)
    (hf : f.IsRestricted r) (hx : ∃ x : A, ‖x‖ = r) (hgap : ∀ y : A, ‖y‖ ≤ r ∨ c ≤ ‖y‖)
    (hnc : ¬f.IsRestricted c) :
    f.convergencePointRadius A = ENNReal.ofReal r := by
  refine le_antisymm (f.convergencePointRadius_le_ofReal_of_norm_le_or_le hc hgap hnc) ?_
  obtain ⟨x, rfl⟩ := hx
  rw [ofReal_norm]
  exact f.le_convergencePointRadius_of_isRestricted hf

end UltrametricEquivalence

end PowerSeries
