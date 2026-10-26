/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer

/-!
# The operator norm over ring scalars

Mathlib's operator norm `ContinuousLinearMap.opNorm` is the infimum of the uniform Lipschitz
bounds `{c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}`, but it is only available when the scalars form a
nontrivially normed field. This file uses the same formula for continuous semilinear maps between
seminormed modules over arbitrary semirings, as a scoped `Norm` instance in the scope
`TauCeti.RingOpNorm`, and develops its basic theory.

Over an arbitrary normed ring a continuous linear map need not admit any uniform bound, and then
the infimum is the junk value `0`. The bound is guaranteed over *Tate* scalars, those whose norm
admits a multiplicative pseudo-uniformiser `ϖ` (`TauCeti.NormedRing.IsTate`): exact scaling by
the powers of `ϖ` moves every vector of nonzero norm into a fixed shell around the origin, where
continuity at zero gives the estimate (`TauCeti.NormedRing.IsTate.bound_of_continuous`). Over Tate
scalars the operator norm is therefore the least uniform bound, and the usual norm, triangle,
ultrametric, composition and scalar laws follow.

Over a nontrivially normed field the scoped norm is definitionally Mathlib's operator norm
(`ContinuousLinearMap.ringOpNorm_eq_opNorm`). The scope should not be opened over a field, where it
would duplicate Mathlib's instance.

## Main definitions

* `ContinuousLinearMap.ringOpNorm`: the infimum of the uniform bounds of a continuous semilinear
  map, installed as the scoped instance `TauCeti.RingOpNorm.hasOpNorm`.

## Main results

* `ContinuousLinearMap.isLeast_ringOpNorm`: if a uniform bound exists, the operator norm is the
  least one.
* `TauCeti.NormedRing.IsTate.bound_of_continuous`: over Tate scalars every continuous linear map
  between seminormed modules with contractive scalar actions has a uniform bound.
* `ContinuousLinearMap.le_ringOpNorm`: `‖f x‖ ≤ ‖f‖ * ‖x‖` over Tate scalars.
* `ContinuousLinearMap.ringOpNorm_le_of_ball`, `ContinuousLinearMap.ringOpNorm_le_of_nhds_zero`:
  a linear bound near zero over Tate scalars bounds the operator norm.
* `TauCeti.NormedRing.PseudoUniformizer.ringOpNorm_le_of_forall_norm_lt`: a constant bound on a
  ball gives a quantitative global operator-norm bound by shell rescaling.
* `LinearMap.norm_pi_apply_le_sum`, `LinearMap.norm_pi_apply_le_sup`,
  `ContinuousLinearMap.ringOpNorm_pi_eq_sup`: finite-free coordinate bounds.
* `ContinuousLinearMap.ringOpNorm_add_le`, `ContinuousLinearMap.ringOpNorm_add_le_max`,
  `ContinuousLinearMap.ringOpNorm_comp_le`, `ContinuousLinearMap.ringOpNorm_smul_le`: the norm laws.
* `ContinuousLinearMap.ringOpNorm_toSpanSingleton`: right multiplication by `v` has norm `‖v‖`
  over a norm-one ring; in particular multiplication by `a` on a norm-one commutative ring has norm
  `‖a‖`.

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §3.

The formula and API shape follow Mathlib's `Mathlib/Analysis/Normed/Operator/Basic.lean`; the
`ringOpNorm` prefix distinguishes this scoped ring-scalar API from Mathlib's field-scalar API.
-/

public section

open Metric Set
open scoped Topology

namespace TauCeti

namespace NormedRing.PseudoUniformizer

variable {R E F 𝓕 : Type*} [SeminormedRing R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]
  [FunLike 𝓕 E F] [LinearMapClass 𝓕 R E F]

/-- A constant bound on a ball gives a global linear bound by rescaling with a multiplicative
pseudo-uniformiser. Continuity of the linear map is not required. -/
theorem bound_of_forall_norm_lt (ϖ : PseudoUniformizer R) (f : 𝓕)
    {δ B : ℝ} (k : ℤ) (hδ : ‖(ϖ.unit : R)‖ ^ k < δ) (hB : 0 ≤ B)
    (hf : ∀ x : E, ‖x‖ < δ → ‖f x‖ ≤ B) (x : E) :
    ‖f x‖ ≤ B * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ * ‖x‖ := by
  set r := ‖(ϖ.unit : R)‖
  have hr0 : 0 < r := ϖ.norm_pos
  rcases eq_or_ne ‖x‖ 0 with hx | hx
  · have hbound : ∀ n : ℕ, ‖f x‖ ≤ r ^ n * B := by
      intro n
      have hy : ‖((ϖ.unit ^ (-(n : ℤ)) : Rˣ) : R) • x‖ < δ := by
        rw [ϖ.norm_zpow_smul, hx, mul_zero]
        exact (zpow_pos hr0 k).trans hδ
      have hfy := hf _ hy
      rw [map_smul, ϖ.norm_zpow_smul, zpow_neg, zpow_natCast] at hfy
      exact (inv_mul_le_iff₀ (pow_pos hr0 n)).mp hfy
    have hzero : ‖f x‖ ≤ 0 := by
      have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le ϖ.norm_lt_one).mul_const B
      exact ge_of_tendsto (by simpa using hlim) (Filter.Eventually.of_forall hbound)
    simpa [hx] using hzero
  obtain ⟨n, hn, hscale⟩ := ϖ.exists_zpow_mul_norm_lt hx k hδ
  have hfy := hf (((ϖ.unit ^ n : Rˣ) : R) • x) (by rwa [ϖ.norm_zpow_smul])
  rw [map_smul, ϖ.norm_zpow_smul] at hfy
  calc ‖f x‖ ≤ (r ^ n)⁻¹ * B := (le_inv_mul_iff₀ (zpow_pos hr0 n)).mpr hfy
    _ ≤ ((r ^ (k + 1))⁻¹ * ‖x‖) * B := mul_le_mul_of_nonneg_right hscale hB
    _ = B * (r ^ (k + 1))⁻¹ * ‖x‖ := by ring

end NormedRing.PseudoUniformizer

namespace NormedRing.IsTate

variable {R E F 𝓕 : Type*} [SeminormedRing R] [IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]
  [FunLike 𝓕 E F] [LinearMapClass 𝓕 R E F]

include R in
/-- **Continuity implies a uniform bound over Tate scalars.** A continuous linear map between
seminormed modules with contractive scalar actions over a ring admitting a multiplicative
pseudo-uniformiser satisfies `‖f x‖ ≤ C * ‖x‖` for some `C > 0`. -/
theorem bound_of_continuous (f : 𝓕) (hf : Continuous f) :
    ∃ C, 0 < C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖ := by
  obtain ⟨ϖ⟩ := nonempty_pseudoUniformizer (R := R)
  obtain ⟨δ, hδ, hfδ⟩ : ∃ δ > 0, ∀ x : E, ‖x‖ < δ → ‖f x‖ < 1 := by
    simpa [dist_eq_norm, map_zero] using Metric.continuous_iff.mp hf 0 1 one_pos
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(ϖ.unit : R)‖ ^ k < δ :=
    exists_pow_lt_of_lt_one hδ ϖ.norm_lt_one
  refine ⟨(‖(ϖ.unit : R)‖ ^ ((k : ℤ) + 1))⁻¹,
    inv_pos.mpr (zpow_pos ϖ.norm_pos _), fun x ↦ ?_⟩
  simpa using ϖ.bound_of_forall_norm_lt f (k : ℤ) (by simpa using hk) zero_le_one
    (fun x hx ↦ (hfδ x hx).le) x

end NormedRing.IsTate

end TauCeti

namespace ContinuousLinearMap

section Semiring

variable {R S T E F G : Type*} [Semiring R] [Semiring S] [Semiring T]
  {σ : R →+* S} {τ : S →+* T} {ρ : R →+* T} [RingHomCompTriple σ τ ρ]
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module S F]
  [SeminormedAddCommGroup G] [Module T G]

/-- The **operator norm** of a continuous semilinear map between seminormed modules over
semirings: the infimum of its uniform bounds. It is the formula of Mathlib's
`ContinuousLinearMap.opNorm` without the assumption that the scalars form a field. -/
noncomputable def ringOpNorm (f : E →SL[σ] F) : ℝ :=
  sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}

end Semiring

end ContinuousLinearMap

namespace TauCeti.RingOpNorm

variable {R S E F : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module S F]

/-- The operator norm over ring scalars, as a scoped instance. -/
noncomputable scoped instance hasOpNorm : Norm (E →SL[σ] F) :=
  ⟨ContinuousLinearMap.ringOpNorm⟩

end TauCeti.RingOpNorm

open scoped TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Semiring

variable {R S T E F G : Type*} [Semiring R] [Semiring S] [Semiring T]
  {σ : R →+* S} {τ : S →+* T} {ρ : R →+* T} [RingHomCompTriple σ τ ρ]
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module S F]
  [SeminormedAddCommGroup G] [Module T G]

/-- The operator norm is the infimum of the nonnegative uniform bounds. -/
theorem ringOpNorm_def (f : E →SL[σ] F) :
    ‖f‖ = sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} :=
  (rfl)

/-- The set of nonnegative uniform bounds is bounded below. -/
theorem ringOpNorm_bounds_bddBelow {f : E →SL[σ] F} :
    BddBelow {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} :=
  ⟨0, fun _ ⟨hn, _⟩ ↦ hn⟩

/-- The operator norm is nonnegative. -/
theorem ringOpNorm_nonneg (f : E →SL[σ] F) : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg fun _ ↦ And.left

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem ringOpNorm_le_bound (f : E →SL[σ] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  csInf_le ringOpNorm_bounds_bddBelow ⟨hMp, hM⟩

/-- **The bound at the infimum**: if `f` has some uniform bound, then its operator norm is its
least nonnegative uniform bound. -/
theorem isLeast_ringOpNorm (f : E →SL[σ] F) (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    IsLeast {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} ‖f‖ := by
  obtain ⟨C, hC⟩ := h
  refine IsClosed.isLeast_csInf ?_ ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
    ringOpNorm_bounds_bddBelow
  · simp only [ofPred_and, ofPred_forall]
    exact isClosed_Ici.inter <| isClosed_iInter fun _ ↦ isClosed_le (by fun_prop) (by fun_prop)
  · exact (hC x).trans (by gcongr; exact le_max_left _ _)

/-- If `f` has some uniform bound, then `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
theorem le_ringOpNorm_of_exists_bound (f : E →SL[σ] F)
    (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  (isLeast_ringOpNorm f h).1.2 x

/-- A nonnegative uniform bound below every other one is the operator norm. -/
theorem ringOpNorm_eq_of_bounds {f : E →SL[σ] F} {M : ℝ} (hM₀ : 0 ≤ M)
    (h_above : ∀ x, ‖f x‖ ≤ M * ‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖f x‖ ≤ N * ‖x‖) → M ≤ N) :
    ‖f‖ = M :=
  le_antisymm (ringOpNorm_le_bound f hM₀ h_above)
    ((le_csInf_iff ringOpNorm_bounds_bddBelow ⟨M, hM₀, h_above⟩).mpr
      fun N ⟨hN₀, hN⟩ ↦ h_below N hN₀ hN)

/-- The norm of the `0` operator is `0`. -/
@[simp]
theorem ringOpNorm_zero : ‖(0 : E →SL[σ] F)‖ = 0 :=
  le_antisymm (ringOpNorm_le_bound _ le_rfl fun _ ↦ by simp) (ringOpNorm_nonneg _)

/-- The norm of the identity is at most `1`. -/
theorem ringOpNorm_id_le : ‖ContinuousLinearMap.id R E‖ ≤ 1 :=
  ringOpNorm_le_bound _ zero_le_one fun x ↦ by simp

/-- If some vector has nonzero norm, then the identity has norm `1`. -/
@[simp]
theorem ringOpNorm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id R E‖ = 1 := by
  refine le_antisymm ringOpNorm_id_le ?_
  obtain ⟨x, hx⟩ := exists_norm_ne_zero E
  have h := le_ringOpNorm_of_exists_bound (ContinuousLinearMap.id R E) ⟨1, fun x ↦ by simp⟩ x
  exact le_of_mul_le_mul_right (by simpa using h) ((norm_nonneg x).lt_of_ne' hx)

/-- A composition of maps with uniform bounds is bounded by the product of their operator
norms. -/
theorem ringOpNorm_comp_le_of_exists_bound (g : F →SL[τ] G) (f : E →SL[σ] F)
    (hg : ∃ C, ∀ y, ‖g y‖ ≤ C * ‖y‖) (hf : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖g.comp f‖ ≤ ‖g‖ * ‖f‖ :=
  ringOpNorm_le_bound _ (mul_nonneg (ringOpNorm_nonneg g) (ringOpNorm_nonneg f)) fun x ↦ by
    rw [ContinuousLinearMap.comp_apply, mul_assoc]
    exact (le_ringOpNorm_of_exists_bound g hg _).trans
      (by gcongr; exacts [ringOpNorm_nonneg g, le_ringOpNorm_of_exists_bound f hf x])

end Semiring

section LocalBounds

variable {R E F : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- Over a Tate ring, a linear norm bound `‖f x‖ ≤ C * ‖x‖` on a ball around `0` extends to all of
`E` and bounds the operator norm `‖f‖` by `C`. -/
theorem ringOpNorm_le_of_ball (f : E →L[R] F) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) :
    ‖f‖ ≤ C := by
  obtain ⟨ϖ⟩ := TauCeti.NormedRing.IsTate.nonempty_pseudoUniformizer (R := R)
  refine f.ringOpNorm_le_bound hC fun x ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(ϖ.unit : R)‖ ^ k * ‖x‖ < ε := by
    rcases le_or_gt ‖x‖ 0 with hx | hx
    · refine ⟨0, lt_of_le_of_lt ?_ hε⟩
      simpa using hx
    · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hx) ϖ.norm_lt_one
      exact ⟨k, (lt_div_iff₀ hx).mp hk⟩
  have hmem : ((ϖ.unit ^ (k : ℤ) : Rˣ) : R) • x ∈ ball (0 : E) ε := by
    rw [mem_ball_zero_iff, ϖ.norm_zpow_smul, zpow_natCast]
    exact hk
  have hfk := hf _ hmem
  rw [map_smul, ϖ.norm_zpow_smul, ϖ.norm_zpow_smul, zpow_natCast] at hfk
  have hrk : 0 < ‖(ϖ.unit : R)‖ ^ k := pow_pos ϖ.norm_pos k
  have hbound : ‖(ϖ.unit : R)‖ ^ k * ‖f x‖ ≤ ‖(ϖ.unit : R)‖ ^ k * (C * ‖x‖) :=
    hfk.trans_eq (by ring)
  exact le_of_mul_le_mul_left hbound hrk

/-- Over a Tate ring, if `‖f x‖ ≤ C * ‖x‖` holds in a neighbourhood of `0`, then `‖f‖ ≤ C`. -/
theorem ringOpNorm_le_of_nhds_zero (f : E →L[R] F) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) :
    ‖f‖ ≤ C := by
  obtain ⟨ε, hε, hfε⟩ := Metric.eventually_nhds_iff_ball.mp hf
  exact f.ringOpNorm_le_of_ball hε hC hfε

end LocalBounds

end ContinuousLinearMap

namespace TauCeti

namespace NormedRing.PseudoUniformizer

variable {R E F : Type*} [SeminormedRing R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- **Quantitative local-to-global operator-norm bound.** If `ϖ` is a multiplicative
pseudo-uniformiser on `R`, `‖(ϖ.unit : R)‖ ^ k < δ`, and `‖f x‖ ≤ B` for every `x` of norm `< δ`,
then `‖f‖ ≤ B * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹`. -/
theorem ringOpNorm_le_of_forall_norm_lt (ϖ : PseudoUniformizer R) (f : E →L[R] F)
    {δ B : ℝ} (k : ℤ) (hδ : ‖(ϖ.unit : R)‖ ^ k < δ) (hB : 0 ≤ B)
    (hf : ∀ x : E, ‖x‖ < δ → ‖f x‖ ≤ B) :
    ‖f‖ ≤ B * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ := by
  exact f.ringOpNorm_le_bound (by positivity)
    (ϖ.bound_of_forall_norm_lt f k hδ hB hf)

end NormedRing.PseudoUniformizer

end TauCeti

namespace ContinuousLinearMap


section Ring

variable {R S E F : Type*} [Ring R] [Ring S] {σ : R →+* S}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module S F]

/-- The operator norm is invariant under negation. -/
@[simp]
theorem ringOpNorm_neg (f : E →SL[σ] F) : ‖-f‖ = ‖f‖ := by
  simp only [ringOpNorm_def, neg_apply, norm_neg]

end Ring

section Tate

variable {R E F G : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]
  [SeminormedAddCommGroup G] [Module R G] [IsBoundedSMul R G]

/-- Over Tate scalars every continuous linear map has a uniform bound. -/
theorem ringOpNorm_bound (f : E →L[R] F) : ∃ C, 0 < C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖ :=
  TauCeti.NormedRing.IsTate.bound_of_continuous f f.continuous

/-- **The fundamental property of the operator norm** over Tate scalars:
`‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
theorem le_ringOpNorm (f : E →L[R] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  le_ringOpNorm_of_exists_bound f ((ringOpNorm_bound f).imp fun _ h ↦ h.2) x

/-- A bound on the operator norm bounds every value. -/
theorem le_of_ringOpNorm_le (f : E →L[R] F) {c : ℝ} (h : ‖f‖ ≤ c) (x : E) :
    ‖f x‖ ≤ c * ‖x‖ :=
  (le_ringOpNorm f x).trans (by gcongr)

/-- Over Tate scalars, `‖f‖ ≤ M` exactly when `M` is a uniform bound for `f`. -/
theorem ringOpNorm_le_iff {f : E →L[R] F} {M : ℝ} (hMp : 0 ≤ M) :
    ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M * ‖x‖ :=
  ⟨le_of_ringOpNorm_le f, ringOpNorm_le_bound f hMp⟩

/-- The operator norm is an upper bound for the ratios `‖f x‖ / ‖x‖`. -/
theorem ratio_le_ringOpNorm (f : E →L[R] F) (x : E) : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
  div_le_of_le_mul₀ (norm_nonneg _) (ringOpNorm_nonneg f) (le_ringOpNorm f x)

/-- The operator norm satisfies the triangle inequality. -/
theorem ringOpNorm_add_le (f g : E →L[R] F) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  ringOpNorm_le_bound _ (add_nonneg (ringOpNorm_nonneg f) (ringOpNorm_nonneg g)) fun x ↦
    (norm_add_le_of_le (le_ringOpNorm f x) (le_ringOpNorm g x)).trans_eq (add_mul _ _ _).symm

/-- The operator norm is ultrametric when the target is. -/
theorem ringOpNorm_add_le_max [IsUltrametricDist F] (f g : E →L[R] F) :
    ‖f + g‖ ≤ max ‖f‖ ‖g‖ :=
  ringOpNorm_le_bound _ ((ringOpNorm_nonneg f).trans (le_max_left _ _)) fun x ↦ by
    rw [add_apply, max_mul_of_nonneg _ _ (norm_nonneg x)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (le_ringOpNorm f x) (le_ringOpNorm g x))

/-- The operator norm is submultiplicative. -/
theorem ringOpNorm_comp_le (g : F →L[R] G) (f : E →L[R] F) : ‖g.comp f‖ ≤ ‖g‖ * ‖f‖ :=
  ringOpNorm_comp_le_of_exists_bound g f ((ringOpNorm_bound g).imp fun _ h ↦ h.2)
    ((ringOpNorm_bound f).imp fun _ h ↦ h.2)

/-- Scalar multiplication of operators is contractive for the operator norm. -/
theorem ringOpNorm_smul_le {S : Type*} [SeminormedAddCommGroup S] [DistribSMul S F]
    [IsBoundedSMul S F]
    [SMulCommClass R S F] (c : S) (f : E →L[R] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  ringOpNorm_le_bound _ (mul_nonneg (norm_nonneg c) (ringOpNorm_nonneg f)) fun x ↦ by
    rw [smul_apply, mul_assoc]
    exact (norm_smul_le c (f x)).trans (by gcongr; exact le_ringOpNorm f x)

end Tate

section SpanSingleton

variable {R E : Type*} [SeminormedRing R] [NormOneClass R]
  [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]

/-- **Right multiplication by `v` has norm `‖v‖`** over a norm-one ring: the map `a ↦ a • v`
from `R` to `E`. For `E = R` commutative, this is multiplication by `v`. -/
@[simp]
theorem ringOpNorm_toSpanSingleton (v : E) : ‖ContinuousLinearMap.toSpanSingleton R v‖ = ‖v‖ := by
  refine ringOpNorm_eq_of_bounds (norm_nonneg v) (fun a ↦ ?_) fun N _ hN ↦ ?_
  · simpa [mul_comm] using norm_smul_le a v
  · simpa using hN 1

end SpanSingleton

/-- Over a nontrivially normed field, the operator norm over ring scalars is Mathlib's operator
norm `ContinuousLinearMap.opNorm`. -/
theorem ringOpNorm_eq_opNorm {K L E F : Type*} [NontriviallyNormedField K]
    [NontriviallyNormedField L] {σ : K →+* L} [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup F] [NormedSpace L F] (f : E →SL[σ] F) :
    ringOpNorm f = opNorm f :=
  (rfl)

end ContinuousLinearMap

/-! ### Finite-free operator bounds -/

namespace LinearMap

variable {R N ι : Type*} [Fintype ι] [DecidableEq ι] [SeminormedRing R]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Any linear map `f : (ι → R) →ₗ[R] N` on a finite product satisfies the coordinate bound
`‖f x‖ ≤ (∑ i, ‖f (Pi.single i 1)‖) * ‖x‖`. -/
theorem norm_pi_apply_le_sum (f : (ι → R) →ₗ[R] N) (x : ι → R) :
    ‖f x‖ ≤ (∑ i : ι, ‖f (Pi.single i 1)‖) * ‖x‖ := by
  calc ‖f x‖ = ‖∑ i : ι, x i • f (Pi.single i 1)‖ := by
         conv_lhs => rw [pi_eq_sum_univ' x, map_sum]
         simp only [map_smul]
    _ ≤ ∑ i : ι, ‖x i • f (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, ‖x i‖ * ‖f (Pi.single i 1)‖ := by
        gcongr with i
        exact norm_smul_le _ _
    _ ≤ ∑ i : ι, ‖x‖ * ‖f (Pi.single i 1)‖ := by
        gcongr with i
        exact norm_le_pi_norm x i
    _ = (∑ i : ι, ‖f (Pi.single i 1)‖) * ‖x‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- When the target module `N` is ultrametric, any linear map `f : (ι → R) →ₗ[R] N` on a finite
product is bounded by the supremum of the norms of the images of the standard basis vectors:
`‖f x‖ ≤ (Finset.univ.sup fun i ↦ ‖f (Pi.single i 1)‖₊) * ‖x‖`. -/
theorem norm_pi_apply_le_sup [IsUltrametricDist N] (f : (ι → R) →ₗ[R] N)
    (x : ι → R) :
    ‖f x‖ ≤ ↑(Finset.univ.sup fun i : ι ↦ ‖f (Pi.single i 1)‖₊) * ‖x‖ := by
  conv_lhs => rw [pi_eq_sum_univ' x, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi ↦ ?_
  calc ‖f (x i • Pi.single i 1)‖
      = ‖x i • f (Pi.single i 1)‖ := by rw [map_smul]
    _ ≤ ‖x i‖ * ‖f (Pi.single i 1)‖ := norm_smul_le _ _
    _ = ‖f (Pi.single i 1)‖ * ‖x i‖ := mul_comm _ _
    _ ≤ ↑(Finset.univ.sup fun j : ι ↦ ‖f (Pi.single j 1)‖₊) * ‖x‖ := by
        gcongr
        · exact_mod_cast Finset.le_sup (f := fun j : ι ↦ ‖f (Pi.single j 1)‖₊) hi
        · exact norm_le_pi_norm x i

end LinearMap

namespace ContinuousLinearMap

variable {R N ι : Type*} [Fintype ι] [DecidableEq ι] [SeminormedRing R]
  [SeminormedAddCommGroup N] [IsUltrametricDist N] [Module R N] [IsBoundedSMul R N]

/-- The operator norm of `f : (ι → R) →L[R] N` into an ultrametric module is bounded by the
supremum of the norms of the images of the standard basis vectors. -/
theorem ringOpNorm_pi_le_sup (f : (ι → R) →L[R] N) :
    ‖f‖ ≤ ↑(Finset.univ.sup fun i : ι ↦ ‖f (Pi.single i 1)‖₊) :=
  f.ringOpNorm_le_bound (by positivity) f.toLinearMap.norm_pi_apply_le_sup

/-- Over a Tate ring, the operator norm of `f : (ι → R) →L[R] N` into an ultrametric module is
the supremum of the norms of the images of the standard basis vectors `Pi.single i 1`. -/
theorem ringOpNorm_pi_eq_sup [TauCeti.NormedRing.IsTate R] (f : (ι → R) →L[R] N) :
    ‖f‖ = ↑(Finset.univ.sup fun i : ι ↦ ‖f (Pi.single i 1)‖₊) := by
  refine le_antisymm f.ringOpNorm_pi_le_sup ?_
  have hsup : (Finset.univ.sup fun i : ι ↦ ‖f (Pi.single i 1)‖₊) ≤
      Real.toNNReal ‖f‖ := by
    refine Finset.sup_le fun i _ ↦ (Real.le_toNNReal_iff_coe_le f.ringOpNorm_nonneg).mpr ?_
    have hsingle : ‖(Pi.single i 1 : ι → R)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j ↦ ?_
      by_cases hji : j = i <;> simp [hji]
    calc ‖f (Pi.single i 1)‖
        ≤ ‖f‖ * ‖(Pi.single i 1 : ι → R)‖ := f.le_ringOpNorm _
      _ ≤ ‖f‖ * 1 := by gcongr; exact f.ringOpNorm_nonneg
      _ = ‖f‖ := mul_one _
  exact (Real.le_toNNReal_iff_coe_le f.ringOpNorm_nonneg).mp hsup

end ContinuousLinearMap
