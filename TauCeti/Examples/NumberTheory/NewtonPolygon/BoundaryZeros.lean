/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.Analysis.Convex.Sequence.Face
public import TauCeti.NumberTheory.NewtonPolygon.Basic
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.Weierstrass.ZeroCount

/-!
# Boundary zeros are not determined by the Newton polygon

At a radius on the boundary of convergence, the Newton polygon of a power series can end in an
infinite ray, while the zeros of the series on that boundary are counted by its first and last
active coefficients. This file compares two power series over `ℚ_[p]`, with respect to the real
`p`-adic additive valuation `TauCeti.padicRealValuation p` normalised by `v(p) = 1`:

```text
ceilSqrtSeries p    = 1 +     ∑_{n ≥ 1} p ^ ⌈√n⌉ Xⁿ,
boundaryZeroSeries p = 1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ Xⁿ.
```

Both have coefficient heights `≥ 0`, equal to `0` at `n = 0` and of sublinear growth, so both
have the same Newton polygon: the identically zero height sequence, an infinite horizontal ray
from `(0, 0)` with every unit edge of slope `0`. In particular neither polygon has a finite face
of slope `0`, so the polygon assigns no finite multiplicity to the boundary slope.

Both series are nevertheless restricted at the unit radius, where their coefficient norms tend to
`0`, and their Gauss norm there is `1`. At this radius the first and last active indices are
`l = u = 0` for `ceilSqrtSeries p`, but `l = 0` and `u = 1` for `boundaryZeroSeries p`.
Consequently, in every complete normed field extension `L` of `ℚ_[p]`, for instance `ℂ_[p]`:

* `ceilSqrtSeries p` has no zeros in the closed unit disc of `L`;
* `boundaryZeroSeries p` has exactly one zero in that disc, counted with multiplicity, and it lies
  on the unit sphere.

So two series with the same Newton polygon can have different numbers of zeros on the boundary
of their disc of convergence. Zero counts at a boundary radius must be read from the active
indices, not from the shape of the polygon.

## Main results

* `TauCeti.NewtonPolygonBoundaryZeroExample.newtonPolygon_ceilSqrtSeries` and
  `TauCeti.NewtonPolygonBoundaryZeroExample.newtonPolygon_boundaryZeroSeries`: both Newton
  polygons are the horizontal ray `0`.
* `TauCeti.NewtonPolygonBoundaryZeroExample.not_isFiniteFace_newtonPolygon_ceilSqrtSeries`: the
  polygon has no finite face of slope `0`.
* `TauCeti.NewtonPolygonBoundaryZeroExample.isDistinguished_ceilSqrtSeries` and
  `TauCeti.NewtonPolygonBoundaryZeroExample.isLowestDominant_ceilSqrtSeries`: `l = u = 0` at the
  unit radius.
* `TauCeti.NewtonPolygonBoundaryZeroExample.isDistinguished_boundaryZeroSeries` and
  `TauCeti.NewtonPolygonBoundaryZeroExample.isLowestDominant_boundaryZeroSeries`: `u = 1` and
  `l = 0` at the unit radius.
* `TauCeti.NewtonPolygonBoundaryZeroExample.zeroMultiset_ceilSqrtSeries`: no zeros in the closed
  unit disc.
* `TauCeti.NewtonPolygonBoundaryZeroExample.card_filter_zeroMultiset_norm_eq_boundaryZeroSeries`
  and `TauCeti.NewtonPolygonBoundaryZeroExample.exists_zeroMultiset_boundaryZeroSeries_eq`:
  exactly one zero, on the unit sphere.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, on the difference between extremal
  coefficient indices and vertices of the polygon at the boundary of convergence.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open Filter Topology _root_.PowerSeries TauCeti TauCeti.PowerSeries

namespace TauCeti.NewtonPolygonBoundaryZeroExample

/-! ### The horizontal-ray envelope -/

/-- A height sequence that is nonnegative, vanishes at `0`, and has height at most `M` at every
square `M ^ 2` with `M ≥ 2` has the identically zero sequence as its lower convex envelope: a
convex minorant starting at height at most `0` with a positive height somewhere would grow
linearly, faster than `√n`. -/
private theorem isLowerConvexEnvelope_zero {a : ℕ → WithTop ℝ} (h0 : a 0 = 0)
    (hnonneg : ∀ n, 0 ≤ a n) (hsq : ∀ M : ℕ, 2 ≤ M → a (M ^ 2) ≤ ((M : ℝ) : WithTop ℝ)) :
    IsLowerConvexEnvelope a 0 := by
  refine ⟨by simpa [Pi.zero_def] using isConvexSeq_affine 0 0, fun n ↦ hnonneg n,
    fun g hg hga n ↦ ?_⟩
  rw [Pi.zero_apply]
  -- The minorant is finite at `0` and at every square `M ^ 2` with `M ≥ 2`, hence everywhere,
  -- with heights at most `0` at `0` and at most `M` at `M ^ 2`.
  have hg0 : g 0 ≠ ⊤ := ne_top_of_le_ne_top (by rw [h0]; exact WithTop.zero_ne_top) (hga 0)
  have hg0le : (g 0).untop₀ ≤ 0 := by
    have h := hga 0
    rwa [h0, ← WithTop.coe_untop₀_of_ne_top hg0, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
  have hgM {M : ℕ} (hM : 2 ≤ M) : g (M ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top ((hga _).trans (hsq M hM))
  have hgMle {M : ℕ} (hM : 2 ≤ M) : (g (M ^ 2)).untop₀ ≤ M := by
    have h := (hga _).trans (hsq M hM)
    rwa [← WithTop.coe_untop₀_of_ne_top (hgM hM), WithTop.coe_le_coe] at h
  have hsq_le {M : ℕ} (hM : n + 2 ≤ M) : n ≤ M ^ 2 :=
    (by omega : n ≤ M).trans (Nat.le_self_pow two_ne_zero M)
  have hgn : g n ≠ ⊤ :=
    hg.ne_top_of_le_of_le hg0 (hgM (by omega : 2 ≤ n + 2)) (Nat.zero_le n) (hsq_le le_rfl)
  by_contra hlt
  rw [not_le, ← WithTop.coe_untop₀_of_ne_top hgn, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hlt
  -- Choose `M ≥ n + 2` with `M * g n > n`.
  set t := (g n).untop₀
  set M := n + ⌈(n : ℝ) / t⌉₊ + 2
  have hM2 : 2 ≤ M := by omega
  have hMt : (n : ℝ) < M * t := by
    have hceil := Nat.le_ceil ((n : ℝ) / t)
    rw [div_le_iff₀ hlt] at hceil
    simp only [M]
    push_cast
    nlinarith
  -- The chord from `0` to `M ^ 2` through `n` forces `M ^ 2 * g n ≤ n * M`, so `M * g n ≤ n`.
  have hchord := hg.chord_inequality hg0 (hgM hM2) (Nat.zero_le n) (hsq_le (by omega))
  push_cast at hchord
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hnM : (n : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hsq_le (by omega)
  have h1 : ((M : ℝ) ^ 2 - n) * (g 0).untop₀ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hg0le
  have h2 : (n : ℝ) * (g (M ^ 2)).untop₀ ≤ n * M :=
    mul_le_mul_of_nonneg_left (hgMle hM2) (Nat.cast_nonneg n)
  have h3 : 0 < (M : ℝ) * (M * t - n) := mul_pos hM (by linarith)
  nlinarith

variable (p : ℕ) [Fact p.Prime]

/-! ### The series without boundary zeros -/

/-- The power series `1 + ∑_{n ≥ 1} p ^ ⌈√n⌉ Xⁿ` over `ℚ_[p]`, whose `n`-th coefficient is
`p ^ ⌈√n⌉`. -/
noncomputable def ceilSqrtSeries : ℚ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦ (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊

/-- The `n`-th coefficient of `ceilSqrtSeries p` is `p ^ ⌈√n⌉`. -/
@[simp]
theorem coeff_ceilSqrtSeries (n : ℕ) :
    coeff n (ceilSqrtSeries p) = (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊ :=
  coeff_mk n _

variable {p}

/-- The constant coefficient of `ceilSqrtSeries p` has norm `1`. -/
private theorem norm_coeff_zero_ceilSqrtSeries : ‖coeff 0 (ceilSqrtSeries p)‖ = 1 := by
  simp

/-- Every coefficient of `ceilSqrtSeries p` has norm at most `1`. -/
private theorem norm_coeff_ceilSqrtSeries_le_one (n : ℕ) : ‖coeff n (ceilSqrtSeries p)‖ ≤ 1 := by
  rw [coeff_ceilSqrtSeries, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le

/-- Every nonconstant coefficient of `ceilSqrtSeries p` has norm strictly less than `1`, since
`⌈√n⌉ ≥ 1` for `n ≥ 1`. -/
private theorem norm_coeff_ceilSqrtSeries_lt_one {n : ℕ} (hn : n ≠ 0) :
    ‖coeff n (ceilSqrtSeries p)‖ < 1 := by
  rw [coeff_ceilSqrtSeries, norm_pow]
  refine pow_lt_one₀ (norm_nonneg _) Padic.norm_p_lt_one (Nat.one_le_iff_ne_zero.mp ?_)
  exact Nat.one_le_ceil_iff.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))

/-- `ceilSqrtSeries p` is restricted at the unit radius: its coefficient norms `p ^ (-⌈√n⌉)`
tend to `0`. -/
theorem isRestricted_one_ceilSqrtSeries : (ceilSqrtSeries p).IsRestricted 1 := by
  rw [isRestricted_iff']
  simp_rw [one_pow, mul_one, coeff_ceilSqrtSeries, norm_pow]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) Padic.norm_p_lt_one).comp
    (tendsto_nat_ceil_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))

/-- The Gauss norm of `ceilSqrtSeries p` at the unit radius is `1`. -/
private theorem gaussNorm_one_ceilSqrtSeries : (ceilSqrtSeries p).gaussNorm norm 1 = 1 := by
  rw [gaussNorm_eq_of_forall_le (s := 0) fun m ↦ ?_, norm_coeff_zero_ceilSqrtSeries, one_pow,
    mul_one]
  rw [one_pow, one_pow, mul_one, mul_one, norm_coeff_zero_ceilSqrtSeries]
  exact norm_coeff_ceilSqrtSeries_le_one m

/-- `ceilSqrtSeries p` is distinguished of degree `0` at the unit radius: its constant
coefficient is the only one of norm `1`. -/
theorem isDistinguished_ceilSqrtSeries : IsDistinguished 1 0 (ceilSqrtSeries p) := by
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [gaussNorm_one_ceilSqrtSeries, norm_coeff_zero_ceilSqrtSeries, one_pow, mul_one]
  · rw [gaussNorm_one_ceilSqrtSeries, one_pow, mul_one]
    exact norm_coeff_ceilSqrtSeries_lt_one hm.ne'

/-- The lowest dominant degree of `ceilSqrtSeries p` at the unit radius is `0`. -/
theorem isLowestDominant_ceilSqrtSeries : IsLowestDominant 1 0 (ceilSqrtSeries p) :=
  isDistinguished_ceilSqrtSeries.isLowestDominant_zero

/-- The coefficient heights of `ceilSqrtSeries p` are `⌈√n⌉`. -/
theorem padicRealValuation_coeff_ceilSqrtSeries (n : ℕ) :
    padicRealValuation p (coeff n (ceilSqrtSeries p)) = ((⌈Real.sqrt n⌉₊ : ℝ) : WithTop ℝ) := by
  rw [coeff_ceilSqrtSeries, (padicRealValuation p).map_pow, padicRealValuation_p, nsmul_one]
  exact (WithTop.coe_natCast _).symm

/-- At a square index `M ^ 2` the coefficient height of `ceilSqrtSeries p` is `M`. -/
private theorem padicRealValuation_coeff_sq_ceilSqrtSeries (M : ℕ) :
    padicRealValuation p (coeff (M ^ 2) (ceilSqrtSeries p)) = ((M : ℝ) : WithTop ℝ) := by
  rw [padicRealValuation_coeff_ceilSqrtSeries, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg M),
    Nat.ceil_natCast]

/-- **The Newton polygon of `1 + ∑_{n ≥ 1} p ^ ⌈√n⌉ Xⁿ` is a horizontal ray.** Its heights are
identically `0`, although no coefficient after the constant one lies on the ray. -/
theorem newtonPolygon_ceilSqrtSeries :
    (ceilSqrtSeries p).newtonPolygon (padicRealValuation p) = 0 := by
  have h :
      IsLowerConvexEnvelope (fun n ↦ padicRealValuation p (coeff n (ceilSqrtSeries p))) 0 := by
    refine isLowerConvexEnvelope_zero ?_ (fun n ↦ ?_) fun M _ ↦
      (padicRealValuation_coeff_sq_ceilSqrtSeries M).le
    · simp
    · rw [padicRealValuation_coeff_ceilSqrtSeries]
      exact_mod_cast Nat.cast_nonneg (α := ℝ) _
  rw [newtonPolygon_def, ← h.eq_lowerConvexEnvelope]

/-- The horizontal Newton polygon of `ceilSqrtSeries p` has no finite face of slope `0`: every
line of slope `0` supporting it touches it nowhere or everywhere. So the polygon does not record
how many zeros the series has on the unit sphere. -/
theorem not_isFiniteFace_newtonPolygon_ceilSqrtSeries (l u : ℕ) :
    ¬IsFiniteFace ((ceilSqrtSeries p).newtonPolygon (padicRealValuation p)) 0 l u := by
  rw [newtonPolygon_ceilSqrtSeries]
  intro h
  obtain ⟨hlu, c, -, hface⟩ := isFiniteFace_iff.mp h
  have hl : l ∈ supportingFace (0 : ℕ → WithTop ℝ) 0 c := hface ▸ ⟨le_rfl, hlu⟩
  have hu : u + 1 ∈ supportingFace (0 : ℕ → WithTop ℝ) 0 c := by
    simpa using hl
  rw [hface] at hu
  exact absurd hu.2 (by omega)

variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]

/-- **No zeros in the closed unit disc.** In every complete normed field extension `L` of
`ℚ_[p]`, such as `ℂ_[p]`, the series `1 + ∑_{n ≥ 1} p ^ ⌈√n⌉ Xⁿ` has no zeros of norm at most
`1`: its last active index at the unit radius is `0`. -/
theorem zeroMultiset_ceilSqrtSeries : (ceilSqrtSeries p).zeroMultiset 1 L = 0 :=
  Multiset.card_eq_zero.mp <| Nat.le_zero.mp <|
    isDistinguished_ceilSqrtSeries.card_zeroMultiset_le one_pos isRestricted_one_ceilSqrtSeries

/-! ### The series with one boundary zero -/

variable (p) in
/-- The power series `1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ Xⁿ` over `ℚ_[p]`: the series
`ceilSqrtSeries p` with its linear coefficient `p` replaced by `1`. -/
noncomputable def boundaryZeroSeries : ℚ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦ if n = 1 then 1 else (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊

variable (p) in
/-- The `n`-th coefficient of `boundaryZeroSeries p` is `1` for `n = 1` and `p ^ ⌈√n⌉`
otherwise. -/
@[simp]
theorem coeff_boundaryZeroSeries (n : ℕ) :
    coeff n (boundaryZeroSeries p) = if n = 1 then 1 else (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊ :=
  coeff_mk n _

/-- Away from the linear term, `boundaryZeroSeries p` has the coefficients of
`ceilSqrtSeries p`. -/
theorem coeff_boundaryZeroSeries_of_ne_one {n : ℕ} (hn : n ≠ 1) :
    coeff n (boundaryZeroSeries p) = coeff n (ceilSqrtSeries p) := by
  simp [hn]

/-- The linear coefficient of `boundaryZeroSeries p` is `1`. -/
theorem coeff_one_boundaryZeroSeries : coeff 1 (boundaryZeroSeries p) = 1 := by
  simp

/-- `boundaryZeroSeries p` is restricted at the unit radius. -/
theorem isRestricted_one_boundaryZeroSeries : (boundaryZeroSeries p).IsRestricted 1 := by
  rw [isRestricted_iff']
  refine ((isRestricted_iff' 1 _).mp (isRestricted_one_ceilSqrtSeries (p := p))).congr' ?_
  filter_upwards [eventually_ne_atTop 1] with n hn
  rw [coeff_boundaryZeroSeries_of_ne_one hn]

/-- Every coefficient of `boundaryZeroSeries p` has norm at most `1`. -/
private theorem norm_coeff_boundaryZeroSeries_le_one (n : ℕ) :
    ‖coeff n (boundaryZeroSeries p)‖ ≤ 1 := by
  rcases eq_or_ne n 1 with rfl | hn
  · rw [coeff_one_boundaryZeroSeries, norm_one]
  · rw [coeff_boundaryZeroSeries_of_ne_one hn]
    exact norm_coeff_ceilSqrtSeries_le_one n

/-- The Gauss norm of `boundaryZeroSeries p` at the unit radius is `1`. -/
private theorem gaussNorm_one_boundaryZeroSeries :
    (boundaryZeroSeries p).gaussNorm norm 1 = 1 := by
  have h0 : ‖coeff 0 (boundaryZeroSeries p)‖ = 1 := by
    rw [coeff_boundaryZeroSeries_of_ne_one zero_ne_one, norm_coeff_zero_ceilSqrtSeries]
  rw [gaussNorm_eq_of_forall_le (s := 0) fun m ↦ ?_, h0, one_pow, mul_one]
  rw [one_pow, one_pow, mul_one, mul_one, h0]
  exact norm_coeff_boundaryZeroSeries_le_one m

/-- `boundaryZeroSeries p` is distinguished of degree `1` at the unit radius: its linear
coefficient is the last one of norm `1`. -/
theorem isDistinguished_boundaryZeroSeries : IsDistinguished 1 1 (boundaryZeroSeries p) := by
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [gaussNorm_one_boundaryZeroSeries, coeff_one_boundaryZeroSeries, norm_one, one_pow,
      mul_one]
  · rw [gaussNorm_one_boundaryZeroSeries, one_pow, mul_one,
      coeff_boundaryZeroSeries_of_ne_one hm.ne']
    exact norm_coeff_ceilSqrtSeries_lt_one (by omega)

/-- The lowest dominant degree of `boundaryZeroSeries p` at the unit radius is `0`: its constant
coefficient already has norm `1`. -/
theorem isLowestDominant_boundaryZeroSeries : IsLowestDominant 1 0 (boundaryZeroSeries p) :=
  ⟨by rw [gaussNorm_one_boundaryZeroSeries]; exact one_pos,
    by rw [gaussNorm_one_boundaryZeroSeries, pow_zero, mul_one,
      coeff_boundaryZeroSeries_of_ne_one zero_ne_one, norm_coeff_zero_ceilSqrtSeries],
    fun _ hm ↦ absurd hm (Nat.not_lt_zero _)⟩

/-- **The Newton polygon of `1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ Xⁿ` is a horizontal ray.** Its heights are
identically `0`, touching the coefficient points at `n = 0` and `n = 1` only. -/
theorem newtonPolygon_boundaryZeroSeries :
    (boundaryZeroSeries p).newtonPolygon (padicRealValuation p) = 0 := by
  have h :
      IsLowerConvexEnvelope (fun n ↦ padicRealValuation p (coeff n (boundaryZeroSeries p))) 0 := by
    refine isLowerConvexEnvelope_zero ?_ (fun n ↦ ?_) fun M hM ↦ ?_
    · simp
    · rcases eq_or_ne n 1 with rfl | hn
      · rw [coeff_one_boundaryZeroSeries, (padicRealValuation p).map_one]
      · rw [coeff_boundaryZeroSeries_of_ne_one hn, padicRealValuation_coeff_ceilSqrtSeries]
        exact_mod_cast Nat.cast_nonneg (α := ℝ) _
    · rw [coeff_boundaryZeroSeries_of_ne_one (by nlinarith),
        padicRealValuation_coeff_sq_ceilSqrtSeries]
  rw [newtonPolygon_def, ← h.eq_lowerConvexEnvelope]

/-- **Equal Newton polygons.** The two series have the same Newton polygon. -/
theorem newtonPolygon_boundaryZeroSeries_eq_newtonPolygon_ceilSqrtSeries :
    (boundaryZeroSeries p).newtonPolygon (padicRealValuation p) =
      (ceilSqrtSeries p).newtonPolygon (padicRealValuation p) := by
  rw [newtonPolygon_boundaryZeroSeries, newtonPolygon_ceilSqrtSeries]

omit [CompleteSpace L] in
/-- The preparation polynomial of `boundaryZeroSeries p` at the unit radius is linear, so it
splits over every extension. -/
private theorem exists_isUnit_isMonicOfDegree_one_mul_eq_boundaryZeroSeries :
    ∃ (e : _root_.PowerSeries.IsRestricted.subring (R := ℚ_[p]) 1) (P : Polynomial ℚ_[p]),
      IsUnit e ∧ P.IsMonicOfDegree 1 ∧ (e : ℚ_[p]⟦X⟧) * P = boundaryZeroSeries p ∧
        (P.map (algebraMap ℚ_[p] L)).Splits := by
  have hd := isDistinguished_boundaryZeroSeries (p := p)
  obtain ⟨e, P, he, hP, hf⟩ := hd.exists_isUnit_isMonicOfDegree_mul_eq
    (isUnit_iff_ne_zero.mpr hd.coeff_ne_zero) one_pos isRestricted_one_boundaryZeroSeries
  exact ⟨e, P, he, hP, hf,
    Polynomial.Splits.of_natDegree_eq_one (hP.map (algebraMap ℚ_[p] L)).natDegree_eq⟩

/-- **One zero in the closed unit disc.** In every complete normed field extension `L` of
`ℚ_[p]`, such as `ℂ_[p]`, the series `1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ Xⁿ` has exactly one zero of norm
at most `1`, counted with multiplicity. -/
theorem card_zeroMultiset_boundaryZeroSeries :
    ((boundaryZeroSeries p).zeroMultiset 1 L).card = 1 := by
  obtain ⟨e, P, he, hP, hf, hs⟩ :=
    exists_isUnit_isMonicOfDegree_one_mul_eq_boundaryZeroSeries (p := p) (L := L)
  exact isDistinguished_boundaryZeroSeries.card_zeroMultiset_eq_of_splits one_pos he hP hf hs

/-- **No zeros in the open unit disc.** In every complete normed field extension `L` of `ℚ_[p]`,
the series `1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ Xⁿ` has no zeros of norm less than `1`. -/
theorem card_filter_zeroMultiset_norm_lt_boundaryZeroSeries :
    (((boundaryZeroSeries p).zeroMultiset 1 L).filter (‖·‖ < 1)).card = 0 :=
  Nat.le_zero.mp <| isLowestDominant_boundaryZeroSeries.card_filter_zeroMultiset_norm_lt_le
    one_pos isRestricted_one_boundaryZeroSeries

/-- **One zero on the unit sphere.** In every complete normed field extension `L` of `ℚ_[p]`,
such as `ℂ_[p]`, the series `1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ Xⁿ` has exactly one zero of norm `1`,
counted with multiplicity, although its Newton polygon is the same horizontal ray as that of
`ceilSqrtSeries p`, which has none. -/
theorem card_filter_zeroMultiset_norm_eq_boundaryZeroSeries :
    (((boundaryZeroSeries p).zeroMultiset 1 L).filter (‖·‖ = 1)).card = 1 := by
  obtain ⟨e, P, he, hP, hf, hs⟩ :=
    exists_isUnit_isMonicOfDegree_one_mul_eq_boundaryZeroSeries (p := p) (L := L)
  exact card_filter_zeroMultiset_norm_eq_eq_of_splits isDistinguished_boundaryZeroSeries
    isLowestDominant_boundaryZeroSeries one_pos he hP hf hs

/-- In every complete normed field extension `L` of `ℚ_[p]`, the zeros of
`1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ Xⁿ` in the closed unit disc consist of a single simple zero, of
norm `1`. -/
theorem exists_zeroMultiset_boundaryZeroSeries_eq :
    ∃ α : L, ‖α‖ = 1 ∧ (boundaryZeroSeries p).zeroMultiset 1 L = {α} := by
  obtain ⟨α, hα⟩ := Multiset.card_eq_one.mp (card_zeroMultiset_boundaryZeroSeries (p := p) (L := L))
  refine ⟨α, le_antisymm (norm_le_of_mem_zeroMultiset (hα ▸ Multiset.mem_singleton_self α))
    (not_lt.mp fun hlt ↦ ?_), hα⟩
  have h := card_filter_zeroMultiset_norm_lt_boundaryZeroSeries (p := p) (L := L)
  simp [hα, Multiset.filter_singleton, hlt] at h

/-! ### Over `ℂ_[p]` -/

example : (ceilSqrtSeries p).zeroMultiset 1 ℂ_[p] = 0 :=
  zeroMultiset_ceilSqrtSeries

example : (((boundaryZeroSeries p).zeroMultiset 1 ℂ_[p]).filter (‖·‖ = 1)).card = 1 :=
  card_filter_zeroMultiset_norm_eq_boundaryZeroSeries

end TauCeti.NewtonPolygonBoundaryZeroExample
