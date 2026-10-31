/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.LatticeGauge.Basic
public import TauCeti.Analysis.Normed.Group.Rounding

/-!
# Discrete and scalar lattice gauges

For a scalar `π` with `0 < ‖π‖ < 1`, the normalised discrete gauge of a lattice `s` is
`inf {‖π‖ ^ n | x ∈ π ^ n • s, n ∈ ℤ}`. On every balanced absorbent set it satisfies

`latticeGauge K s x ≤ discreteLatticeGauge s π x ≤ ‖π‖⁻¹ * latticeGauge K s x`.

These are multiplicative-constant bounds, not merely an identification of topologies. They
apply to algebra lattices and module lattices alike, without discreteness of the scalar norm
or completeness. For an algebra lattice the discrete gauge is the existing Tate gauge with
base `‖π‖⁻¹` and the image of `π` as pseudo-uniformiser.

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Set Pointwise

namespace TauCeti

section NormedField

variable {K M : Type*} [NormedField K] [AddCommGroup M] [Module K M]
  {s : Set M} {π : K} {x : M}

/-- The normalised discrete lattice gauge, taking its infimum only over powers of `π`.
Its value is zero if no power absorbs `x`; use absorbency and balancedness to exclude this
empty-infimum case. -/
noncomputable def discreteLatticeGauge (s : Set M) (π : K) (x : M) : ℝ :=
  sInf ((fun n : ℤ ↦ ‖π‖ ^ n) '' {n | x ∈ (π ^ n) • s})

theorem discreteLatticeGauge_def (s : Set M) (π : K) (x : M) :
    discreteLatticeGauge s π x = sInf ((fun n : ℤ ↦ ‖π‖ ^ n) '' {n | x ∈ (π ^ n) • s}) :=
  (rfl)

/-- The radii defining a discrete gauge are bounded below by zero. -/
private theorem bddBelow_discreteLatticeGauge_radii (s : Set M) (π : K) (x : M) :
    BddBelow ((fun n : ℤ ↦ ‖π‖ ^ n) '' {n | x ∈ (π ^ n) • s}) :=
  ⟨0, by rintro _ ⟨n, -, rfl⟩; exact zpow_nonneg (norm_nonneg π) n⟩

theorem discreteLatticeGauge_nonneg (s : Set M) (π : K) (x : M) :
    0 ≤ discreteLatticeGauge s π x := by
  exact Real.sInf_nonneg fun _ ⟨n, _, hn⟩ ↦ hn ▸ zpow_nonneg (norm_nonneg π) n

/-- A discrete scalar witness bounds the discrete gauge. -/
theorem discreteLatticeGauge_le_zpow {n : ℤ} (hx : x ∈ (π ^ n) • s) :
    discreteLatticeGauge s π x ≤ ‖π‖ ^ n :=
  csInf_le (bddBelow_discreteLatticeGauge_radii s π x) ⟨n, hx, rfl⟩

/-- Round a scalar witness upwards to a power of `π`, losing less than the factor `‖π‖⁻¹`. -/
theorem exists_mem_zpow_smul_of_mem_smul (hb : Balanced K s) (hπ₀ : 0 < ‖π‖)
    (hπ₁ : ‖π‖ < 1) {c : K} (hc : c ≠ 0) (hx : x ∈ c • s) :
    ∃ n : ℤ, x ∈ (π ^ n) • s ∧ ‖c‖ ≤ ‖π‖ ^ n ∧ ‖π‖ ^ n < ‖π‖⁻¹ * ‖c‖ := by
  obtain ⟨n, hn⟩ := exists_zpowCeil_eq_zpow (c := ‖π‖) (norm_pos_iff.2 hc)
  have hle : ‖c‖ ≤ ‖π‖ ^ n := hn ▸ le_zpowCeil hπ₀ hπ₁ ‖c‖
  refine ⟨n, hb.smul_mono (by simpa using hle) hx, hle, ?_⟩
  have hlt := mul_zpowCeil_lt hπ₀ hπ₁ (norm_pos_iff.2 hc)
  rw [hn] at hlt
  exact (lt_inv_mul_iff₀ hπ₀).2 hlt

/-- Multiplication by `π ^ k` scales the discrete gauge exactly by `‖π‖ ^ k`. -/
theorem discreteLatticeGauge_zpow_smul (hπ : π ≠ 0) (k : ℤ) (x : M) :
    discreteLatticeGauge s π ((π ^ k) • x) = ‖π‖ ^ k * discreteLatticeGauge s π x := by
  have hmem (n : ℤ) : (π ^ k) • x ∈ (π ^ n) • s ↔ x ∈ (π ^ (n - k)) • s := by
    rw [mem_smul_set_iff_inv_smul_mem₀ (zpow_ne_zero n hπ),
      mem_smul_set_iff_inv_smul_mem₀ (zpow_ne_zero (n - k) hπ)]
    simp only [← zpow_neg, smul_smul, ← zpow_add₀ hπ, neg_sub, neg_add_eq_sub]
  have hradii : ((fun n : ℤ ↦ ‖π‖ ^ n) '' {n | (π ^ k) • x ∈ (π ^ n) • s}) =
      ‖π‖ ^ k • ((fun n : ℤ ↦ ‖π‖ ^ n) '' {n | x ∈ (π ^ n) • s}) := by
    ext r
    simp only [mem_image, mem_ofPred_eq, mem_smul_set, smul_eq_mul, hmem]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨_, ⟨n - k, hn, rfl⟩, by rw [← zpow_add₀ (norm_ne_zero_iff.2 hπ)]; congr 1; ring⟩
    · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      exact ⟨n + k, by simpa using hn, by rw [← zpow_add₀ (norm_ne_zero_iff.2 hπ), add_comm]⟩
  rw [discreteLatticeGauge_def, hradii, Real.sInf_smul_of_nonneg
    (zpow_nonneg (norm_nonneg π) k), smul_eq_mul, ← discreteLatticeGauge_def]

/-- The discrete gauge vanishes at zero, including when the set of witnesses is empty. -/
@[simp]
theorem discreteLatticeGauge_zero (hπ₀ : 0 < ‖π‖) (hπ₁ : ‖π‖ < 1) (s : Set M) :
    discreteLatticeGauge s π 0 = 0 := by
  have h := discreteLatticeGauge_zpow_smul (s := s) (norm_pos_iff.1 hπ₀) 1 (0 : M)
  simp only [smul_zero, zpow_one] at h
  nlinarith [discreteLatticeGauge_nonneg s π 0]

end NormedField

section NontriviallyNormedField

variable {K M : Type*} [NontriviallyNormedField K] [AddCommGroup M] [Module K M]
  {s : Set M} {π : K} {x : M}

/-- Balanced absorbent sets have a nonempty family of discrete scalar witnesses. -/
private theorem nonempty_discreteLatticeGauge_radii (hb : Balanced K s) (hs : Absorbent K s)
    (hπ₀ : 0 < ‖π‖) (hπ₁ : ‖π‖ < 1) (x : M) :
    ((fun n : ℤ ↦ ‖π‖ ^ n) '' {n | x ∈ (π ^ n) • s}).Nonempty := by
  obtain ⟨c, hc, hx, -⟩ := (latticeGauge_lt_iff hs).1 (lt_add_one (latticeGauge K s x))
  obtain ⟨n, hn, -⟩ := exists_mem_zpow_smul_of_mem_smul hb hπ₀ hπ₁ hc hx
  exact ⟨_, n, hn, rfl⟩

/-- Below any strict bound for the discrete gauge there is an actual discrete witness. -/
theorem discreteLatticeGauge_lt_iff (hb : Balanced K s) (hs : Absorbent K s)
    (hπ₀ : 0 < ‖π‖) (hπ₁ : ‖π‖ < 1) {r : ℝ} :
    discreteLatticeGauge s π x < r ↔ ∃ n : ℤ, x ∈ (π ^ n) • s ∧ ‖π‖ ^ n < r := by
  rw [discreteLatticeGauge_def,
    csInf_lt_iff (bddBelow_discreteLatticeGauge_radii s π x)
      (nonempty_discreteLatticeGauge_radii hb hs hπ₀ hπ₁ x)]
  simp

/-- The scalar lattice gauge is at most the normalised discrete gauge. -/
theorem latticeGauge_le_discreteLatticeGauge (hb : Balanced K s) (hs : Absorbent K s)
    (hπ₀ : 0 < ‖π‖) (hπ₁ : ‖π‖ < 1) (x : M) :
    latticeGauge K s x ≤ discreteLatticeGauge s π x := by
  refine le_csInf (nonempty_discreteLatticeGauge_radii hb hs hπ₀ hπ₁ x) ?_
  rintro _ ⟨n, hn, rfl⟩
  simpa using latticeGauge_le_norm (zpow_ne_zero n (norm_pos_iff.1 hπ₀)) hn

/-- Rounding a scalar witness costs at most the factor `‖π‖⁻¹`, even when the scalar value
group is not discrete and neither infimum is attained. -/
theorem discreteLatticeGauge_le_inv_mul_latticeGauge (hb : Balanced K s) (hs : Absorbent K s)
    (hπ₀ : 0 < ‖π‖) (hπ₁ : ‖π‖ < 1) (x : M) :
    discreteLatticeGauge s π x ≤ ‖π‖⁻¹ * latticeGauge K s x := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  have hr' : latticeGauge K s x < ‖π‖ * r := (inv_mul_lt_iff₀ hπ₀).1 hr
  obtain ⟨c, hc, hx, hcr⟩ := (latticeGauge_lt_iff hs).1 hr'
  obtain ⟨n, hn, -, hnc⟩ := exists_mem_zpow_smul_of_mem_smul hb hπ₀ hπ₁ hc hx
  exact (discreteLatticeGauge_le_zpow hn).trans
    (hnc.trans ((inv_mul_lt_iff₀ hπ₀).2 hcr)).le

end NontriviallyNormedField

end TauCeti
