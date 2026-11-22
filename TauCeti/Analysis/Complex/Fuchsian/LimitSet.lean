/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Compactification
public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Endpoint
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.GroupTheory.GroupAction.ConjAct

/-!
# Limit sets of subgroups of `PSL(2, ℝ)`

The limit set `Λ(Γ)` of a subgroup `Γ` of `PSL(2, ℝ)` is the set of ideal points of
`∂ℍ = OnePoint ℝ`, including `∞`, at which an orbit `Γ • z` accumulates in the Riemann sphere,
that is, in the compactification `ℍ ∪ ∂ℍ`, a closed disc. It is the ideal boundary
(`TauCeti.UpperHalfPlane.idealBoundary`) of an orbit. Orbits of two points stay within bounded
hyperbolic distance of each other, so the limit set does not depend on the orbit. No discreteness
or finite generation is assumed in the definition.

Limit sets are the input to the convex core of a Fuchsian group: the group is of the first kind
when its limit set is the whole circle and of the second kind otherwise, and its Nielsen region is
the hyperbolic convex hull of its limit set.

## Main statements

* `Subgroup.limitSet`: the limit set, defined with the orbit of `i`.
* `Subgroup.limitSet_eq_idealBoundary_orbit`: any orbit may be used instead.
* `Subgroup.coe_mem_limitSet_iff`, `Subgroup.infty_mem_limitSet_iff`: a real point is a limit
  point when an orbit comes arbitrarily close to it, and `∞` is when an orbit is unbounded.
* `Subgroup.isClosed_limitSet`: the limit set is closed.
* `Subgroup.limitSet_conjAct_smul`: `Λ(g Γ g⁻¹) = g • Λ(Γ)`; in particular `Γ` preserves its
  limit set (`Subgroup.smul_limitSet`).
* `Subgroup.limitSet_eq_empty_of_finite`: a finite group has empty limit set.
* `Subgroup.limitSet_zpowers_upperRightHom`: a group of translations `z ↦ z + k t` has limit set
  `{∞}`.
* `Subgroup.limitSet_zpowers_dilation`: a group of dilations `z ↦ exp (k s) z` has limit set
  `{0, ∞}`.
* `Subgroup.limitSet_zpowers_of_two_lt_abs_trace`: a cyclic hyperbolic group has limit set the two
  fixed points of its generator, conjugating it to a group of dilations.
* `Subgroup.mem_limitSet_of_smul_eq`: hence the fixed points of a hyperbolic element of `Γ` are
  limit points.

## References

* Zhipeng Lu, *Geodesic cover of Fuchsian groups*, Ann. Math. Blaise Pascal 30 (2023), 189–199,
  §3.1 (the limit set, its independence of the orbit, and the fixed points of hyperbolic
  elements).
* W. Duke, Ö. Imamoglu and Á. Tóth, *Geometric invariants for real quadratic fields*, Ann. of
  Math. 184 (2016), 949–990, §2 (the limit set and the Nielsen region).
-/

public section

noncomputable section

open MulAction Set UpperHalfPlane TauCeti.UpperHalfPlane
open scoped MatrixGroups OnePoint Pointwise

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ))

/-- The **limit set** of a subgroup `Γ` of `PSL(2, ℝ)`: the ideal points of `∂ℍ = OnePoint ℝ` at
which the orbit `Γ • i` accumulates in the Riemann sphere. It does not depend on the basepoint
(`Subgroup.limitSet_eq_idealBoundary_orbit`). -/
def limitSet : Set (OnePoint ℝ) :=
  idealBoundary (orbit Γ UpperHalfPlane.I)

/-- The limit set is the set of ideal points at which the orbit of any point accumulates. -/
theorem limitSet_eq_idealBoundary_orbit (z : ℍ) : Γ.limitSet = idealBoundary (orbit Γ z) := by
  have key (z w : ℍ) : idealBoundary (orbit Γ z) ⊆ idealBoundary (orbit Γ w) :=
    idealBoundary_subset_of_forall_exists_dist_le (C := dist z w) <| by
      rintro _ ⟨γ, rfl⟩
      exact ⟨γ • w, mem_orbit w γ, by simp [Subgroup.smul_def, dist_smul]⟩
  exact (key _ _).antisymm (key _ _)

/-- A real point is a limit point exactly when the orbit of `z` comes arbitrarily close to it. -/
theorem coe_mem_limitSet_iff (z : ℍ) {x : ℝ} :
    (x : OnePoint ℝ) ∈ Γ.limitSet ↔ ∀ ε > 0, ∃ γ ∈ Γ, dist ((γ • z : ℍ) : ℂ) x < ε := by
  simp [limitSet_eq_idealBoundary_orbit Γ z, coe_mem_idealBoundary_iff, orbit, Subgroup.smul_def]

/-- The point `∞` is a limit point exactly when the orbit of `z` is unbounded in `ℂ`. -/
theorem infty_mem_limitSet_iff (z : ℍ) :
    ∞ ∈ Γ.limitSet ↔ ∀ r : ℝ, ∃ γ ∈ Γ, r < ‖((γ • z : ℍ) : ℂ)‖ := by
  simp [limitSet_eq_idealBoundary_orbit Γ z, infty_mem_idealBoundary_iff, orbit,
    Subgroup.smul_def]

/-- The limit set is closed in the ideal boundary. -/
theorem isClosed_limitSet : IsClosed Γ.limitSet :=
  isClosed_idealBoundary _

variable {Γ} in
@[gcongr]
theorem limitSet_mono {Γ' : Subgroup PSL(2, ℝ)} (h : Γ ≤ Γ') : Γ.limitSet ⊆ Γ'.limitSet :=
  idealBoundary_mono <| by
    rintro _ ⟨γ, rfl⟩
    exact ⟨⟨γ, h γ.property⟩, rfl⟩

/-- The limit set of a conjugate `g Γ g⁻¹` is the translate by `g` of the limit set of `Γ`. -/
theorem limitSet_conjAct_smul (g : PSL(2, ℝ)) :
    (ConjAct.toConjAct g • Γ).limitSet = g • Γ.limitSet := by
  rw [limitSet_eq_idealBoundary_orbit _ (g • UpperHalfPlane.I),
    TauCeti.MulAction.orbit_smul_of_conjAct_smul_eq rfl, idealBoundary_smul, limitSet]

/-- The limit set of `Γ` is invariant under `Γ`. -/
theorem smul_limitSet {γ : PSL(2, ℝ)} (hγ : γ ∈ Γ) : γ • Γ.limitSet = Γ.limitSet := by
  rw [← limitSet_conjAct_smul, conjAct_pointwise_smul_eq_self (le_normalizer hγ)]

/-- A finite subgroup has empty limit set. -/
theorem limitSet_eq_empty_of_finite [Finite Γ] : Γ.limitSet = ∅ :=
  idealBoundary_eq_empty_of_isBounded (finite_range _).isBounded

open Matrix.ProjectiveSpecialLinearGroup in
/-- **The limit set of a translation group is `{∞}`**: the orbit of `i` under the translations
by the multiples of `t ≠ 0` runs off to `∞` along the horizontal line at height `1`. In
particular a cyclic parabolic group is elementary. -/
theorem limitSet_zpowers_upperRightHom {t : ℝ} (ht : t ≠ 0) :
    (zpowers (upperRightHom t)).limitSet = {∞} := by
  have hpow (k : ℤ) : upperRightHom t ^ k • UpperHalfPlane.I = (k * t) +ᵥ UpperHalfPlane.I := by
    rw [← AddChar.map_zsmul_eq_zpow, upperRightHom_smul, zsmul_eq_mul]
  ext ξ
  induction ξ using OnePoint.rec with
  | infty =>
    simp only [mem_singleton_iff, iff_true, infty_mem_limitSet_iff _ UpperHalfPlane.I,
      mem_zpowers_iff, exists_exists_eq_and, hpow]
    intro r
    obtain ⟨k, hk⟩ := exists_int_gt (r / |t|)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ (abs_pos.2 ht)] at hk
    calc r < k * |t| := hk
      _ ≤ |(k : ℝ)| * |t| := by gcongr; exact le_abs_self _
      _ = |(((k * t) +ᵥ UpperHalfPlane.I : ℍ) : ℂ).re| := by simp [abs_mul]
      _ ≤ ‖(((k * t) +ᵥ UpperHalfPlane.I : ℍ) : ℂ)‖ := Complex.abs_re_le_norm _
  | coe x =>
    simp only [mem_singleton_iff, OnePoint.coe_ne_infty, iff_false,
      coe_mem_limitSet_iff _ UpperHalfPlane.I, mem_zpowers_iff, exists_exists_eq_and, hpow,
      not_forall, not_exists, not_lt]
    refine ⟨1, one_pos, fun k ↦ ?_⟩
    calc (1 : ℝ) = |((((k * t) +ᵥ UpperHalfPlane.I : ℍ) : ℂ) - x).im| := by simp
      _ ≤ dist (((k * t) +ᵥ UpperHalfPlane.I : ℍ) : ℂ) x := by
        rw [Complex.dist_eq]; exact Complex.abs_im_le_norm _

open Matrix.SpecialLinearGroup (dilation dilation_zpow) in
/-- **A cyclic group of dilations has limit set `{0, ∞}`**: the orbit `exp (k s) • i` of `i` runs
up the imaginary axis to `∞` and down to `0`. -/
theorem limitSet_zpowers_dilation {s : ℝ} (hs : s ≠ 0) :
    (zpowers ((dilation s : SL(2, ℝ)) : PSL(2, ℝ))).limitSet = {((0 : ℝ) : OnePoint ℝ), ∞} := by
  wlog hs' : 0 < s generalizing s
  · have h := this (neg_ne_zero.2 hs) (neg_pos.2 (lt_of_le_of_ne (not_lt.1 hs') hs))
    rwa [← Matrix.SpecialLinearGroup.dilation_inv, QuotientGroup.mk_inv, zpowers_inv] at h
  have hpow (k : ℤ) : ((((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) ^ k • UpperHalfPlane.I : ℍ) : ℂ) =
      (Real.exp (k * s) : ℂ) * Complex.I := by
    rw [← QuotientGroup.mk_zpow, dilation_zpow, UpperHalfPlane.pslMk_smul, coe_dilation_smul,
      UpperHalfPlane.coe_I]
  have hnorm (k : ℤ) : ‖(Real.exp (k * s) : ℂ) * Complex.I‖ = Real.exp (k * s) := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  ext ξ
  induction ξ using OnePoint.rec with
  | infty =>
    simp only [mem_insert_iff, mem_singleton_iff, OnePoint.infty_ne_coe, or_true, iff_true,
      infty_mem_limitSet_iff _ UpperHalfPlane.I, mem_zpowers_iff, exists_exists_eq_and, hpow]
    intro r
    obtain ⟨k, hk⟩ := exists_int_gt (r / s)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hs'] at hk
    calc r < k * s := hk
      _ < Real.exp (k * s) := by linarith [Real.add_one_le_exp (k * s)]
      _ = ‖(Real.exp (k * s) : ℂ) * Complex.I‖ := (hnorm k).symm
  | coe x =>
    simp only [mem_insert_iff, mem_singleton_iff, OnePoint.coe_ne_infty, or_false,
      OnePoint.coe_eq_coe, coe_mem_limitSet_iff _ UpperHalfPlane.I, mem_zpowers_iff,
      exists_exists_eq_and, hpow]
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [iff_true, Complex.ofReal_zero, dist_zero_right]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_int_lt (Real.log ε / s)
      refine ⟨k, ?_⟩
      rw [lt_div_iff₀ hs'] at hk
      calc ‖(Real.exp (k * s) : ℂ) * Complex.I‖ = Real.exp (k * s) := hnorm k
        _ < Real.exp (Real.log ε) := Real.exp_lt_exp.2 hk
        _ = ε := Real.exp_log hε
    · simp only [hx, iff_false, not_forall, not_exists, not_lt]
      refine ⟨|x|, abs_pos.2 hx, fun k ↦ ?_⟩
      calc |x| = |((Real.exp (k * s) : ℂ) * Complex.I - x).re| := by
            rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, zero_sub,
              Complex.ofReal_re, abs_neg]
        _ ≤ dist ((Real.exp (k * s) : ℂ) * Complex.I) x := by
          rw [Complex.dist_eq]; exact Complex.abs_re_le_norm _

open Matrix.SpecialLinearGroup (dilation) in
/-- **The limit set of a cyclic hyperbolic group is the fixed-point set of its generator**, a
pair of ideal points
(`Matrix.ProjectiveSpecialLinearGroup.exists_ne_smul_eq_self_of_two_lt_abs_trace`). In particular
a cyclic hyperbolic group is elementary. -/
theorem limitSet_zpowers_of_two_lt_abs_trace {A : SL(2, ℝ)}
    (htr : 2 < |(A : Matrix (Fin 2) (Fin 2) ℝ).trace|) :
    (zpowers (A : PSL(2, ℝ))).limitSet = {ξ | (A : PSL(2, ℝ)) • ξ = ξ} := by
  -- `A` is conjugate to a nontrivial dilation, whose fixed points are `0` and `∞`
  obtain ⟨g, s, hs, hA⟩ := exists_eq_conj_dilation_of_two_lt_abs_trace htr
  have hz : zpowers (A : PSL(2, ℝ)) =
      ConjAct.toConjAct g • zpowers ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) := by
    ext x
    rw [Subgroup.mem_conjAct_smul_iff, mem_zpowers_iff, mem_zpowers_iff, hA]
    refine exists_congr fun k ↦ ?_
    rw [conj_zpow]
    constructor
    · rintro rfl
      group
    · intro h
      rw [h]
      group
  have hfix (ξ : OnePoint ℝ) :
      (A : PSL(2, ℝ)) • ξ = ξ ↔ g⁻¹ • ξ ∈ ({((0 : ℝ) : OnePoint ℝ), ∞} : Set (OnePoint ℝ)) := by
    rw [hA, mul_smul, mul_smul, ← eq_inv_smul_iff]
    generalize g⁻¹ • ξ = η
    induction η using OnePoint.rec with
    | infty =>
      rw [dilation_smul_infty]
      simp
    | coe x =>
      rw [dilation_smul_coe, OnePoint.coe_eq_coe, eq_comm]
      simp only [mem_insert_iff, mem_singleton_iff, OnePoint.coe_ne_infty, or_false,
        OnePoint.coe_eq_coe]
      constructor
      · intro h
        have : (Real.exp s - 1) * x = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left
          (sub_ne_zero.2 fun h1 ↦ hs (Real.exp_eq_one_iff s |>.1 h1))
      · rintro rfl
        simp
  rw [hz, limitSet_conjAct_smul, limitSet_zpowers_dilation hs]
  ext ξ
  rw [mem_smul_set_iff_inv_smul_mem]
  exact (hfix ξ).symm

/-- **The fixed points of a hyperbolic element of `Γ` are limit points.** An element of `Γ`
represented by a matrix whose trace has absolute value greater than `2` fixes two ideal points,
and both lie in the limit set of `Γ`. -/
theorem mem_limitSet_of_smul_eq {A : SL(2, ℝ)} (hA : (A : PSL(2, ℝ)) ∈ Γ)
    (htr : 2 < |(A : Matrix (Fin 2) (Fin 2) ℝ).trace|) {ξ : OnePoint ℝ}
    (hξ : (A : PSL(2, ℝ)) • ξ = ξ) : ξ ∈ Γ.limitSet :=
  limitSet_mono (zpowers_le.2 hA) <| by
    rw [limitSet_zpowers_of_two_lt_abs_trace htr]
    exact hξ

end Subgroup
