/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
import TauCeti.Analysis.Complex.Fuchsian.Margulis
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.Fuchsian.Systole
import TauCeti.Analysis.Complex.UpperHalfPlane.Displacement
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.MeasureTheory.Group.Action

/-!
# A cofinite Fuchsian group has finitely many elliptic orbits

Let `Γ ≤ PSL(2, ℝ)` be cofinite. An *elliptic point* of `Γ` is a point `w ∈ ℍ` fixed by a
nonidentity element of `Γ`. This file shows that the thin part of `Γ \ ℍ` near the elliptic points
is controlled uniformly, and deduces that `Γ` has only finitely many orbits of elliptic points.

* **Separation.** There is `c > 0` such that every element of `Γ` either fixes a given elliptic
  point `w` or moves it at least `c`. If `g ≠ 1` fixes `w` and `k • w ≠ w`, then the commutator
  `⁅g, k⁆` has trace `2 + (4 - tr² g) / 2 · (cosh (dist (k • w) w) - 1) > 2`, so it is hyperbolic.
  It moves `k • w` to `g • k • w`, at most twice as far as `k` moves `w`. Since the hyperbolic
  elements of a cofinite group move every point at least a fixed positive distance
  (`Subgroup.IsCofinite.exists_pos_le_dist_smul_of_two_lt_abs_trace`), this bounds the
  displacement of `w` below.
* **Elliptic thin parts.** There is `τ > 0` such that a point moved less than `τ` by a nonidentity
  element `g` fixing `w` is moved at least `τ` by every element of `Γ` not fixing `w`. If `g`
  rotates through a small angle, so that `4 - tr² g` is small, this is the Margulis lemma in trace
  form (`Subgroup.conj_eq_or_conj_eq_inv_of_cosh_dist`): an element `k` moving the point little
  conjugates `g` to `g` or `g⁻¹`, so `k` fixes the fixed point `w` of `g`. Otherwise the point is
  close to `w`, and an element moving it little moves `w` less than the separation constant.
* **Finiteness.** At each elliptic point `w` choose a nonidentity `g` fixing `w` whose rotation
  angle is least, and a point `y` that `g` moves exactly `τ / 2`. Every other element fixing `w`
  moves `y` at least as far, and every element not fixing `w` moves it at least `τ`, so `y` is
  `τ / 2`-thick. The ball of radius `τ / 4` about `y` lies in the `τ`-thin part of `w`, so by the
  previous point the balls chosen at representatives of distinct elliptic orbits have pairwise
  disjoint translates. They all have the same positive area, and a fundamental domain has finite
  area, so there are only finitely many elliptic orbits.

Compare `Subgroup.finite_ellipticOrbits`, which deduces the same finiteness from compactness of
the cusp compactification. Here finite covolume suffices, as is needed to bound the part of a
Dirichlet domain lying in the thin part near elliptic points.

## Main results

* `Subgroup.IsCofinite.exists_pos_le_dist_smul_of_smul_eq_self`: the elliptic points of a cofinite
  group are moved at least a fixed positive distance by every element not fixing them.
* `Subgroup.IsCofinite.exists_pos_le_dist_smul_of_dist_smul_lt`: a point moved little by an
  element fixing an elliptic point `w` is moved far by every element not fixing `w`.
* `Subgroup.IsCofinite.finite_ellipticOrbits`: a cofinite Fuchsian group has finitely many
  elliptic orbits.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.2 (finitely many elliptic cycles, deduced there from Siegel's theorem).
* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the thick-thin decomposition of a finite-volume hyperbolic
  manifold).
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §5.4 (Jørgensen's inequality and its consequences).
-/

public section

open Filter MeasureTheory Metric MulAction Set TauCeti TauCeti.UpperHalfPlane UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise Topology commutatorElement

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- **Elliptic points of a cofinite group are not moved a short distance.** For a cofinite
`Γ ≤ PSL(2, ℝ)` there is `c > 0` such that if a nonidentity element of `Γ` fixes `w ∈ ℍ`, then
every element of `Γ` not fixing `w` moves it a hyperbolic distance at least `c`. -/
theorem IsCofinite.exists_pos_le_dist_smul_of_smul_eq_self (hΓ : Γ.IsCofinite) :
    ∃ c > 0, ∀ g ∈ Γ, g ≠ 1 → ∀ w : ℍ, g • w = w → ∀ k ∈ Γ, k • w ≠ w →
      c ≤ dist (k • w) w := by
  obtain ⟨δ, hδ, hδA⟩ := hΓ.exists_pos_le_dist_smul_of_two_lt_abs_trace
  refine ⟨δ / 2, half_pos hδ, fun g hg hg₁ w hgw k hk hkw ↦ ?_⟩
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective k
  rw [pslMk_smul] at hgw hkw ⊢
  -- `A` is elliptic, so the commutator `⁅A, B⁆` has trace greater than `2`
  have hell := (Matrix.isElliptic_iff_abs_trace_lt_two A.det_coe).1
    (Matrix.SpecialLinearGroup.isElliptic_of_smul_eq_self_of_ne_one hgw hg₁)
  have htr : 2 < |((⁅A, B⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| := by
    rw [Matrix.SpecialLinearGroup.trace_commutatorElement_of_smul_eq_self hgw B]
    have h₄ : 0 < 4 - (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 := by
      nlinarith [abs_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ).trace,
        sq_abs (A : Matrix (Fin 2) (Fin 2) ℝ).trace]
    have h₁ : 1 < Real.cosh (dist (B • w) w) := Real.one_lt_cosh.2 (dist_ne_zero.2 hkw)
    have hpos : 0 < (4 - (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) / 2 *
        (Real.cosh (dist (B • w) w) - 1) := mul_pos (half_pos h₄) (sub_pos.2 h₁)
    rw [abs_of_pos (by linarith)]
    linarith
  have hmem : ((⁅A, B⁆ : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hg hk) (Γ.inv_mem hg)) (Γ.inv_mem hk)
  -- the commutator moves `B • w` to `A • B • w`, at most twice as far as `B` moves `w`
  have h := hδA _ hmem htr (B • w)
  have hA : A⁻¹ • w = w := by rw [inv_smul_eq_iff, hgw]
  rw [commutatorElement_def, mul_smul, mul_smul, mul_smul, inv_smul_smul, hA] at h
  have hAB : dist (A • B • w) w = dist (B • w) w := by
    rw [show dist (A • B • w) w = dist (A • B • w) (A • w) by rw [hgw], dist_smul]
  have := dist_triangle (A • B • w) w (B • w)
  rw [hAB, dist_comm w] at this
  linarith

/-- **The thin part at an elliptic point.** For a cofinite `Γ ≤ PSL(2, ℝ)` there is `τ > 0` with
the following property. If a nonidentity element `g ∈ Γ` fixes `w ∈ ℍ` and moves `y ∈ ℍ` less
than `τ`, then every element of `Γ` not fixing `w` moves `y` a hyperbolic distance at least `τ`.
In particular the `τ`-thin parts of distinct elliptic points are disjoint. -/
theorem IsCofinite.exists_pos_le_dist_smul_of_dist_smul_lt (hΓ : Γ.IsCofinite) :
    ∃ τ > 0, ∀ g ∈ Γ, g ≠ 1 → ∀ w : ℍ, g • w = w → ∀ k ∈ Γ, k • w ≠ w → ∀ y : ℍ,
      dist (g • y) y < τ → τ ≤ dist (k • y) y := by
  have := hΓ.discreteTopology
  obtain ⟨c, hc, hcA⟩ := hΓ.exists_pos_le_dist_smul_of_smul_eq_self
  have hs : 0 < Real.sinh (c / 4) ^ 2 := pow_pos (Real.sinh_pos_iff.2 (by positivity)) 2
  -- choose `τ` small enough for the Margulis lemma and for the separation constant `c`
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ ≤ c / 2 ∧
      4 * (Real.cosh τ * Real.cosh τ - 1) < 1 / 2 ∧
      4 * (Real.cosh τ - 1) < Real.sinh (c / 4) ^ 2 := by
    have h₁ : Tendsto (fun τ ↦ 4 * (Real.cosh τ * Real.cosh τ - 1)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const.mul ((Real.continuous_cosh.mul Real.continuous_cosh).sub
        continuous_const)).tendsto (0 : ℝ) (f := fun τ ↦ 4 * (Real.cosh τ * Real.cosh τ - 1))
    have h₂ : Tendsto (fun τ ↦ 4 * (Real.cosh τ - 1)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const.mul (Real.continuous_cosh.sub continuous_const)).tendsto
        (0 : ℝ) (f := fun τ ↦ 4 * (Real.cosh τ - 1))
    exact eventually_mem_nhdsWithin.and <| ((eventually_le_nhds (half_pos hc)).and
      ((h₁.eventually (gt_mem_nhds (by norm_num))).and
        (h₂.eventually (gt_mem_nhds hs)))).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ, hτ, hτc, hτM, hτs⟩ := hev.exists
  refine ⟨τ, hτ, fun g hg hg₁ w hgw k hk hkw y hgy ↦ ?_⟩
  by_contra! hky
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective k
  have hAw : A • w = w := (pslMk_smul A w).symm.trans hgw
  rw [pslMk_smul] at hgy hky
  set t := (A : Matrix (Fin 2) (Fin 2) ℝ).trace
  have hell := (Matrix.isElliptic_iff_abs_trace_lt_two A.det_coe).1
    (Matrix.SpecialLinearGroup.isElliptic_of_smul_eq_self_of_ne_one hAw hg₁)
  have ht : t ^ 2 < 4 := by nlinarith [abs_nonneg t, sq_abs t]
  have hcosh_lt {d : ℝ} (hd₀ : 0 ≤ d) (hd : d < τ) : Real.cosh d < Real.cosh τ := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg hd₀, abs_of_pos hτ]
    exact hd
  have hgτ := hcosh_lt dist_nonneg hgy
  have hkτ := hcosh_lt dist_nonneg hky
  have hdisp := Matrix.SpecialLinearGroup.cosh_dist_smul_of_smul_eq_self hAw y
  by_cases hsmall : 4 - t ^ 2 < 1 / 2
  · -- a small rotation: by the Margulis lemma `k` conjugates `g` to `g^{± 1}`, so it fixes `w`
    have hM := conj_eq_or_conj_eq_inv_of_cosh_dist hg hk y (by
      rw [abs_of_neg (by linarith : t ^ 2 - 4 < 0)]
      have h₁ := Real.one_le_cosh (dist (A • y) y)
      have h₂ := Real.one_le_cosh (dist (B • y) y)
      have hτ₁ := Real.one_le_cosh τ
      nlinarith [mul_le_mul hgτ.le hkτ.le (by linarith) (by linarith)])
    refine hkw ?_
    by_contra hne
    have hfix : ((B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹) • ((B : PSL(2, ℝ)) • w) =
        (B : PSL(2, ℝ)) • w := by
      rw [mul_smul, mul_smul, inv_smul_smul, hgw]
    have hgw' : (A : PSL(2, ℝ))⁻¹ • w = w := by rw [inv_smul_eq_iff, hgw]
    rcases hM with h | h <;> rw [h] at hfix
    · exact hg₁ (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self hgw
        hfix hne)
    · exact hg₁ (inv_eq_one.1
        (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self hgw' hfix hne))
  · -- a large rotation: `y` is close to `w`, so `k` moves `w` less than `c`
    rw [not_lt] at hsmall
    have hsinh : Real.sinh (dist y w) ^ 2 < Real.sinh (c / 4) ^ 2 := by
      nlinarith [sq_nonneg (Real.sinh (dist y w))]
    rw [sq_lt_sq, abs_of_nonneg (Real.sinh_nonneg_iff.2 dist_nonneg),
      abs_of_pos (Real.sinh_pos_iff.2 (by positivity))] at hsinh
    have hyw := Real.sinh_lt_sinh.1 hsinh
    have hkw' := hcA _ hg hg₁ w hgw _ hk hkw
    rw [pslMk_smul] at hkw'
    have := dist_triangle4 (B • w) (B • y) y w
    rw [dist_smul, dist_comm w y] at this
    linarith

/-- At an elliptic point `w` of `Γ`, given `τ` as in
`Subgroup.IsCofinite.exists_pos_le_dist_smul_of_dist_smul_lt`, there are a nonidentity `g ∈ Γ`
fixing `w` and a `τ / 2`-thick point `y` that `g` moves exactly `τ / 2`. The element `g` is one
of least rotation angle about `w`, and `y` lies on a geodesic through `w`. -/
private theorem exists_dist_smul_eq_and_forall_le [DiscreteTopology Γ] {τ : ℝ} (hτ : 0 < τ)
    (hP : ∀ g ∈ Γ, g ≠ 1 → ∀ w : ℍ, g • w = w → ∀ k ∈ Γ, k • w ≠ w → ∀ y : ℍ,
      dist (g • y) y < τ → τ ≤ dist (k • y) y)
    {g : PSL(2, ℝ)} (hg : g ∈ Γ) (hg₁ : g ≠ 1) {w : ℍ} (hgw : g • w = w) :
    ∃ g₀ ∈ Γ, g₀ ≠ 1 ∧ g₀ • w = w ∧ ∃ y : ℍ, dist (g₀ • y) y = τ / 2 ∧
      ∀ k ∈ Γ, k ≠ 1 → τ / 2 ≤ dist (k • y) y := by
  -- the nonidentity elements of `Γ` fixing `w` form a finite set; take one moving `y₀` least
  set S : Set PSL(2, ℝ) := {k | k ∈ Γ ∧ k ≠ 1 ∧ k • w = w}
  have hS : S.Finite := by
    refine ((ProperlyDiscontinuousSMul.finite_stabilizer' Γ w).image Subtype.val).subset ?_
    rintro k ⟨hk, -, hkw⟩
    exact ⟨⟨k, hk⟩, hkw, rfl⟩
  obtain ⟨G, hG⟩ := exists_geodesicLine_zero_eq w
  have hdist (a : ℝ) (ha : 0 ≤ a) : dist (geodesicLine G a) w = a := by
    rw [← hG, dist_geodesicLine, sub_zero, abs_of_nonneg ha]
  set y₀ := geodesicLine G 1
  have hy₀ : y₀ ≠ w := fun h ↦ by
    have h₁ := hdist 1 zero_le_one
    rw [show geodesicLine G 1 = w from h, dist_self] at h₁
    exact zero_ne_one h₁
  obtain ⟨g₀, ⟨hg₀, hg₀₁, hg₀w⟩, hmin⟩ :=
    S.exists_min_image (fun k ↦ dist (k • y₀) y₀) hS ⟨g, hg, hg₁, hgw⟩
  -- `g₀` moves each `y` a distance `δ` with `cosh δ = 1 + κ sinh² (dist y w)`, where `κ > 0`
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective g₀
  have hAw : A • w = w := (pslMk_smul A w).symm.trans (hA ▸ hg₀w)
  set κ := (4 - (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) / 2
  have hκ (y : ℍ) : Real.cosh (dist (g₀ • y) y) = 1 + κ * Real.sinh (dist y w) ^ 2 := by
    rw [← hA, pslMk_smul]
    exact Matrix.SpecialLinearGroup.cosh_dist_smul_of_smul_eq_self hAw y
  have hκ₀ : 0 < κ := by
    have hne : g₀ • y₀ ≠ y₀ := fun h ↦ hg₀₁
      (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self hg₀w h hy₀)
    have h₁ := Real.one_lt_cosh.2 (dist_ne_zero.2 hne)
    rw [hκ, hdist 1 zero_le_one] at h₁
    exact pos_of_mul_pos_left (by linarith) (sq_nonneg _)
  -- the point `y` at distance `a` from `w` with `κ sinh² a = cosh (τ / 2) - 1`
  set a := Real.arsinh (√((Real.cosh (τ / 2) - 1) / κ))
  have ha : 0 ≤ a := Real.arsinh_nonneg_iff.2 (Real.sqrt_nonneg _)
  set y := geodesicLine G a
  have hgy : dist (g₀ • y) y = τ / 2 := by
    have h := hκ y
    rw [hdist a ha, Real.sinh_arsinh,
      Real.sq_sqrt (div_nonneg (sub_nonneg.2 (Real.one_le_cosh _)) hκ₀.le),
      mul_div_cancel₀ _ hκ₀.ne', add_sub_cancel] at h
    have h₁ := Real.cosh_le_cosh.1 h.le
    have h₂ := Real.cosh_le_cosh.1 h.ge
    rw [abs_dist, abs_of_pos (half_pos hτ)] at h₁ h₂
    exact le_antisymm h₁ h₂
  refine ⟨g₀, hg₀, hg₀₁, hg₀w, y, hgy, fun k hk hk₁ ↦ ?_⟩
  by_cases hkw : k • w = w
  · rw [← hgy]
    exact Matrix.ProjectiveSpecialLinearGroup.dist_smul_le_dist_smul_of_smul_eq_self hg₀w hkw hy₀
      (hmin k ⟨hk, hk₁, hkw⟩) y
  · exact (half_le_self hτ.le).trans
      (hP g₀ hg₀ hg₀₁ w hg₀w k hk hkw y (by rw [hgy]; exact half_lt_self hτ))

/-- Let `τ` be as in `Subgroup.IsCofinite.exists_pos_le_dist_smul_of_dist_smul_lt`, and for
`i = 1, 2` let a nonidentity `gᵢ ∈ Γ` fix `wᵢ` and move `yᵢ` exactly `τ / 2`. If the ball of
radius `τ / 4` about `y₂` meets the `k`-translate of the ball about `y₁`, for some `k ∈ Γ`, then
`k • w₁ = w₂`: the meeting point is moved less than `τ` by `g₂` and by `k g₁ k⁻¹`, which fixes
`k • w₁`. -/
private theorem smul_eq_of_dist_lt {τ : ℝ}
    (hP : ∀ g ∈ Γ, g ≠ 1 → ∀ w : ℍ, g • w = w → ∀ k ∈ Γ, k • w ≠ w → ∀ y : ℍ,
      dist (g • y) y < τ → τ ≤ dist (k • y) y)
    {g₁ g₂ k : PSL(2, ℝ)} {w₁ w₂ y₁ y₂ z : ℍ} (hg₁ : g₁ ∈ Γ) (hg₁₁ : g₁ ≠ 1)
    (hgw₁ : g₁ • w₁ = w₁) (hgy₁ : dist (g₁ • y₁) y₁ = τ / 2) (hg₂ : g₂ ∈ Γ) (hg₂₁ : g₂ ≠ 1)
    (hgw₂ : g₂ • w₂ = w₂) (hgy₂ : dist (g₂ • y₂) y₂ = τ / 2) (hk : k ∈ Γ)
    (hz₁ : dist z (k • y₁) < τ / 4) (hz₂ : dist z y₂ < τ / 4) : k • w₁ = w₂ := by
  -- the points of the ball of radius `τ / 4` about `y` are moved less than `τ` by `g`
  have hball {g : PSL(2, ℝ)} {y : ℍ} (hgy : dist (g • y) y = τ / 2) {x : ℍ}
      (hx : dist x y < τ / 4) : dist (g • x) x < τ := by
    have := dist_triangle4 (g • x) (g • y) y x
    rw [dist_smul, hgy, dist_comm y x] at this
    linarith
  have hh : k * g₁ * k⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hk hg₁) (Γ.inv_mem hk)
  have hhz : dist ((k * g₁ * k⁻¹) • z) z < τ := by
    have := hball hgy₁ (x := k⁻¹ • z) (by rw [← dist_smul k, smul_inv_smul]; exact hz₁)
    rwa [← dist_smul k, smul_inv_smul, ← mul_smul, ← mul_smul] at this
  -- so `k g₁ k⁻¹` fixes `w₂`, by the choice of `τ`
  have hhw : (k * g₁ * k⁻¹) • w₂ = w₂ := by
    by_contra hne
    exact (hP g₂ hg₂ hg₂₁ w₂ hgw₂ _ hh hne z (hball hgy₂ hz₂)).not_gt hhz
  have hh₁ : k * g₁ * k⁻¹ ≠ 1 := by
    rw [Ne, mul_inv_eq_one, mul_eq_left]
    exact hg₁₁
  have hhw₁ : (k * g₁ * k⁻¹) • (k • w₁) = k • w₁ := by
    rw [mul_smul, mul_smul, inv_smul_smul, hgw₁]
  -- a nonidentity element fixes at most one point
  by_contra hne
  exact hh₁ (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self hhw₁ hhw
    (Ne.symm hne))

/-- **Packing balls in a fundamental domain.** Let `Γ ≤ PSL(2, ℝ)` be discrete, and let `y i`,
for `i` in a finite set `s`, be centres of balls of radius `r` such that the ball about `y j`
meets the `k`-translate of the ball about `y i`, for `k ∈ Γ`, only when `k = 1` and `i = j`. Then
the balls have pairwise disjoint translates, so their total area is at most the covolume. -/
private theorem card_mul_volume_ball_le_covolume [DiscreteTopology Γ] {ι : Type*} (s : Finset ι)
    {y : ι → ℍ} {r : ℝ}
    (h : ∀ k ∈ Γ, ∀ i ∈ s, ∀ j ∈ s, ∀ z : ℍ, dist z (k • y i) < r → dist z (y j) < r →
      k = 1 ∧ i = j) :
    s.card * volume (ball I r) ≤ covolume Γ ℍ := by
  set t := ⋃ i ∈ s, ball (y i) r
  obtain ⟨F, -, -, hF⟩ := exists_isFundamentalDomain Γ
  have hvol : volume t = s.card * volume (ball I r) := by
    rw [measure_biUnion_finset (fun i hi j hj hne ↦ ?_) fun i _ ↦ measurableSet_ball]
    · rw [Finset.sum_congr rfl fun i _ ↦
        measure_ball_eq_measure_ball (G := PSL(2, ℝ)) volume (y i) I r]
      simp
    · rw [Function.onFun, Set.disjoint_left]
      intro z hz₁ hz₂
      exact hne (h 1 Γ.one_mem i hi j hj z (by rwa [one_smul]) hz₂).2
  rw [← hvol, hF.covolume_eq_volume]
  refine hF.measure_le_of_pairwise_disjoint
    (s.measurableSet_biUnion fun i _ ↦ measurableSet_ball).nullMeasurableSet
    fun γ₁ γ₂ hγ ↦ Disjoint.aedisjoint ?_
  refine Disjoint.mono inter_subset_left inter_subset_left ?_
  simp only [t, smul_set_iUnion₂, disjoint_iUnion₂_left, disjoint_iUnion₂_right]
  intro i hi j hj
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rw [mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, mem_ball] at hz₁ hz₂
  push_cast at hz₁ hz₂
  -- translating by `γ₂⁻¹`, the ball about `y j` meets the `γ₂⁻¹ γ₁`-translate of that about `y i`
  have h' := h ((γ₂ : PSL(2, ℝ))⁻¹ * γ₁) (Γ.mul_mem (Γ.inv_mem γ₂.2) γ₁.2) j hj i hi _ (by
      rwa [mul_smul, dist_smul, ← dist_smul (γ₁ : PSL(2, ℝ))⁻¹, inv_smul_smul]) hz₂
  exact hγ (Subtype.ext (inv_mul_eq_one.1 h'.1)).symm

/-- **A cofinite Fuchsian group has finitely many elliptic orbits.** For a cofinite
`Γ ≤ PSL(2, ℝ)`, only finitely many `Γ`-orbits in `ℍ` consist of points with nontrivial stabilizer
in `Γ`. -/
theorem IsCofinite.finite_ellipticOrbits [DiscreteTopology Γ] (hΓ : Γ.IsCofinite) :
    Γ.ellipticOrbits.Finite := by
  obtain ⟨τ, hτ, hP⟩ := hΓ.exists_pos_le_dist_smul_of_dist_smul_lt
  -- at a representative `w q` of each elliptic orbit `q`, a nonidentity `g q` fixing `w q`, and a
  -- `τ / 2`-thick point `y q` moved exactly `τ / 2` by `g q`
  have hex : ∀ q ∈ Γ.ellipticOrbits, ∃ w : ℍ, Quotient.mk (orbitRel Γ ℍ) w = q ∧
      ∃ g ∈ Γ, g ≠ 1 ∧ g • w = w ∧ ∃ y : ℍ, dist (g • y) y = τ / 2 ∧
        ∀ k ∈ Γ, k ≠ 1 → τ / 2 ≤ dist (k • y) y := by
    intro q hq
    obtain ⟨w, rfl⟩ := Quotient.mk_surjective q
    rw [quotientMk_mem_ellipticOrbits_iff] at hq
    have hne : stabilizer Γ w ≠ ⊥ := fun h ↦ hq ((mem_freeLocus Γ ℍ).2 h)
    obtain ⟨γ, hγ₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    refine ⟨w, rfl, exists_dist_smul_eq_and_forall_le hτ hP (γ : Γ).2
      (fun h ↦ hγ₁ (Subtype.ext (Subtype.ext h))) (mem_stabilizer_iff.1 γ.2)⟩
  choose! w hwq g hg hg₁ hgw y hgy hthick using hex
  -- if the ball about `y q₂` meets the `k`-translate of the ball about `y q₁`, then `q₁ = q₂`,
  -- and then `k = 1` since `y q₁` is `τ / 2`-thick
  have hkey : ∀ k ∈ Γ, ∀ q₁ ∈ Γ.ellipticOrbits, ∀ q₂ ∈ Γ.ellipticOrbits, ∀ z : ℍ,
      dist z (k • y q₁) < τ / 4 → dist z (y q₂) < τ / 4 → k = 1 ∧ q₁ = q₂ := by
    intro k hk q₁ hq₁ q₂ hq₂ z hz₁ hz₂
    have hw := smul_eq_of_dist_lt hP (hg q₁ hq₁) (hg₁ q₁ hq₁) (hgw q₁ hq₁) (hgy q₁ hq₁)
      (hg q₂ hq₂) (hg₁ q₂ hq₂) (hgw q₂ hq₂) (hgy q₂ hq₂) hk hz₁ hz₂
    have hq : q₁ = q₂ := by
      rw [← hwq q₁ hq₁, ← hwq q₂ hq₂, ← hw]
      exact (Quotient.sound (show k • w q₁ ∈ orbit Γ (w q₁) from ⟨⟨k, hk⟩, rfl⟩)).symm
    subst hq
    refine ⟨by_contra fun hk₁ ↦ ?_, rfl⟩
    have := hthick q₁ hq₁ k hk hk₁
    have := dist_triangle (k • y q₁) z (y q₁)
    rw [dist_comm] at hz₁
    linarith
  have hcard (s : Finset (orbitRel.Quotient Γ ℍ)) (hs : ↑s ⊆ Γ.ellipticOrbits) :=
    card_mul_volume_ball_le_covolume s fun k hk q₁ hq₁ q₂ hq₂ ↦
      hkey k hk q₁ (hs hq₁) q₂ (hs hq₂)
  -- infinitely many elliptic orbits would give balls of unbounded total area
  by_contra hinf
  have hv : 0 < volume (ball I (τ / 4)) := measure_ball_pos volume I (by positivity)
  have hv' : volume (ball I (τ / 4)) ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hΓ.covolume_ne_top hv.ne').ne
  obtain ⟨s, hs, hsn⟩ := Set.Infinite.exists_subset_card_eq hinf n
  have h := hcard s hs
  rw [hsn] at h
  rw [ENNReal.div_lt_iff (Or.inl hv.ne') (Or.inl hv')] at hn
  exact (hn.trans_le h).false

end Subgroup
