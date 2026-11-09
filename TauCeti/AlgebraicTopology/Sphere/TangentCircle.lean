/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.UnitInterval

/-!
# Sweeping a sphere by circles tangent to a direction

Let `p` and `u` be orthonormal vectors of a real inner product space `V`. The points `q` of the
unit sphere `S_V` orthogonal to `u` form the equator `E` through `p` orthogonal to `u`. For each
`q ∈ E` there is exactly one circle on `S_V` through `p` and `q` that is tangent to `u` at `p`: the
section of `S_V` by the affine plane through `p` spanned by `u` and `q - p`. Run from `p` in the
direction of `u`, proportionally to arc length, it reaches `q` at half time:

`θ ↦ ((1 + cos θ) / 2) • p + ((1 - cos θ) / 2) • q + (‖q - p‖ / 2 * sin θ) • u`
(`TauCeti.tangentCircle`), a constant loop at `p` when `q = p`.

Every point of `S_V` other than `p` lies on exactly one of these circles, at exactly one time
strictly between `0` and `2π`: the component along `u` and the component orthogonal to `u`
recover first `q`, on the ray from `p`, and then the angle
(`TauCeti.eq_of_tangentCircle_eq`, `TauCeti.exists_tangentCircle_eq`). Hence the family of
circles, read on a cube through a generalized loop `c` of `E` that covers `E` off `p` and
identifies only points of the boundary of its cube, is a generalized loop of `S_V` one dimension
higher with the same two properties (`TauCeti.tangentCircleGenLoop`,
`TauCeti.eq_or_of_tangentCircleGenLoop_eq`, `TauCeti.surjective_tangentCircleGenLoop`). Its
pointed map out of the sphere is then a homeomorphism, so its Hurewicz class generates the top
homology of `S_V` (`TauCeti.isIso_hurewicz_tangentCircleGenLoop`).

This is the family `φ_{V,u} : E_{V,p,u} → Ω_p S_V` of Barraud–Damian–Humilière–Oancea,
Example 6.20, and the statement that its adjoint represents a generator of the top homotopy and
homology of `S_V` is the first step of their Proposition 6.21. The two properties proved of the
circles are those asked of `c`, which is what the composite `Σ_p → Ω_p E → Ω_p Ω_p Sⁿ` of
Example 6.20 needs: there `c` is itself a family of circles, in a sphere of one dimension less.
For a sphere of dimension `k + 1`, the cube collapse `TauCeti.cubeToSphere` onto the equator
`TauCeti.sphereEquator u` meets the hypotheses on `c` (`TauCeti.exists_genLoop_sphereEquator`).

## Main declarations

* `TauCeti.tangentCircle p u q θ`: the circle through `p` tangent to `u` and through `q`.
* `TauCeti.tangentCircleGenLoop hu c`: the circles through the points of a generalized loop `c`
  of the equator, as a generalized loop of the sphere.
* `TauCeti.isIso_hurewicz_tangentCircleGenLoop`: its Hurewicz class is an isomorphism
  `R ≅ H_{k+1}(S_V; R)` when `c` is surjective off `p` and identifies only boundary points.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Example 6.20 and Proposition 6.21.
-/

public section

noncomputable section

open Metric Real Set
open scoped RealInnerProductSpace Topology unitInterval Topology.Homotopy

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The circles -/

/-- The circle through `p` and `q` tangent to `u` at `p`, at the angle `θ`:
`((1 + cos θ) / 2) • p + ((1 - cos θ) / 2) • q + (‖q - p‖ / 2 * sin θ) • u`. When `p`, `q` are unit
vectors orthogonal to the unit vector `u`, it runs on the unit sphere
(`TauCeti.norm_tangentCircle`), from `p` at `θ = 0` to `q` at `θ = π`, proportionally to arc
length, and back to `p` at `θ = 2π`. -/
def tangentCircle (p u q : V) (θ : ℝ) : V :=
  ((1 + cos θ) / 2) • p + ((1 - cos θ) / 2) • q + (‖q - p‖ / 2 * sin θ) • u

/-- The defining formula of `TauCeti.tangentCircle`. -/
theorem tangentCircle_def (p u q : V) (θ : ℝ) :
    tangentCircle p u q θ =
      ((1 + cos θ) / 2) • p + ((1 - cos θ) / 2) • q + (‖q - p‖ / 2 * sin θ) • u :=
  (rfl)

@[simp]
theorem tangentCircle_zero (p u q : V) : tangentCircle p u q 0 = p := by
  simp [tangentCircle]

@[simp]
theorem tangentCircle_pi (p u q : V) : tangentCircle p u q π = q := by
  simp [tangentCircle]

@[simp]
theorem tangentCircle_self (p u : V) (θ : ℝ) : tangentCircle p u p θ = p := by
  rw [tangentCircle, sub_self, norm_zero]
  module

theorem tangentCircle_add_two_pi (p u q : V) (θ : ℝ) :
    tangentCircle p u q (θ + 2 * π) = tangentCircle p u q θ := by
  simp [tangentCircle]

theorem continuous_tangentCircle (p u : V) :
    Continuous fun x : V × ℝ ↦ tangentCircle p u x.1 x.2 := by
  unfold tangentCircle
  fun_prop

variable {p u q : V}

/-- The component of the circle along `u`. -/
theorem inner_tangentCircle (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hqu : ⟪q, u⟫ = 0) (θ : ℝ) :
    ⟪tangentCircle p u q θ, u⟫ = ‖q - p‖ / 2 * sin θ := by
  simp [tangentCircle, inner_add_left, real_inner_smul_left, hpu, hqu, hu]

/-- The component of the circle orthogonal to `u` lies on the segment from `p` to `q`. -/
theorem tangentCircle_sub_inner_smul (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hqu : ⟪q, u⟫ = 0)
    (θ : ℝ) :
    tangentCircle p u q θ - ⟪tangentCircle p u q θ, u⟫ • u = p + ((1 - cos θ) / 2) • (q - p) := by
  rw [inner_tangentCircle hu hpu hqu, tangentCircle]
  module

/-- The circle lies on the unit sphere. -/
theorem norm_tangentCircle (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hq : ‖q‖ = 1)
    (hqu : ⟪q, u⟫ = 0) (θ : ℝ) : ‖tangentCircle p u q θ‖ = 1 := by
  have hpq : ‖q - p‖ ^ 2 = 2 - 2 * ⟪p, q⟫ := by
    rw [norm_sub_sq_real, hp, hq, real_inner_comm]
    ring
  have h : ‖tangentCircle p u q θ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [tangentCircle, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hpu, hqu, real_inner_comm p u, real_inner_comm q u,
      real_inner_comm p q]
    simp only [real_inner_self_eq_norm_sq, hp, hq, hu]
    linear_combination (1 / 4 * sin θ ^ 2) * hpq + (1 / 2 - ⟪p, q⟫ / 2) * sin_sq_add_cos_sq θ
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- The circle passes through `p` only at the angles `2πk`, unless it is the constant loop
`q = p`. -/
theorem tangentCircle_eq_self_iff (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hqu : ⟪q, u⟫ = 0)
    (θ : ℝ) : tangentCircle p u q θ = p ↔ q = p ∨ cos θ = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h' := tangentCircle_sub_inner_smul hu hpu hqu θ
    rw [h, hpu, zero_smul, sub_zero, left_eq_add, smul_eq_zero, div_eq_zero_iff, sub_eq_zero,
      sub_eq_zero] at h'
    rcases h' with (h' | h') | h'
    · exact Or.inr h'.symm
    · norm_num at h'
    · exact Or.inl h'
  · rintro (rfl | h)
    · exact tangentCircle_self _ _ θ
    · have hs : sin θ = 0 := by nlinarith [sin_sq_add_cos_sq θ]
      simp [tangentCircle, h, hs]

/-- **The circles are disjoint off `p`.** Two points of these circles that agree and differ from
`p` lie on the same circle, at angles with the same cosine and sine. -/
theorem eq_of_tangentCircle_eq (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (hq : ‖q‖ = 1)
    (hqu : ⟪q, u⟫ = 0) {q' : V} (hq' : ‖q'‖ = 1) (hq'u : ⟪q', u⟫ = 0) {θ θ' : ℝ}
    (h : tangentCircle p u q θ = tangentCircle p u q' θ') (hne : tangentCircle p u q θ ≠ p) :
    q = q' ∧ cos θ = cos θ' ∧ sin θ = sin θ' := by
  have h₁ := tangentCircle_sub_inner_smul hu hpu hqu θ
  have h₂ := tangentCircle_sub_inner_smul hu hpu hq'u θ'
  rw [← h, h₁, add_right_inj] at h₂
  set w := ((1 - cos θ) / 2) • (q - p) with hw
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, add_zero] at h₁
    -- A unit vector whose component orthogonal to `u` is `p` has inner product `‖p‖ ^ 2` with `p`.
    have hyp := congrArg (⟪·, p⟫) h₁
    simp only [inner_sub_left, real_inner_smul_left, real_inner_comm p u, hpu, mul_zero,
      sub_zero] at hyp
    exact hne (eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
      (by rw [norm_tangentCircle hp hu hpu hq hqu θ, hp]) (by simpa using hyp))
  have hb : (1 - cos θ) / 2 ≠ 0 := fun h0 ↦ hw0 (by rw [hw, h0, zero_smul])
  have hb' : (1 - cos θ') / 2 ≠ 0 := fun h0 ↦ hw0 (by rw [h₂, h0, zero_smul])
  have hqw : q = p + ((1 - cos θ) / 2)⁻¹ • w := by
    rw [hw, smul_smul, inv_mul_cancel₀ hb, one_smul, add_sub_cancel]
  have hq'w : q' = p + ((1 - cos θ') / 2)⁻¹ • w := by
    rw [h₂, smul_smul, inv_mul_cancel₀ hb', one_smul, add_sub_cancel]
  -- The line through `p` along `w` meets the unit sphere at one nonzero parameter.
  have hline (c : ℝ) (hc : c ≠ 0) (hc' : ‖p + c • w‖ = 1) :=
    ((EuclideanGeometry.dist_smul_vadd_eq_dist p 0 hw0 c).1 (by
      rw [vadd_eq_add, dist_zero_right, dist_zero_right, add_comm, hc', hp])).resolve_left hc
  have hab := (hline _ (inv_ne_zero hb) (hqw ▸ hq)).trans
    (hline _ (inv_ne_zero hb') (hq'w ▸ hq')).symm
  have hc : cos θ = cos θ' := by
    have := inv_injective hab
    linarith
  have hqq' : q = q' := by rw [hqw, hq'w, hab]
  refine ⟨hqq', hc, ?_⟩
  have hs := congrArg (⟪·, u⟫) h
  simp only [inner_tangentCircle hu hpu hqu, ← hqq'] at hs
  have hqp0 : q - p ≠ 0 := fun h0 ↦ hw0 (by rw [hw, h0, smul_zero])
  have hqp : ‖q - p‖ / 2 ≠ 0 := div_ne_zero (norm_ne_zero_iff.2 hqp0) two_ne_zero
  exact mul_left_cancel₀ hqp hs

/-- **The circles sweep the sphere.** Every point `y` of the unit sphere lies on the circle through
`p` tangent to `u` and through some unit vector `q` orthogonal to `u`. -/
theorem exists_tangentCircle_eq (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) {y : V}
    (hy : ‖y‖ = 1) : ∃ q, ‖q‖ = 1 ∧ ⟪q, u⟫ = 0 ∧ ∃ θ, tangentCircle p u q θ = y := by
  by_cases hyp : y = p
  · exact ⟨p, hp, hpu, 0, by rw [tangentCircle_zero, hyp]⟩
  set s := ⟪y, u⟫ with hs
  set d := y - s • u - p with hd
  have hdu : ⟪d, u⟫ = 0 := by
    simp [hd, inner_sub_left, real_inner_smul_left, hu, hpu, ← hs]
  have hd0 : d ≠ 0 := by
    intro h0
    -- A unit vector whose component orthogonal to `u` is `p` has inner product `‖p‖ ^ 2` with `p`.
    have hyp' := congrArg (⟪·, p⟫) h0
    simp only [hd, inner_sub_left, real_inner_smul_left, real_inner_comm p u, hpu, mul_zero,
      sub_zero, inner_zero_left, sub_eq_zero] at hyp'
    exact hyp (eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) (by rw [hy, hp]) (by simpa using hyp'))
  have hyd : y = p + d + s • u := by rw [hd]; abel
  set D := ‖d‖ ^ 2 with hD
  have hDpos : 0 < D := by positivity
  -- The unit length of `y` determines the component of `d` along `p`.
  have hpd : -2 * ⟪p, d⟫ = D + s ^ 2 := by
    have h : ‖y‖ ^ 2 = 1 := by rw [hy, one_pow]
    rw [hyd, norm_add_sq_real, norm_add_sq_real, inner_add_left, real_inner_smul_right,
      real_inner_smul_right, hpu, hdu, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu, hp] at h
    linarith
  set l := (D + s ^ 2) / D with hl
  have hlD : l * D = D + s ^ 2 := div_mul_cancel₀ _ hDpos.ne'
  have hl1 : 1 ≤ l := by rw [hl, le_div_iff₀ hDpos]; nlinarith
  have hl0 : 0 < l := by linarith
  set q := p + l • d with hq
  have hqn : ‖q‖ = 1 := by
    have : ‖q‖ ^ 2 = 1 := by
      rw [hq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs, hp, ← hD]
      nlinarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
  have hqu : ⟪q, u⟫ = 0 := by
    rw [hq, inner_add_left, real_inner_smul_left, hpu, hdu, mul_zero, add_zero]
  have hqp : ‖q - p‖ = l * ‖d‖ := by
    rw [hq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
  have hnd : 0 < ‖d‖ := norm_pos_iff.2 hd0
  obtain ⟨t, hc, hsn⟩ := exists_cos_sin_two_pi_mul_eq (a := 1 - 2 / l) (b := 2 * s / (l * ‖d‖))
    (by
      field_simp
      rw [← hD]
      nlinarith)
  refine ⟨q, hqn, hqu, 2 * π * t, ?_⟩
  have hb : (1 - cos (2 * π * t)) / 2 * l = 1 := by rw [hc]; field_simp; ring
  have hsc : ‖q - p‖ / 2 * sin (2 * π * t) = s := by rw [hsn, hqp]; field_simp
  calc tangentCircle p u q (2 * π * t)
      = p + ((1 - cos (2 * π * t)) / 2 * l) • d + (‖q - p‖ / 2 * sin (2 * π * t)) • u := by
        rw [tangentCircle, hq, mul_smul]; module
    _ = y := by rw [hb, hsc, one_smul, hyd]

/-! ### The family of circles as a generalized loop -/

variable {k : ℕ} {p₀ : sphereEquator u}

/-- **The circles through the points of a generalized loop of the equator.** For a generalized
loop `c : I^k → E` of the equator `E` at `p₀`, the generalized loop of the unit sphere at `p₀`
sending `y` to the point at the angle `2π y₀` of the circle through `p₀` tangent to `u` and through
`c (Fin.tail y)`. -/
def tangentCircleGenLoop (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀) :
    Ω^ (Fin (k + 1)) (sphere (0 : V) 1) (p₀ : sphere (0 : V) 1) where
  val :=
    { toFun y := ⟨tangentCircle ((p₀ : sphere (0 : V) 1) : V) u
          ((c (Fin.tail y) : sphere (0 : V) 1) : V) (2 * π * y 0),
        mem_sphere_zero_iff_norm.2 (norm_tangentCircle (mem_sphere_zero_iff_norm.1 p₀.1.2) hu
          p₀.2 (mem_sphere_zero_iff_norm.1 (c (Fin.tail y)).1.2) (c (Fin.tail y)).2 _)⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ((continuous_tangentCircle _ u).comp
          (Continuous.prodMk ?_ ?_)) _
        · exact continuous_subtype_val.comp (continuous_subtype_val.comp
            (c.1.continuous.comp (continuous_pi fun i ↦ continuous_apply _)))
        · exact continuous_const.mul (continuous_subtype_val.comp (continuous_apply 0)) }
  property y hy := by
    refine Subtype.ext ((tangentCircle_eq_self_iff hu p₀.2 (c (Fin.tail y)).2 _).2 ?_)
    rcases Cube.boundary_fin_succ_iff.1 hy with h | h
    · right
      rcases h with h | h <;> simp [h]
    · left
      rw [GenLoop.boundary c _ h]

@[simp]
theorem coe_tangentCircleGenLoop_apply (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (y : I^(Fin (k + 1))) :
    (tangentCircleGenLoop hu c y : V) = tangentCircle ((p₀ : sphere (0 : V) 1) : V) u
      ((c (Fin.tail y) : sphere (0 : V) 1) : V) (2 * π * y 0) :=
  (rfl)

/-- A generalized loop of the equator that covers the equator off `p₀` and identifies only points
of the boundary sends only points of the boundary to `p₀`. -/
private lemma mem_boundary_of_eq (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hinj : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k))
    {y : I^(Fin k)} (hy : c y = p₀) : y ∈ Cube.boundary (Fin k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- The cube is a point; it must reach the antipode of `p₀`, which differs from `p₀`.
    let q : sphereEquator u := ⟨-(p₀ : sphere (0 : V) 1), by
      simp [coe_neg_sphere, inner_neg_left, p₀.2.out]⟩
    have hq : q ≠ p₀ := fun h ↦ ne_neg_of_mem_unit_sphere ℝ (p₀ : sphere (0 : V) 1)
      (congrArg Subtype.val h).symm
    obtain ⟨z, hz⟩ := hsurj q hq
    rw [Subsingleton.elim z y, hy] at hz
    exact absurd hz.symm hq
  · have h0 : (0 : I^(Fin k)) ∈ Cube.boundary (Fin k) := ⟨⟨0, hk⟩, Or.inl rfl⟩
    rcases hinj y 0 (hy.trans (GenLoop.boundary c 0 h0).symm) with rfl | ⟨h, -⟩
    exacts [h0, h]

/-- The generalized loop of circles sends only points of the boundary to `p₀`. -/
private lemma mem_boundary_of_tangentCircleGenLoop_eq (hu : ‖u‖ = 1)
    (c : Ω^ (Fin k) (sphereEquator u) p₀) (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hinj : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k))
    {y : I^(Fin (k + 1))} (hy : tangentCircleGenLoop hu c y = p₀) :
    y ∈ Cube.boundary (Fin (k + 1)) := by
  have hy' := congrArg Subtype.val hy
  rw [coe_tangentCircleGenLoop_apply,
    tangentCircle_eq_self_iff hu p₀.2 (c (Fin.tail y)).2] at hy'
  rcases hy' with h | h
  · exact Cube.boundary_fin_succ_iff.2 (Or.inr (mem_boundary_of_eq c hsurj hinj
      (Subtype.ext (Subtype.ext h))))
  · exact Cube.boundary_fin_succ_iff.2 (Or.inl (eq_zero_or_eq_one_of_cos_two_pi_mul_eq_one h))

/-- **The circles identify only points of the boundary**, when `c` covers the equator off `p₀` and
identifies only points of the boundary. -/
theorem eq_or_of_tangentCircleGenLoop_eq (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hinj : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k))
    {y z : I^(Fin (k + 1))} (h : tangentCircleGenLoop hu c y = tangentCircleGenLoop hu c z) :
    y = z ∨ y ∈ Cube.boundary (Fin (k + 1)) ∧ z ∈ Cube.boundary (Fin (k + 1)) := by
  by_cases hy : tangentCircleGenLoop hu c y = p₀
  · exact Or.inr ⟨mem_boundary_of_tangentCircleGenLoop_eq hu c hsurj hinj hy,
      mem_boundary_of_tangentCircleGenLoop_eq hu c hsurj hinj (h ▸ hy)⟩
  left
  have hp := mem_sphere_zero_iff_norm.1 (p₀ : sphere (0 : V) 1).2
  have hne : tangentCircle ((p₀ : sphere (0 : V) 1) : V) u
      ((c (Fin.tail y) : sphere (0 : V) 1) : V) (2 * π * y 0) ≠ p₀ :=
    fun h' ↦ hy (Subtype.ext h')
  obtain ⟨hq, hc, hs⟩ := eq_of_tangentCircle_eq hp hu p₀.2
    (mem_sphere_zero_iff_norm.1 (c (Fin.tail y)).1.2) (c (Fin.tail y)).2
    (mem_sphere_zero_iff_norm.1 (c (Fin.tail z)).1.2) (c (Fin.tail z)).2
    (congrArg Subtype.val h) hne
  have h1 : cos (2 * π * y 0) ≠ 1 := fun h1 ↦
    hne ((tangentCircle_eq_self_iff hu p₀.2 (c (Fin.tail y)).2 _).2 (Or.inr h1))
  have h0 : y 0 = z 0 := by
    rcases eq_or_of_cos_sin_two_pi_mul_eq hc hs with h0 | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h0
    · simp [h0] at h1
    · simp [h0] at h1
  have htail : Fin.tail y = Fin.tail z := by
    rcases hinj _ _ (Subtype.ext (Subtype.ext hq)) with h' | ⟨h', -⟩
    · exact h'
    · exact absurd ((tangentCircle_eq_self_iff hu p₀.2 (c (Fin.tail y)).2 _).2
        (Or.inl (by rw [GenLoop.boundary c _ h']))) hne
  rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail z, h0, htail]

/-- **The circles sweep the sphere**, when `c` covers the equator off `p₀`. -/
theorem surjective_tangentCircleGenLoop (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q) : Function.Surjective (tangentCircleGenLoop hu c) := by
  intro w
  have hp := mem_sphere_zero_iff_norm.1 (p₀ : sphere (0 : V) 1).2
  obtain ⟨q, hq, hqu, θ, hθ⟩ := exists_tangentCircle_eq hp hu p₀.2
    (mem_sphere_zero_iff_norm.1 w.2)
  by_cases hqp : q = p₀
  · refine ⟨0, Subtype.ext ?_⟩
    rw [← hθ, hqp, tangentCircle_self, coe_tangentCircleGenLoop_apply]
    simp
  obtain ⟨y, hy⟩ := hsurj ⟨⟨q, mem_sphere_zero_iff_norm.2 hq⟩, hqu⟩
    fun h ↦ hqp (congrArg (fun r : sphereEquator u ↦ ((r : sphere (0 : V) 1) : V)) h)
  obtain ⟨t, hc, hs⟩ := exists_cos_sin_two_pi_mul_eq (cos_sq_add_sin_sq θ)
  refine ⟨Fin.cons t y, Subtype.ext ?_⟩
  rw [coe_tangentCircleGenLoop_apply, Fin.tail_cons, Fin.cons_zero, hy, ← hθ]
  simp only [tangentCircle, hc, hs]

/-! ### The standard collapse onto the equator -/

/-- **The equator is a sphere collapsed from a cube.** If `V` has dimension `k + 2`, then for every
point `p₀` of the equator orthogonal to the nonzero vector `u` there is a generalized loop of the
equator at `p₀`, out of the cube `I^k`, that covers the equator off `p₀` and identifies only
points of the boundary of the cube: the collapse `TauCeti.cubeToSphere` of the cube onto the unit
sphere of `ℝᵏ⁺¹`, followed by a linear isometry of `ℝᵏ⁺¹` onto `u⊥` sending the north pole to
`p₀`. So the hypotheses of `TauCeti.isIso_hurewicz_tangentCircleGenLoop` can be met. -/
theorem exists_genLoop_sphereEquator [FiniteDimensional ℝ V] (hu : u ≠ 0)
    (hV : Module.finrank ℝ V = k + 2) (p₀ : sphereEquator u) :
    ∃ c : Ω^ (Fin k) (sphereEquator u) p₀, (∀ q, q ≠ p₀ → ∃ y, c y = q) ∧
      ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k) := by
  have : Fact (Module.finrank ℝ V = (k + 1) + 1) := ⟨hV⟩
  have hK : Module.finrank ℝ (ℝ ∙ u)ᗮ = k + 1 := Submodule.finrank_orthogonal_span_singleton hu
  let e₀ : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ :=
    ((stdOrthonormalBasis ℝ (ℝ ∙ u)ᗮ).reindex (finCongr hK)).repr.symm
  let P : (ℝ ∙ u)ᗮ := ⟨p₀.1.1, Submodule.mem_orthogonal_singleton_iff_inner_left.2 p₀.2⟩
  obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin (k + 1)), b = sphereNorthPole k := ⟨_, rfl⟩
  have hab : ‖b‖ = ‖e₀.symm P‖ := by
    rw [LinearIsometryEquiv.norm_map, hb]
    simp [P, norm_eq_of_mem_sphere]
  -- Rotate the north pole onto the preimage of `p₀` by a reflection.
  let e := (ℝ ∙ (b - e₀.symm P))ᗮ.reflection.trans e₀
  have he : sphereToEquator e (sphereNorthPole k) = p₀ := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_sphereToEquator, ← hb]
    simp [e, Submodule.reflection_sub hab, P]
  refine ⟨GenLoop.map (sphereToEquator e) he (sphereGenLoop k), fun q hq ↦ ?_, fun y z h ↦ ?_⟩
  · obtain ⟨s, rfl⟩ := surjective_sphereToEquator e q
    obtain ⟨y, hy⟩ := exists_cubeToSphere_eq_of_ne (s := s) fun hs ↦ hq (by rw [hs, he])
    exact ⟨y, by rw [GenLoop.map_apply, sphereGenLoop_apply, hy]⟩
  · rw [GenLoop.map_apply, GenLoop.map_apply, sphereGenLoop_apply, sphereGenLoop_apply] at h
    exact cubeToSphere_eq_cubeToSphere_iff.1 (injective_sphereToEquator e h)

end TauCeti

namespace TauCeti

open CategoryTheory Limits

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V} {k : ℕ}
  {p₀ : sphereEquator u} {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C] (R : C)

/-- **The circles represent a generator** (Barraud–Damian–Humilière–Oancea, Proposition 6.21, the
step for `φ_{V,u}`). If the generalized loop `c` of the equator covers the equator off `p₀` and
identifies only points of the boundary of its cube, then the Hurewicz class of the generalized
loop of circles through the points of `c` is an isomorphism `R ≅ H_{k+1}(S_V; R)`. -/
theorem isIso_hurewicz_tangentCircleGenLoop (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hinj : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k)) :
    IsIso (GenLoop.hurewicz R (tangentCircleGenLoop hu c)) :=
  GenLoop.isIso_hurewicz_of_bijective_toSphere R
    ⟨(GenLoop.injective_toSphere_iff _).2 fun _ _ h ↦
        eq_or_of_tangentCircleGenLoop_eq hu c hsurj hinj h,
      (GenLoop.surjective_toSphere_iff _).2 (surjective_tangentCircleGenLoop hu c hsurj)⟩

end TauCeti
