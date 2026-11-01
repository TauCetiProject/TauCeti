/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.InnerProductSpace.Sphere.Boost
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import TauCeti.Analysis.Complex.Inner

/-!
# The boost diffeotopy of a unit sphere

The conformal boosts `TauCeti.sphereBoost v a` toward a unit vector `v` of a finite-dimensional
real inner product space `E` form a one-parameter group of analytic self-maps of the unit sphere.
Running the boosts of rapidities `a * t` for `t ∈ [0, 1]` is therefore a diffeotopy of the sphere,
`TauCeti.sphereBoostDiffeotopy`, from the identity to the boost of rapidity `a`. For `0 < a` it
moves every point other than `-v` toward `v` while fixing `±v`: it pushes everything except a
small cap around `-v` into an arbitrarily small cap around `v`, and blows that small cap around
`-v` up to almost the whole sphere.

The unit circle of `ℂ` is the case `E = ℂ`, `v = i`, giving `TauCeti.circleBoostDiffeotopy`. By
`LinearIsometry.sphereBoost_map`, the boost toward `ι i` of a sphere restricts on the
great circle cut out by a linear isometry `ι : ℂ →ₗᵢ[ℝ] E` to the boost of the circle.

## Main definitions

* `TauCeti.sphereBoostDiffeotopy hv a`: the diffeotopy of the unit sphere running the boosts
  toward `v` of rapidities from `0` to `a`.
* `TauCeti.circleBoostDiffeotopy a`: the corresponding diffeotopy of the unit circle, toward `i`.

## Main results

* `TauCeti.coe_sphereBoostDiffeotopy_apply`, `TauCeti.coe_sphereBoostDiffeotopy_final_apply`: the
  diffeotopy at time `t` is the boost of rapidity `a * t`, and it ends at the boost of
  rapidity `a`.
* `TauCeti.coe_circleBoostDiffeotopy_apply`, `TauCeti.coe_circleBoostDiffeotopy_final_apply`: the
  same for the circle boost diffeotopy.
* `TauCeti.sphereBoost_circleBoostDiffeotopy_neg`,
  `TauCeti.sphereBoost_circleBoostDiffeotopy_final_neg`: the boost toward `i` undoes the circle
  boost diffeotopy of the opposite rapidity.
* `TauCeti.eventually_forall_im_pos_of_circleBoostDiffeotopy_final_notMem`: a large boost of the
  circle toward `i` carries the complement of a neighbourhood of `-i` into the open upper half.
-/

public section

noncomputable section

open Metric Module Real Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {v : E} {m : ℕ∞ω}

/-- The boost of rapidity `a` toward the unit vector `v`, as a self-map of the unit sphere. -/
private def sphereBoostOnSphere (hv : ‖v‖ = 1) (a : ℝ) (x : sphere (0 : E) 1) :
    sphere (0 : E) 1 :=
  ⟨sphereBoost v a x,
    mem_sphere_zero_iff_norm.2 (norm_sphereBoost hv (norm_eq_of_mem_sphere x) a)⟩

private theorem coe_sphereBoostOnSphere (hv : ‖v‖ = 1) (a : ℝ) (x : sphere (0 : E) 1) :
    (sphereBoostOnSphere hv a x : E) = sphereBoost v a x :=
  (rfl)

private theorem sphereBoostOnSphere_sphereBoostOnSphere (hv : ‖v‖ = 1) (a b : ℝ)
    (x : sphere (0 : E) 1) :
    sphereBoostOnSphere hv a (sphereBoostOnSphere hv b x) = sphereBoostOnSphere hv (a + b) x :=
  Subtype.ext (sphereBoost_sphereBoost hv (norm_eq_of_mem_sphere x) a b)

private theorem sphereBoostOnSphere_zero (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) :
    sphereBoostOnSphere hv 0 x = x :=
  Subtype.ext (by simp [coe_sphereBoostOnSphere])

/-- A smooth family of rapidities and points of the sphere gives a smooth family of boosted
points. -/
private theorem contMDiff_sphereBoostOnSphere (hv : ‖v‖ = 1)
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} {M : Type*} [TopologicalSpace M] [ChartedSpace G M]
    [IsManifold J m M] {r : M → ℝ} {x : M → sphere (0 : E) 1} (hr : ContMDiff J 𝓘(ℝ) m r)
    (hx : ContMDiff J (𝓡 n) m x) :
    ContMDiff J (𝓡 n) m fun p => sphereBoostOnSphere hv (r p) (x p) := by
  refine ContMDiff.codRestrict_sphere (f := fun p => sphereBoost v (r p) (x p)) ?_ _
  have hg : ContMDiff J 𝓘(ℝ, ℝ × E) m fun p => (r p, (x p : E)) :=
    hr.prodMk_space (contMDiff_coe_sphere.comp hx)
  intro p
  -- The boost formula is smooth at every pair `(a, y)` with nonzero denominator.
  have hF : ContDiffAt ℝ m (fun q : ℝ × E => sphereBoost v q.1 q.2) (r p, (x p : E)) := by
    simp only [sphereBoost_def]
    have hD : ContDiff ℝ m fun q : ℝ × E => cosh q.1 + sinh q.1 * ⟪q.2, v⟫ :=
      (contDiff_cosh.comp contDiff_fst).add
        ((contDiff_sinh.comp contDiff_fst).mul (contDiff_snd.inner ℝ contDiff_const))
    have hN : ContDiff ℝ m fun q : ℝ × E => q.2 + (sinh q.1 + (cosh q.1 - 1) * ⟪q.2, v⟫) • v :=
      contDiff_snd.add (((contDiff_sinh.comp contDiff_fst).add
        (((contDiff_cosh.comp contDiff_fst).sub contDiff_const).mul
          (contDiff_snd.inner ℝ contDiff_const))).smul contDiff_const)
    exact ((hD.contDiffAt (x := (r p, (x p : E)))).inv
      (cosh_add_sinh_mul_inner_pos hv (norm_eq_of_mem_sphere (x p)) (r p)).ne').smul
        hN.contDiffAt
  exact hF.contMDiffAt.comp p (hg p)

/-- The **boost diffeotopy** of the unit sphere toward the unit vector `v`: at time `t` it is the
boost `TauCeti.sphereBoost v (a * t)` of rapidity `a * t`, so it runs from the identity to the
boost of rapidity `a`. -/
def sphereBoostDiffeotopy (hv : ‖v‖ = 1) (a : ℝ) : Diffeotopy (𝓡 n) m (sphere (0 : E) 1) where
  toDiffeomorph :=
    { toFun := fun p => (p.1, sphereBoostOnSphere hv (a * p.1) p.2)
      invFun := fun p => (p.1, sphereBoostOnSphere hv (-(a * p.1)) p.2)
      left_inv := fun p => by
        simp [sphereBoostOnSphere_sphereBoostOnSphere, sphereBoostOnSphere_zero]
      right_inv := fun p => by
        simp [sphereBoostOnSphere_sphereBoostOnSphere, sphereBoostOnSphere_zero]
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_sphereBoostOnSphere hv
        ((contDiff_const.mul contDiff_id).contMDiff.comp
          (contMDiff_subtypeVal_Icc.comp contMDiff_fst)) contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_sphereBoostOnSphere hv
        ((contDiff_const.mul contDiff_id).neg.contMDiff.comp
          (contMDiff_subtypeVal_Icc.comp contMDiff_fst)) contMDiff_snd) }
  fst_apply _ := rfl
  snd_apply_zero' x := by
    -- The total map is a structure literal, which `simp` does not unfold; `change` exposes its
    -- value at time `0`.
    change sphereBoostOnSphere hv (a * ((0 : I) : ℝ)) x = x
    rw [Set.Icc.coe_zero, mul_zero, sphereBoostOnSphere_zero]

/-- At time `t` the boost diffeotopy is the boost of rapidity `a * t`. -/
@[simp]
theorem coe_sphereBoostDiffeotopy_apply (hv : ‖v‖ = 1) (a : ℝ) (p : I × sphere (0 : E) 1) :
    (sphereBoostDiffeotopy (n := n) (m := m) hv a p : E) = sphereBoost v (a * p.1) p.2 := by
  rfl

/-- The boost diffeotopy ends at the boost of rapidity `a`. -/
theorem coe_sphereBoostDiffeotopy_final_apply (hv : ‖v‖ = 1) (a : ℝ) (x : sphere (0 : E) 1) :
    ((sphereBoostDiffeotopy (n := n) (m := m) hv a).final x : E) = sphereBoost v a x := by
  rw [Diffeotopy.final_apply, coe_sphereBoostDiffeotopy_apply, Set.Icc.coe_one, mul_one]

section Circle

attribute [local instance] finrank_real_complex_fact'

/-- The boost diffeotopy of the unit circle toward `i`: at time `t` it is the boost
`TauCeti.sphereBoost Complex.I (a * t)` of the circle. `Circle` is by definition the unit sphere of
`ℂ`, with the charted-space structure of that sphere, so this is the case `E = ℂ` of
`TauCeti.sphereBoostDiffeotopy`. -/
def circleBoostDiffeotopy (a : ℝ) : Diffeotopy (𝓡 1) m Circle :=
  sphereBoostDiffeotopy (E := ℂ) (v := Complex.I) (by simp) a

/-- At time `t` the circle boost diffeotopy is the boost of rapidity `a * t` toward `i`. -/
@[simp]
theorem coe_circleBoostDiffeotopy_apply (a : ℝ) (p : I × Circle) :
    (circleBoostDiffeotopy (m := m) a p : ℂ) = sphereBoost Complex.I (a * p.1) p.2 :=
  coe_sphereBoostDiffeotopy_apply (E := ℂ) (v := Complex.I) (by simp) a p

/-- The circle boost diffeotopy ends at the boost of rapidity `a` toward `i`. -/
theorem coe_circleBoostDiffeotopy_final_apply (a : ℝ) (z : Circle) :
    ((circleBoostDiffeotopy (m := m) a).final z : ℂ) = sphereBoost Complex.I a z :=
  coe_sphereBoostDiffeotopy_final_apply (E := ℂ) (v := Complex.I) (by simp) a z

/-- At time `s`, the boost of rapidity `a * s` toward `i` undoes the circle boost diffeotopy of
rapidity `-a`. -/
theorem sphereBoost_circleBoostDiffeotopy_neg (a : ℝ) (s : I) (z : Circle) :
    sphereBoost Complex.I (a * s) (circleBoostDiffeotopy (m := m) (-a) (s, z) : ℂ) = z := by
  rw [coe_circleBoostDiffeotopy_apply, sphereBoost_sphereBoost (by simp) (Circle.norm_coe z),
    neg_mul, add_neg_cancel, sphereBoost_zero, id]

/-- The boost of rapidity `a` toward `i` undoes the final circle boost of rapidity `-a`. -/
theorem sphereBoost_circleBoostDiffeotopy_final_neg (a : ℝ) (z : Circle) :
    sphereBoost Complex.I a ((circleBoostDiffeotopy (m := m) (-a)).final z : ℂ) = z := by
  simpa using sphereBoost_circleBoostDiffeotopy_neg (m := m) a 1 z

/-- **Boosting the circle away from a neighbourhood of `-i`.** For a neighbourhood `U` of the bottom
point `-i` of the circle, once the rapidity `a` is large enough every parameter `w` whose boost
back by rapidity `-a` lies outside `U` is in the open upper half of the circle. -/
theorem eventually_forall_im_pos_of_circleBoostDiffeotopy_final_notMem {z₀ : Circle}
    {U : Set Circle} (hU : U ∈ 𝓝 z₀) (hz₀ : (z₀ : ℂ) = -Complex.I) :
    ∀ᶠ a in atTop, ∀ w : Circle, (circleBoostDiffeotopy (m := m) (-a)).final w ∉ U →
      0 < (w : ℂ).im := by
  obtain ⟨V, hVU, hVo, hz₀V⟩ := _root_.mem_nhds_iff.1 hU
  have h := (hVo.isClosed_compl.isCompact.image continuous_subtype_val
    ).eventually_forall_inner_sphereBoost_pos (v := Complex.I) (by simp)
      (by rintro _ ⟨z, -, rfl⟩; exact Circle.norm_coe z) fun ⟨z, hz, hz'⟩ =>
        hz ((Subtype.ext (hz'.trans hz₀.symm) : z = z₀) ▸ hz₀V)
  filter_upwards [h] with a ha w hw
  have hpos := ha _ ⟨_, fun h => hw (hVU h), rfl⟩
  rwa [sphereBoost_circleBoostDiffeotopy_final_neg, Complex.real_inner_I_right] at hpos

end Circle

end TauCeti
