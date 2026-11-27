/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.SphereCircle
public import TauCeti.Geometry.Manifold.Morse.Bott.MappingTorus.NegativeOrientation
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Morse.Prod
import TauCeti.Geometry.Manifold.Morse.ScalarComposition
import TauCeti.Geometry.Manifold.Orientation.Sphere

/-!
# A Morse–Bott function on an oriented mapping torus of `S² × S¹`

Let `E` be a three-dimensional real inner product space with unit sphere `S²`, `S¹` the unit circle
of `ℂ`, `v ≠ 0` a vector of `E` and `u` a unit vector orthogonal to `v`. The diffeomorphism
`τ (p, w) = (ρ p, conj w)` of `S² × S¹`, with `ρ` the reflection of `E` across `v^⊥`, preserves the
orientation, so its mapping torus `X` is an oriented closed four-manifold
(`TauCeti.sphereCircleReflection`). For `ε > 0` the function

`h (p, w) = ⟪p, u⟫ + ε Re w`

of `S² × S¹` (`TauCeti.sphereCircleHeight u ε`) is invariant under `τ`, since `ρ u = u`, so it
induces the function `[t, p, w] ↦ ⟪p, u⟫ + ε Re w` on `X` (`TauCeti.sphereCircleTorusHeight`). For
`E = ℝ³`, `v` the second and `u` the third coordinate vector, this is the function
`f([t, p, θ]) = z(p) + ε cos θ` of the Morse–Bott example in which an oriented manifold has
non-orientable trajectory spaces between oriented critical submanifolds.

The function `h` is the sum of the height `⟪p, u⟫` on `S²` and `ε` times the height `Re w` on `S¹`,
so it is a Morse function with the four critical points `(±u, ±1)`
(`TauCeti.mem_criticalPoints_sphereCircleHeight_iff`), all fixed by `τ`, of Morse indices `3`,
`2`, `1` and `0` for `(u, 1)`, `(u, -1)`, `(-u, 1)` and `(-u, -1)`. Hence the induced function on
`X` is Morse–Bott, with the four closed orbits `t ↦ [t, ±u, ±1]` of the suspension flow as its
critical circles (`TauCeti.isMorseBottFamily_sphereCircleTorusHeight`). Its Morse index along each
circle, which is the rank of its negative normal bundle there, is the index of `h` at the
corresponding critical point: `3`, `2`, `1` and `0` for the circles `(N, 0)`, `(N, π)`, `(S, 0)`
and `(S, π)`, where `N = u` and `S = -u` are the poles and `θ = 0, π` the points `w = 1, -1`
(`TauCeti.manifoldMorseIndex_sphereCircleTorusHeight_self_one` and its three companions).

Although the mapping torus is oriented, the negative normal bundle of the circle `(N, π)` is not
orientable, for every fibre metric
(`TauCeti.isEmpty_vectorBundleOrientation_negativeNormalSpace_sphereCircleCriticalCircle`).
It is a plane bundle over the circle: at `(u, -1)` the Hessian of `h` is negative definite on the
tangent plane `T_u S²` of the sphere, and going once around the circle the fibre comes back through
the differential of `τ`, which acts on this plane as the reflection `ρ` does, by a map of
determinant `-1` (for `E = ℝ³`, `diag(1, -1)` in the coordinates `x, y`). On the whole normal space
`T_u S² × T_{-1} S¹` of the circle, `τ` also reverses the circle factor, so it acts with
determinant `+1` (for `E = ℝ³`, `diag(1, -1, -1)`), as it must since the mapping torus and the
circle are oriented. So the orientation local system that twists the homology across the level of
`(N, π)` is that of the negative plane bundle, not that of the whole normal bundle; the
orientability of the whole normal bundle is background here and is not formalized.

## Main definitions

* `TauCeti.sphereCircleHeight u ε`: the function `(p, w) ↦ ⟪p, u⟫ + ε Re w` on `S² × S¹`.
* `TauCeti.sphereCircleTorusHeight huv ε`: the function it induces on the mapping torus of `τ`.
* `TauCeti.sphereCircleCriticalCircle huv hε x`: its critical circle `t ↦ [t, x]` through a
  critical point `x` of `h`.

## Main results

* `TauCeti.isMorse_sphereCircleHeight`: `h` is a Morse function for `ε ≠ 0`.
* `TauCeti.mem_criticalPoints_sphereCircleHeight_iff`: its critical points are `(±u, ±1)`.
* `TauCeti.isFixedPt_sphereCircleReflection_of_mem_criticalPoints`: they are fixed by `τ`.
* `TauCeti.isMorseBottFamily_sphereCircleTorusHeight`: the induced function is Morse–Bott, with
  the closed orbits through the four critical points as its critical circles.
* `TauCeti.mk_mem_criticalPoints_sphereCircleTorusHeight_iff`: its critical points are the points
  `[t, ±u, ±1]`.
* `TauCeti.manifoldMorseIndex_sphereCircleTorusHeight_self_one`,
  `TauCeti.manifoldMorseIndex_sphereCircleTorusHeight_self_neg_one`,
  `TauCeti.manifoldMorseIndex_sphereCircleTorusHeight_neg_self_one`,
  `TauCeti.manifoldMorseIndex_sphereCircleTorusHeight_neg_self_neg_one`: its Morse indices `3`,
  `2`, `1` and `0` along the four critical circles.
* `TauCeti.isEmpty_vectorBundleOrientation_negativeNormalSpace_sphereCircleCriticalCircle`:
  the negative normal bundle of the circle `(N, π)` is not orientable.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (orientations of Morse–Bott trajectory spaces).
-/

public section

noncomputable section

open Function Metric Module Set
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The function on `S² × S¹` -/

/-- The function `(p, w) ↦ ⟪p, u⟫ + ε Re w` on `S² × S¹`: the height in the direction `u` on the
sphere plus `ε` times the height `Re w` on the unit circle of `ℂ`. -/
def sphereCircleHeight (u : sphere (0 : E) 1) (ε : ℝ) :
    sphere (0 : E) 1 × sphere (0 : ℂ) 1 → ℝ :=
  sphereHeight u ∘ Prod.fst + ((ε * ·) ∘ sphereHeight 1) ∘ Prod.snd

/-- `TauCeti.sphereCircleHeight u ε` takes the value `⟪p, u⟫ + ε Re w` at `(p, w)`. -/
@[simp]
theorem sphereCircleHeight_apply (u : sphere (0 : E) 1) (ε : ℝ)
    (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    sphereCircleHeight u ε x = ⟪(x.1 : E), (u : E)⟫_ℝ + ε * (x.2 : ℂ).re := by
  simp [sphereCircleHeight, sphereHeight_apply, Complex.inner]

variable {v : E} {u : sphere (0 : E) 1}

variable [Fact (finrank ℝ E = 2 + 1)]

/-- **The function is invariant under `τ`** when `u` is orthogonal to `v`: the reflection across
`v^⊥` fixes `u`, and conjugation does not change the real part. -/
theorem sphereCircleHeight_sphereCircleReflection (huv : ⟪v, (u : E)⟫_ℝ = 0) (ε : ℝ)
    (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    sphereCircleHeight u ε (sphereCircleReflection v x) = sphereCircleHeight u ε x := by
  rw [sphereCircleHeight_apply, sphereCircleHeight_apply, coe_sphereCircleReflection_apply_fst,
    coe_sphereCircleReflection_apply_snd, Complex.conj_re]
  congr 1
  conv_lhs => rw [← reflection_orthogonal_singleton_eq_self_of_inner_eq_zero huv]
  rw [LinearIsometryEquiv.inner_map_map]

/-- A space of dimension `2 + 1` is finite-dimensional, so its unit sphere is compact. -/
local instance instFiniteDimensionalOfFinrankEqThree : FiniteDimensional ℝ E :=
  .of_fact_finrank_eq_succ 2

omit [Fact (finrank ℝ E = 2 + 1)] in
/-- `ε` times the height on the circle is smooth. -/
private theorem contMDiff_mul_sphereHeight (ε : ℝ) {m : WithTop ℕ∞} :
    ContMDiff (𝓡 1) 𝓘(ℝ) m ((ε * ·) ∘ sphereHeight (1 : sphere (0 : ℂ) 1)) :=
  (contDiff_const.mul contDiff_id).contMDiff.comp (contMDiff_sphereHeight 1)

/-- **The function is Morse** for `ε ≠ 0`: it is the separated sum of the height on `S²` and of
`ε` times the height on `S¹`, both Morse functions. -/
theorem isMorse_sphereCircleHeight (u : sphere (0 : E) 1) {ε : ℝ} (hε : ε ≠ 0) :
    IsMorse ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) :=
  (isMorse_sphereHeight u).comp_fst_add_comp_snd ((isMorse_sphereHeight 1).scalar_comp
    (fun _ ↦ (contDiff_const.mul contDiff_id).contDiffAt) fun _ ↦ by simpa using hε)

/-- **The critical points of the function** are the four pairs `(±u, ±1)` of poles, for
`ε ≠ 0`. -/
theorem mem_criticalPoints_sphereCircleHeight_iff (u : sphere (0 : E) 1) {ε : ℝ} (hε : ε ≠ 0)
    (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    x ∈ criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) ↔
      (x.1 = u ∨ x.1 = -u) ∧ (x.2 = 1 ∨ x.2 = -1) := by
  have hφ : ∀ w : sphere (0 : ℂ) 1, deriv (ε * ·) (sphereHeight 1 w) ≠ 0 := fun _ ↦ by
    simpa using hε
  rw [mem_criticalPoints, sphereCircleHeight, mvfderiv_comp_fst_add_comp_snd_eq_zero_iff
    ((contMDiff_sphereHeight (m := 1) u x.1).mdifferentiableAt one_ne_zero)
    ((contMDiff_mul_sphereHeight (m := 1) ε x.2).mdifferentiableAt one_ne_zero),
    ← mem_criticalPoints, ← mem_criticalPoints,
    mem_criticalPoints_scalar_comp_iff ((contMDiff_sphereHeight (m := 1) 1 x.2).mdifferentiableAt
      one_ne_zero) (hφ x.2), mem_criticalPoints, mem_criticalPoints,
    mvfderiv_sphereHeight_eq_zero_iff, mvfderiv_sphereHeight_eq_zero_iff]

/-- The critical points of the function are fixed by `τ`, when `u` is orthogonal to `v` and
`ε ≠ 0`. -/
theorem isFixedPt_sphereCircleReflection_of_mem_criticalPoints (huv : ⟪v, (u : E)⟫_ℝ = 0)
    {ε : ℝ} (hε : ε ≠ 0) {x : sphere (0 : E) 1 × sphere (0 : ℂ) 1}
    (hx : x ∈ criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε)) :
    IsFixedPt (sphereCircleReflection v) x := by
  obtain ⟨hp, hw⟩ := (mem_criticalPoints_sphereCircleHeight_iff u hε x).1 hx
  have hu := reflection_orthogonal_singleton_eq_self_of_inner_eq_zero huv
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [coe_sphereCircleReflection_apply_fst]
    rcases hp with hp | hp <;> rw [hp]
    · exact hu
    · rw [coe_neg_sphere, map_neg, hu]
  · rw [coe_sphereCircleReflection_apply_snd]
    rcases hw with hw | hw <;> rw [hw] <;> simp

/-- The Morse index of the function at a critical point `(p, w)` is the sum of the indices of the
two heights, for `ε > 0`. -/
private theorem manifoldMorseIndex_sphereCircleHeight (u : sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε)
    {p : sphere (0 : E) 1} {w : sphere (0 : ℂ) 1}
    (hw : w ∈ criticalPoints (𝓡 1) (sphereHeight (1 : sphere (0 : ℂ) 1))) :
    manifoldMorseIndex ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) (p, w) =
      manifoldMorseIndex (𝓡 2) (sphereHeight u) p +
        manifoldMorseIndex (𝓡 1) (sphereHeight (1 : sphere (0 : ℂ) 1)) w := by
  rw [sphereCircleHeight, manifoldMorseIndex_comp_fst_add_comp_snd
    (contMDiff_sphereHeight (m := 2) u p).contDiffAt_comp_extChartAt_symm
    (contMDiff_mul_sphereHeight (m := 2) ε w).contDiffAt_comp_extChartAt_symm,
    manifoldMorseIndex_scalar_comp_of_pos (φ := (ε * ·)) (contMDiff_sphereHeight (m := 2) 1 w)
      (contDiff_const.mul contDiff_id).contDiffAt hw (by simpa using hε)]

/-! ### The induced function on the mapping torus -/

/-- The function `[t, p, w] ↦ ⟪p, u⟫ + ε Re w` on the mapping torus of
`τ = TauCeti.sphereCircleReflection v`, for a unit vector `u` orthogonal to `v`. For `E = ℝ³`, `v`
the second and `u` the third coordinate vector it is `[t, p, θ] ↦ z(p) + ε cos θ`. -/
def sphereCircleTorusHeight (huv : ⟪v, (u : E)⟫_ℝ = 0) (ε : ℝ) :
    SmoothMappingTorus (sphereCircleReflection v) → ℝ :=
  SmoothMappingTorus.liftOfInvariant _ (sphereCircleHeight u ε)
    (sphereCircleHeight_sphereCircleReflection huv ε)

/-- The function `TauCeti.sphereCircleTorusHeight` takes the value `⟪p, u⟫ + ε Re w` at
`[t, p, w]`. -/
@[simp]
theorem sphereCircleTorusHeight_mk (huv : ⟪v, (u : E)⟫_ℝ = 0) (ε t : ℝ)
    (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    sphereCircleTorusHeight huv ε (SmoothMappingTorus.mk _ t x) = sphereCircleHeight u ε x :=
  SmoothMappingTorus.liftOfInvariant_mk _ _ t x

/-- The **critical circle** `t ↦ [t, p, w]` of the function on the mapping torus through a critical
point `(p, w)` of `TauCeti.sphereCircleHeight u ε`: the closed orbit of the suspension flow through
it, a smooth embedding of the circle `ℝ / ℤ`, since `(p, w)` is fixed by `τ`. -/
def sphereCircleCriticalCircle (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ} (hε : ε ≠ 0)
    (x : criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε)) :
    SmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) ∞ (AddCircle ((1 : ℕ) : ℝ))
      (SmoothMappingTorus (sphereCircleReflection v)) :=
  SmoothMappingTorus.closedOrbitEmbedding
    ((isFixedPt_sphereCircleReflection_of_mem_criticalPoints huv hε x.property).isPeriodicPt 1)
    (by simp) (minimalPeriod_eq_one_iff_isFixedPt.2
      (isFixedPt_sphereCircleReflection_of_mem_criticalPoints huv hε x.property))

/-- The critical circle through `x` sends `t` to `[t, x]`. -/
@[simp]
theorem sphereCircleCriticalCircle_coe (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ} (hε : ε ≠ 0)
    (x : criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε)) (t : ℝ) :
    sphereCircleCriticalCircle huv hε x t =
      SmoothMappingTorus.mk _ t (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) := by
  rw [sphereCircleCriticalCircle, SmoothMappingTorus.coe_closedOrbitEmbedding,
    SmoothMappingTorus.closedOrbit_coe]

/-- **The function on the mapping torus is Morse–Bott** for `ε ≠ 0`: the closed orbits
`t ↦ [t, ±u, ±1]` of the suspension flow through the four critical points of
`TauCeti.sphereCircleHeight u ε` are its critical circles. -/
theorem isMorseBottFamily_sphereCircleTorusHeight (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ}
    (hε : ε ≠ 0) :
    IsMorseBottFamily (sphereCircleCriticalCircle huv hε) (sphereCircleTorusHeight huv ε) :=
  SmoothMappingTorus.isMorseBottFamily_liftOfInvariant _ _ (isMorse_sphereCircleHeight u hε)
    fun _ hx ↦ isFixedPt_sphereCircleReflection_of_mem_criticalPoints huv hε hx

/-- **The critical points of the function on the mapping torus** are the points `[t, ±u, ±1]` of
the four critical circles, for `ε ≠ 0`. -/
theorem mk_mem_criticalPoints_sphereCircleTorusHeight_iff (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ}
    (hε : ε ≠ 0) (t : ℝ) (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    SmoothMappingTorus.mk _ t x ∈
        criticalPoints (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (sphereCircleTorusHeight huv ε) ↔
      (x.1 = u ∨ x.1 = -u) ∧ (x.2 = 1 ∨ x.2 = -1) := by
  rw [sphereCircleTorusHeight,
    SmoothMappingTorus.mk_mem_criticalPoints_liftOfInvariant_iff _ _ (by simp),
    mem_criticalPoints_sphereCircleHeight_iff u hε]

/-- The Morse index of the function on the mapping torus at `[t, p, w]` is the sum of the indices
of the two heights at `p` and `w`, for `ε > 0`. -/
private theorem manifoldMorseIndex_sphereCircleTorusHeight (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ}
    (hε : 0 < ε) (t : ℝ) {p : sphere (0 : E) 1} {w : sphere (0 : ℂ) 1}
    (hp : p = u ∨ p = -u) (hw : w = 1 ∨ w = -1) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (sphereCircleTorusHeight huv ε)
        (SmoothMappingTorus.mk _ t (p, w)) =
      manifoldMorseIndex (𝓡 2) (sphereHeight u) p +
        manifoldMorseIndex (𝓡 1) (sphereHeight (1 : sphere (0 : ℂ) 1)) w := by
  have hcrit := (mem_criticalPoints_sphereCircleHeight_iff u hε.ne' (p, w)).2 ⟨hp, hw⟩
  have hw' : w ∈ criticalPoints (𝓡 1) (sphereHeight (1 : sphere (0 : ℂ) 1)) := by
    rw [mem_criticalPoints, mvfderiv_sphereHeight_eq_zero_iff]
    exact hw
  rw [sphereCircleTorusHeight,
    SmoothMappingTorus.manifoldMorseIndex_liftOfInvariant_mk _ _ (by simp)
    ((isMorse_sphereCircleHeight u hε.ne').contMDiff.of_le (by simp) _) hcrit,
    manifoldMorseIndex_sphereCircleHeight u hε hw']

/-- The Morse index along the critical circle `(N, 0)`, through `[t, u, 1]`, is `3`. -/
theorem manifoldMorseIndex_sphereCircleTorusHeight_self_one (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ}
    (hε : 0 < ε) (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (sphereCircleTorusHeight huv ε)
      (SmoothMappingTorus.mk _ t (u, 1)) = 3 := by
  rw [manifoldMorseIndex_sphereCircleTorusHeight huv hε t (.inl rfl) (.inl rfl),
    manifoldMorseIndex_sphereHeight_self, manifoldMorseIndex_sphereHeight_self]

/-- The Morse index along the critical circle `(N, π)`, through `[t, u, -1]`, is `2`. -/
theorem manifoldMorseIndex_sphereCircleTorusHeight_self_neg_one (huv : ⟪v, (u : E)⟫_ℝ = 0)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (sphereCircleTorusHeight huv ε)
      (SmoothMappingTorus.mk _ t (u, -1)) = 2 := by
  rw [manifoldMorseIndex_sphereCircleTorusHeight huv hε t (.inl rfl) (.inr rfl),
    manifoldMorseIndex_sphereHeight_self, manifoldMorseIndex_sphereHeight_neg]

/-- The Morse index along the critical circle `(S, 0)`, through `[t, -u, 1]`, is `1`. -/
theorem manifoldMorseIndex_sphereCircleTorusHeight_neg_self_one (huv : ⟪v, (u : E)⟫_ℝ = 0)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (sphereCircleTorusHeight huv ε)
      (SmoothMappingTorus.mk _ t (-u, 1)) = 1 := by
  rw [manifoldMorseIndex_sphereCircleTorusHeight huv hε t (.inr rfl) (.inl rfl),
    manifoldMorseIndex_sphereHeight_neg, manifoldMorseIndex_sphereHeight_self]

/-- The Morse index along the critical circle `(S, π)`, through `[t, -u, -1]`, is `0`. -/
theorem manifoldMorseIndex_sphereCircleTorusHeight_neg_self_neg_one (huv : ⟪v, (u : E)⟫_ℝ = 0)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (sphereCircleTorusHeight huv ε)
      (SmoothMappingTorus.mk _ t (-u, -1)) = 0 := by
  rw [manifoldMorseIndex_sphereCircleTorusHeight huv hε t (.inr rfl) (.inr rfl),
    manifoldMorseIndex_sphereHeight_neg, manifoldMorseIndex_sphereHeight_neg]

/-! ### The negative normal plane of the circle `(N, π)` -/

section NegativeNormal

open Bundle Submodule

variable (hn : (∞ : ℕ∞ω) ≠ 0)

/-- At `(u, -1)` the Hessian of `TauCeti.sphereCircleHeight u ε` is negative definite on the sphere
directions `(a, 0)`, since the height `⟪p, u⟫` has a nondegenerate maximum at `u`. -/
private theorem criticalHessian_sphereCircleHeight_inl_neg (u : sphere (0 : E) 1) (ε : ℝ)
    (a : EuclideanSpace ℝ (Fin 2)) (ha : a ≠ 0) :
    criticalHessian ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) (u, -1)
      (LinearMap.inl ℝ _ (EuclideanSpace ℝ (Fin 1)) a)
      (LinearMap.inl ℝ _ (EuclideanSpace ℝ (Fin 1)) a) < 0 := by
  rw [sphereCircleHeight, criticalHessian_comp_fst_add_comp_snd_apply
    (contMDiff_sphereHeight (m := 2) u u).contDiffAt_comp_extChartAt_symm
    (contMDiff_mul_sphereHeight (m := 2) ε (-1)).contDiffAt_comp_extChartAt_symm]
  have hmax := (manifoldMorseIndex_eq_finrank_iff (I := 𝓡 2) (f := sphereHeight u)
    (x := u)).1 (by rw [manifoldMorseIndex_sphereHeight_self, finrank_euclideanSpace_fin]) a ha
  -- The circle component of `(a, 0)` vanishes.
  have h0 : criticalHessian (𝓡 1) ((ε * ·) ∘ sphereHeight 1) (-1 : sphere (0 : ℂ) 1)
      (LinearMap.inl ℝ _ (EuclideanSpace ℝ (Fin 1)) a).2
      (LinearMap.inl ℝ _ (EuclideanSpace ℝ (Fin 1)) a).2 = 0 := by
    -- The second component is the zero of `EuclideanSpace ℝ (Fin 1)`; reading it as the zero of
    -- the tangent space, the domain of the Hessian, lets `map_zero` apply. The zero bilinear map
    -- then vanishes on it by definition.
    change criticalHessian (𝓡 1) _ _ 0 (LinearMap.inl ℝ _ (EuclideanSpace ℝ (Fin 1)) a).2 = 0
    rw [ContinuousLinearMap.map_zero]
    rfl
  rw [h0, add_zero]
  exact hmax

/-- The Morse index of the function on the mapping torus is `2` along the critical circle through
`(u, -1)`, the circle `(N, π)`. -/
theorem manifoldMorseIndex_sphereCircleCriticalCircle_of_eq_self_neg_one
    (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ} (hε : 0 < ε)
    {x : criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε)}
    (hx : (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) = (u, -1))
    (s : AddCircle ((1 : ℕ) : ℝ)) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (sphereCircleTorusHeight huv ε)
      (sphereCircleCriticalCircle huv hε.ne' x s) = 2 := by
  induction s using QuotientAddGroup.induction_on with | H t => ?_
  rw [sphereCircleCriticalCircle_coe, hx]
  exact manifoldMorseIndex_sphereCircleTorusHeight_self_neg_one huv hε t

/-- **The negative normal bundle of the circle `(N, π)` is not orientable.** Let `x = (u, -1)`, so
that the critical circle `C = {[t, u, -1]}` is the circle `(N, π)` of Morse index `2`, and let `g`
be a `C^k` fibre metric on its normal bundle, with negative normal bundle `ν⁻`, a plane bundle over
the circle. Then `ν⁻` is not orientable.

At `x` the Hessian of `h` is negative definite on the tangent plane `T_u S²` of the sphere, where
the height `⟪p, u⟫` has its maximum, and `τ` acts on this plane by the differential of the
reflection `ρ`, which reverses the orientation of the sphere and fixes `u`, so it has negative
determinant (for `E = ℝ³` it is `diag(1, -1)`). Hence the orientation of `ν⁻` has monodromy `-1`
around `C` (`isEmpty_vectorBundleOrientation_negativeNormalSpace_of_det_neg`, in the namespace
`TauCeti.SmoothMappingTorus`).

This happens although the mapping torus is oriented
(`TauCeti.orientable_smoothMappingTorus_sphereCircleReflection`) and so is the circle `C`: on the
whole normal space `T_u S² × T_{-1} S¹` of `C`, the differential of `τ` also reverses the circle
factor (for `E = ℝ³` it is `diag(1, -1, -1)`, of determinant `+1`). So the orientation local system
of the negative normal bundle, which twists the homology across the level of `C`, is not that of the
whole normal bundle. -/
theorem isEmpty_vectorBundleOrientation_negativeNormalSpace_sphereCircleCriticalCircle
    (hv : v ≠ 0) (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ} (hε : 0 < ε)
    {x : criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε)}
    (hx : (x : sphere (0 : E) 1 × sphere (0 : ℂ) 1) = (u, -1))
    {k : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) -
      finrank ℝ ℝ)
    (g : letI := (sphereCircleCriticalCircle huv hε.ne' x).normalSpaceFiberBundle hn hdim
      letI := (sphereCircleCriticalCircle huv hε.ne' x).normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric 𝓘(ℝ) k P
        fun s ↦ (sphereCircleCriticalCircle huv hε.ne' x).isImmersion.NormalSpace s hn) :
    haveI : IsManifold (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) ((k : ℕ∞ω) + 2)
        (SmoothMappingTorus (sphereCircleReflection v)) :=
      .of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
    haveI : IsManifold 𝓘(ℝ) ((k : ℕ∞ω) + 1) (AddCircle ((1 : ℕ) : ℝ)) :=
      .of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
    letI := (sphereCircleCriticalCircle huv hε.ne' x).normalSpaceFiberBundle hn hdim
    letI := (sphereCircleCriticalCircle huv hε.ne' x).normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin 2 → ℝ)
      (((isMorseBottFamily_sphereCircleTorusHeight huv hε.ne').isNondegenerateCriticalSubmanifold
        x).negativeNormalSpace hn g.toRiemannianMetric)
    letI := (((isMorseBottFamily_sphereCircleTorusHeight huv
      hε.ne').isNondegenerateCriticalSubmanifold
        x).hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn
        (WithTop.coe_le_coe.2 le_top : (k : ℕ∞ω) + 1 ≤ ∞)
        (fun s ↦ ((isMorseBottFamily_sphereCircleTorusHeight huv hε.ne').contMDiff _).of_le
          (WithTop.coe_le_coe.2 le_top)) hdim g
        (manifoldMorseIndex_sphereCircleCriticalCircle_of_eq_self_neg_one huv hε hx)).fiberBundle
    haveI := (((isMorseBottFamily_sphereCircleTorusHeight huv
      hε.ne').isNondegenerateCriticalSubmanifold
        x).hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn
        (WithTop.coe_le_coe.2 le_top : (k : ℕ∞ω) + 1 ≤ ∞)
        (fun s ↦ ((isMorseBottFamily_sphereCircleTorusHeight huv hε.ne').contMDiff _).of_le
          (WithTop.coe_le_coe.2 le_top)) hdim g
        (manifoldMorseIndex_sphereCircleCriticalCircle_of_eq_self_neg_one huv hε hx)).vectorBundle
    IsEmpty (VectorBundleOrientation (Fin 2 → ℝ)
      (fun s ↦ ((isMorseBottFamily_sphereCircleTorusHeight huv
        hε.ne').isNondegenerateCriticalSubmanifold x).negativeNormalSpace hn g.toRiemannianMetric s)
      (Fin 2)) := by
  obtain ⟨⟨p, w⟩, hpw⟩ := x
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  let j := LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1))
  -- `τ` acts on the sphere directions at `(u, -1)` by the differential `A` of `ρ` at `u`.
  let A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (mfderiv (𝓡 2) (𝓡 2) (ℝ ∙ v)ᗮ.reflection.unitSphereEquiv p).toLinearMap
  have hA (a : EuclideanSpace ℝ (Fin 2)) :
      mfderiv ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1)) (sphereCircleReflection v) (p, -1) (j a) =
        j (A a) := by
    -- `j a` is `(a, 0)`, read in the tangent space of the product.
    have hj : j a = (Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 1)
        ((p, -1) : sphere (0 : E) 1 × sphere (0 : ℂ) 1)).symm (a, 0) :=
      (Manifold.tangentSpaceProdEquiv_symm_apply _ _).symm
    rw [coe_sphereCircleReflection, hj,
      Manifold.mfderiv_prodMap_apply
        ((LinearIsometryEquiv.contMDiff_unitSphereEquiv (n := 2) (k := 2) (m := 1)
          _).mdifferentiableAt one_ne_zero)
        ((LinearIsometryEquiv.contMDiff_unitSphereEquiv (n := 1) (k := 1) (m := 1)
          _).mdifferentiableAt one_ne_zero), map_zero, Manifold.tangentSpaceProdEquiv_symm_apply]
    -- Both sides are now `(A a, 0)`, by the definitions of `A` and of `j = LinearMap.inl`.
    rfl
  exact SmoothMappingTorus.isEmpty_vectorBundleOrientation_negativeNormalSpace_of_det_neg hn
    (h := sphereCircleHeight p ε) (hh := sphereCircleHeight_sphereCircleReflection huv ε)
    (sphereCircleCriticalCircle_coe huv hε.ne' _)
    ((isMorseBottFamily_sphereCircleTorusHeight huv hε.ne').isNondegenerateCriticalSubmanifold _)
    (fun _ ↦ ((isMorseBottFamily_sphereCircleTorusHeight huv hε.ne').contMDiff _).of_le
      (WithTop.coe_le_coe.2 le_top)) hdim g
    (manifoldMorseIndex_sphereCircleCriticalCircle_of_eq_self_neg_one huv hε hx)
    (V := EuclideanSpace ℝ (Fin 2)) finrank_euclideanSpace_fin j A hA
    (det_mfderiv_unitSphereEquiv_neg (by
      rw [← LinearEquiv.coe_det, linearEquiv_det_reflection_orthogonal_singleton hv]
      exact neg_one_lt_zero)
      (by simpa using reflection_orthogonal_singleton_eq_self_of_inner_eq_zero huv))
    (criticalHessian_sphereCircleHeight_inl_neg p ε)

end NegativeNormal

end TauCeti
