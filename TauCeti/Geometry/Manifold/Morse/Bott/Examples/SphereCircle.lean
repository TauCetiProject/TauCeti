/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.SphereCircle
public import TauCeti.Geometry.Manifold.Morse.Bott.MappingTorus
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Morse.Prod
import TauCeti.Geometry.Manifold.Morse.ScalarComposition

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

## Main definitions

* `TauCeti.sphereCircleHeight u ε`: the function `(p, w) ↦ ⟪p, u⟫ + ε Re w` on `S² × S¹`.
* `TauCeti.sphereCircleTorusHeight huv ε`: the function it induces on the mapping torus of `τ`.

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
local instance finiteDimensional_of_fact_finrank_eq_three : FiniteDimensional ℝ E :=
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

/-- **The function on the mapping torus is Morse–Bott** for `ε ≠ 0`: the closed orbits
`t ↦ [t, ±u, ±1]` of the suspension flow through the four critical points of
`TauCeti.sphereCircleHeight u ε` are its critical circles. -/
theorem isMorseBottFamily_sphereCircleTorusHeight (huv : ⟪v, (u : E)⟫_ℝ = 0) {ε : ℝ}
    (hε : ε ≠ 0) :
    IsMorseBottFamily (fun x : criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) ↦
      SmoothMappingTorus.closedOrbitEmbedding
        ((isFixedPt_sphereCircleReflection_of_mem_criticalPoints huv hε x.property).isPeriodicPt 1)
        (by simp) (minimalPeriod_eq_one_iff_isFixedPt.2
          (isFixedPt_sphereCircleReflection_of_mem_criticalPoints huv hε x.property)))
      (sphereCircleTorusHeight huv ε) :=
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

end TauCeti
