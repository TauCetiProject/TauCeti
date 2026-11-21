/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.SphereCircle
public import TauCeti.Geometry.Manifold.Morse.Bott.MappingTorus
public import TauCeti.Geometry.Manifold.Morse.ScalarComposition
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# A Morse–Bott function with four critical circles on a mapping torus of `S² × S¹`

Let `E` be a three-dimensional real inner product space with unit sphere `S²`, let `S¹` be the
unit circle of `ℂ`, and let `τ (p, w) = (ρ p, conj w)` be the diffeomorphism of `S² × S¹` which
reflects the sphere across the plane `v^⊥` and conjugates the circle
(`TauCeti.sphereCircleReflection v`). Its mapping torus `X` is an oriented closed four-manifold
(`TauCeti.orientable_smoothMappingTorus_sphereCircleReflection`).

For a unit vector `u` orthogonal to `v` and a real `ε ≠ 0`, the function

`(p, w) ↦ ⟪p, u⟫ + ε Re w`

on `S² × S¹` (`TauCeti.sphereCircleHeight u ε`), the height `z` of the sphere in the direction `u`
plus `ε cos θ` for `w = e^{iθ}`, is a Morse function. Its critical points are the four pairs
`(±u, ±1)` of a pole and a real point of the circle. The function is invariant under `τ`, because
`ρ` fixes `u` and conjugation fixes real parts, and `τ` fixes the four critical points. So it
descends to the function `[t, p, w] ↦ ⟪p, u⟫ + ε Re w` on `X`
(`TauCeti.sphereCircleReflection.torusHeight`), which is a Morse–Bott function whose critical set
is the union of the four circles `[t] ↦ [t, (±u, ±1)]`
(`TauCeti.sphereCircleReflection.isMorseBottFamily_torusHeight`). For `ε > 0` their Morse indices,
the ranks of the negative normal bundles, are `3`, `2`, `1` and `0` for the circles through
`(u, 1)`, `(u, -1)`, `(-u, 1)` and `(-u, -1)`: the north pole is a maximum of the height, of index
`2`, and `1` is a maximum of `Re`, of index `1`.

This is the classical example of a Morse–Bott function on an oriented manifold whose critical
submanifolds are oriented circles, while the space of its gradient trajectories between the
circles through `(u, -1)` and `(-u, -1)` is a Klein bottle: the negative normal bundle of the circle
through `(u, -1)` is the tangent plane of the sphere at the north pole, on which `ρ` acts with
determinant `-1`, so its orientation line is twisted around the circle although the whole normal
bundle is not. The trajectory spaces themselves are not studied here.

## Main definitions

* `TauCeti.sphereCircleHeight u ε`: the function `(p, w) ↦ ⟪p, u⟫ + ε Re w` on `S² × S¹`.
* `TauCeti.sphereCircleReflection.torusHeight huv ε`: the function it induces on the mapping torus
  of `τ`.

## Main results

* `TauCeti.isMorse_sphereCircleHeight`: for `ε ≠ 0`, the function on `S² × S¹` is Morse.
* `TauCeti.mem_criticalPoints_sphereCircleHeight_iff`: its critical points are the four pairs
  `(±u, ±1)`.
* `TauCeti.sphereCircleReflection.contMDiff_torusHeight`: the induced function on the mapping
  torus is smooth.
* `TauCeti.sphereCircleReflection.isMorseBottFamily_torusHeight`: the induced function on the
  mapping torus is Morse–Bott, with the four circles through the critical points as its critical
  submanifolds.
* `TauCeti.sphereCircleReflection.mk_mem_criticalPoints_torusHeight_iff`: its critical points are
  the points of these four circles.
* `TauCeti.sphereCircleReflection.manifoldMorseIndex_torusHeight_mk_self_one`,
  `TauCeti.sphereCircleReflection.manifoldMorseIndex_torusHeight_mk_self_neg_one`,
  `TauCeti.sphereCircleReflection.manifoldMorseIndex_torusHeight_mk_neg_self_one` and
  `TauCeti.sphereCircleReflection.manifoldMorseIndex_torusHeight_mk_neg_self_neg_one`: for `ε > 0`
  the circles through `(u, 1)`, `(u, -1)`, `(-u, 1)` and `(-u, -1)` have Morse indices `3`, `2`,
  `1` and `0`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott functions and the orientations of
  their trajectory spaces).
-/

public section

noncomputable section

open Function Metric Module Set
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]

/-- A space of dimension `2 + 1` is finite-dimensional, so its unit sphere is compact. -/
local instance finiteDimensional_sphereCircleHeightAmbient : FiniteDimensional ℝ E :=
  .of_fact_finrank_eq_succ 2

/-! ### The function on `S² × S¹` -/

/-- The function `(p, w) ↦ ⟪p, u⟫ + ε Re w` on `S² × S¹`: the height of the sphere in the direction
`u` plus `ε` times the real part on the unit circle of `ℂ`, which is the height of the circle in
the direction `1`. -/
def sphereCircleHeight (u : sphere (0 : E) 1) (ε : ℝ) :
    sphere (0 : E) 1 × sphere (0 : ℂ) 1 → ℝ :=
  sphereHeight u ∘ Prod.fst + ((ε * ·) ∘ sphereHeight (1 : sphere (0 : ℂ) 1)) ∘ Prod.snd

variable (u : sphere (0 : E) 1) (ε : ℝ)

omit [Fact (finrank ℝ E = 2 + 1)] in
/-- The value of the function `(p, w) ↦ ⟪p, u⟫ + ε Re w`. -/
@[simp]
theorem sphereCircleHeight_apply (q : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    sphereCircleHeight u ε q = ⟪(q.1 : E), (u : E)⟫ + ε * (q.2 : ℂ).re := by
  simp [sphereCircleHeight, sphereHeight_apply, Complex.inner]

omit [Fact (finrank ℝ E = 2 + 1)] in
/-- Multiplication by `ε` is smooth. -/
private theorem contDiff_mul_left {m : ℕ∞ω} : ContDiff ℝ m (ε * · : ℝ → ℝ) :=
  contDiff_const.mul contDiff_id

/-- `ε` times the height of the circle is smooth. -/
private theorem contMDiff_mul_sphereHeight {m : ℕ∞ω} :
    ContMDiff (𝓡 1) 𝓘(ℝ) m ((ε * ·) ∘ sphereHeight (1 : sphere (0 : ℂ) 1)) :=
  (contDiff_mul_left ε).contMDiff.comp (contMDiff_sphereHeight 1)

/-- The function on `S² × S¹` is smooth. -/
theorem contMDiff_sphereCircleHeight {m : ℕ∞ω} :
    ContMDiff ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ) m (sphereCircleHeight u ε) :=
  ((contMDiff_sphereHeight u).comp contMDiff_fst).add
    ((contMDiff_mul_sphereHeight ε).comp contMDiff_snd)

variable {u ε}

/-- **The function `(p, w) ↦ ⟪p, u⟫ + ε Re w` is a Morse function** on `S² × S¹`, for `ε ≠ 0`: it
is the sum of the height function of the sphere and of `ε` times that of the circle. -/
theorem isMorse_sphereCircleHeight (hε : ε ≠ 0) :
    IsMorse ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) :=
  (isMorse_sphereHeight u).comp_fst_add_comp_snd ((isMorse_sphereHeight 1).scalar_comp
    (fun _ ↦ (contDiff_mul_left ε).contDiffAt) (fun _ ↦ by simpa using hε))

/-- **The critical points of `(p, w) ↦ ⟪p, u⟫ + ε Re w`**, for `ε ≠ 0`, are the four pairs
`(±u, ±1)` of a pole of the sphere and a real point of the circle. -/
theorem mem_criticalPoints_sphereCircleHeight_iff (hε : ε ≠ 0)
    {q : sphere (0 : E) 1 × sphere (0 : ℂ) 1} :
    q ∈ criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) ↔
      (q.1 = u ∨ q.1 = -u) ∧ (q.2 = 1 ∨ q.2 = -1) := by
  have hcirc : q.2 ∈ criticalPoints (𝓡 1) ((ε * ·) ∘ sphereHeight (1 : sphere (0 : ℂ) 1)) ↔
      q.2 ∈ criticalPoints (𝓡 1) (sphereHeight (1 : sphere (0 : ℂ) 1)) :=
    mem_criticalPoints_scalar_comp_iff
      ((contMDiff_sphereHeight (m := 1) 1 q.2).mdifferentiableAt one_ne_zero) (by simpa using hε)
  rw [sphereCircleHeight, mem_criticalPoints,
    mvfderiv_comp_fst_add_comp_snd_eq_zero_iff
      ((contMDiff_sphereHeight (m := 1) u q.1).mdifferentiableAt one_ne_zero)
      ((contMDiff_mul_sphereHeight (m := 1) ε q.2).mdifferentiableAt one_ne_zero),
    ← mem_criticalPoints, ← mem_criticalPoints, hcirc, criticalPoints_sphereHeight,
    criticalPoints_sphereHeight]
  simp

/-- At a critical point `(p, w)` of `(p, w) ↦ ⟪p, u⟫ + ε Re w`, for `ε > 0`, the Morse index is
the sum of the Morse indices of the height functions of the sphere at `p` and of the circle at
`w`. -/
theorem manifoldMorseIndex_sphereCircleHeight (hε : 0 < ε)
    {q : sphere (0 : E) 1 × sphere (0 : ℂ) 1}
    (hq : q ∈ criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε)) :
    manifoldMorseIndex ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) q =
      manifoldMorseIndex (𝓡 2) (sphereHeight u) q.1 +
        manifoldMorseIndex (𝓡 1) (sphereHeight (1 : sphere (0 : ℂ) 1)) q.2 := by
  have hq2 : q.2 ∈ criticalPoints (𝓡 1) (sphereHeight (1 : sphere (0 : ℂ) 1)) := by
    rw [criticalPoints_sphereHeight]
    exact ((mem_criticalPoints_sphereCircleHeight_iff hε.ne').1 hq).2
  rw [sphereCircleHeight, manifoldMorseIndex_comp_fst_add_comp_snd
    (g := (ε * ·) ∘ sphereHeight (1 : sphere (0 : ℂ) 1))
    (contMDiff_sphereHeight (m := 2) u q.1).contDiffAt_comp_extChartAt_symm
    ((contMDiff_mul_sphereHeight (m := 2) ε q.2).contDiffAt_comp_extChartAt_symm),
    manifoldMorseIndex_scalar_comp_of_pos (contMDiff_sphereHeight 1 q.2)
      (contDiff_mul_left ε).contDiffAt hq2 (by simpa using hε)]

/-! ### Invariance under the reflection `τ` -/

variable {v : E}

/-- **The function `(p, w) ↦ ⟪p, u⟫ + ε Re w` is invariant under `τ`** when `u` is orthogonal to
`v`: the reflection across `v^⊥` fixes `u`, and conjugation does not change real parts. -/
theorem sphereCircleHeight_sphereCircleReflection (huv : ⟪(u : E), v⟫ = 0) (ε : ℝ)
    (q : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    sphereCircleHeight u ε (sphereCircleReflection v q) = sphereCircleHeight u ε q := by
  have hu : (ℝ ∙ v)ᗮ.reflection (u : E) = u :=
    reflection_orthogonal_singleton_eq_self_of_inner_eq_zero (by rw [real_inner_comm, huv])
  rw [sphereCircleHeight_apply, sphereCircleHeight_apply, coe_sphereCircleReflection_apply_fst,
    coe_sphereCircleReflection_apply_snd, Complex.conj_re]
  congr 1
  calc ⟪(ℝ ∙ v)ᗮ.reflection (q.1 : E), (u : E)⟫
      = ⟪(ℝ ∙ v)ᗮ.reflection (q.1 : E), (ℝ ∙ v)ᗮ.reflection (u : E)⟫ := by rw [hu]
    _ = ⟪(q.1 : E), (u : E)⟫ := LinearIsometryEquiv.inner_map_map _ _ _

/-- **`τ` fixes the critical points** of `(p, w) ↦ ⟪p, u⟫ + ε Re w`, for `u` orthogonal to `v` and
`ε ≠ 0`: it fixes the poles `±u` and the real points `±1` of the circle. -/
theorem isFixedPt_sphereCircleReflection_of_mem_criticalPoints (huv : ⟪(u : E), v⟫ = 0)
    (hε : ε ≠ 0) {q : sphere (0 : E) 1 × sphere (0 : ℂ) 1}
    (hq : q ∈ criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε)) :
    IsFixedPt (sphereCircleReflection v) q := by
  have hu : (ℝ ∙ v)ᗮ.reflection (u : E) = u :=
    reflection_orthogonal_singleton_eq_self_of_inner_eq_zero (by rw [real_inner_comm, huv])
  obtain ⟨h₁, h₂⟩ := (mem_criticalPoints_sphereCircleHeight_iff hε).1 hq
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [coe_sphereCircleReflection_apply_fst]
    rcases h₁ with h | h <;> rw [h]
    · exact hu
    · rw [coe_neg_sphere, map_neg, hu]
  · rw [coe_sphereCircleReflection_apply_snd]
    rcases h₂ with h | h <;> rw [h] <;> simp

/-! ### The Morse–Bott function on the mapping torus -/

namespace sphereCircleReflection

/-- The function `[t, p, w] ↦ ⟪p, u⟫ + ε Re w` on the mapping torus of `τ`, induced by the
`τ`-invariant function `TauCeti.sphereCircleHeight u ε` on `S² × S¹`
(`TauCeti.sphereCircleReflection.torusHeight_mk`). -/
def torusHeight (huv : ⟪(u : E), v⟫ = 0) (ε : ℝ) :
    SmoothMappingTorus (sphereCircleReflection v) → ℝ :=
  MulAction.orbitRelQuotientLift
    (fun z ↦ sphereCircleHeight u ε ((SmoothMappingTorus.Cover.ofProd _).symm z).2) fun k z ↦ by
      -- Invariance under `τ` is invariance under all of its integer powers.
      have h : Semiconj (sphereCircleHeight u ε) (sphereCircleReflection v)
          (1 : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) := fun q ↦ by
        rw [Diffeomorph.coe_one, id_eq]
        exact sphereCircleHeight_sphereCircleReflection huv ε q
      rw [SmoothMappingTorus.Cover.ofProd_symm_smul, h.diffeomorph_zpow_right, one_zpow,
        Diffeomorph.coe_one, id_eq]

variable (huv : ⟪(u : E), v⟫ = 0)

/-- The function on the mapping torus sends `[t, (p, w)]` to `⟪p, u⟫ + ε Re w`. -/
@[simp]
theorem torusHeight_mk (ε : ℝ) (t : ℝ) (q : sphere (0 : E) 1 × sphere (0 : ℂ) 1) :
    torusHeight huv ε (SmoothMappingTorus.mk _ t q) = sphereCircleHeight u ε q := by
  rw [torusHeight, SmoothMappingTorus.mk_def, MulAction.orbitRelQuotientLift_mk,
    Equiv.symm_apply_apply]

/-- The function `[t, p, w] ↦ ⟪p, u⟫ + ε Re w` on the mapping torus is smooth. -/
theorem contMDiff_torusHeight (ε : ℝ) :
    ContMDiff (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) 𝓘(ℝ) ∞ (torusHeight huv ε) :=
  (SmoothMappingTorus.contMDiff_iff_of_forall_mk_eq _ (torusHeight_mk huv ε) le_rfl).2
    (contMDiff_sphereCircleHeight u ε)

/-- **The function `[t, p, w] ↦ ⟪p, u⟫ + ε Re w` is Morse–Bott** on the mapping torus of `τ`, for
`u` orthogonal to `v` and `ε ≠ 0`: its critical submanifolds are the four circles `[t] ↦ [t, q]`
through the critical points `q = (±u, ±1)` of the function on `S² × S¹`. -/
theorem isMorseBottFamily_torusHeight (hε : ε ≠ 0) :
    IsMorseBottFamily
      (fun q : criticalPoints ((𝓡 2).prod (𝓡 1)) (sphereCircleHeight u ε) ↦
        SmoothMappingTorus.fixedPtCircle _
          (isFixedPt_sphereCircleReflection_of_mem_criticalPoints huv hε q.property))
      (torusHeight huv ε) :=
  (isMorse_sphereCircleHeight hε).isMorseBottFamily_fixedPtCircle (torusHeight_mk huv ε) _

/-- **The critical points of `[t, p, w] ↦ ⟪p, u⟫ + ε Re w`** on the mapping torus, for `ε ≠ 0`, are
the points `[t, (±u, ±1)]` of the four critical circles. -/
theorem mk_mem_criticalPoints_torusHeight_iff (hε : ε ≠ 0) {t : ℝ}
    {q : sphere (0 : E) 1 × sphere (0 : ℂ) 1} :
    SmoothMappingTorus.mk _ t q ∈
        criticalPoints (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (torusHeight huv ε) ↔
      (q.1 = u ∨ q.1 = -u) ∧ (q.2 = 1 ∨ q.2 = -1) := by
  rw [SmoothMappingTorus.mk_mem_criticalPoints_iff_of_forall_mk_eq _ (torusHeight_mk huv ε),
    mem_criticalPoints_sphereCircleHeight_iff hε]

variable {huv}

/-- The Morse index of `[t, p, w] ↦ ⟪p, u⟫ + ε Re w` at a point of a critical circle, for
`ε > 0`, is the Morse index of the height of the sphere plus that of the height of the circle. -/
private theorem manifoldMorseIndex_torusHeight_mk (hε : 0 < ε) (t : ℝ)
    {q : sphere (0 : E) 1 × sphere (0 : ℂ) 1}
    (hq : (q.1 = u ∨ q.1 = -u) ∧ (q.2 = 1 ∨ q.2 = -1)) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (torusHeight huv ε)
        (SmoothMappingTorus.mk _ t q) =
      manifoldMorseIndex (𝓡 2) (sphereHeight u) q.1 +
        manifoldMorseIndex (𝓡 1) (sphereHeight (1 : sphere (0 : ℂ) 1)) q.2 := by
  have hq' := (mem_criticalPoints_sphereCircleHeight_iff hε.ne').2 hq
  rw [SmoothMappingTorus.manifoldMorseIndex_mk_of_forall_mk_eq _ (torusHeight_mk huv ε)
    (contMDiff_sphereCircleHeight u ε q) hq', manifoldMorseIndex_sphereCircleHeight hε hq']

/-- For `ε > 0`, the critical circle through `(u, 1)` has Morse index `3`: there the height of the
sphere and the real part on the circle are both maximal. -/
theorem manifoldMorseIndex_torusHeight_mk_self_one (hε : 0 < ε) (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (torusHeight huv ε)
      (SmoothMappingTorus.mk _ t (u, 1)) = 3 := by
  rw [manifoldMorseIndex_torusHeight_mk hε t (by simp), manifoldMorseIndex_sphereHeight_self,
    manifoldMorseIndex_sphereHeight_self]

/-- For `ε > 0`, the critical circle through `(u, -1)` has Morse index `2`. -/
theorem manifoldMorseIndex_torusHeight_mk_self_neg_one (hε : 0 < ε) (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (torusHeight huv ε)
      (SmoothMappingTorus.mk _ t (u, -1)) = 2 := by
  rw [manifoldMorseIndex_torusHeight_mk hε t (by simp), manifoldMorseIndex_sphereHeight_self,
    manifoldMorseIndex_sphereHeight_neg]

/-- For `ε > 0`, the critical circle through `(-u, 1)` has Morse index `1`. -/
theorem manifoldMorseIndex_torusHeight_mk_neg_self_one (hε : 0 < ε) (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (torusHeight huv ε)
      (SmoothMappingTorus.mk _ t (-u, 1)) = 1 := by
  rw [manifoldMorseIndex_torusHeight_mk hε t (by simp), manifoldMorseIndex_sphereHeight_neg,
    manifoldMorseIndex_sphereHeight_self]

/-- For `ε > 0`, the critical circle through `(-u, -1)` has Morse index `0`: there the height of
the sphere and the real part on the circle are both minimal. -/
theorem manifoldMorseIndex_torusHeight_mk_neg_self_neg_one (hε : 0 < ε) (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 1))) (torusHeight huv ε)
      (SmoothMappingTorus.mk _ t (-u, -1)) = 0 := by
  rw [manifoldMorseIndex_torusHeight_mk hε t (by simp), manifoldMorseIndex_sphereHeight_neg,
    manifoldMorseIndex_sphereHeight_neg]

end sphereCircleReflection

end TauCeti
