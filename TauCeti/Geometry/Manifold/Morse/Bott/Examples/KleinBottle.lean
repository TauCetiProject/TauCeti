/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.KleinBottle
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Lift
public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Morse.Prod

/-!
# The height function on the Klein bottle is Morse–Bott

On the Klein bottle `K = (ℝ × S¹) / ((t + 1, z) ∼ (t, conj z))` (`TauCeti.KleinBottle`), the
function `[t, z] ↦ Re z`, that is `[t, e^{iθ}] ↦ cos θ`, is well defined since conjugation
preserves real parts (`TauCeti.KleinBottle.height`). It is smooth, because on the cylinder it is
the height function `TauCeti.sphereHeight 1` of the circle, a function of the second factor, and
the quotient map `(t, z) ↦ [t, z]` is a surjective local diffeomorphism.

Its critical set is the union of two circles, the closed orbits `t ↦ [t, 1]` and `t ↦ [t, -1]`
of the suspension flow through the two fixed points of conjugation
(`TauCeti.KleinBottle.criticalPoints_height`, `TauCeti.KleinBottle.criticalCircle`). Both are
Morse–Bott critical submanifolds
(`TauCeti.KleinBottle.isNondegenerateCriticalSubmanifold_criticalCircle`): on the cylinder the
kernel of the Hessian of `(t, z) ↦ Re z` at `(t, ±1)` is the `t`-direction, since `±1` are
nondegenerate critical points of the height of the circle, and the quotient map carries it onto
the tangent line of the critical circle (`IsLocalDiffeomorphAt.ker_criticalHessian_eq_map`). The
maximum circle `C₁ = {θ = 0}` has Morse index `1` and the minimum circle `C₀ = {θ = π}` has Morse
index `0` (`TauCeti.KleinBottle.manifoldMorseIndex_height_mk_one`,
`TauCeti.KleinBottle.manifoldMorseIndex_height_mk_neg_one`): these are the ranks of their
negative normal bundles.

This is the standard example of a Morse–Bott function with a nonorientable negative normal bundle.
The negative normal direction along `C₁` is the vertical direction of the cylinder, which the
identification `[t + 1, z] = [t, conj z]` reverses, so the negative normal bundle of `C₁` is the
Möbius line and its orientation local system has monodromy `-1`, while that of `C₀` has rank `0`.
That monodromy computation is not formalized here.

## Main definitions

* `TauCeti.KleinBottle.height`: the function `[t, z] ↦ Re z` on the Klein bottle.
* `TauCeti.KleinBottle.criticalCircle`: the closed orbit `t ↦ [t, z]` through a fixed point
  `z = ±1` of conjugation, as a smooth embedding of the circle.

## Main results

* `TauCeti.KleinBottle.contMDiff_height`: the height function is smooth.
* `TauCeti.KleinBottle.mk_mem_criticalPoints_height_iff`,
  `TauCeti.KleinBottle.criticalPoints_height`: its critical set is the union of the two critical
  circles.
* `TauCeti.KleinBottle.isNondegenerateCriticalSubmanifold_criticalCircle`: both critical circles
  are Morse–Bott critical submanifolds.
* `TauCeti.KleinBottle.manifoldMorseIndex_height_mk_one`,
  `TauCeti.KleinBottle.manifoldMorseIndex_height_mk_neg_one`: their Morse indices are `1` and `0`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2 (Morse–Bott homology and its orientation local systems).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

noncomputable section

open Metric Set Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace KleinBottle

attribute [local instance] finrank_real_complex_fact'

/-- The **height function** `[t, z] ↦ Re z`, that is `[t, e^{iθ}] ↦ cos θ`, on the Klein bottle.
It is well defined since conjugation preserves real parts. -/
def height : KleinBottle → ℝ :=
  SmoothMappingTorus.lift conjCircleDiffeomorph (fun _ z ↦ sphereHeight 1 z) fun _ z ↦ by
    simp

/-- The height of `[t, z]` is the real part of `z`. -/
@[simp]
theorem height_mk (t : ℝ) (z : sphere (0 : ℂ) 1) : height (mk t z) = (z : ℂ).re := by
  rw [height, mk, SmoothMappingTorus.lift_mk, sphereHeight_one_apply]

/-- On the cylinder, the height function is the height of the circle, a function of the second
factor. -/
theorem height_comp_uncurry_mk :
    height ∘ uncurry (SmoothMappingTorus.mk conjCircleDiffeomorph) =
      sphereHeight 1 ∘ Prod.snd :=
  SmoothMappingTorus.lift_comp_uncurry_mk _ _

/-- The height function on the Klein bottle is smooth. -/
theorem contMDiff_height : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞ height :=
  (SmoothMappingTorus.contMDiff_lift_iff _ _ le_rfl).2
    ((contMDiff_sphereHeight (n := 1) 1).comp contMDiff_snd)

/-- The height function is `C^2` at every point, as the critical Hessian requires. -/
private theorem contMDiffAt_height (p : KleinBottle) :
    ContMDiffAt (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) 2 height p :=
  contMDiff_height.contMDiffAt.of_le (by simp)

/-- **The critical points of the height function** are the points `[t, z]` with `z = ±1`. -/
theorem mk_mem_criticalPoints_height_iff {t : ℝ} {z : sphere (0 : ℂ) 1} :
    mk t z ∈ criticalPoints (𝓘(ℝ).prod (𝓡 1)) height ↔ z = 1 ∨ z = -1 := by
  have h := (SmoothMappingTorus.isLocalDiffeomorph_uncurry_mk (n := ∞) conjCircleDiffeomorph
    (t, z)).mem_criticalPoints_comp_iff (by simp) (f := height)
  rw [height_comp_uncurry_mk, mem_criticalPoints_comp_snd_iff, criticalPoints_sphereHeight] at h
  exact h.symm

/-- The points `±1` are fixed by conjugation. -/
private theorem isFixedPt_conjCircleDiffeomorph {z : sphere (0 : ℂ) 1} (hz : z = 1 ∨ z = -1) :
    IsFixedPt conjCircleDiffeomorph z := by
  rcases hz with rfl | rfl <;> simp [IsFixedPt]

/-- The **critical circle** `t ↦ [t, z]` of the height function through a fixed point `z = ±1` of
conjugation: the closed orbit of the suspension flow through `[0, z]`, a smooth embedding of the
circle `ℝ / ℤ` into the Klein bottle. -/
def criticalCircle (z : sphere (0 : ℂ) 1) (hz : z = 1 ∨ z = -1) :
    SmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod (𝓡 1)) ∞ (AddCircle ((1 : ℕ) : ℝ)) KleinBottle :=
  .ofIsSmoothEmbedding _ <|
    (SmoothMappingTorus.isSmoothEmbedding_closedOrbit_iff
      ((isFixedPt_conjCircleDiffeomorph hz).isPeriodicPt 1) (by simp)).2 <|
      minimalPeriod_eq_one_iff_isFixedPt.2 (isFixedPt_conjCircleDiffeomorph hz)

/-- The critical circle through `z` sends `t` to `[t, z]`. -/
@[simp]
theorem criticalCircle_coe {z : sphere (0 : ℂ) 1} (hz : z = 1 ∨ z = -1) (t : ℝ) :
    criticalCircle z hz t = mk t z := by
  rw [criticalCircle, SmoothEmbedding.ofIsSmoothEmbedding_apply,
    SmoothMappingTorus.closedOrbit_coe]

/-- The point `[t, y]` lies on the critical circle through `z` exactly when `y = z`. -/
theorem mk_mem_range_criticalCircle_iff {z : sphere (0 : ℂ) 1} (hz : z = 1 ∨ z = -1) {t : ℝ}
    {y : sphere (0 : ℂ) 1} : mk t y ∈ range (criticalCircle z hz) ↔ y = z := by
  rw [criticalCircle, SmoothEmbedding.coe_ofIsSmoothEmbedding, mk,
    SmoothMappingTorus.mk_mem_range_closedOrbit_iff]
  simp only [((isFixedPt_conjCircleDiffeomorph hz).iterate _).eq]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨0, h.symm⟩⟩

/-- **The critical set of the height function** is the union of the critical circles through `1`
and through `-1`. -/
theorem criticalPoints_height :
    criticalPoints (𝓘(ℝ).prod (𝓡 1)) height =
      range (criticalCircle 1 (.inl rfl)) ∪ range (criticalCircle (-1) (.inr rfl)) := by
  ext y
  obtain ⟨⟨t, z⟩, rfl⟩ := SmoothMappingTorus.uncurry_mk_surjective conjCircleDiffeomorph y
  rw [uncurry_apply_pair, ← mk, mk_mem_criticalPoints_height_iff, mem_union,
    mk_mem_range_criticalCircle_iff, mk_mem_range_criticalCircle_iff]

/-- The points `±1` are nondegenerate critical points of the height of the circle. -/
private theorem isManifoldNondegenerateCriticalPoint_sphereHeight_one {z : sphere (0 : ℂ) 1}
    (hz : z = 1 ∨ z = -1) : IsManifoldNondegenerateCriticalPoint (𝓡 1) (sphereHeight 1) z := by
  rcases hz with rfl | rfl
  · exact isManifoldNondegenerateCriticalPoint_sphereHeight_self 1
  · exact isManifoldNondegenerateCriticalPoint_sphereHeight_neg 1

/-- **The critical circles are Morse–Bott critical submanifolds** of the height function on the
Klein bottle: at each point of the critical circle through `z = ±1`, the kernel of the critical
Hessian of the height function is the tangent line of the circle. -/
theorem isNondegenerateCriticalSubmanifold_criticalCircle {z : sphere (0 : ℂ) 1}
    (hz : z = 1 ∨ z = -1) : (criticalCircle z hz).IsNondegenerateCriticalSubmanifold height where
  contMDiffAt _ := contMDiffAt_height _
  mem_criticalPoints s := by
    induction s using QuotientAddGroup.induction_on with | H t => ?_
    rw [criticalCircle_coe]
    exact mk_mem_criticalPoints_height_iff.2 hz
  ker_criticalHessian_le s := by
    induction s using QuotientAddGroup.induction_on with | H t => ?_
    intro v hv
    have hcrit : uncurry (SmoothMappingTorus.mk conjCircleDiffeomorph) (t, z) ∈
        criticalPoints (𝓘(ℝ).prod (𝓡 1)) height :=
      mk_mem_criticalPoints_height_iff.2 hz
    have hpt : criticalCircle z hz t =
        uncurry (SmoothMappingTorus.mk conjCircleDiffeomorph) (t, z) :=
      criticalCircle_coe hz t
    rw [hpt, (SmoothMappingTorus.isLocalDiffeomorph_uncurry_mk (n := ∞) conjCircleDiffeomorph
      (t, z)).ker_criticalHessian_eq_map (by simp)
      (contMDiffAt_height _) hcrit, height_comp_uncurry_mk] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    -- The vertical component of `u` lies in the kernel of the Hessian of the height of the circle
    -- at the nondegenerate critical point `z`, so it vanishes.
    have hnd := isManifoldNondegenerateCriticalPoint_sphereHeight_one hz
    have hu₂ : u.2 = 0 := by
      refine hnd.isInvertible_criticalHessian.injective (ContinuousLinearMap.ext fun w ↦ ?_)
      have h := congr($(LinearMap.mem_ker.1 hu) ((0 : ℝ), w))
      rw [ContinuousLinearMap.coe_coe, criticalHessian_comp_apply rfl hnd.contMDiffAt
        contMDiffAt_snd hnd.mem_criticalPoints u ((0 : ℝ), w), mfderiv_snd] at h
      exact h.trans
        (DFunLike.congr_fun (map_zero (criticalHessian (𝓡 1) (sphereHeight 1) z)) w).symm
    -- The critical circle is a closed orbit, whose velocity is the time vector field, the image
    -- of the `t`-direction `(1, 0)` of the cylinder.
    refine LinearMap.mem_range.2 ⟨u.1, ?_⟩
    rw [ContinuousLinearMap.coe_coe, criticalCircle, SmoothEmbedding.coe_ofIsSmoothEmbedding,
      SmoothMappingTorus.mfderiv_closedOrbit, SmoothMappingTorus.closedOrbit_coe,
      SmoothMappingTorus.timeVectorField_mk, Manifold.tangentSpaceProdEquiv_symm_apply]
    -- Two definitional equalities close the goal: `smulRight 1 v` sends `u.1` to `u.1 • v`, and
    -- a tangent vector of `ℝ × S¹` is a pair (`tangentSpaceProdEquiv` is the identity on
    -- vectors), so `u = u.1 • (1, 0)` by `Prod.ext` as `u.2 = 0`. Rewriting with
    -- `smulRight_apply` fails here: elaborating it does not find `Module ℝ` on its domain, the
    -- type synonym `TangentSpace 𝓘(ℝ) ↑t`.
    exact (map_smul _ u.1 _).symm.trans
      (DFunLike.congr_arg _ (Prod.ext (mul_one u.1) ((smul_zero u.1).trans hu₂.symm)))

/-- At a point `[t, z]` of a critical circle, the Morse index of the height function is that of
the height of the circle at `z`. -/
private theorem manifoldMorseIndex_height_mk {z : sphere (0 : ℂ) 1} (hz : z = 1 ∨ z = -1)
    (t : ℝ) : manifoldMorseIndex (𝓘(ℝ).prod (𝓡 1)) height (mk t z) =
      manifoldMorseIndex (𝓡 1) (sphereHeight 1) z := by
  have h := (SmoothMappingTorus.isLocalDiffeomorph_uncurry_mk (n := ∞) conjCircleDiffeomorph
    (t, z)).manifoldMorseIndex_comp (by simp) (f := height)
    (contMDiffAt_height _) (mk_mem_criticalPoints_height_iff.2 hz)
  rw [height_comp_uncurry_mk, manifoldMorseIndex_comp_snd] at h
  exact h.symm

/-- **The maximum circle has Morse index `1`**: at every point `[t, 1]` of the circle `θ = 0`, where
the height function `cos θ` attains its maximum, the Morse index is `1`, the rank of the negative
normal bundle. -/
theorem manifoldMorseIndex_height_mk_one (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod (𝓡 1)) height (mk t 1) = 1 := by
  rw [manifoldMorseIndex_height_mk (.inl rfl), manifoldMorseIndex_sphereHeight_self]

/-- **The minimum circle has Morse index `0`**: at every point `[t, -1]` of the circle `θ = π`,
where the height function `cos θ` attains its minimum, the Morse index is `0`. -/
theorem manifoldMorseIndex_height_mk_neg_one (t : ℝ) :
    manifoldMorseIndex (𝓘(ℝ).prod (𝓡 1)) height (mk t (-1)) = 0 := by
  rw [manifoldMorseIndex_height_mk (.inr rfl), manifoldMorseIndex_sphereHeight_neg]

end KleinBottle

end TauCeti
