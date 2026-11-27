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
public import TauCeti.Geometry.Manifold.Morse.Bott.RankDegreeHomology
public import TauCeti.Geometry.Manifold.Morse.Bott.Splitting
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.Immersion.NormalSpace.Basic
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Morse.Prod
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
import TauCeti.RingTheory.Ideal.Quotient.LinearEquiv
import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.VectorBundle.Orientation.ZeroSectionCompl

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
Since `C₁` has codimension `1` and Morse index `1`, its negative normal space is its whole normal
line, for every fibre metric (`TauCeti.KleinBottle.negativeNormalSpace_criticalCircle_one_eq_top`).
That line is spanned by the class of the vertical vector `∂_θ` at `[t, 1]`, and the identification
`[t + 1, z] = [t, conj z]` carries `∂_θ` at `[1, 1]` to `-∂_θ` at `[0, 1]`, because conjugation
acts by `-1` on the tangent line of the circle at `1` (`TauCeti.mfderiv_conjCircleDiffeomorph_one`).
So the orientations of the negative normal lines of `C₁` have monodromy `-1` around the circle, and
the negative normal bundle of `C₁` is not orientable
(`TauCeti.KleinBottle.isEmpty_vectorBundleOrientation_negativeNormalSpace_criticalCircle_one`). Up
to isomorphism it is the Möbius line over the circle; that identification is background here, and
what is formalized is the non-orientability that twists the coefficients of the homology across the
top level. The negative normal bundle of `C₀` has rank `0` and carries its canonical orientation
(`TauCeti.VectorBundleOrientation.positive`).

The twist is visible in the homology across the top level. Let `-1 < a < 1 < b`, so that the band
`{a ≤ h ≤ b}` contains `C₁` and no other critical point. Bott's description of a level in the
degree of its index (`nonempty_singularHomology_sublevelPair_iso_twistedHomology`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`) identifies
`H₁({h ≤ b}, {h ≤ a}; R)` with the zeroth homology `H₀(C₁; o(ν⁻) ⊗ R)` of the circle twisted by the
orientation local system of its negative normal line, and since that line is not orientable this is
`R ⧸ 2R` for every commutative ring `R`
(`nonempty_singularHomology_sublevelPair_linearEquiv_quotient_two` in the same namespace, and
`TauCeti.KleinBottle.nonempty_singularHomology_sublevelPair_height_linearEquiv_quotient_two`).
Constant coefficients would give `H₀(C₁; R) = R` instead. Whenever `2 ≠ 0` in `R`, for instance
over `ℤ`, where the top level contributes `ℤ/2` and not `ℤ`, the group is not `R`
(`KleinBottle.not_nonempty_singularHomology_sublevelPair_height_linearEquiv_self_of_two_ne_zero`),
and over a ring in which `2` is a unit, such as `ℚ`, it contributes nothing in degree one
(`TauCeti.KleinBottle.subsingleton_singularHomology_sublevelPair_height_of_isUnit_two`). Below the
index the relative homology vanishes
(`TauCeti.KleinBottle.isZero_singularHomology_zero_sublevelPair_height`).

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
* `TauCeti.KleinBottle.negativeNormalSpace_criticalCircle_one_eq_top`: along the maximum circle the
  negative normal space is the whole normal line.
* `TauCeti.KleinBottle.isEmpty_vectorBundleOrientation_negativeNormalSpace_criticalCircle_one`: the
  negative normal bundle of the maximum circle is not orientable.
* `TauCeti.KleinBottle.nonempty_singularHomology_sublevelPair_height_linearEquiv_quotient_two`:
  across the top level, `H₁({h ≤ b}, {h ≤ a}; R) ≅ R ⧸ 2R`.
* `KleinBottle.not_nonempty_singularHomology_sublevelPair_height_linearEquiv_self_of_two_ne_zero`:
  when `2 ≠ 0` in `R`, for instance over `ℤ`, this group is not `R`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2 (Morse–Bott homology and its orientation local systems).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle Metric Module Set Function Manifold
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

/-! ### The negative normal line of the maximum circle -/

section NegativeNormal

variable (hn : (∞ : ℕ∞ω) ≠ 0)

/-- The Morse index of the height function along the maximum circle is `1`. -/
private theorem manifoldMorseIndex_height_criticalCircle_one (s : AddCircle ((1 : ℕ) : ℝ)) :
    manifoldMorseIndex (𝓘(ℝ).prod (𝓡 1)) height (criticalCircle 1 (.inl rfl) s) = 1 := by
  induction s using QuotientAddGroup.induction_on with | H t => ?_
  rw [criticalCircle_coe, manifoldMorseIndex_height_mk_one]

/-- **The negative normal space along the maximum circle is its whole normal line**, for every
fibre metric `g`: the Morse index `1` along the circle is its codimension. -/
@[simp]
theorem negativeNormalSpace_criticalCircle_one_eq_top
    (g : RiemannianMetric fun s ↦ (criticalCircle 1 (.inl rfl)).isImmersion.NormalSpace s hn)
    (s : AddCircle ((1 : ℕ) : ℝ)) :
    (isNondegenerateCriticalSubmanifold_criticalCircle (.inl rfl)).negativeNormalSpace hn g s =
      ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [Manifold.IsImmersion.finrank_normalSpace_eq_one (criticalCircle 1 (.inl rfl)).isImmersion
      hn (by simp) s,
    SmoothEmbedding.IsNondegenerateCriticalSubmanifold.finrank_negativeNormalSpace _
      (isNondegenerateCriticalSubmanifold_criticalCircle (.inl rfl))]
  exact manifoldMorseIndex_height_criticalCircle_one s

/-- The vertical tangent vectors `d[t, ·]₁ w` at the points `[t, 1]` of the maximum circle depend
continuously on `t`: on the cylinder they form the constant vector field `(0, w)` along
`t ↦ (t, 1)`. -/
private theorem continuous_mfderiv_mk_one (w : TangentSpace (𝓡 1) (1 : sphere (0 : ℂ) 1)) :
    Continuous fun t : ℝ ↦ (⟨mk t 1, mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1 w⟩ :
      TangentBundle (𝓘(ℝ).prod (𝓡 1)) KleinBottle) := by
  have hc : Continuous fun t : ℝ ↦ (⟨(t, 1), (0, w)⟩ :
      TangentBundle (𝓘(ℝ).prod (𝓡 1)) (ℝ × sphere (0 : ℂ) 1)) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ)) (M := ℝ) (I' := 𝓡 1)
      (M' := sphere (0 : ℂ) 1) (n := 0)).continuous.comp
      ((Trivialization.continuous_zeroSection ℝ (E := TangentSpace 𝓘(ℝ, ℝ) (M := ℝ))).prodMk
        (continuous_const (y := (⟨1, w⟩ : TangentBundle (𝓡 1) (sphere (0 : ℂ) 1)))))
  refine ((SmoothMappingTorus.contMDiff_uncurry_mk conjCircleDiffeomorph).continuous_tangentMap
    (by simp)).comp hc |>.congr fun t ↦ ?_
  rw [Function.comp_apply, tangentMap,
    SmoothMappingTorus.mfderiv_mk_apply conjCircleDiffeomorph (by simp),
    Manifold.tangentSpaceProdEquiv_symm_apply]
  simp only [Function.uncurry_apply_pair]
  -- The two sides now differ only by the abbreviation `mk t 1` for
  -- `SmoothMappingTorus.mk conjCircleDiffeomorph t 1` and by implicit fibre-type arguments of the
  -- tangent bundle, which agree definitionally.
  rfl

/-- A nonzero vertical vector at a point of the maximum circle is not tangent to the circle, so
its normal class does not vanish. -/
private theorem normalClass_mfderiv_mk_one_ne_zero {w : TangentSpace (𝓡 1) (1 : sphere (0 : ℂ) 1)}
    (hw : w ≠ 0) (t : ℝ) :
    (criticalCircle 1 (.inl rfl)).isImmersion.normalClass (t : AddCircle ((1 : ℕ) : ℝ)) hn
      (mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1 w) ≠ 0 := by
  intro h0
  obtain ⟨u, hu⟩ :=
    ((criticalCircle 1 (.inl rfl)).isImmersion.normalClass_eq_zero_iff _ hn _).1 h0
  have hper := (isFixedPt_conjCircleDiffeomorph (.inl rfl)).isPeriodicPt 1
  have hγ : ⇑(criticalCircle 1 (.inl rfl)) = SmoothMappingTorus.closedOrbit _ hper :=
    SmoothEmbedding.coe_ofIsSmoothEmbedding _ _
  -- The tangent vector `u` of the circle has the vertical image `d[t, ·]₁ w`.
  have hu' : mfderiv 𝓘(ℝ) (𝓘(ℝ).prod (𝓡 1)) (SmoothMappingTorus.closedOrbit _ hper)
      (t : AddCircle ((1 : ℕ) : ℝ)) u = mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1 w := by
    rw [← hγ]
    exact hu
  -- The projection to the circle undoes the velocity of the circle and kills vertical vectors.
  have hvert := (SmoothMappingTorus.range_mfderiv_mk conjCircleDiffeomorph t 1) ▸
    LinearMap.mem_range_self (mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1).toLinearMap w
  -- Both tangent spaces of the circle are `ℝ`, read in the charts of the circle.
  have h₁ := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L u)
    (SmoothMappingTorus.mfderiv_proj_comp_mfderiv_closedOrbit hper (by simp) t)
  have h₂ : mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) (SmoothMappingTorus.proj conjCircleDiffeomorph)
      (SmoothMappingTorus.closedOrbit _ hper t)
      (mfderiv 𝓘(ℝ) (𝓘(ℝ).prod (𝓡 1)) (SmoothMappingTorus.closedOrbit _ hper) t u) =
        mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) (SmoothMappingTorus.proj conjCircleDiffeomorph) (mk t 1)
          (mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1 w) := by
    rw [hu']
    exact congrArg (fun L : ℝ × EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ ↦ L _)
      (mfderiv_congr_point (SmoothMappingTorus.closedOrbit_coe hper t))
  have h₃ : mfderiv (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) (SmoothMappingTorus.proj conjCircleDiffeomorph) (mk t 1)
      (mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1 w) = 0 :=
    LinearMap.mem_ker.1 hvert
  have hu0 : u = 0 := h₁.symm.trans (h₂.trans h₃)
  rw [hu0, map_zero] at hu'
  exact hw (SmoothMappingTorus.injective_mfderiv_mk conjCircleDiffeomorph (by simp) t 1
    (hu'.symm.trans (map_zero _).symm))

/-- **The seam of the maximum circle.** At `[1, 1] = [0, conj 1]` the vertical vector `d[1, ·]₁ w`
is `-d[0, ·]₁ w`, since conjugation acts by `-1` on the tangent line of the circle at `1`. -/
private theorem mfderiv_mk_one_one_eq_neg (w : TangentSpace (𝓡 1) (1 : sphere (0 : ℂ) 1)) :
    mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk 1) 1 w =
      -mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk 0) 1 w := by
  have h1 := SmoothMappingTorus.mfderiv_mk_add_one conjCircleDiffeomorph (by simp) 0 1 w
  rw [zero_add, mfderiv_conjCircleDiffeomorph_one] at h1
  exact h1.trans ((congrArg (fun L : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin 1) ↦
    L (-w)) (mfderiv_congr_point conjCircleDiffeomorph_one)).trans (map_neg _ w))

/-- The normal classes of the vertical vectors `d[t, ·]₁ w` at the points `[t, 1]` of the maximum
circle form a continuous path in its normal bundle. -/
private theorem continuous_normalClass_mfderiv_mk_one {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hdim : finrank ℝ W = finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 1)) - finrank ℝ ℝ)
    (w : TangentSpace (𝓡 1) (1 : sphere (0 : ℂ) 1)) :
    letI := (criticalCircle 1 (.inl rfl)).normalSpaceFiberBundle hn hdim
    Continuous fun t : ℝ ↦ (⟨(t : AddCircle ((1 : ℕ) : ℝ)),
      (criticalCircle 1 (.inl rfl)).isImmersion.normalClass t hn
        (mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1 w)⟩ :
      TotalSpace W fun s ↦ (criticalCircle 1 (.inl rfl)).isImmersion.NormalSpace s hn) := by
  let c := criticalCircle 1 (.inl rfl)
  let := c.normalSpaceFiberBundle hn hdim
  -- The vertical vectors form a continuous path in the pulled-back tangent bundle.
  have hq : Continuous fun t : ℝ ↦ (⟨(t : AddCircle ((1 : ℕ) : ℝ)),
      mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1 w⟩ :
        TotalSpace (ℝ × EuclideanSpace ℝ (Fin 1)) (⇑c *ᵖ (TangentSpace (𝓘(ℝ).prod (𝓡 1))))) :=
    Pullback.continuous_iff.2 ⟨AddCircle.continuous_mk' (p := ((1 : ℕ) : ℝ)),
      (continuous_mfderiv_mk_one w).congr fun t ↦ TotalSpace.ext (criticalCircle_coe _ t).symm
        HEq.rfl⟩
  refine ((c.contMDiff_normalQuotientMap hn (m := 0) (by simp) hdim).continuous.comp hq).congr
    fun t ↦ ?_
  rw [Function.comp_apply, SmoothEmbedding.normalQuotientMap_apply]

/-- **The negative normal line of the maximum circle is not orientable.** Let `g` be a fibre
metric on the normal bundle of the maximum circle `C₁ = {θ = 0}` of the height function
`[t, e^{iθ}] ↦ cos θ` on the Klein bottle, and suppose that the negative normal spaces relative to
`g` have continuous local frames of size `1`, so that they form the negative normal bundle `ν⁻`, a
real line bundle over the circle. Such frames exist for smooth `g`, since the Morse index along
`C₁` is `1` (`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`). Then `ν⁻` is not orientable.

Its fibres are the whole normal lines of `C₁` (`negativeNormalSpace_criticalCircle_one_eq_top`),
spanned by the vertical vectors `∂_θ` at the points `[t, 1]`. The identification
`[t + 1, z] = [t, conj z]` carries `∂_θ` at `[1, 1]` to `-∂_θ` at `[0, 1]`, since conjugation
reverses the tangent line of the circle at `1` (`TauCeti.mfderiv_conjCircleDiffeomorph_one`): the
orientation of `ν⁻` has monodromy `-1` around `C₁`, as for the Möbius line. -/
theorem isEmpty_vectorBundleOrientation_negativeNormalSpace_criticalCircle_one
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hdim : finrank ℝ W = finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 1)) - finrank ℝ ℝ)
    (g : RiemannianMetric fun s ↦ (criticalCircle 1 (.inl rfl)).isImmersion.NormalSpace s hn)
    (hV : letI := (criticalCircle 1 (.inl rfl)).normalSpaceFiberBundle hn hdim
      letI := (criticalCircle 1 (.inl rfl)).normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames W (Fin 1)
        ((isNondegenerateCriticalSubmanifold_criticalCircle (.inl rfl)).negativeNormalSpace hn
          g)) :
    letI := (criticalCircle 1 (.inl rfl)).normalSpaceFiberBundle hn hdim
    letI := (criticalCircle 1 (.inl rfl)).normalSpaceVectorBundle hn hdim
    letI := subbundleTopology W (F' := Fin 1 → ℝ)
      ((isNondegenerateCriticalSubmanifold_criticalCircle (.inl rfl)).negativeNormalSpace hn g)
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    IsEmpty (VectorBundleOrientation (Fin 1 → ℝ)
      (fun s ↦ (isNondegenerateCriticalSubmanifold_criticalCircle (.inl rfl)).negativeNormalSpace
        hn g s) (Fin 1)) := by
  let c := criticalCircle 1 (.inl rfl)
  let h := isNondegenerateCriticalSubmanifold_criticalCircle (.inl rfl)
  let := c.normalSpaceFiberBundle hn hdim
  let := c.normalSpaceVectorBundle hn hdim
  let := subbundleTopology W (F' := Fin 1 → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  -- The normal class of the vertical vector `d[t, ·]₁ w` at `[t, 1]`, a vector of `ν⁻`.
  let ν (w : TangentSpace (𝓡 1) (1 : sphere (0 : ℂ) 1)) (t : ℝ) :
      TotalSpace (Fin 1 → ℝ) fun s ↦ h.negativeNormalSpace hn g s :=
    ⟨t, ⟨c.isImmersion.normalClass t hn (mfderiv (𝓡 1) (𝓘(ℝ).prod (𝓡 1)) (mk t) 1 w),
      (negativeNormalSpace_criticalCircle_one_eq_top hn g t).symm ▸ Submodule.mem_top⟩⟩
  have : Nontrivial (TangentSpace (𝓡 1) (1 : sphere (0 : ℂ) 1)) :=
    inferInstanceAs (Nontrivial (EuclideanSpace ℝ (Fin 1)))
  obtain ⟨w, hw⟩ := exists_ne (0 : TangentSpace (𝓡 1) (1 : sphere (0 : ℂ) 1))
  have hν (t : ℝ) : ν w t ∈ zeroSectionCompl (Fin 1 → ℝ) _ :=
    mem_zeroSectionCompl.2 fun h0 ↦ normalClass_mfderiv_mk_one_ne_zero hn hw t
      (congrArg Subtype.val h0)
  have hcont : Continuous (ν w) :=
    (isEmbedding_totalSpace_subbundle W (Fin 1 → ℝ)
      (h.negativeNormalSpace hn g)).isInducing.continuous_iff.2
      (continuous_normalClass_mfderiv_mk_one hn hdim w)
  refine VectorBundleOrientation.isEmpty_of_continuous_of_eq_deck (by simp)
    ((zeroSectionComplOrientation (by simp)).continuous.comp (hcont.subtype_mk hν)) (x := 0)
    (y := 1) ?_
  -- At the seam `[1, z] = [0, conj z]` the normal class of `d[1, ·]₁ w` is that of `-d[0, ·]₁ w`.
  -- Normal classes over equal points of the circle with the same representative agree.
  have hmk (s s' : AddCircle ((1 : ℕ) : ℝ)) (hs : s = s') (v : ℝ × EuclideanSpace ℝ (Fin 1))
      (hv : c.isImmersion.normalClass s hn v ∈ h.negativeNormalSpace hn g s)
      (hv' : c.isImmersion.normalClass s' hn v ∈ h.negativeNormalSpace hn g s') :
      (⟨s, ⟨_, hv⟩⟩ : TotalSpace (Fin 1 → ℝ) fun s ↦ h.negativeNormalSpace hn g s) =
        ⟨s', ⟨_, hv'⟩⟩ := by
    subst hs
    rfl
  have hbase : ((1 : ℝ) : AddCircle ((1 : ℕ) : ℝ)) = ((0 : ℝ) : AddCircle ((1 : ℕ) : ℝ)) := by
    simp
  have hν₁ : ν w 1 = ⟨(0 : ℝ), -(ν w 0).snd⟩ := by
    refine (hmk _ _ hbase _ _ ?_).trans (congrArg (TotalSpace.mk _) (Subtype.ext ?_))
    · rw [negativeNormalSpace_criticalCircle_one_eq_top]
      exact Submodule.mem_top
    · exact (congrArg (c.isImmersion.normalClass _ hn) (mfderiv_mk_one_one_eq_neg w)).trans
        (map_neg _ _)
  simp only [Function.comp_apply]
  have hx := mem_zeroSectionCompl.1 (hν 0)
  have h₁ : (⟨ν w 1, hν 1⟩ : zeroSectionCompl (Fin 1 → ℝ) _) =
      ⟨⟨(0 : ℝ), -(ν w 0).snd⟩, mem_zeroSectionCompl.2 (neg_ne_zero.2 hx)⟩ :=
    Subtype.ext hν₁
  rw [h₁]
  exact zeroSectionComplOrientation_neg _ hx

end NegativeNormal

/-! ### The homology across the top level -/

section TopLevel

/-- The height function is constant along the critical circle through `z`, equal to `Re z`. -/
@[simp]
theorem height_criticalCircle {z : sphere (0 : ℂ) 1} (hz : z = 1 ∨ z = -1)
    (s : AddCircle ((1 : ℕ) : ℝ)) : height (criticalCircle z hz s) = (z : ℂ).re := by
  induction s using QuotientAddGroup.induction_on with | H t => ?_
  rw [criticalCircle_coe, height_mk]

/-- A band `[a, b]` of heights with `-1 < a` contains no critical point off the maximum circle. -/
private theorem criticalPoints_inter_preimage_Icc_subset {a b : ℝ} (ha : -1 < a) :
    criticalPoints (𝓘(ℝ).prod (𝓡 1)) height ∩ height ⁻¹' Icc a b ⊆
      range (criticalCircle 1 (.inl rfl)) := by
  rintro x ⟨hx, hab⟩
  rw [criticalPoints_height] at hx
  rcases hx with hx | ⟨s, rfl⟩
  · exact hx
  · rw [mem_preimage, height_criticalCircle] at hab
    exact absurd hab.1 (not_le.2 (by simpa using ha))

/-- **The homology across the top level of the Klein bottle is `R ⧸ 2R` in degree one.** Let
`-1 < a < 1 < b`, so that the band `{a ≤ h ≤ b}` of the height function `h = Re z` on the Klein
bottle contains the maximum circle `C₁ = {h = 1}` and no other critical point. Then, for every
commutative ring `R`, `H₁({h ≤ b}, {h ≤ a}; R) ≅ R ⧸ 2R`.

Bott's description of the level identifies this group with `H₀(C₁; o(ν⁻) ⊗ R)`, the zeroth homology
of the circle twisted by the orientation local system of the negative normal line `ν⁻` of `C₁`,
which is not orientable (`isEmpty_vectorBundleOrientation_negativeNormalSpace_criticalCircle_one`).
Constant coefficients would give `H₀(C₁; R) = R` instead. -/
theorem nonempty_singularHomology_sublevelPair_height_linearEquiv_quotient_two {a b : ℝ}
    (ha : a ∈ Ioo (-1) 1) (hb : 1 < b) (R : Type) [CommRing R] :
    Nonempty (((sublevelPair height (ha.2.trans hb).le).singularHomology (ModuleCat.of R R) 1 :
      ModuleCat R) ≃ₗ[R] R ⧸ Ideal.span {(2 : R)}) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let c := criticalCircle 1 (.inl rfl)
  have h := isNondegenerateCriticalSubmanifold_criticalCircle (.inl rfl)
  have : IsManifold 𝓘(ℝ) (∞ + 1) (AddCircle ((1 : ℕ) : ℝ)) := by
    simpa using (inferInstance : IsManifold 𝓘(ℝ) ∞ (AddCircle ((1 : ℕ) : ℝ)))
  -- Choose a smooth fibre metric `g` on the normal bundle of `C₁`; since the Morse index is `1`
  -- along `C₁`, the negative normal spaces relative to `g` form a line bundle `ν⁻`.
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 1)) -
      finrank ℝ ℝ))) = finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 1)) - finrank ℝ ℝ :=
    finrank_euclideanSpace_fin
  let := c.normalSpaceFiberBundle hn hdim
  let := c.normalSpaceVectorBundle hn hdim
  have := c.normalSpaceContMDiffVectorBundle hn (m := ∞) (by simp) hdim
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := 𝓘(ℝ)) (n := ⊤)
    (F := EuclideanSpace ℝ (Fin (finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 1)) - finrank ℝ ℝ)))
    (E := fun s ↦ c.isImmersion.NormalSpace s hn)
  let := subbundleTopology
    (EuclideanSpace ℝ (Fin (finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 1)) - finrank ℝ ℝ)))
    (F' := Fin 1 → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have hV := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ (contMDiff_height (c s)).of_le (by simp)) hdim g
    manifoldMorseIndex_height_criticalCircle_one).hasLocalSubbundleFrames
  -- Across a connected level whose negative normal bundle is not orientable, the homology in the
  -- degree of the index is `R ⧸ 2R`.
  exact h.nonempty_singularHomology_sublevelPair_linearEquiv_quotient_two hn contMDiff_height
    (fun s ↦ by simp) ha.2 hb (isClosed_Icc.preimage contMDiff_height.continuous).isCompact
    (criticalPoints_inter_preimage_Icc_subset ha.1) hdim g hV
    (isEmpty_vectorBundleOrientation_negativeNormalSpace_criticalCircle_one hn hdim
      g.toRiemannianMetric hV) R

/-- **Below the index the top level contributes nothing.** For `-1 < a < 1 < b`, the relative
homology `H₀({h ≤ b}, {h ≤ a})` of the height function on the Klein bottle vanishes, with
coefficients in any abelian category with coproducts: the maximum circle has Morse index `1`. -/
theorem isZero_singularHomology_zero_sublevelPair_height {a b : ℝ} (ha : a ∈ Ioo (-1) 1)
    (hb : 1 < b) {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    [CategoryTheory.Limits.HasCoproducts.{0} C] (R : C) :
    CategoryTheory.Limits.IsZero
      ((sublevelPair height (ha.2.trans hb).le).singularHomology R 0) :=
  SmoothEmbedding.IsNondegenerateCriticalSubmanifold.isZero_singularHomology_sublevelPair_of_lt
    (isNondegenerateCriticalSubmanifold_criticalCircle (.inl rfl)) contMDiff_height
    (fun s ↦ by simp) ha.2 hb (isClosed_Icc.preimage contMDiff_height.continuous).isCompact
    (criticalPoints_inter_preimage_Icc_subset ha.1) manifoldMorseIndex_height_criticalCircle_one R
    zero_lt_one

/-- **Unless `2 = 0`, the top level does not contribute `R`.** For `-1 < a < 1 < b` and a
commutative ring `R` in which `2 ≠ 0`, the group `H₁({h ≤ b}, {h ≤ a}; R)` of the height function on
the Klein bottle is not isomorphic to `R = H₀(C₁; R)`, the group that constant coefficients on the
maximum circle `C₁` would give. Over `ℤ` the top level contributes `ℤ/2`, not `ℤ`. -/
theorem not_nonempty_singularHomology_sublevelPair_height_linearEquiv_self_of_two_ne_zero {a b : ℝ}
    (ha : a ∈ Ioo (-1) 1) (hb : 1 < b) (R : Type) [CommRing R] (h2 : (2 : R) ≠ 0) :
    ¬Nonempty (((sublevelPair height (ha.2.trans hb).le).singularHomology (ModuleCat.of R R) 1 :
      ModuleCat R) ≃ₗ[R] R) := fun ⟨φ⟩ ↦ by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_height_linearEquiv_quotient_two ha hb R
  -- `R ⧸ 2R` is not isomorphic to `R` since `2R ≠ 0`.
  exact h2 (Ideal.span_singleton_eq_bot.1
    (Ideal.nonempty_quotient_linearEquiv_self_iff.1 ⟨e.symm ≪≫ₗ φ⟩))

/-- **With `2` invertible the top level contributes nothing in degree one.** For `-1 < a < 1 < b`
and a commutative ring `R` in which `2` is a unit, for instance `ℚ`, the group
`H₁({h ≤ b}, {h ≤ a}; R)` of the height function on the Klein bottle is trivial, although
`H₀(C₁; R) = R` for the maximum circle `C₁`. -/
theorem subsingleton_singularHomology_sublevelPair_height_of_isUnit_two {a b : ℝ}
    (ha : a ∈ Ioo (-1) 1) (hb : 1 < b) (R : Type) [CommRing R] (h2 : IsUnit (2 : R)) :
    Subsingleton ((sublevelPair height (ha.2.trans hb).le).singularHomology (ModuleCat.of R R) 1 :
      ModuleCat R) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_height_linearEquiv_quotient_two ha hb R
  have : Subsingleton (R ⧸ Ideal.span {(2 : R)}) := by
    rw [Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]
    exact h2
  exact e.toEquiv.subsingleton

end TopLevel

end KleinBottle

end TauCeti
