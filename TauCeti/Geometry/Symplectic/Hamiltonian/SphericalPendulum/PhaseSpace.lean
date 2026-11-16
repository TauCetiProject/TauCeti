/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The phase space of the spherical pendulum as a smooth manifold

The phase space of the spherical pendulum is the cotangent bundle of the unit sphere, realized
inside `ℝ³ × ℝ³` as `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}`
(`TauCeti.sphericalPendulumPhaseSpace`). It is the level over `(1, 0)` of the constraint map

`g(q, p) = (‖q‖², ⟪q, p⟫)`

(`TauCeti.sphericalPendulumConstraint`), whose differential `(a, b) ↦ (2 ⟪q, a⟫, ⟪q, b⟫ + ⟪a, p⟫)`
is onto `ℝ²` at every point of the level: the vector `((u / 2) q, w q)` is sent to `(u, w)`. So
`(1, 0)` is a regular value of `g`, and the phase space carries the atlas of a regular level
(`TauCeti.regularLevelChartedSpace`), modelled on `ℝ⁴`. With it, the phase space is a smooth
four-manifold, smoothly embedded in `ℝ³ × ℝ³`, and its tangent space at `(q, p)` is the kernel of
`dg`, the vectors `(a, b)` with `⟪q, a⟫ = 0` and `⟪q, b⟫ + ⟪a, p⟫ = 0`.

This is the smooth structure on which the rank of the energy–momentum map of the pendulum, and
hence its critical points and critical values, are defined.

## Main declarations

* `TauCeti.sphericalPendulumConstraint`: the constraint map `g`.
* `TauCeti.isRegularValue_sphericalPendulumConstraint`: `(1, 0)` is a regular value of `g`.
* The instances `ChartedSpace (Fin 4 → ℝ) sphericalPendulumPhaseSpace` and
  `IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ sphericalPendulumPhaseSpace`.
* `TauCeti.isSmoothEmbedding_coe_sphericalPendulumPhaseSpace`: the phase space is a smoothly
  embedded submanifold of `ℝ³ × ℝ³`.
* `TauCeti.range_mfderiv_coe_sphericalPendulumPhaseSpace`: its tangent space is `ker dg`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 and Proposition 5.38 (regular level sets and their tangent
  spaces).
* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
-/

public section

open Function Module Set
open scoped InnerProductSpace Manifold ContDiff

namespace TauCeti

/-- The constraint map `(q, p) ↦ (‖q‖², ⟪q, p⟫)`, whose level over `(1, 0)` is the phase space
`T*S²` of the spherical pendulum. -/
noncomputable def sphericalPendulumConstraint
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) : ℝ × ℝ :=
  (‖x.1‖ ^ 2, ⟪x.1, x.2⟫_ℝ)

@[simp]
theorem sphericalPendulumConstraint_apply (q p : EuclideanSpace ℝ (Fin 3)) :
    sphericalPendulumConstraint (q, p) = (‖q‖ ^ 2, ⟪q, p⟫_ℝ) :=
  (rfl)

/-- The phase space of the spherical pendulum is the level of the constraint map over `(1, 0)`. -/
theorem sphericalPendulumConstraint_eq_iff
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} :
    sphericalPendulumConstraint x = (1, 0) ↔ x ∈ sphericalPendulumPhaseSpace := by
  rw [sphericalPendulumConstraint, Prod.mk.injEq, mem_sphericalPendulumPhaseSpace,
    pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

/-- The constraint map is smooth. -/
theorem contDiff_sphericalPendulumConstraint {n : WithTop ℕ∞} :
    ContDiff ℝ n sphericalPendulumConstraint :=
  (contDiff_norm_sq ℝ |>.comp contDiff_fst).prodMk (contDiff_fst.inner ℝ contDiff_snd)

/-- The differential of the constraint map: `(a, b) ↦ (2 ⟪q, a⟫, ⟪q, b⟫ + ⟪a, p⟫)`. -/
theorem fderiv_sphericalPendulumConstraint_apply
    (x v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ sphericalPendulumConstraint x v =
      (2 * ⟪x.1, v.1⟫_ℝ, ⟪x.1, v.2⟫_ℝ + ⟪v.1, x.2⟫_ℝ) := by
  have h : HasFDerivAt sphericalPendulumConstraint _ x :=
    ((hasStrictFDerivAt_norm_sq x.1).hasFDerivAt.comp x hasFDerivAt_fst).prodMk
      (hasFDerivAt_fst.inner ℝ hasFDerivAt_snd)
  rw [h.fderiv]
  simp [fderivInnerCLM_apply]

/-! ### The phase space as a regular level -/

/-- `(1, 0)` is a regular value of the constraint map `(q, p) ↦ (‖q‖², ⟪q, p⟫)`: at a point of the
phase space, the tangent vector `((u / 2) q, w q)` has image `(u, w)`. -/
theorem isRegularValue_sphericalPendulumConstraint :
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ × ℝ)
      sphericalPendulumConstraint (1, 0) := by
  refine isRegularValue_iff.2 fun x hx ↦ ?_
  rw [isRegularPoint_iff_surjective_fderiv]
  obtain ⟨hq, hqp⟩ := mem_sphericalPendulumPhaseSpace.1 (sphericalPendulumConstraint_eq_iff.1 hx)
  rintro ⟨u, w⟩
  refine ⟨((u / 2) • x.1, w • x.1), ?_⟩
  rw [fderiv_sphericalPendulumConstraint_apply]
  simp only [inner_smul_right, inner_smul_left, real_inner_self_eq_norm_sq, hq, hqp,
    RCLike.conj_to_real, Prod.mk.injEq]
  constructor <;> ring

/-- The phase space of the spherical pendulum, identified with the level of the constraint map
over `(1, 0)`. It is the identity on points (`coe_sphericalPendulumPhaseSpaceHomeomorph_apply`). -/
noncomputable def sphericalPendulumPhaseSpaceHomeomorph :
    sphericalPendulumPhaseSpace ≃ₜ {x // sphericalPendulumConstraint x = (1, 0)} :=
  (Homeomorph.refl _).subtype fun _ ↦ sphericalPendulumConstraint_eq_iff.symm

@[simp]
theorem coe_sphericalPendulumPhaseSpaceHomeomorph_apply (x : sphericalPendulumPhaseSpace) :
    (sphericalPendulumPhaseSpaceHomeomorph x :
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) = x :=
  (rfl)

@[simp]
theorem coe_sphericalPendulumPhaseSpaceHomeomorph_symm_apply
    (x : {x // sphericalPendulumConstraint x = (1, 0)}) :
    (sphericalPendulumPhaseSpaceHomeomorph.symm x :
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) = x :=
  (rfl)

/-- The smoothness of the constraint map along its level, in the form the regular-level atlas
takes it. -/
private theorem contMDiffAt_sphericalPendulumConstraint {m : WithTop ℕ∞} :
    ∀ x, sphericalPendulumConstraint x = (1, 0) →
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ × ℝ) m
        sphericalPendulumConstraint x :=
  fun _ _ ↦ contDiff_sphericalPendulumConstraint.contMDiff.contMDiffAt

/-- The regular level of the constraint map has dimension `6 - 2 = 4`. -/
private theorem finrank_sub_finrank_sphericalPendulumConstraint :
    finrank ℝ (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) - finrank ℝ (ℝ × ℝ) = 4 := by
  simp

/-- The preferred atlas of the regular level of the constraint map over `(1, 0)`. -/
private noncomputable abbrev levelChartedSpace :
    ChartedSpace (Fin 4 → ℝ) {x // sphericalPendulumConstraint x = (1, 0)} :=
  regularLevelChartedSpace contMDiffAt_sphericalPendulumConstraint
    isRegularValue_sphericalPendulumConstraint finrank_sub_finrank_sphericalPendulumConstraint

private theorem isManifold_levelChartedSpace :
    letI := levelChartedSpace
    IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ {x // sphericalPendulumConstraint x = (1, 0)} :=
  isManifold_regularLevel (m := ∞) (by simp) contMDiffAt_sphericalPendulumConstraint
    isRegularValue_sphericalPendulumConstraint finrank_sub_finrank_sphericalPendulumConstraint

/-- The phase space `T*S²` of the spherical pendulum, with the atlas of the regular level
`‖q‖² = 1`, `⟪q, p⟫ = 0` of `ℝ³ × ℝ³` (`TauCeti.regularLevelChartedSpace`), transported along
`TauCeti.sphericalPendulumPhaseSpaceHomeomorph`. -/
noncomputable instance : ChartedSpace (Fin 4 → ℝ) sphericalPendulumPhaseSpace :=
  -- The body of a public instance is exposed, so it cannot mention the private
  -- `levelChartedSpace`; this is the same term, up to the proofs of its hypotheses.
  letI := regularLevelChartedSpace (n := 4)
    (fun x _ ↦ contDiff_sphericalPendulumConstraint.contMDiff.contMDiffAt)
    isRegularValue_sphericalPendulumConstraint (by simp)
  sphericalPendulumPhaseSpaceHomeomorph.pullbackChartedSpace

/-- **The phase space of the spherical pendulum is a smooth four-manifold.** -/
instance : IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ sphericalPendulumPhaseSpace :=
  letI := levelChartedSpace
  haveI := isManifold_levelChartedSpace
  sphericalPendulumPhaseSpaceHomeomorph.pullback_isManifold _ _

/-- The inclusion of the phase space is the inclusion of the regular level, after the
diffeomorphism pulled back from `TauCeti.sphericalPendulumPhaseSpaceHomeomorph`. -/
private theorem coe_eq_coe_comp_pullbackDiffeomorph :
    letI := levelChartedSpace
    (Subtype.val : sphericalPendulumPhaseSpace → _) =
      Subtype.val ∘ sphericalPendulumPhaseSpaceHomeomorph.pullbackDiffeomorph
        𝓘(ℝ, Fin 4 → ℝ) ∞ := by
  funext x
  simp

/-- **The phase space of the spherical pendulum is a smoothly embedded submanifold** of
`ℝ³ × ℝ³`. -/
theorem isSmoothEmbedding_coe_sphericalPendulumPhaseSpace :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin 4 → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ∞
      (Subtype.val : sphericalPendulumPhaseSpace → _) := by
  let := levelChartedSpace
  have := isManifold_levelChartedSpace
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  rw [coe_eq_coe_comp_pullbackDiffeomorph]
  exact (isImmersionOfComplement_comp_diffeomorph _
    (isImmersionOfComplement_coe_regularLevel (m := ∞) (by simp)
      contMDiffAt_sphericalPendulumConstraint isRegularValue_sphericalPendulumConstraint
      finrank_sub_finrank_sphericalPendulumConstraint)).isImmersion

/-- **The tangent space of the phase space** at `(q, p)` is the kernel of the differential of the
constraint map: the vectors `(a, b)` of `ℝ³ × ℝ³` with `⟪q, a⟫ = 0` and `⟪q, b⟫ + ⟪a, p⟫ = 0`. -/
theorem range_mfderiv_coe_sphericalPendulumPhaseSpace (x : sphericalPendulumPhaseSpace) :
    (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        (Subtype.val : sphericalPendulumPhaseSpace → _) x).range =
      (fderiv ℝ sphericalPendulumConstraint x).ker := by
  let := levelChartedSpace
  have := isManifold_levelChartedSpace
  let e := sphericalPendulumPhaseSpaceHomeomorph.pullbackDiffeomorph 𝓘(ℝ, Fin 4 → ℝ) ∞
  -- The inclusion of the phase space is that of the regular level after the diffeomorphism `e`,
  -- so both have the same tangent image; the latter has range the kernel of `dg`.
  have h : (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
      (Subtype.val : sphericalPendulumPhaseSpace → _) x).range =
        (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
          (Subtype.val : {x // sphericalPendulumConstraint x = (1, 0)} → _) (e x)).range := by
    rw [coe_eq_coe_comp_pullbackDiffeomorph]
    exact e.range_mfderiv_comp_diffeomorph (by simp) Subtype.val x
  have hex : ((e x : {x // sphericalPendulumConstraint x = (1, 0)}) :
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) = x := by
    simp [e]
  rw [h, range_mfderiv_coe_regularLevel, mfderiv_eq_fderiv]
  ext v
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace_apply,
    NormedSpace.fromTangentSpace_symm_apply, hex]
  -- Both sides say that `dg v = 0`; the left one is read in the tangent space of `ℝ × ℝ`.
  exact Iff.rfl

end TauCeti
