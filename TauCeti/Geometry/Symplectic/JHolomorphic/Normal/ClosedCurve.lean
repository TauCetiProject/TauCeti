/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Model
public import TauCeti.Geometry.Symplectic.Manifold.CurvePairing
import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Closed curves in the normal model are constant

Let `C` be an embedded pseudoholomorphic curve in an almost complex four-manifold, with real
normal Cauchy–Riemann operator `D_C s = ∂bar s + ν s + μ conj s` over a holomorphic chart of `C`
and in a unitary frame of the normal line. The almost complex structure `J_N` of the normal model
on `ℂ × ℂ` (`TauCeti.normalModelStructure`) is

`J_N(z, w)(ξ, η) = (I ξ, I η + 2 I c conj ξ)`,  `c = ν(z) w + μ(z) conj w`.

For smooth coefficients this file packages `J_N` as a smooth almost complex structure on the
model manifold `ℂ × ℂ` (`TauCeti.smoothNormalModelStructure`). It is the block structure
(`TauCeti.ComplexStructureFamily.blockAlmostComplexStructure`) over the base `ℂ` with connection
block `ξ ↦ 2 I c conj ξ` and fibre block multiplication by `I`. So the projection to the base is
pseudoholomorphic (`TauCeti.isPseudoholomorphic_fst_smoothNormalModelStructure`), and every
fibre `{z₀} × ℂ` carries the standard structure
(`TauCeti.fiberAlmostComplexStructure_smoothNormalModelStructure`).

Both are tamed by the standard area form of `ℂ`, so a closed connected `J_N`-holomorphic curve is
constant (`TauCeti.apply_eq_of_isPseudoholomorphicAt_smoothNormalModelStructure`): its base
component is a closed holomorphic curve in `ℂ`, hence constant, so the curve lies in one normal
fibre, where it is a closed holomorphic curve in `ℂ` again. So the normal model `ℂ × ℂ` contains
no closed nonconstant `J_N`-curve.

This is motivated by Taubes's reconstruction of curves from limits of Seiberg–Witten solutions:
the limiting curve lives in the total space of the normal bundle `N_C` with the structure `J_N`,
and its components are either projected with positive degree to `C` or vertical, contained in one
normal fibre. A vertical component lies over one point of `C`, hence in a single trivialized chart
`ℂ × ℂ` of `N_C`. Concluding that `N_C` has no compact nonconstant vertical component needs the
normal bundle `N_C` carrying `J_N` as an almost complex manifold, which is not formalized here.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Complex ComplexConjugate
open scoped ContDiff Manifold

namespace TauCeti

variable {ν μ : ℂ → ℂ}

/-! ### `J_N` as a smooth almost complex structure -/

/-- The connection block `ξ ↦ 2 I c conj ξ` of `J_N` at `p = (z, w)`, where
`c = ν z w + μ z conj w`. -/
private def normalModelConnectionBlock (ν μ : ℂ → ℂ) (p : ℂ × ℂ) : ℂ →L[ℝ] ℂ :=
  (2 * I * (ν p.1 * p.2 + μ p.1 * conj p.2)) • Complex.conjCLE.toContinuousLinearMap

private theorem normalModelConnectionBlock_apply (p : ℂ × ℂ) (ξ : ℂ) :
    normalModelConnectionBlock ν μ p ξ = 2 * I * (ν p.1 * p.2 + μ p.1 * conj p.2) * conj ξ := by
  simp [normalModelConnectionBlock]

private theorem contDiff_normalModelConnectionBlock (hν : ContDiff ℝ ∞ ν)
    (hμ : ContDiff ℝ ∞ μ) : ContDiff ℝ ∞ (normalModelConnectionBlock ν μ) := by
  have hc : ContDiff ℝ ∞ (fun q : ℂ × ℂ ↦ ν q.1 * q.2 + μ q.1 * conj q.2) :=
    ((hν.comp contDiff_fst).mul contDiff_snd).add
      ((hμ.comp contDiff_fst).mul
        (Complex.conjCLE.toContinuousLinearMap.contDiff.comp contDiff_snd))
  exact (contDiff_const.mul hc).smul contDiff_const

/-- **`J_N` as a smooth almost complex structure.** For smooth coefficients `ν` and `μ`, the
almost complex structure `J_N(z, w)(ξ, η) = (I ξ, I η + 2 I c conj ξ)`, `c = ν z w + μ z conj w`,
of the normal model (`TauCeti.normalModelStructure`) as a smooth almost complex structure on the
model manifold `ℂ × ℂ`. It is the block structure over the base `ℂ` with connection block
`ξ ↦ 2 I c conj ξ` and fibre block multiplication by `I`. -/
def smoothNormalModelStructure (hν : ContDiff ℝ ∞ ν) (hμ : ContDiff ℝ ∞ μ) :
    SmoothAlmostComplexStructure 𝓘(ℝ, ℂ × ℂ) (ℂ × ℂ) :=
  ComplexStructureFamily.blockAlmostComplexStructure
    (LinearMap.toContinuousLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap)
    (normalModelConnectionBlock ν μ)
    (fun _ ↦ LinearMap.toContinuousLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap)
    (contDiff_normalModelConnectionBlock hν hμ) contDiff_const
    (AlmostComplexStructure.ofComplexModule ℂ).apply_apply
    (fun _ ↦ (AlmostComplexStructure.ofComplexModule ℂ).apply_apply) fun p a ↦ by
      simp only [normalModelConnectionBlock_apply, LinearMap.coe_toContinuousLinearMap',
        AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul, map_mul, conj_I]
      ring

variable (hν : ContDiff ℝ ∞ ν) (hμ : ContDiff ℝ ∞ μ)

/-- The smooth structure acts on tangent vectors as the normal model structure `J_N`. -/
theorem smoothNormalModelStructure_apply (p ξ : ℂ × ℂ) :
    smoothNormalModelStructure hν hμ p ξ = normalModelStructure ν μ p ξ := by
  refine (ComplexStructureFamily.blockAlmostComplexStructure_apply _ _ _ _ _ _ _ _ p ξ).trans ?_
  rw [normalModelStructure_apply]
  refine Prod.ext (by simp [AlmostComplexStructure.ofComplexModule_apply]) ?_
  simp only [normalModelConnectionBlock_apply, LinearMap.coe_toContinuousLinearMap',
    AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul]
  ring

/-- The tangent endomorphism of the smooth structure at `p` is the normal model structure `J_N`
at `p`. -/
@[simp]
theorem smoothNormalModelStructure_toEndomorphism (p : ℂ × ℂ) :
    (smoothNormalModelStructure hν hμ).toEndomorphism p =
      LinearMap.toContinuousLinearMap (normalModelStructure ν μ p).toLinearMap :=
  ContinuousLinearMap.ext fun ξ ↦ smoothNormalModelStructure_apply hν hμ p ξ

/-- At every point the smooth structure is the normal model structure `J_N`. This identifies
pseudoholomorphic maps between the model spaces with the `J_N`-holomorphic maps of
`TauCeti.normalModelStructure` (`TauCeti.isPseudoholomorphicAt_iff_isJHolomorphicAt`). -/
@[simp]
theorem almostComplexStructureAt_smoothNormalModelStructure (p : ℂ × ℂ) :
    (smoothNormalModelStructure hν hμ).almostComplexStructureAt p = normalModelStructure ν μ p :=
  AlmostComplexStructure.ext fun ξ ↦ by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    exact smoothNormalModelStructure_apply hν hμ p ξ

/-- **The projection to the base is pseudoholomorphic** for `J_N`, with the standard structure on
the base `ℂ`. -/
theorem isPseudoholomorphic_fst_smoothNormalModelStructure :
    IsPseudoholomorphic (smoothNormalModelStructure hν hμ)
      (SmoothAlmostComplexStructure.const
        (LinearMap.toContinuousLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap)
        (AlmostComplexStructure.ofComplexModule ℂ).apply_apply) Prod.fst :=
  ComplexStructureFamily.isPseudoholomorphic_fst_blockAlmostComplexStructure _ _ _ _ _ _ _ _

/-- **The normal fibres carry the standard structure**: the fibre structure of `J_N` over every
point of the base is multiplication by `I`. -/
@[simp]
theorem fiberAlmostComplexStructure_smoothNormalModelStructure (z₀ : ℂ) :
    ComplexStructureFamily.fiberAlmostComplexStructure (smoothNormalModelStructure hν hμ)
        (isPseudoholomorphic_fst_smoothNormalModelStructure hν hμ) z₀ =
      (AlmostComplexStructure.ofComplexModule ℂ).constSmooth := by
  ext w v
  -- `v` is a tangent vector of the model manifold `ℂ` at `w`, whose type
  -- `TangentSpace 𝓘(ℝ, ℂ) w` is `ℂ` by definition; retype it as a complex number so that it can be
  -- paired with `0 : ℂ` into a tangent vector `(0, v)` of `ℂ × ℂ`
  let v' : ℂ := v
  refine (ComplexStructureFamily.fiberAlmostComplexStructure_apply _ _ z₀ w v').trans ?_
  refine (congrArg Prod.snd (smoothNormalModelStructure_apply hν hμ (z₀, w) (0, v'))).trans ?_
  refine Eq.trans ?_ (AlmostComplexStructure.constSmooth_apply _ w v').symm
  simp

/-! ### Closed curves -/

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*}
  [TopologicalSpace C] [ChartedSpace H' C] [IsManifold I' ∞ C] [BoundarylessManifold I' C]
  [T2Space C] [CompactSpace C] [PreconnectedSpace C]
  {j : SmoothAlmostComplexStructure I' C} {o : Manifold.Orientation I' C (Fin 2)}

/-- **Closed curves in the normal model are constant.** For smooth coefficients `ν` and `μ`,
every smooth `J_N`-holomorphic map from a closed connected surface, oriented so that the frames
`(e, j e)` are positive, to the total space `ℂ × ℂ` of the normal model is constant. Its base
component is a closed holomorphic curve in `ℂ`, hence constant, and a closed curve in one normal
fibre is a closed holomorphic curve in `ℂ` again. In particular the normal model contains no
compact nonconstant vertical curve. -/
theorem apply_eq_of_isPseudoholomorphicAt_smoothNormalModelStructure {u : C → ℂ × ℂ}
    (hu : ContMDiff I' 𝓘(ℝ, ℂ × ℂ) ∞ u)
    (ho : ∀ c (e : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), e 1 = j c (e 0) →
      e.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j (smoothNormalModelStructure hν hμ) u c) (c c' : C) :
    u c = u c' := by
  -- the standard area form of `ℂ` tames multiplication by `I`, on the base and on every fibre
  refine ComplexStructureFamily.apply_eq_of_isPseudoholomorphic_fst
    (isPseudoholomorphic_fst_smoothNormalModelStructure hν hμ)
    (β := stdComplexSymplecticForm.toBilinForm.toContinuousBilinearMap)
    stdComplexSymplecticForm.isAlt stdComplexSymplecticForm_tames
    (θ := fun _ ↦ stdComplexSymplecticForm.constSmooth) (fun z₀ w v hv ↦ ?_)
    (fun _ ↦ (mem_closedForms _ _).mpr ((SmoothForm.isClosed_def _).mp
      (SymplecticForm.isClosed_constSmooth _))) hu ho hhol c c'
  rw [fiberAlmostComplexStructure_smoothNormalModelStructure]
  exact SmoothTwoForm.tames_iff.1
    (SymplecticForm.tames_constSmooth_iff.2 stdComplexSymplecticForm_tames) w v hv

end TauCeti
