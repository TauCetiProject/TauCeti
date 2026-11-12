/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Topology
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Projectivization.ZeroLocus
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.Immersion.ModelChange
import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph

/-!
# Complex elliptic curves are Riemann surfaces

Let `W` be an elliptic curve over `ℂ`. Its native projective points `W.Point`, with the analytic
topology induced from the complex projective plane, are homeomorphic to the zero locus of the
homogeneous Weierstrass cubic `W(X, Y, Z)` in `ℂℙ²`
(`WeierstrassCurve.Projective.Point.homeomorphZeroLocus`). Every point of that zero locus is
nonsingular, so some partial derivative of the cubic is nonzero there: the cone Jacobian of the
cubic is surjective at every point of the curve
(`WeierstrassCurve.Projective.mulVec_surjective_jacobiMatrixAt`). By the holomorphic implicit
function theorem, the curve is therefore flattened near each point by an analytic slice chart of
`ℂℙ²` (`TauCeti.complexProjectiveZeroLocusSliceChart`), taken in a standard affine chart `Xᵢ ≠ 0`
containing the point. Its tangential coordinate is an abstract linear coordinate on the kernel of
the derivative of the affine equation; it is not identified here with the classical local
coordinates `x`, `y` or `X / Y`. These slice charts make the zero locus a complex submanifold of
`ℂℙ²` modelled on `Fin 1 → ℂ` (`TauCeti.complexProjectiveZeroLocusChartedSpace`). Pulling that
atlas back to `W.Point` and reading its model `Fin 1 → ℂ` in `ℂ` (`ChartedSpace.comp`) gives an
atlas of `W.Point` modelled on `ℂ`, whose transition maps are analytic. The embedding into `ℂℙ²`
is transported along the same linear change of model
(`TauCeti.isImmersionAt_comp_diffeomorph_of_image_range_eq`).

This makes the points of a complex elliptic curve, already compact and connected in their analytic
topology, a one-dimensional complex manifold
(`WeierstrassCurve.Projective.Point.instChartedSpace` and
`WeierstrassCurve.Projective.Point.instIsManifold`), embedded holomorphically in `ℂℙ²`
(`WeierstrassCurve.Projective.Point.isSmoothEmbedding_toProjectivization`). Consequently a map to
`W.Point` is holomorphic exactly when its composite with the embedding is, which can be checked on
local holomorphic homogeneous coordinates
(`WeierstrassCurve.Projective.Point.contMDiff_iff_contMDiff_toProjectivization_comp`). This is the
complex-manifold structure on which the complex Lie group structure of `E(ℂ)` and the complex
uniformization `ℂ / Λ ≃ E(ℂ)` are built.

## Main results

* `WeierstrassCurve.Projective.mulVec_surjective_jacobiMatrixAt`: the projective cubic of a
  complex elliptic curve is a smooth zero locus.
* `WeierstrassCurve.Projective.Point.instChartedSpace`: the atlas of `W.Point` modelled on `ℂ`.
* `WeierstrassCurve.Projective.Point.instIsManifold`: `W.Point` is an analytic manifold.
* `WeierstrassCurve.Projective.Point.isSmoothEmbedding_toProjectivization`: the comparison with
  projective space is a holomorphic embedding.
* `WeierstrassCurve.Projective.Point.contMDiff_iff_contMDiff_toProjectivization_comp` and
  `WeierstrassCurve.Projective.Point.contMDiffAt_iff_contMDiffAt_toProjectivization_comp`: maps to
  `W.Point` are holomorphic exactly when their composites with the embedding are.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §VI.1.
* R. Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter I, §2 and §3 (charts of smooth affine and projective
  plane curves given by the implicit function theorem).
-/

public section

open MvPolynomial Projectivization Set Topology
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace WeierstrassCurve.Projective

variable (W : Projective ℂ) [W.IsElliptic]

/-- **The projective cubic of a complex elliptic curve is smooth.** At every point of the zero
locus of the Weierstrass cubic in `ℂℙ²`, some partial derivative of the cubic is nonzero, so its
cone Jacobian is surjective. -/
theorem mulVec_surjective_jacobiMatrixAt {L : ℙ ℂ (Fin 3 → ℂ)}
    (hL : L ∈ TauCeti.complexProjectiveZeroLocus fun _ : Unit ↦ W.polynomial) :
    (TauCeti.jacobiMatrixAt (fun _ : Unit ↦ W.polynomial) L.rep).mulVec.Surjective := by
  rw [TauCeti.mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero]
  rw [← mk_rep L, TauCeti.complexProjectiveZeroLocus_mk_iff
    (fun _ ↦ W.isHomogeneous_polynomial)] at hL
  obtain ⟨-, h | h | h⟩ :=
    (equation_iff_nonsingular_of_ne_zero (W := W) L.rep_ne_zero).1 (hL ())
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

namespace Point

/-- The zero locus of the Weierstrass cubic in `ℂℙ²`, the image of the points of `W`. -/
private noncomputable abbrev zeroLocus : Set (ℙ ℂ (Fin 3 → ℂ)) :=
  TauCeti.complexProjectiveZeroLocus fun _ : Unit ↦ W.polynomial

/-- The tangential model `Fin (2 - 1) → ℂ` of the slice-chart atlas of a plane curve, read in
`ℂ`. -/
private noncomputable def modelEquiv : (Fin (2 - Fintype.card Unit) → ℂ) ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ

/-- The atlas of the zero locus induced by its slice charts, modelled on `Fin (2 - 1) → ℂ`. -/
@[instance_reducible]
private noncomputable def zeroLocusChartedSpace :
    ChartedSpace (Fin (2 - Fintype.card Unit) → ℂ) (zeroLocus W) :=
  TauCeti.complexProjectiveZeroLocusChartedSpace (fun _ ↦ W.isHomogeneous_polynomial) isOpen_univ
    (inter_univ _).symm fun _ hL ↦ W.mulVec_surjective_jacobiMatrixAt hL

/-- The atlas of the zero locus, pulled back to the points of `W`. -/
@[instance_reducible]
private noncomputable def slicePointChartedSpace :
    ChartedSpace (Fin (2 - Fintype.card Unit) → ℂ) W.Point :=
  letI := zeroLocusChartedSpace W
  (homeomorphZeroLocus W).pullbackChartedSpace

/-- The tangential model `Fin (2 - 1) → ℂ`, charted by `ℂ` through `modelEquiv`. -/
@[instance_reducible]
private noncomputable def modelChartedSpace : ChartedSpace ℂ (Fin (2 - Fintype.card Unit) → ℂ) :=
  (modelEquiv.toContDiffDiffeomorph ω).toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace
    (Homeomorph.toOpenPartialHomeomorph_source _)

/-- **The complex charts of an elliptic curve.** The points of a complex elliptic curve are
charted by `ℂ`: the chart at a point reads the tangential coordinate of the analytic slice chart of
`ℂℙ²` that flattens the curve near that point. -/
@[no_expose]
noncomputable instance instChartedSpace : ChartedSpace ℂ W.Point :=
  letI := slicePointChartedSpace W
  letI := modelChartedSpace
  ChartedSpace.comp ℂ (Fin (2 - Fintype.card Unit) → ℂ) W.Point

/-- The points of `W` form a `C^r` manifold for the atlas pulled back from the zero locus. -/
private theorem isManifold_slicePointChartedSpace (r : ℕ∞ω) :
    letI := slicePointChartedSpace W
    IsManifold 𝓘(ℂ, Fin (2 - Fintype.card Unit) → ℂ) r W.Point :=
  letI := zeroLocusChartedSpace W
  haveI := TauCeti.isManifold_complexProjectiveZeroLocus (fun _ ↦ W.isHomogeneous_polynomial)
    isOpen_univ (inter_univ _).symm (fun _ hL ↦ W.mulVec_surjective_jacobiMatrixAt hL) r
  (homeomorphZeroLocus W).pullback_isManifold _ r

/-- **The points of a complex elliptic curve form a Riemann surface.** Their atlas is analytic,
and `C^r` for every `r`. -/
instance instIsManifold (r : ℕ∞ω) : IsManifold 𝓘(ℂ) r W.Point :=
  letI := slicePointChartedSpace W
  haveI := isManifold_slicePointChartedSpace W ω
  haveI : IsManifold 𝓘(ℂ) ω W.Point :=
    (modelEquiv.toContDiffDiffeomorph ω).isManifold_chartedSpaceComp W.Point
  IsManifold.of_le le_top

/-- The charts of `W.Point` are those of the zero locus atlas, read in `ℂ` through
`modelEquiv`. -/
private theorem extChartAt_eq (P : W.Point) :
    letI := slicePointChartedSpace W
    (extChartAt 𝓘(ℂ) P : W.Point → ℂ) =
      modelEquiv ∘ extChartAt 𝓘(ℂ, Fin (2 - Fintype.card Unit) → ℂ) P := by
  let := slicePointChartedSpace W
  let := modelChartedSpace
  funext Q
  -- A chart of `instChartedSpace` is a zero locus chart followed by the single chart
  -- `modelEquiv` of `modelChartedSpace`.
  rw [extChartAt_coe, extChartAt_coe, instChartedSpace, chartAt_comp, modelChartedSpace,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]
  simp only [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
    Diffeomorph.coe_toHomeomorph, ContinuousLinearEquiv.coe_toContDiffDiffeomorph,
    modelWithCornersSelf_coe, Function.comp_apply, id_eq]

/-- The identity of `W.Point`, from the atlas modelled on `ℂ` to the zero locus atlas modelled on
`Fin (2 - 1) → ℂ`. -/
private noncomputable def modelChangeDiffeomorph (r : ℕ∞ω) :
    letI := slicePointChartedSpace W
    W.Point ≃ₘ^r⟮𝓘(ℂ), 𝓘(ℂ, Fin (2 - Fintype.card Unit) → ℂ)⟯ W.Point :=
  letI := slicePointChartedSpace W
  { toEquiv := Equiv.refl _
    contMDiff_toFun := fun P ↦ by
      refine contMDiffAt_iff_target.2 ⟨continuousAt_id, ?_⟩
      have h : (extChartAt 𝓘(ℂ, Fin (2 - Fintype.card Unit) → ℂ) P : W.Point → _) ∘ id =
          modelEquiv.symm ∘ extChartAt 𝓘(ℂ) P := by
        rw [extChartAt_eq]
        funext Q
        exact (modelEquiv.symm_apply_apply _).symm
      exact h ▸ modelEquiv.symm.contDiff.contMDiff.contMDiffAt.comp P contMDiffAt_extChartAt
    contMDiff_invFun := fun P ↦ by
      have := isManifold_slicePointChartedSpace W r
      refine contMDiffAt_iff_target.2 ⟨continuousAt_id, ?_⟩
      exact (extChartAt_eq W P).symm ▸
        modelEquiv.contDiff.contMDiff.contMDiffAt.comp P contMDiffAt_extChartAt }

/-- **A complex elliptic curve is holomorphically embedded in `ℂℙ²`.** The comparison of its
points with lines in `ℂ³` is a `C^r` embedding for every `r`; in particular it is holomorphic. -/
theorem isSmoothEmbedding_toProjectivization (r : ℕ∞ω) :
    Manifold.IsSmoothEmbedding 𝓘(ℂ) 𝓘(ℂ, Fin 2 → ℂ) r
      (toProjectivization : W.Point → ℙ ℂ (Fin 3 → ℂ)) := by
  let := zeroLocusChartedSpace W
  let := slicePointChartedSpace W
  have := TauCeti.isManifold_complexProjectiveZeroLocus (fun _ ↦ W.isHomogeneous_polynomial)
    isOpen_univ (inter_univ _).symm (fun _ hL ↦ W.mulVec_surjective_jacobiMatrixAt hL) r
  have := isManifold_slicePointChartedSpace W r
  have h := TauCeti.isSmoothEmbedding_comp_isLocalDiffeomorph
    ((homeomorphZeroLocus W).pullbackDiffeomorph 𝓘(ℂ, Fin (2 - Fintype.card Unit) → ℂ)
      r).isLocalDiffeomorph
    (by rw [Homeomorph.coe_pullbackDiffeomorph]; exact (homeomorphZeroLocus W).isEmbedding)
    (TauCeti.isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus
      (fun _ ↦ W.isHomogeneous_polynomial) isOpen_univ (inter_univ _).symm
      (fun _ hL ↦ W.mulVec_surjective_jacobiMatrixAt hL) r)
  rw [Homeomorph.coe_pullbackDiffeomorph] at h
  have hP : (Subtype.val ∘ homeomorphZeroLocus W : W.Point → ℙ ℂ (Fin 3 → ℂ)) =
      toProjectivization := by
    funext P
    rw [Function.comp_apply, coe_homeomorphZeroLocus_apply]
  rw [hP] at h
  refine ⟨TauCeti.isImmersion_iff_forall_isImmersionAt.2 fun P ↦ ?_, isEmbedding_toProjectivization⟩
  exact TauCeti.isImmersionAt_comp_diffeomorph_of_image_range_eq modelEquiv.symm
    (by simp only [modelWithCornersSelf_coe, range_id]
        exact image_univ_of_surjective modelEquiv.symm.surjective)
    (modelChangeDiffeomorph W r) le_rfl (h.isImmersion.isImmersionAt P)

variable {W} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} [TopologicalSpace M] [ChartedSpace H M] {r : ℕ∞ω}
  {f : M → W.Point}

/-- **Holomorphic maps to a complex elliptic curve.** A map to the points of a complex elliptic
curve is `C^r` at `x` exactly when its composite with the embedding into `ℂℙ²` is. -/
theorem contMDiffAt_iff_contMDiffAt_toProjectivization_comp {x : M} :
    ContMDiffAt I 𝓘(ℂ) r f x ↔ ContMDiffAt I 𝓘(ℂ, Fin 2 → ℂ) r (toProjectivization ∘ f) x := by
  rw [ContMDiffAt.iff_comp_isImmersionAt
    ((isSmoothEmbedding_toProjectivization W r).isImmersion.isImmersionAt (f x)),
    and_iff_right_of_imp fun h ↦ ?_]
  exact (isEmbedding_toProjectivization.isInducing.continuousAt_iff).2 h.continuousAt

/-- **Holomorphic maps to a complex elliptic curve.** A map to the points of a complex elliptic
curve is `C^r` exactly when its composite with the embedding into `ℂℙ²` is. -/
theorem contMDiff_iff_contMDiff_toProjectivization_comp :
    ContMDiff I 𝓘(ℂ) r f ↔ ContMDiff I 𝓘(ℂ, Fin 2 → ℂ) r (toProjectivization ∘ f) :=
  forall_congr' fun _ ↦ contMDiffAt_iff_contMDiffAt_toProjectivization_comp

/-- A map to the points of a complex elliptic curve given near `x` by `C^r` nonsingular
homogeneous coordinates is `C^r` at `x`; for `r = ω` it is holomorphic there. -/
theorem contMDiffAt_of_eventually_eq_mk {x : M} {P : M → Fin 3 → ℂ}
    (hP : ContMDiffAt I 𝓘(ℂ, Fin 3 → ℂ) r P x)
    (hf : ∀ᶠ y in 𝓝 x, ∃ h : W.Nonsingular (P y),
      Point.mk ((nonsingularLift_iff (P y)).mpr h) = f y) :
    ContMDiffAt I 𝓘(ℂ) r f x := by
  rw [contMDiffAt_iff_contMDiffAt_toProjectivization_comp]
  refine Projectivization.contMDiffAt_of_eventually_eq_mk hP ?_
  filter_upwards [hf] with y ⟨h, hy⟩
  exact ⟨ne_zero_of_nonsingular h, by rw [Function.comp_apply, ← hy, toProjectivization_mk]⟩

end Point

end WeierstrassCurve.Projective
