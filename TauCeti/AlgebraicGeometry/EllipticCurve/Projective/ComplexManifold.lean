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
coordinates `x`, `y` or `X / Y`. Reading the tangential coordinate of these slice charts in `ℂ`
gives an atlas of `W.Point` modelled on `ℂ`, whose transition maps are analytic.

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

/-- The model `(Fin (2 - 1) → ℂ) × (Unit → ℂ)` of the slice charts of a plane curve, with its
tangential factor read in `ℂ`. -/
private noncomputable def modelEquiv :
    ((Fin (2 - Fintype.card Unit) → ℂ) × (Unit → ℂ)) ≃L[ℂ] ℂ × (Unit → ℂ) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).prodCongr (ContinuousLinearEquiv.refl ℂ _)

/-- The model identification does not change the transverse coordinate. -/
private theorem modelEquiv_toHomeomorph_apply_snd
    (v : (Fin (2 - Fintype.card Unit) → ℂ) × (Unit → ℂ)) : (modelEquiv.toHomeomorph v).2 = v.2 :=
  (rfl)

/-- The analytic slice chart of `ℂℙ²` flattening the curve near the point `L`, with tangential
coordinate in `ℂ`. -/
private noncomputable def sliceChart (L : zeroLocus W) :
    OpenPartialHomeomorph (ℙ ℂ (Fin 3 → ℂ)) (ℂ × (Unit → ℂ)) :=
  (TauCeti.complexProjectiveZeroLocusSliceChart (fun _ ↦ W.isHomogeneous_polynomial) L.2
    (exists_mem_affineOpen (L : ℙ ℂ (Fin 3 → ℂ))).choose_spec
    (W.mulVec_surjective_jacobiMatrixAt L.2)).transHomeomorph modelEquiv.toHomeomorph

private theorem isSliceChart_sliceChart (L : zeroLocus W) :
    TauCeti.IsSliceChart (sliceChart W L) ((univ : Set ℂ) ×ˢ ({0} : Set (Unit → ℂ)))
      (zeroLocus W) := by
  refine TauCeti.isSliceChart_iff.2 fun y hy ↦ ?_
  rw [sliceChart, OpenPartialHomeomorph.transHomeomorph_source] at hy
  rw [sliceChart, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
    TauCeti.isSliceChart_iff.1 (TauCeti.isSliceChart_complexProjectiveZeroLocusSliceChart _ _ _ _)
      y hy]
  simp only [mem_prod, mem_univ, true_and, mem_singleton_iff, modelEquiv_toHomeomorph_apply_snd]

private theorem mem_sliceChart_source (L : zeroLocus W) :
    (L : ℙ ℂ (Fin 3 → ℂ)) ∈ (sliceChart W L).source :=
  TauCeti.mem_complexProjectiveZeroLocusSliceChart_source _ _ _ _

private theorem contMDiffOn_sliceChart (r : ℕ∞ω) (L : zeroLocus W) :
    ContMDiffOn 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, ℂ × (Unit → ℂ)) r (sliceChart W L)
      (sliceChart W L).source := by
  rw [sliceChart, OpenPartialHomeomorph.transHomeomorph_apply,
    OpenPartialHomeomorph.transHomeomorph_source]
  exact modelEquiv.contDiff.contMDiff.comp_contMDiffOn
    (TauCeti.contMDiffOn_complexProjectiveZeroLocusSliceChart _ _ _ _ r)

private theorem contMDiffOn_sliceChart_symm (r : ℕ∞ω) (L : zeroLocus W) :
    ContMDiffOn 𝓘(ℂ, ℂ × (Unit → ℂ)) 𝓘(ℂ, Fin 2 → ℂ) r (sliceChart W L).symm
      (sliceChart W L).target := by
  rw [sliceChart, OpenPartialHomeomorph.transHomeomorph_symm_apply,
    OpenPartialHomeomorph.transHomeomorph_target]
  exact (TauCeti.contMDiffOn_complexProjectiveZeroLocusSliceChart_symm _ _ _ _ r).comp
    modelEquiv.symm.contDiff.contMDiff.contMDiffOn fun _ hv ↦ hv

/-- The atlas of the zero locus induced by its slice charts. -/
@[instance_reducible]
private noncomputable def zeroLocusChartedSpace : ChartedSpace ℂ (zeroLocus W) :=
  TauCeti.linearSliceChartedSpace (sliceChart W) (isSliceChart_sliceChart W)
    (mem_sliceChart_source W)

/-- **The complex charts of an elliptic curve.** The points of a complex elliptic curve are
charted by `ℂ`: the chart at a point reads the tangential coordinate of the analytic slice chart of
`ℂℙ²` that flattens the curve near that point. -/
@[no_expose]
noncomputable instance instChartedSpace : ChartedSpace ℂ W.Point :=
  letI := zeroLocusChartedSpace W
  (homeomorphZeroLocus W).pullbackChartedSpace

/-- **The points of a complex elliptic curve form a Riemann surface.** Their atlas is analytic,
and `C^r` for every `r`. -/
instance instIsManifold (r : ℕ∞ω) : IsManifold 𝓘(ℂ) r W.Point :=
  letI := zeroLocusChartedSpace W
  haveI : IsManifold 𝓘(ℂ) r (zeroLocus W) :=
    TauCeti.isManifold_linearSliceChartedSpace (sliceChart W) (isSliceChart_sliceChart W)
      (fun L _ hz ↦ (contMDiffOn_sliceChart W r L).contMDiffAt
        ((sliceChart W L).open_source.mem_nhds hz))
      (fun L _ hz ↦ (contMDiffOn_sliceChart_symm W r L).contMDiffAt
        ((sliceChart W L).open_target.mem_nhds hz))
      (mem_sliceChart_source W)
  (homeomorphZeroLocus W).pullback_isManifold 𝓘(ℂ) r

/-- **A complex elliptic curve is holomorphically embedded in `ℂℙ²`.** The comparison of its
points with lines in `ℂ³` is a `C^r` embedding for every `r`; in particular it is holomorphic. -/
theorem isSmoothEmbedding_toProjectivization (r : ℕ∞ω) :
    Manifold.IsSmoothEmbedding 𝓘(ℂ) 𝓘(ℂ, Fin 2 → ℂ) r
      (toProjectivization : W.Point → ℙ ℂ (Fin 3 → ℂ)) := by
  let := zeroLocusChartedSpace W
  have hval : Manifold.IsSmoothEmbedding 𝓘(ℂ) 𝓘(ℂ, Fin 2 → ℂ) r
      (Subtype.val : zeroLocus W → ℙ ℂ (Fin 3 → ℂ)) :=
    TauCeti.isSmoothEmbedding_subtypeVal_linearSliceChartedSpace (sliceChart W)
      (isSliceChart_sliceChart W)
      (fun _ ↦ ContinuousLinearEquiv.ofFinrankEq (by simp))
      (contMDiffOn_sliceChart W r) (contMDiffOn_sliceChart_symm W r) (mem_sliceChart_source W)
  have h := TauCeti.isSmoothEmbedding_comp_isLocalDiffeomorph
    ((homeomorphZeroLocus W).pullbackDiffeomorph 𝓘(ℂ) r).isLocalDiffeomorph
    (by rw [Homeomorph.coe_pullbackDiffeomorph]; exact (homeomorphZeroLocus W).isEmbedding) hval
  rw [Homeomorph.coe_pullbackDiffeomorph] at h
  convert h using 1
  funext P
  rw [Function.comp_apply, coe_homeomorphZeroLocus_apply]

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
