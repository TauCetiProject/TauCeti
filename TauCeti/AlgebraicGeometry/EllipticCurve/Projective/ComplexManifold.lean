/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.LocalParameter
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Topology
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Projectivization.ZeroLocus
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.Immersion.ModelChange
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
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
atlas back to `W.Point` and reading its model `Fin 1 → ℂ` in `ℂ`
(`Homeomorph.chartedSpaceComp`) gives an atlas of `W.Point` modelled on `ℂ`, whose transition
maps are analytic. The embedding into `ℂℙ²` is transported along the same linear change of model
(`Diffeomorph.isSmoothEmbedding_chartedSpaceComp`).

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
* `WeierstrassCurve.Projective.Point.contMDiffAt_localParameter_mk`: the local parameter `-X / Y`,
  the negative of the coordinate `X / Y` of the affine chart `Y = 1`
  (`WeierstrassCurve.Projective.Point.localParameter_eq_neg_affineChart`), is holomorphic at the
  points `[X : Y : Z]` with `Y ≠ 0`; in particular near the origin
  (`WeierstrassCurve.Projective.Point.eventually_contMDiffAt_localParameter` and
  `WeierstrassCurve.Projective.Point.contMDiffAt_localParameter_zero`).
* `WeierstrassCurve.Projective.Point.hasMFDerivAt_affineChart_apply_one_zero`: the other coordinate
  `Z / Y` of that chart vanishes to second order at the origin.
* `WeierstrassCurve.Projective.isLocalDiffeomorphAt_localParameter_zero`: the local parameter is
  a local coordinate at the origin, independently of uniformization.

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

/-- **The complex charts of an elliptic curve.** The points of a complex elliptic curve are
charted by `ℂ`: the chart at a point reads the tangential coordinate of the analytic slice chart of
`ℂℙ²` that flattens the curve near that point, in `ℂ` through `modelEquiv`. -/
@[no_expose]
noncomputable instance instChartedSpace : ChartedSpace ℂ W.Point :=
  letI := slicePointChartedSpace W
  (modelEquiv.toContDiffDiffeomorph ω).toHomeomorph.chartedSpaceComp W.Point

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
  have := isManifold_slicePointChartedSpace W ω
  exact (modelEquiv.toContDiffDiffeomorph ω).isSmoothEmbedding_chartedSpaceComp modelEquiv.symm
    (by simp only [modelWithCornersSelf_coe, range_id]
        exact image_univ_of_surjective modelEquiv.symm.surjective) le_top h

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

/-- **Local holomorphic representatives.** Every point `P₀` of a complex elliptic curve admits
a map `s : W.Point → Fin 3 → ℂ` analytic at `P₀` that gives nonsingular homogeneous
representatives of the points near `P₀`. -/
theorem exists_contMDiffAt_mk_eq (P₀ : W.Point) :
    ∃ s : W.Point → Fin 3 → ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin 3 → ℂ) ω s P₀ ∧
      ∀ᶠ P in 𝓝 P₀, ∃ h : W.Nonsingular (s P),
        Point.mk ((nonsingularLift_iff (s P)).mpr h) = P := by
  obtain ⟨i, hi⟩ := exists_mem_affineOpen P₀.toProjectivization
  have hU := (isOpen_affineOpen (K := ℂ) i).mem_nhds hi
  refine ⟨fun P ↦ Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i P.toProjectivization),
    ((contMDiffOn_insertNth_affineChart i ω).contMDiffAt hU).comp P₀
      ((isSmoothEmbedding_toProjectivization W ω).contMDiff P₀), ?_⟩
  filter_upwards [continuous_toProjectivization.continuousAt.preimage_mem_nhds hU] with P hP
  have h : Projectivization.mk ℂ _ (Fin.insertNth_one_ne_zero i _) = P.toProjectivization :=
    (affineChart_symm_apply i _).symm.trans ((affineChart i).left_inv (by rwa [affineChart_source]))
  exact ⟨(exists_toProjectivization_eq_mk_iff _ _).mp ⟨P, h.symm⟩,
    toProjectivization_injective ((toProjectivization_mk _).trans h)⟩

omit [W.IsElliptic] in
/-- The local parameter `-X / Y` is the negative of the coordinate `X / Y` of the affine chart
`Y = 1` of `ℂℙ²`; both take the junk value `0` where `Y = 0`. -/
theorem localParameter_eq_neg_affineChart :
    (localParameter : W.Point → ℂ) = fun P ↦ -(affineChart 1 P.toProjectivization 0) := by
  funext P
  obtain ⟨v, hv⟩ := Quotient.exists_rep P.point
  have hns : W.NonsingularLift ⟦v⟧ := hv.symm ▸ P.nonsingular
  have hP : Point.mk hns = P := Point.ext hv
  rw [← hP, localParameter_mk, toProjectivization_mk, affineChart_mk]
  simp only [Fin.succAbove_ne_zero_zero (one_ne_zero : (1 : Fin 3) ≠ 0)]

omit [W.IsElliptic] in
/-- The origin `[0 : 1 : 0]` lies in the affine chart `Y = 1`. -/
theorem toProjectivization_zero_mem_affineOpen :
    (0 : W.Point).toProjectivization ∈ affineOpen 1 := by
  simp [toProjectivization_zero]

/-- The affine chart `Y = 1` of `ℂℙ²`, read on the points of `W`, is holomorphic where `Y ≠ 0`. -/
private theorem contMDiffAt_affineChart_one {P : W.Point}
    (hP : P.toProjectivization ∈ affineOpen 1) (r : ℕ∞ω) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin 2 → ℂ) r (fun Q : W.Point ↦ affineChart 1 Q.toProjectivization) P :=
  ((contMDiffOn_affineChart 1 r).contMDiffAt ((isOpen_affineOpen 1).mem_nhds hP)).comp P
    ((isSmoothEmbedding_toProjectivization W r).contMDiff P)

/-- The local parameter is holomorphic where `Y ≠ 0`, as a coordinate of the affine chart
`Y = 1`. -/
private theorem contMDiffAt_localParameter {P : W.Point}
    (hP : P.toProjectivization ∈ affineOpen 1) (r : ℕ∞ω) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) r (localParameter : W.Point → ℂ) P := by
  rw [localParameter_eq_neg_affineChart]
  exact (contDiff_apply ℂ (fun _ : Fin 2 ↦ ℂ) 0).neg.contMDiff.contMDiffAt.comp P
    (contMDiffAt_affineChart_one hP r)

/-- **The local parameter is holomorphic where `Y ≠ 0`.** -/
theorem contMDiffAt_localParameter_mk {P : Fin 3 → ℂ} (hP : W.NonsingularLift ⟦P⟧)
    (hY : P 1 ≠ 0) (r : ℕ∞ω) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) r (localParameter : W.Point → ℂ) (Point.mk hP) :=
  contMDiffAt_localParameter (by rwa [toProjectivization_mk, mk_mem_affineOpen_iff]) r

omit [W.IsElliptic] in
/-- The points near the origin lie in the affine chart `Y = 1`. -/
private theorem eventually_mem_affineOpen :
    ∀ᶠ P in 𝓝 (0 : W.Point), P.toProjectivization ∈ affineOpen 1 :=
  continuous_toProjectivization.continuousAt.preimage_mem_nhds
    ((isOpen_affineOpen 1).mem_nhds toProjectivization_zero_mem_affineOpen)

/-- **The local parameter is holomorphic near the origin**, where `Y ≠ 0`. -/
theorem eventually_contMDiffAt_localParameter (r : ℕ∞ω) :
    ∀ᶠ P in 𝓝 (0 : W.Point), ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) r (localParameter : W.Point → ℂ) P :=
  eventually_mem_affineOpen.mono fun _ hP ↦ contMDiffAt_localParameter hP r

/-- **The local parameter at the origin is holomorphic there.** -/
theorem contMDiffAt_localParameter_zero (r : ℕ∞ω) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) r (localParameter : W.Point → ℂ) 0 :=
  (eventually_contMDiffAt_localParameter r).self_of_nhds

omit [W.IsElliptic] in
/-- The Weierstrass cubic, dehomogenized in the chart `Y = 1`, has differential `dZ` at the
center `[0 : 1 : 0]` of the chart: its partial derivatives in `X` and `Z` there are `0` and `1`. -/
private theorem hasFDerivAt_eval_dehomogenize_polynomial :
    HasFDerivAt (fun v : Fin 2 → ℂ ↦ eval v (TauCeti.dehomogenize 1 W.polynomial))
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) 0 := by
  convert (TauCeti.dehomogenize 1 W.polynomial).hasFDerivAt_eval 0 using 1
  ext v
  -- The point `Fin.insertNth 1 1 0` is `[0 : 1 : 0]`, and the retained coordinates are `X` and `Z`.
  have h010 : (Fin.insertNth 1 1 0 : Fin 3 → ℂ) = ![0, 1, 0] := by
    ext i
    fin_cases i <;> rfl
  have hX : eval (Fin.insertNth 1 1 0) (pderiv (Fin.succAbove 1 0) W.polynomial) = 0 := by
    rw [h010, show (Fin.succAbove 1 0 : Fin 3) = 0 from rfl, ← polynomialX, eval_polynomialX]
    simp
  have hZ : eval (Fin.insertNth 1 1 0) (pderiv (Fin.succAbove 1 1) W.polynomial) = 1 := by
    rw [h010, show (Fin.succAbove 1 1 : Fin 3) = 2 from rfl, ← polynomialZ, eval_polynomialZ]
    simp
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Fin.sum_univ_two, TauCeti.pderiv_dehomogenize,
    TauCeti.eval_dehomogenize, hX, hZ, zero_mul, one_mul, zero_add]

/-- Near the origin, the coordinates `(X / Y, Z / Y)` of the points of `W` solve the dehomogenized
cubic. -/
private theorem eval_dehomogenize_polynomial_affineChart_eventuallyEq :
    (fun P : W.Point ↦
      eval (affineChart 1 P.toProjectivization) (TauCeti.dehomogenize 1 W.polynomial)) =ᶠ[𝓝 0]
      fun _ ↦ 0 :=
  eventually_mem_affineOpen.mono fun P hP ↦
    (TauCeti.mem_complexProjectiveZeroLocus_iff_eval_affineChart
      (fun _ ↦ W.isHomogeneous_polynomial) hP).1
      (by simpa only [coe_homeomorphZeroLocus_apply] using (homeomorphZeroLocus W P).property) ()

/-- **In the affine chart `Y = 1`, the coordinate `Z / Y` vanishes to second order at the
origin**: the cubic has differential `dZ` there, and vanishes on the curve. -/
theorem hasMFDerivAt_affineChart_apply_one_zero :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun P : W.Point ↦ affineChart 1 P.toProjectivization 1) 0 0 := by
  have hf := (contMDiffAt_affineChart_one (W := W) toProjectivization_zero_mem_affineOpen
    1).mdifferentiableAt one_ne_zero
  have hf0 : affineChart 1 (0 : W.Point).toProjectivization = 0 := by
    ext i
    fin_cases i <;> simp [toProjectivization_zero]
  have hE : HasFDerivAt (fun v : Fin 2 → ℂ ↦ eval v (TauCeti.dehomogenize 1 W.polynomial))
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1)
      (affineChart 1 (0 : W.Point).toProjectivization) := by
    rw [hf0]
    exact hasFDerivAt_eval_dehomogenize_polynomial
  have hd := (hE.hasMFDerivAt.comp 0 hf.hasMFDerivAt).mfderiv
  rw [Function.comp_def, eval_dehomogenize_polynomial_affineChart_eventuallyEq.mfderiv_eq,
    mfderiv_const, ContinuousLinearMap.comp_zero] at hd
  have hc := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).hasFDerivAt
    |>.hasMFDerivAt.comp 0 hf.hasMFDerivAt
  exact hc.congr_mfderiv hd.symm

end Point

/-- In the affine chart `Y = 1`, the cubic has differential `dZ` at infinity, so the injective
differential of the embedding is detected by `dX = -dt`. -/
private theorem isInvertible_mfderiv_localParameter_zero :
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (Point.localParameter : W.Point → ℂ) 0).IsInvertible := by
  let f : W.Point → Fin 2 → ℂ := affineOpenPartialHomeomorph 1 ∘ Point.toProjectivization
  have hc : IsLocalDiffeomorphAt 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 2 → ℂ) 1
      (affineOpenPartialHomeomorph 1) (0 : W.Point).toProjectivization :=
    (affineOpenPartialHomeomorph 1).isLocalDiffeomorphAt_of_mem_maximalAtlas
    (affineOpenPartialHomeomorph_mem_maximalAtlas (I := 𝓘(ℂ, Fin 2 → ℂ)) (r := 1) 1) (by
        rw [affineOpenPartialHomeomorph_toPartialEquiv, affineChart_source]
        exact Point.toProjectivization_zero_mem_affineOpen)
  have he := (Point.isSmoothEmbedding_toProjectivization W 1).contMDiff.mdifferentiable
    one_ne_zero
  have hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, Fin 2 → ℂ) f 0 :=
    (hc.mdifferentiableAt one_ne_zero).comp 0 (he 0)
  have hinj : Function.Injective (mvfderiv 𝓘(ℂ) f 0) := by
    rw [TauCeti.injective_mvfderiv_iff, mfderiv_comp 0 (hc.mdifferentiableAt one_ne_zero) (he 0)]
    exact (hc.isInvertible_mfderiv one_ne_zero).injective.comp
      ((Point.isSmoothEmbedding_toProjectivization W 1).isImmersion.mfderiv_injective
        one_ne_zero 0)
  -- The coordinates of `f` are `X / Y = -t` and `Z / Y`, whose differential vanishes at `0`.
  have ht : (Point.localParameter : W.Point → ℂ) = fun P ↦ -(f P 0) := by
    rw [Point.localParameter_eq_neg_affineChart]
    simp only [f, Function.comp_apply, coe_affineOpenPartialHomeomorph]
  have hZ : mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun P ↦ f P 1) 0 = 0 := by
    have hf1 : (fun P : W.Point ↦ f P 1) = fun P ↦ affineChart 1 P.toProjectivization 1 := by
      funext P
      simp only [f, Function.comp_apply]
      rw [coe_affineOpenPartialHomeomorph]
    rw [hf1]
    exact (Point.hasMFDerivAt_affineChart_apply_one_zero (W := W)).mfderiv
  have hX (u : TangentSpace 𝓘(ℂ) (0 : W.Point)) :
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (Point.localParameter : W.Point → ℂ) 0 u = -(mvfderiv 𝓘(ℂ) f 0 u 0) := by
    rw [← mvfderiv_apply_eq_mfderiv_apply, ht, mvfderiv_fun_neg]
    exact congrArg Neg.neg (TauCeti.mvfderiv_apply_apply hf u 0).symm
  have hY (u : TangentSpace 𝓘(ℂ) (0 : W.Point)) : mvfderiv 𝓘(ℂ) f 0 u 1 = 0 := by
    rw [TauCeti.mvfderiv_apply_apply hf, mvfderiv_apply_eq_mfderiv_apply, hZ]
    exact zero_apply u
  apply (TauCeti.isInvertible_mfderiv_iff_injective rfl).mpr
  intro v w hvw
  apply hinj
  ext i
  fin_cases i
  · rw [hX v, hX w] at hvw
    exact neg_injective hvw
  · exact (hY v).trans (hY w).symm

/-- **The local parameter is a local coordinate at the origin**: it is a local diffeomorphism
of every class `C^n`, including `n = ω`. -/
theorem isLocalDiffeomorphAt_localParameter_zero {n : ℕ∞ω} :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) n (Point.localParameter : W.Point → ℂ) 0 := by
  obtain ⟨e, he⟩ := W.isInvertible_mfderiv_localParameter_zero
  exact (TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq (n := ω) (s := {P | ∀ᶠ Q in 𝓝 P,
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Point.localParameter : W.Point → ℂ) Q})
    (fun _ hP ↦ hP.self_of_nhds.contMDiffWithinAt) isOpen_setOfPred_eventually_nhds
    (Point.eventually_contMDiffAt_localParameter ω)
    (by exact BoundarylessManifold.isInteriorPoint) (by exact le_top) he).of_le le_top

end WeierstrassCurve.Projective
