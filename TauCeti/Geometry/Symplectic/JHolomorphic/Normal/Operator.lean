/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Linearization
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.NormalBundle
import Mathlib.Geometry.Manifold.Notation
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.ComplexStructure

/-!
# The normal Cauchy–Riemann operator of an embedded pseudoholomorphic curve

Let `f : M → X` be an embedding of a manifold with an almost complex structure `j`, for instance a
Riemann surface, into a manifold with an almost complex structure `J`, and suppose that `f` is
pseudoholomorphic, `df ∘ j = J ∘ df`. Its normal bundle `N_x = T_{f x} X ⧸ range (df_x)` carries
the complex structure `J_N [w] = [J w]`, which makes it a complex vector bundle
(`TauCeti.SmoothEmbedding.normalComplexStructure`). For an embedded pseudoholomorphic curve `C`
in an almost complex four-manifold this is the complex normal line `N_C`. This file constructs the
normal Cauchy–Riemann operator `D_N` of `f` on the sections of this complex bundle
(`TauCeti.SmoothEmbedding.normalCauchyRiemannOperator`) and proves that it is a real
Cauchy–Riemann operator in the sense of McDuff–Salamon, Definition C.1.5
(`TauCeti.SmoothEmbedding.isRealCauchyRiemannOperator_normalCauchyRiemannOperator`): its values
are `(0,1)`-forms, it is additive, and it satisfies the Leibniz rule
`D_N (g • ν) = g • D_N ν + (∂bar g) ⊗ ν` for real functions `g`. The target `J` need not be
integrable.

**The construction.** The operator is the linearization of the Cauchy–Riemann equation of `f`,
projected to the normal bundle. Fix a Riemannian metric on `X`. At a point `x`, a normal section `ν`
is lifted to the ambient tangent vectors orthogonal to the curve
(`TauCeti.SmoothEmbedding.normalRepresentative`), and the lift is read in the charts at `x` and at
`f x` (`TauCeti.SmoothEmbedding.normalChartLift`). With `u` the map `f` and `J'` the structure `J`
read in these charts, the linearization of the Cauchy–Riemann defect `du ∘ j - J'(u) ∘ du` in the
direction `ξ` of this lift is (`TauCeti.cauchyRiemannLinearization`)

`L ξ = dξ ∘ j_x - J'(u) ∘ dξ - (dJ'(u) ξ) ∘ du`,

with the source structure frozen at its value `j_x` at the chart centre
(`TauCeti.SmoothEmbedding.normalChartLinearization`). This uses the unnormalized defect, whose
linearization satisfies `L (j v) = -J (L v)` at the chart centre
(`TauCeti.SmoothEmbedding.isComplexAntilinear_normalChartLinearization`) and the Leibniz rule
`L (g ξ) = g L ξ + dg (j v) ξ - dg v J ξ`
(`TauCeti.SmoothEmbedding.normalChartLinearization_smul_apply`). The normal operator is the
normal class of `L`, normalized by `J_N / 2`:

`D_N ν x = (1 / 2) J_N [L ξ]`

(`TauCeti.SmoothEmbedding.fiberEquiv_normalCauchyRiemannOperator_apply`). With this
normalization the Leibniz remainder `(1 / 2) J_N (dg (j v) [ξ] - dg v J_N [ξ])` is exactly
`(∂bar g) ⊗ ν = (1 / 2) (dg v ν + dg (j v) i ν)`, as McDuff–Salamon's axioms ask.

**Differentiability.** A section of the complex normal bundle that is differentiable at `x` in its
complex charts is differentiable as a section of the real normal bundle
(`TauCeti.Bundle.ContinuousComplexStructure.mdifferentiableAt_totalSpace_fiberEquiv`), because
`J_N` is smooth; its orthogonal lift is then differentiable, so its chart lift is differentiable at
the chart centre (`TauCeti.SmoothEmbedding.differentiableAt_normalChartLift`). This is where the
embedding is assumed `C²` and the metric `C¹`.

**The choice of lift.** The lift fixes the ambient metric. Two lifts of the same normal section
differ by a tangent vector field `du · a`, and the normal class of `L (du · a)` vanishes at a
pseudoholomorphic map, so the operator does not depend on the metric; this independence is not
proved here. For a source structure that is constant in the chart, the vanishing of the normal
class of `L (du · a)` is `TauCeti.normalCauchyRiemannLinearization_add_fderiv_apply`.

## Main definitions

* `TauCeti.SmoothEmbedding.normalChartLift`: the orthogonal lift of a normal section, read in the
  charts at `x` and `f x`.
* `TauCeti.SmoothEmbedding.normalChartLinearization`: the Cauchy–Riemann linearization of `f` at
  the chart centre, in the direction of the chart lift.
* `TauCeti.SmoothEmbedding.normalCauchyRiemannOperator`: the normal Cauchy–Riemann operator, on
  sections of the complex normal bundle.

## Main results

* `TauCeti.SmoothEmbedding.isRealCauchyRiemannOperator_normalCauchyRiemannOperator`: the normal
  Cauchy–Riemann operator of a `C²` pseudoholomorphic embedding is a real Cauchy–Riemann operator
  on its complex normal bundle.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 (the linearized operator and the normal bundle of an embedded curve) and
  Appendix C.1 (real linear Cauchy–Riemann operators).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893 (the normal operator of an embedded curve).
-/

public section

noncomputable section

open Bundle Set Module Filter
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothEmbedding

variable {E V P H H' M X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ V H'}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace X] [ChartedSpace H' X] [IsManifold I' ∞ X] {n : ℕ∞ω}
  [RiemannianBundle (fun y : X ↦ TangentSpace I' y)]

/-! ### The chart lift of a normal section -/

section ChartLift

variable (f : SmoothEmbedding I I' n M X) (hn : n ≠ 0)

/-- The **chart lift** of a normal section `ν` at `x`: the orthogonal representative of `ν` at the
point `y` with chart coordinate `z` in the chart at `x`, read in the trivialization of the tangent
bundle of `X` at `f x`. Near the chart centre it is a vector field along the coordinate expression
of `f`, lifting `ν`. -/
def normalChartLift (ν : Π x, f.isImmersion.NormalSpace x hn) (x : M) (z : E) : V :=
  (trivializationAt V (TangentSpace I') (f x)
    ⟨f ((extChartAt I x).symm z),
      f.normalRepresentative ((extChartAt I x).symm z) hn (ν ((extChartAt I x).symm z))⟩).2

variable {f hn}

theorem normalChartLift_add (ν ν' : Π x, f.isImmersion.NormalSpace x hn) (x : M) :
    f.normalChartLift hn (ν + ν') x = f.normalChartLift hn ν x + f.normalChartLift hn ν' x := by
  funext z
  simp only [normalChartLift, TangentBundle.trivializationAt_apply, Pi.add_apply, map_add]
  -- The tangent trivialization acts on each fibre by a continuous linear map.
  exact map_add _ _ _

theorem normalChartLift_smul (g : M → ℝ) (ν : Π x, f.isImmersion.NormalSpace x hn) (x : M) :
    f.normalChartLift hn (g • ν) x =
      fun z ↦ g ((extChartAt I x).symm z) • f.normalChartLift hn ν x z := by
  funext z
  simp only [normalChartLift, TangentBundle.trivializationAt_apply, Pi.smul_apply',
    ContinuousLinearMap.map_smul]
  -- The tangent trivialization acts on each fibre by a continuous linear map.
  exact map_smul _ _ _

/-- At the chart centre the chart lift is the orthogonal representative of the section. -/
theorem normalChartLift_extChartAt (ν : Π x, f.isImmersion.NormalSpace x hn) (x : M) :
    f.normalChartLift hn ν x (extChartAt I x x) = f.normalRepresentative x hn (ν x) := by
  rw [normalChartLift, extChartAt_to_inv]
  -- The tangent trivialization at `f x`, read at `f x`, is the identity coordinate change.
  exact tangentCoordChange_self (I := I') (mem_extChartAt_source (f x))

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [IsManifold I ∞ M]

/-- For a `C²` embedding and a `C¹` metric, the chart lift of a normal section that is
differentiable at `x` is differentiable at the chart centre. -/
theorem differentiableAt_normalChartLift [I.Boundaryless]
    [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)]
    (h2 : 2 ≤ n) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {ν : Π x, f.isImmersion.NormalSpace x hn} {x : M}
    (hν : letI := f.normalSpaceFiberBundle hn hdim
      MDifferentiableAt I (I.prod 𝓘(ℝ, P)) (fun y ↦ TotalSpace.mk' P y (ν y)) x) :
    DifferentiableAt ℝ (f.normalChartLift hn ν x) (extChartAt I x x) := by
  let := f.normalSpaceFiberBundle hn hdim
  have hR := ((f.contMDiff_normalRepresentative (m := 1) hn
    (by rw [one_add_one_eq_two]; exact h2) hdim) ⟨x, ν x⟩).mdifferentiableAt one_ne_zero
  have h := ((mdifferentiableAt_totalSpace _ _).1 (hR.comp x hν)).2
  exact h.differentiableAt_comp_extChartAt_symm

end ChartLift

/-! ### The normal Cauchy–Riemann operator -/

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [IsManifold I ∞ M]
  (f : SmoothEmbedding I I' n M X) (hn : n ≠ 0)
  (j : SmoothAlmostComplexStructure I M) (J : SmoothAlmostComplexStructure I' X)

/-- The **chart linearization** of `f` at `x` in the direction of a normal section `ν`: the
linearization `dξ ∘ j_x - J'(u) ∘ dξ - (dJ'(u) ξ) ∘ du` of the Cauchy–Riemann defect of the
coordinate expression `u` of `f`, at the chart centre, in the direction of the chart lift `ξ` of
`ν`. Here `J'` is `J` read in the chart at `f x` and `j_x` is the value of `j` at `x`, read in the
chart at `x`. -/
def normalChartLinearization (ν : Π x, f.isImmersion.NormalSpace x hn) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I' (f x) :=
  cauchyRiemannLinearization (U := E) (V := V) (j.inChart x (extChartAt I x x)) (J.inChart (f x))
    (writtenInExtChartAt I I' x f) (f.normalChartLift hn ν x) (extChartAt I x x)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ P = 2 * finrank ℂ G)]

variable (P) in
/-- The **normal Cauchy–Riemann operator** of an embedding whose tangent spaces are `J`-invariant,
on the sections of its complex normal bundle: at `x` it sends `ν` to `(1 / 2) J_N [L ξ]`, the
normal class of the chart linearization in the direction of the lift of `ν`, multiplied by
`J_N / 2` (`TauCeti.SmoothEmbedding.fiberEquiv_normalCauchyRiemannOperator_apply`). For a
pseudoholomorphic embedding it is a real Cauchy–Riemann operator
(`TauCeti.SmoothEmbedding.isRealCauchyRiemannOperator_normalCauchyRiemannOperator`). -/
def normalCauchyRiemannOperator
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hJ : ∀ x, MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
      (f.isImmersion.tangentRange x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (Π x, (f.normalComplexStructure hn J hdim hJ).Fiber x) →
      Π x, TangentSpace I x →L[ℝ] (f.normalComplexStructure hn J hdim hJ).Fiber x :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  fun ν x ↦
    let JN := f.normalComplexStructure hn J hdim hJ
    ((JN.fiberEquiv x).symm : _ →L[ℝ] _).comp ((2⁻¹ : ℝ) • (JN x).comp
      ((f.isImmersion.normalClassL x hn).comp
        (f.normalChartLinearization hn j J (fun y ↦ JN.fiberEquiv y (ν y)) x)))

variable {f hn j J}

/-- The defining formula of the normal Cauchy–Riemann operator: `D_N ν x v` is
`(1 / 2) J_N [L v]`, with `L` the chart linearization in the direction of the lift of `ν`. -/
theorem fiberEquiv_normalCauchyRiemannOperator_apply
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hJ : ∀ x, MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
      (f.isImmersion.tangentRange x hn))
    (ν : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      Π x, (f.normalComplexStructure hn J hdim hJ).Fiber x) (x : M) (v : TangentSpace I x) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.normalComplexStructure hn J hdim hJ).fiberEquiv x
        (f.normalCauchyRiemannOperator P hn j J hdim hJ ν x v) =
      (2⁻¹ : ℝ) • f.normalComplexStructureAt hn J x (hJ x) (f.isImmersion.normalClass x hn
        (f.normalChartLinearization hn j J
          (fun y ↦ (f.normalComplexStructure hn J hdim hJ).fiberEquiv y (ν y)) x v)) := by
  rw [normalCauchyRiemannOperator]
  dsimp only
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, normalComplexStructure_apply,
    Manifold.IsImmersion.normalClassL_apply]

section Boundaryless

variable [I.Boundaryless] [I'.Boundaryless]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [IsManifold I' ∞ X]
  [IsManifold I ∞ M] [RiemannianBundle (fun y : X ↦ TangentSpace I' y)] [I'.Boundaryless] in
/-- The derivative at the chart centre of the coordinate expression of `f` is `df_x`. -/
private theorem fderiv_writtenInExtChartAt {x : M} (hfx : MDifferentiableAt I I' f x) :
    fderiv ℝ (writtenInExtChartAt I I' x f) (extChartAt I x x) = mfderiv I I' f x := by
  rw [hfx.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  -- The casts between the tangent spaces and the model spaces are identities.
  rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [IsManifold I' ∞ X]
  [IsManifold I ∞ M] [RiemannianBundle (fun y : X ↦ TangentSpace I' y)] [I.Boundaryless]
  [I'.Boundaryless] in
/-- The coordinate expression of `f` at the chart centre: the point `f x` in its own chart. -/
private theorem writtenInExtChartAt_extChartAt (x : M) :
    writtenInExtChartAt I I' x f (extChartAt I x x) = extChartAt I' (f x) (f x) := by
  rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, extChartAt_to_inv]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]
  [RiemannianBundle (fun y : X ↦ TangentSpace I' y)] [I'.Boundaryless] in
/-- At a point where `f` is pseudoholomorphic, its coordinate expression solves the
Cauchy–Riemann equation at the chart centre. -/
private theorem cauchyRiemannOperator_writtenInExtChartAt {x : M}
    (hfx : IsPseudoholomorphicAt j J f x) :
    cauchyRiemannOperator (j.inChart x (extChartAt I x x)) (J.inChart (f x))
      (writtenInExtChartAt I I' x f) (extChartAt I x x) = 0 := by
  ext v
  rw [cauchyRiemannOperator_apply, zero_apply, fderiv_writtenInExtChartAt hfx.mdifferentiableAt,
    writtenInExtChartAt_extChartAt, J.inChart_extChartAt_self, j.inChart_extChartAt_self]
  exact sub_eq_zero.2 (hfx.mfderiv_apply_commute v)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [IsManifold I ∞ M]
  [RiemannianBundle (fun y : X ↦ TangentSpace I' y)] [I.Boundaryless] in
/-- Near the chart image of `f x`, the structure `J` read in the chart at `f x` squares to `-1`. -/
private theorem eventually_inChart_inChart (x : M) :
    ∀ᶠ y in 𝓝 (writtenInExtChartAt I I' x f (extChartAt I x x)),
      ∀ v, J.inChart (f x) y (J.inChart (f x) y v) = -v := by
  rw [writtenInExtChartAt_extChartAt]
  filter_upwards [extChartAt_target_mem_nhds (I := I') (f x)] with y hy v
  exact J.inChart_inChart (f x) hy v

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- At a pseudoholomorphic point, the chart linearization is complex antilinear: it anticommutes
`j_x` on the source with `J_{f x}` on the ambient tangent space, `L (j v) = -J (L v)`. -/
theorem isComplexAntilinear_normalChartLinearization {x : M}
    (hfx : IsPseudoholomorphicAt j J f x) (ν : Π x, f.isImmersion.NormalSpace x hn) :
    IsComplexAntilinear (j.toEndomorphism x).toLinearMap (J.toEndomorphism (f x)).toLinearMap
      (f.normalChartLinearization hn j J ν x).toLinearMap := by
  have h := isComplexAntilinear_cauchyRiemannLinearization (f.normalChartLift hn ν x)
    (fun v ↦ by rw [j.inChart_extChartAt_self]; exact j.apply_apply x v)
    (eventually_inChart_inChart x) (cauchyRiemannOperator_writtenInExtChartAt hfx)
  rw [writtenInExtChartAt_extChartAt] at h
  -- Read `j x` and `J (f x)` as the structures in the charts at their own centres.
  rw [← j.inChart_extChartAt_self, ← J.inChart_extChartAt_self]
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [I.Boundaryless] [I'.Boundaryless] in
/-- The chart linearization is additive on normal sections whose chart lifts are differentiable at
the chart centre. -/
theorem normalChartLinearization_add {x : M} {ν ν' : Π x, f.isImmersion.NormalSpace x hn}
    (hν : DifferentiableAt ℝ (f.normalChartLift hn ν x) (extChartAt I x x))
    (hν' : DifferentiableAt ℝ (f.normalChartLift hn ν' x) (extChartAt I x x)) :
    f.normalChartLinearization hn j J (ν + ν') x =
      f.normalChartLinearization hn j J ν x + f.normalChartLinearization hn j J ν' x := by
  rw [normalChartLinearization, normalChartLift_add]
  exact cauchyRiemannLinearization_add _ _ _ _ _ _ hν hν'

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [I'.Boundaryless] in
/-- The Leibniz rule of the chart linearization: multiplying a normal section by a real function
`g` adds `dg (j v) w - dg v J w`, where `w` is the orthogonal representative of the section at
`x`. -/
theorem normalChartLinearization_smul_apply {x : M} {g : M → ℝ}
    {ν : Π x, f.isImmersion.NormalSpace x hn} (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hν : DifferentiableAt ℝ (f.normalChartLift hn ν x) (extChartAt I x x))
    (v : TangentSpace I x) :
    f.normalChartLinearization hn j J (g • ν) x v =
      g x • f.normalChartLinearization hn j J ν x v +
        mvfderiv I g x (j x v) • f.normalRepresentative x hn (ν x) -
          mvfderiv I g x v • J (f x) (f.normalRepresentative x hn (ν x)) := by
  rw [normalChartLinearization, normalChartLift_smul]
  have h := cauchyRiemannLinearization_fun_smul (j.inChart x (extChartAt I x x)) (J.inChart (f x))
    (writtenInExtChartAt I I' x f) (f.normalChartLift hn ν x) (g ∘ (extChartAt I x).symm)
    (extChartAt I x x) v hg.differentiableAt_comp_extChartAt_symm hν
  rw [Function.comp_apply, extChartAt_to_inv, ← mvfderiv_eq_fderiv_comp_extChartAt_symm,
    normalChartLift_extChartAt, writtenInExtChartAt_extChartAt] at h
  -- Read `j x` and `J (f x)` as the structures in the charts at their own centres.
  beta_reduce
  rw [← j.inChart_extChartAt_self, ← J.inChart_extChartAt_self]
  exact h

variable [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)]

omit [I'.Boundaryless] in
/-- A section of the complex normal bundle that is differentiable at `x` has a chart lift that is
differentiable at the chart centre. -/
private theorem differentiableAt_normalChartLift_fiberEquiv (h2 : 2 ≤ n)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hJ : ∀ x, MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
      (f.isImmersion.tangentRange x hn))
    {ν : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      Π x, (f.normalComplexStructure hn J hdim hJ).Fiber x} {x : M}
    (hν : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      MDifferentiableAt I (I.prod 𝓘(ℝ, G)) (fun y ↦ TotalSpace.mk' G y (ν y)) x) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    DifferentiableAt ℝ (f.normalChartLift hn
      (fun y ↦ (f.normalComplexStructure hn J hdim hJ).fiberEquiv y (ν y)) x)
      (extChartAt I x x) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have hJN := ((f.contMDiff_normalComplexStructureAt_hom_bundle (m := 1) hn J
    (by rw [one_add_one_eq_two]; exact h2) hdim hJ) x).mdifferentiableAt one_ne_zero
  -- `J_N` as a section of the endomorphism bundle, read as the normal complex structures.
  have hJN' : MDifferentiableAt I (I.prod 𝓘(ℝ, P →L[ℝ] P))
      (fun b ↦ TotalSpace.mk' (P →L[ℝ] P)
        (E := fun b ↦ f.isImmersion.NormalSpace b hn →L[ℝ] f.isImmersion.NormalSpace b hn) b
        (f.normalComplexStructure hn J hdim hJ b)) x := by
    convert hJN using 3 with b
    exact ContinuousLinearMap.ext fun w ↦ normalComplexStructure_apply f hn J hdim hJ b w
  exact differentiableAt_normalChartLift h2 hdim
    ((f.normalComplexStructure hn J hdim hJ).mdifferentiableAt_totalSpace_fiberEquiv G hJN' hν)

variable (P G) in
/-- **The normal Cauchy–Riemann operator is a real Cauchy–Riemann operator.** For a `C²`
pseudoholomorphic embedding `f` and a `C¹` metric on the target, the normal Cauchy–Riemann operator
of `f` takes values in `(0,1)`-forms, is additive on sections differentiable at a point, and
satisfies the Leibniz rule `D_N (g • ν) = g • D_N ν + (∂bar g) ⊗ ν`. -/
theorem isRealCauchyRiemannOperator_normalCauchyRiemannOperator (h2 : 2 ≤ n)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsPseudoholomorphic j J f) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    IsRealCauchyRiemannOperator G j (f.normalCauchyRiemannOperator P hn j J hdim
      fun x ↦ mapsTo_tangentRange_of_isPseudoholomorphicAt hn (hf.isPseudoholomorphicAt x)) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  set hJ := fun x ↦ mapsTo_tangentRange_of_isPseudoholomorphicAt hn (hf.isPseudoholomorphicAt x)
  set JN := f.normalComplexStructure hn J hdim hJ
  refine ⟨fun ν x ↦ ?_, fun {ν ν' x} hν hν' ↦ ?_, fun {ν g x} hν hg ↦ ?_⟩
  · -- `(1 / 2) J_N [L (j v)] = (1 / 2) [L v] = -i • (1 / 2) J_N [L v]`.
    rw [SmoothAlmostComplexStructure.isZeroOneForm_iff]
    intro v
    apply (JN.fiberEquiv x).injective
    have hL := (isComplexAntilinear_normalChartLinearization (hf.isPseudoholomorphicAt x)
      (fun y ↦ JN.fiberEquiv y (ν y))).apply v
    simp only [ContinuousLinearMap.coe_coe] at hL
    rw [map_neg, JN.fiberEquiv_I_smul, fiberEquiv_normalCauchyRiemannOperator_apply,
      fiberEquiv_normalCauchyRiemannOperator_apply]
    beta_reduce
    rw [hL,
      map_neg, ← normalComplexStructureAt_normalClass (hJ x), normalComplexStructure_apply,
      map_smul, map_neg, normalComplexStructureAt_normalComplexStructureAt, smul_neg, smul_neg,
      neg_neg]
  · have hsum : (fun y ↦ JN.fiberEquiv y ((ν + ν') y)) =
        (fun y ↦ JN.fiberEquiv y (ν y)) + fun y ↦ JN.fiberEquiv y (ν' y) :=
      funext fun y ↦ map_add _ _ _
    refine ContinuousLinearMap.ext fun v ↦ (JN.fiberEquiv x).injective ?_
    rw [add_apply, map_add, fiberEquiv_normalCauchyRiemannOperator_apply,
      fiberEquiv_normalCauchyRiemannOperator_apply, fiberEquiv_normalCauchyRiemannOperator_apply,
      hsum, normalChartLinearization_add (differentiableAt_normalChartLift_fiberEquiv h2 hdim hJ hν)
        (differentiableAt_normalChartLift_fiberEquiv h2 hdim hJ hν'),
      add_apply, map_add, map_add, smul_add]
  · -- Both sides are `(1 / 2) J_N` applied to `g [L ξ] + dg (j v) [w] - dg v J_N [w]`.
    have hsmul : (fun y ↦ JN.fiberEquiv y ((g • ν) y)) = g • fun y ↦ JN.fiberEquiv y (ν y) :=
      funext fun y ↦ by rw [Pi.smul_apply', Pi.smul_apply', map_smul]
    refine ContinuousLinearMap.ext fun v ↦ (JN.fiberEquiv x).injective ?_
    rw [add_apply, smul_apply, map_add, map_smul, fiberEquiv_normalCauchyRiemannOperator_apply,
      fiberEquiv_normalCauchyRiemannOperator_apply,
      SmoothAlmostComplexStructure.dbarSMulRight_apply, map_smul, map_add, map_smul, map_smul,
      JN.fiberEquiv_I_smul, normalComplexStructure_apply, hsmul,
      normalChartLinearization_smul_apply hg
        (differentiableAt_normalChartLift_fiberEquiv h2 hdim hJ hν)]
    simp only [map_sub, map_add, map_smul, normalClass_normalRepresentative,
      ← normalComplexStructureAt_normalClass (hJ x),
      normalComplexStructureAt_normalComplexStructureAt]
    module

end Boundaryless

end TauCeti.SmoothEmbedding
