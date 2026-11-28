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
import TauCeti.Analysis.Calculus.LeftInverseAlong
import TauCeti.Geometry.Manifold.MFDeriv.Coordinates
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Coordinates
import TauCeti.Geometry.Symplectic.Manifold.CauchyRiemann
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

**The choice of lift.** The lift fixes the ambient metric, but the operator does not depend on
it. Let `ξ` be any vector field along `u`, differentiable at the chart centre, that lifts `ν` near
`x`. Near the centre, `ξ` and the chart lift differ by a vector in the range of `du`, so their
difference is `du · a` for a vector field `a` differentiable at the centre, by a differentiable
family of left inverses of `du` (`DifferentiableAt.exists_differentiableAt_eventually_eq_apply`).
Near the centre `u` solves the Cauchy–Riemann equation for the source structure `j` read in the
chart at `x` (`TauCeti.eventually_cauchyRiemannOperator_writtenInExtChartAt_eq_zero`), so
`L (du · a)` is tangent, `du (da ∘ j_x - j_x ∘ da - ∂_a j)`
(`TauCeti.cauchyRiemannLinearization_fderiv_apply_of_varying`). Hence `[L ξ] = [L ν]`
(`TauCeti.SmoothEmbedding.normalClass_cauchyRiemannLinearization_eq_of_lift`),
and the operators built from two `C¹` metrics agree on sections differentiable at the point
(`TauCeti.SmoothEmbedding.normalCauchyRiemannOperator_congr_riemannianBundle`).

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
* `TauCeti.SmoothEmbedding.normalCauchyRiemannOperator_congr_riemannianBundle`: at a point near
  which `f` is pseudoholomorphic, its value on a section differentiable there does not depend on
  the metric used to lift normal sections.
* `TauCeti.SmoothEmbedding.normalClass_cauchyRiemannLinearization_eq_of_lift`:
  the normal class of the linearization in the direction of any differentiable lift of a normal
  section is that of the chart linearization.

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

/-- The defining formula of the chart lift: at the point with chart coordinate `z` in the chart at
`x`, it is the orthogonal representative of `ν` there, read in the trivialization of the tangent
bundle of `X` at `f x`. -/
theorem normalChartLift_apply (ν : Π x, f.isImmersion.NormalSpace x hn) (x : M) (z : E) :
    f.normalChartLift hn ν x z =
      (trivializationAt V (TangentSpace I') (f x)
        ⟨f ((extChartAt I x).symm z),
          f.normalRepresentative ((extChartAt I x).symm z) hn (ν ((extChartAt I x).symm z))⟩).2 :=
  (rfl)

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

/-- The chart lift lifts the normal section: at a chart point `z` whose point `y` is mapped into
the chart at `f x`, the tangent vector at `f y` with coordinates the chart lift at `z` has normal
class `ν y`. -/
theorem normalClass_trivializationAt_symm_normalChartLift (ν : Π x, f.isImmersion.NormalSpace x hn)
    {x : M} {z : E} (hz : f ((extChartAt I x).symm z) ∈ (chartAt H' (f x)).source) :
    f.isImmersion.normalClass ((extChartAt I x).symm z) hn
        ((trivializationAt V (TangentSpace I') (f x)).symm (f ((extChartAt I x).symm z))
          (f.normalChartLift hn ν x z)) =
      ν ((extChartAt I x).symm z) := by
  have hb : f ((extChartAt I x).symm z) ∈ (trivializationAt V (TangentSpace I') (f x)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hz
  rw [normalChartLift_apply, (trivializationAt V (TangentSpace I') (f x)).symm_apply_apply_mk hb,
    normalClass_normalRepresentative]

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

variable {f hn j J} in
omit [FiniteDimensional ℝ E] in
/-- The defining formula of the chart linearization: the Cauchy–Riemann linearization of the
coordinate expression of `f` at the chart centre, in the direction of the chart lift of `ν`. -/
theorem normalChartLinearization_def (ν : Π x, f.isImmersion.NormalSpace x hn) (x : M) :
    f.normalChartLinearization hn j J ν x =
      cauchyRiemannLinearization (U := E) (V := V) (j.inChart x (extChartAt I x x))
        (J.inChart (f x)) (writtenInExtChartAt I I' x f) (f.normalChartLift hn ν x)
        (extChartAt I x x) :=
  (rfl)

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
  simp [normalCauchyRiemannOperator, normalComplexStructure_apply,
    Manifold.IsImmersion.normalClassL_apply]

section Boundaryless

variable [I.Boundaryless] [I'.Boundaryless]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [IsManifold I ∞ M]
  [RiemannianBundle (fun y : X ↦ TangentSpace I' y)] [I.Boundaryless] in
/-- Near the chart image of `f x`, the structure `J` read in the chart at `f x` squares to `-1`. -/
private theorem eventually_inChart_inChart (x : M) :
    ∀ᶠ y in 𝓝 (writtenInExtChartAt I I' x f (extChartAt I x x)),
      ∀ v, J.inChart (f x) y (J.inChart (f x) y v) = -v := by
  rw [writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)]
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
    (eventually_inChart_inChart x) hfx.cauchyRiemannOperator_writtenInExtChartAt_eq_zero
  rw [writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)] at h
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
    normalChartLift_extChartAt, writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)]
    at h
  -- Read `j x` and `J (f x)` as the structures in the charts at their own centres.
  beta_reduce
  rw [← j.inChart_extChartAt_self, ← J.inChart_extChartAt_self]
  exact h

variable [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)]

omit [RiemannianBundle (fun y : X ↦ TangentSpace I' y)] [I.Boundaryless]
  [I'.Boundaryless] [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)] in
/-- A section of the complex normal bundle that is differentiable at `x` is differentiable at `x`
as a section of the real normal bundle. -/
private theorem mdifferentiableAt_totalSpace_fiberEquiv (h2 : 2 ≤ n)
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
    MDifferentiableAt I (I.prod 𝓘(ℝ, P)) (fun y ↦ TotalSpace.mk' P y
      ((f.normalComplexStructure hn J hdim hJ).fiberEquiv y (ν y))) x := by
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
  exact (f.normalComplexStructure hn J hdim hJ).mdifferentiableAt_totalSpace_fiberEquiv G hJN' hν

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
      (extChartAt I x x) :=
  differentiableAt_normalChartLift h2 hdim (mdifferentiableAt_totalSpace_fiberEquiv h2 hdim hJ hν)

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
    rw [hL, normalComplexStructure_apply]
    -- Unfolding `JN` identifies the lift on the left with the lift in `hL`.
    simp only [JN, map_neg, map_smul, smul_neg, neg_neg,
      ← normalComplexStructureAt_normalClass (hJ x),
      normalComplexStructureAt_normalComplexStructureAt]
  · have hsum : (fun y ↦ JN.fiberEquiv y ((ν + ν') y)) =
        (fun y ↦ JN.fiberEquiv y (ν y)) + fun y ↦ JN.fiberEquiv y (ν' y) :=
      funext fun y ↦ map_add _ _ _
    refine ContinuousLinearMap.ext fun v ↦ (JN.fiberEquiv x).injective ?_
    rw [add_apply, map_add, fiberEquiv_normalCauchyRiemannOperator_apply,
      fiberEquiv_normalCauchyRiemannOperator_apply, fiberEquiv_normalCauchyRiemannOperator_apply,
      hsum, normalChartLinearization_add (differentiableAt_normalChartLift_fiberEquiv h2 hdim hJ hν)
        (differentiableAt_normalChartLift_fiberEquiv h2 hdim hJ hν')]
    simp only [add_apply, map_add, smul_add]
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

/-! ### Independence of the metric -/

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]
  [RiemannianBundle (fun y : X ↦ TangentSpace I' y)] [I.Boundaryless] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)] in
/-- A vector tangent to `f` at a point `y` of the chart at `x`, read in the trivialization of the
tangent bundle of `X` at `f x`, lies in the range of the derivative of the coordinate expression
of `f` at the chart image of `y`. -/
private theorem trivializationAt_mem_range_fderiv_writtenInExtChartAt {x y : M}
    (hy : y ∈ (extChartAt I x).source) (hfy : f y ∈ (extChartAt I' (f x)).source)
    (hd : DifferentiableAt ℝ (writtenInExtChartAt I I' x f) (extChartAt I x y))
    {τ : TangentSpace I' (f y)} (hτ : τ ∈ f.isImmersion.tangentRange y hn) :
    (trivializationAt V (TangentSpace I') (f x) ⟨f y, τ⟩).2 ∈
      (fderiv ℝ (writtenInExtChartAt I I' x f) (extChartAt I x y)).toLinearMap.range := by
  obtain ⟨w, rfl⟩ := hτ
  rw [ContinuousLinearMap.coe_coe,
    (f.contMDiff.mdifferentiableAt hn).trivializationAt_mfderiv_apply hy
    (by rwa [← extChartAt_source I']) hd]
  exact LinearMap.mem_range_self _ _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]
  [RiemannianBundle (fun y : X ↦ TangentSpace I' y)]
  [I'.Boundaryless] [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)] in
/-- Near the chart centre, the chart lifts of a normal section for two metrics differ by a vector
tangent to `f`: their difference lies in the range of the derivative of the coordinate expression
of `f`. -/
private theorem eventually_normalChartLift_sub_mem_range (h2 : 2 ≤ n)
    (g g' : RiemannianBundle (fun y : X ↦ TangentSpace I' y))
    (ν : Π x, f.isImmersion.NormalSpace x hn) (x : M) :
    ∀ᶠ z in 𝓝 (extChartAt I x x), (letI := g; f.normalChartLift hn ν x) z -
      (letI := g'; f.normalChartLift hn ν x) z ∈
        (fderiv ℝ (writtenInExtChartAt I I' x f) z).toLinearMap.range := by
  obtain ⟨hopen, hx, hcd, -⟩ :=
    TauCeti.isOpen_mem_contDiffOn_mapsTo_writtenInExtChartAt (f.contMDiff.of_le h2) x
  filter_upwards [hopen.mem_nhds hx] with z hz
  set y := (extChartAt I x).symm z
  have hzy : extChartAt I x y = z := (extChartAt I x).right_inv hz.1
  have hτ : (letI := g; f.normalRepresentative y hn (ν y)) -
      (letI := g'; f.normalRepresentative y hn (ν y)) ∈ f.isImmersion.tangentRange y hn := by
    rw [← Manifold.IsImmersion.normalClass_eq_zero_iff, map_sub,
      (letI := g; f.normalClass_normalRepresentative y hn (ν y)),
      (letI := g'; f.normalClass_normalRepresentative y hn (ν y)), sub_self]
  have h := trivializationAt_mem_range_fderiv_writtenInExtChartAt (f := f)
    ((extChartAt I x).map_target hz.1) hz.2
    (by rw [hzy]; exact (hcd.contDiffAt (hopen.mem_nhds hz)).differentiableAt (by norm_num)) hτ
  rw [hzy] at h
  convert h using 1
  simp only [normalChartLift, TangentBundle.trivializationAt_apply]
  -- The tangent trivialization acts on each fibre by a continuous linear map.
  exact (map_sub _ _ _).symm

omit [RiemannianBundle (fun y : X ↦ TangentSpace I' y)]
  [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)] in
/-- **The chart linearization does not depend on the metric modulo tangent vectors.** For a `C²`
embedding pseudoholomorphic near `x` and two `C¹` metrics on the target, the chart linearizations in
the directions of the two orthogonal lifts of a normal section differentiable at `x` have the same
normal class: the lifts differ by a vector field tangent to `f`, on which the linearization is
tangent (`TauCeti.cauchyRiemannLinearization_apply_mem_range_of_eventually_mem_range`). -/
theorem normalClass_normalChartLinearization_congr_riemannianBundle (h2 : 2 ≤ n)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {x : M}
    (hf : ∀ᶠ y in 𝓝 x, IsPseudoholomorphicAt j J f y)
    (g g' : RiemannianBundle (fun y : X ↦ TangentSpace I' y))
    (hg : letI := g; IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y))
    (hg' : letI := g'; IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y))
    {ν : Π x, f.isImmersion.NormalSpace x hn}
    (hν : letI := f.normalSpaceFiberBundle hn hdim
      MDifferentiableAt I (I.prod 𝓘(ℝ, P)) (fun y ↦ TotalSpace.mk' P y (ν y)) x)
    (v : TangentSpace I x) :
    f.isImmersion.normalClass x hn ((letI := g; f.normalChartLinearization hn j J ν x) v) =
      f.isImmersion.normalClass x hn ((letI := g'; f.normalChartLinearization hn j J ν x) v) := by
  set u := writtenInExtChartAt I I' x f
  set z₀ := extChartAt I x x
  set ξ := (letI := g; f.normalChartLift hn ν x)
  set ξ' := (letI := g'; f.normalChartLift hn ν x)
  have hξ : DifferentiableAt ℝ ξ z₀ := by
    let := g
    exact differentiableAt_normalChartLift h2 hdim hν
  have hξ' : DifferentiableAt ℝ ξ' z₀ := by
    let := g'
    exact differentiableAt_normalChartLift h2 hdim hν
  have hdu : fderiv ℝ u z₀ = mfderiv I I' f x :=
    (f.contMDiff.mdifferentiableAt hn).fderiv_writtenInExtChartAt
  have hj : DifferentiableAt ℝ (j.inChart x) z₀ := by
    have h := j.differentiableWithinAt_inChart x
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ] at h
  have hJ : DifferentiableAt ℝ (J.inChart (f x)) (u z₀) := by
    have h := J.differentiableWithinAt_inChart (f x)
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
      ← writtenInExtChartAt_apply_extChartAt (I := I) (f := f) (mem_extChartAt_source x)] at h
  -- The two lifts differ by a vector field tangent to `f` near `x`, on which the linearization
  -- is tangent at `x`.
  have hL := cauchyRiemannLinearization_apply_mem_range_of_eventually_mem_range
    (j.inChart x) (J.inChart (f x)) v ((f.contMDiff.of_le h2) x).contDiffAt_writtenInExtChartAt
    (by rw [hdu]; exact f.isImmersion.mfderiv_injective hn x) (hξ.sub hξ') hj hJ
    (eventually_cauchyRiemannOperator_writtenInExtChartAt_eq_zero hf)
    (eventually_normalChartLift_sub_mem_range h2 g g' ν x)
  rw [hdu] at hL
  have hadd := cauchyRiemannLinearization_add (j.inChart x z₀) (J.inChart (f x)) u ξ' (ξ - ξ') z₀
    hξ' (hξ.sub hξ')
  rw [add_sub_cancel ξ' ξ] at hadd
  rw [← sub_eq_zero, ← map_sub, Manifold.IsImmersion.normalClass_eq_zero_iff]
  have heq : (letI := g; f.normalChartLinearization hn j J ν x) v -
      (letI := g'; f.normalChartLinearization hn j J ν x) v =
        cauchyRiemannLinearization (j.inChart x z₀) (J.inChart (f x)) u (ξ - ξ') z₀ v := by
    rw [(letI := g; normalChartLinearization_def ν x),
      (letI := g'; normalChartLinearization_def ν x), hadd]
    exact add_sub_cancel_left _ _
  rw [heq]
  exact hL

omit [RiemannianBundle (fun y : X ↦ TangentSpace I' y)]
  [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)] in
/-- **The normal Cauchy–Riemann operator does not depend on the metric.** For a `C²` embedding
`f` pseudoholomorphic near `x`, the normal Cauchy–Riemann operators built from any two `C¹`
metrics on the target take the same value at `x` on every section of the complex normal bundle
differentiable at `x`.
The metric only chooses the orthogonal lift of a normal section, and two lifts differ by a vector
field tangent to `f` (`normalClass_normalChartLinearization_congr_riemannianBundle`). -/
theorem normalCauchyRiemannOperator_congr_riemannianBundle (h2 : 2 ≤ n)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {x : M}
    (hf : ∀ᶠ y in 𝓝 x, IsPseudoholomorphicAt j J f y)
    (hJ : ∀ x, MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
      (f.isImmersion.tangentRange x hn))
    (g g' : RiemannianBundle (fun y : X ↦ TangentSpace I' y))
    (hg : letI := g; IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y))
    (hg' : letI := g'; IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y))
    {ν : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      Π x, (f.normalComplexStructure hn J hdim hJ).Fiber x}
    (hν : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      MDifferentiableAt I (I.prod 𝓘(ℝ, G)) (fun y ↦ TotalSpace.mk' G y (ν y)) x) :
    (letI := g; f.normalCauchyRiemannOperator P hn j J hdim hJ) ν x =
      (letI := g'; f.normalCauchyRiemannOperator P hn j J hdim hJ) ν x := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  refine ContinuousLinearMap.ext fun v ↦
    ((f.normalComplexStructure hn J hdim hJ).fiberEquiv x).injective ?_
  rw [(let := g; fiberEquiv_normalCauchyRiemannOperator_apply hdim hJ ν x v),
    (let := g'; fiberEquiv_normalCauchyRiemannOperator_apply hdim hJ ν x v),
    normalClass_normalChartLinearization_congr_riemannianBundle h2 hdim hf g g' hg hg'
      (mdifferentiableAt_totalSpace_fiberEquiv h2 hdim hJ hν)]

/-! ### Independence of the lift -/

omit [FiniteDimensional ℝ E] [I'.Boundaryless]
  [IsContMDiffRiemannianBundle I' 1 V (fun y : X ↦ TangentSpace I' y)] in
/-- Near the chart centre, a vector field `ξ` along the coordinate expression of `f` that lifts
the normal section `ν` differs from the chart lift of `ν` by a vector in the range of the derivative
of the coordinate expression. -/
private theorem eventually_sub_normalChartLift_mem_range
    {ν : Π x, f.isImmersion.NormalSpace x hn} {x : M} {ξ : E → V}
    (hlift : ∀ᶠ z in 𝓝 (extChartAt I x x),
      f.isImmersion.normalClass ((extChartAt I x).symm z) hn
        ((trivializationAt V (TangentSpace I') (f x)).symm (f ((extChartAt I x).symm z)) (ξ z)) =
        ν ((extChartAt I x).symm z)) :
    ∀ᶠ z in 𝓝 (extChartAt I x x), (ξ - f.normalChartLift hn ν x) z ∈
      Set.range (fderiv ℝ (writtenInExtChartAt I I' x f) z) := by
  have hsrc : (f : M → X) ⁻¹' (chartAt H' (f x)).source ∈ 𝓝 x :=
    f.contMDiff.continuous.continuousAt.preimage_mem_nhds (chart_source_mem_nhds H' (f x))
  filter_upwards [extChartAt_target_mem_nhds (I := I) x, extChartAt_preimage_mem_nhds hsrc, hlift]
    with z hz hzf hzν
  set y := (extChartAt I x).symm z
  set T := trivializationAt V (TangentSpace I') (f x)
  have hy : y ∈ (chartAt H x).source := by
    rw [← extChartAt_source I]
    exact (extChartAt I x).map_target hz
  have hb : f y ∈ T.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hzf
  set e := T.continuousLinearEquivAt ℝ (f y) hb
  -- In the trivialization at `f x`, `ξ z` and the chart lift are the coordinates of two ambient
  -- vectors at `f y` with the same normal class, whose difference is tangent.
  have hξz : ξ z = e (T.symm (f y) (ξ z)) := by
    rw [← Trivialization.continuousLinearEquivAt_symm_apply ℝ _ _ hb,
      ContinuousLinearEquiv.apply_symm_apply]
  have hℓz : f.normalChartLift hn ν x z = e (f.normalRepresentative y hn (ν y)) := by
    rw [normalChartLift_apply, Trivialization.continuousLinearEquivAt_apply]
  have hmem : T.symm (f y) (ξ z) - f.normalRepresentative y hn (ν y) ∈
      f.isImmersion.tangentRange y hn := by
    rw [← Manifold.IsImmersion.normalClass_eq_iff, normalClass_normalRepresentative]
    exact hzν
  have hrange := f.map_tangentRange_inTangentCoordinates hn hy hzf
  rw [← (f.contMDiff.mdifferentiableAt (by simpa using hn) :
      MDifferentiableAt I I' f y).fderiv_writtenInExtChartAt_eq_inTangentCoordinates hy hzf,
    (extChartAt I x).right_inv hz] at hrange
  have he := Submodule.mem_map_of_mem (f := e.toLinearMap) hmem
  rw [hrange] at he
  obtain ⟨w, hw⟩ := he
  refine ⟨w, ?_⟩
  rw [Pi.sub_apply, hξz, hℓz, ← map_sub]
  exact hw

/-- **The normal linearization does not depend on the lift.** Let `f` be a `C²` embedding,
pseudoholomorphic near `x`, and `ξ` a vector field along its coordinate expression `u` in the
charts at `x` and `f x`, differentiable at the chart centre, that lifts the normal section `ν` near
`x`: at each chart point `z` near the centre, the tangent vector at `f y`, `y = φ⁻¹ z`, with
coordinates `ξ z` in the trivialization at `f x` has normal class `ν y`. Then the linearization of
the Cauchy–Riemann defect of `u` in the direction `ξ`, at the chart centre, has the same normal
class as the chart linearization of `ν`, which uses the orthogonal lift. -/
theorem normalClass_cauchyRiemannLinearization_eq_of_lift
    (h2 : 2 ≤ n) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {x : M}
    (hf : ∀ᶠ y in 𝓝 x, IsPseudoholomorphicAt j J f y) {ν : Π x, f.isImmersion.NormalSpace x hn}
    (hν : letI := f.normalSpaceFiberBundle hn hdim
      MDifferentiableAt I (I.prod 𝓘(ℝ, P)) (fun y ↦ TotalSpace.mk' P y (ν y)) x)
    {ξ : E → V} (hξ : DifferentiableAt ℝ ξ (extChartAt I x x))
    (hlift : ∀ᶠ z in 𝓝 (extChartAt I x x),
      f.isImmersion.normalClass ((extChartAt I x).symm z) hn
        ((trivializationAt V (TangentSpace I') (f x)).symm (f ((extChartAt I x).symm z)) (ξ z)) =
        ν ((extChartAt I x).symm z))
    (v : E) :
    f.isImmersion.normalClass x hn
        (cauchyRiemannLinearization (j.inChart x (extChartAt I x x)) (J.inChart (f x))
          (writtenInExtChartAt I I' x f) ξ (extChartAt I x x) v) =
      f.isImmersion.normalClass x hn (f.normalChartLinearization hn j J ν x v) := by
  set c := extChartAt I x x
  set u := writtenInExtChartAt I I' x f
  have hfC2 : ContMDiffAt I I' 2 f x := (f.contMDiff x).of_le h2
  have hu : ContDiffAt ℝ 2 u c := hfC2.contDiffAt_writtenInExtChartAt
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) c :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfx : MDifferentiableAt I I' f x := hfC2.mdifferentiableAt (by norm_num)
  have hℓ := differentiableAt_normalChartLift h2 hdim hν
  -- The difference of the two lifts is `du · a` near the centre, with `a` differentiable there.
  have hinj : (fderiv ℝ u c).HasLeftInverse := by
    refine .of_injective_of_finiteDimensional ?_
    rw [hfx.fderiv_writtenInExtChartAt]
    exact f.isImmersion.mfderiv_injective hn x
  obtain ⟨a, ha, hη⟩ := hdu.exists_differentiableAt_eventually_eq_apply hinj (hξ.sub hℓ)
    (eventually_sub_normalChartLift_mem_range hlift)
  have hξeq : ξ =ᶠ[𝓝 c] f.normalChartLift hn ν x + fun z ↦ fderiv ℝ u z (a z) := by
    filter_upwards [hη] with z hz
    rw [Pi.add_apply, ← hz, Pi.sub_apply, add_sub_cancel]
  -- Near the centre `u` solves the Cauchy–Riemann equation for the structures read in charts.
  have hhol := eventually_cauchyRiemannOperator_writtenInExtChartAt_eq_zero hf
  have hj : DifferentiableAt ℝ (j.inChart x) c :=
    ((j.contDiffOn_inChart x).contDiffAt (extChartAt_target_mem_nhds x)).differentiableAt
      (by simp)
  have huc : u c = extChartAt I' (f x) (f x) :=
    writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)
  have hJ : DifferentiableAt ℝ (J.inChart (f x)) (u c) := by
    rw [huc]
    exact ((J.contDiffOn_inChart (f x)).contDiffAt
      (extChartAt_target_mem_nhds (f x))).differentiableAt (by simp)
  have hL : cauchyRiemannLinearization (j.inChart x c) (J.inChart (f x)) u ξ c =
      cauchyRiemannLinearization (j.inChart x c) (J.inChart (f x)) u
        (f.normalChartLift hn ν x + fun z ↦ fderiv ℝ u z (a z)) c := by
    ext w
    simp only [cauchyRiemannLinearization_apply, hξeq.fderiv_eq, hξeq.eq_of_nhds]
  rw [hL, cauchyRiemannLinearization_add _ _ _ _ _ _ hℓ (hdu.clm_apply ha)]
  rw [add_apply,
    cauchyRiemannLinearization_fderiv_apply_of_varying (j.inChart x) _ u a c v hu ha hj hJ hhol,
    hfx.fderiv_writtenInExtChartAt]
  rw [normalChartLinearization_def]
  -- The ambient vectors live in `TangentSpace I' (f x)`, whose additive structure is that of `V`.
  exact (f.isImmersion.normalClass_eq_iff x hn _ _).2
    ((f.isImmersion.mem_tangentRange_iff x hn _).2 ⟨_, (add_sub_cancel_left _ _).symm⟩)
end Boundaryless

end TauCeti.SmoothEmbedding
