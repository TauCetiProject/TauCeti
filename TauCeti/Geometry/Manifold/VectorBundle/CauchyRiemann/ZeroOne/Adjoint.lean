/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Adjoint
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Analysis.Complex.OperatorNorm
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# The formal adjoint of a real Cauchy–Riemann operator in a chart

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`,
smooth metrics on `TM` and `V` for which `i` is orthogonal, and `D` a smooth real Cauchy–Riemann
operator with formal adjoint `D*` (`TauCeti.IsRealCauchyRiemannOperator.formalAdjoint`).

In chart `i`, a `(0,1)`-form `η` reads as a complex antilinear map, so it is determined by the
field `r = ηᵢ(·)(1) : ℂ → F` of its values at `1`. This file shows that `D*` is a first-order
operator with smooth coefficients in `r`:

`(D* η)ᵢ = Kᵢ r - λᵢ⁻¹ (∂ₛ r - i ∂ₜ r)`,

(`TauCeti.FiniteBundleAtlas.coord_formalAdjoint_eq`), where `λᵢ` is the conformal factor of the
metric in chart `i` (`TauCeti.FiniteBundleAtlas.chartConformalFactor`, the squared length of the
tangent vector read as `1`) and `Kᵢ` is the zeroth-order term
(`TauCeti.FiniteBundleAtlas.chartZeroOneZeroOrder`), the reading of `D*` on the chart frame of
`(0,1)`-forms (`TauCeti.FiniteBundleAtlas.zeroOneFrame`). Both coefficients are smooth where the
trivialization of one-forms is defined (`TauCeti.FiniteBundleAtlas.contDiffOn_chartConformalFactor`,
`TauCeti.FiniteBundleAtlas.contDiffOn_chartZeroOneZeroOrder`), a neighbourhood of the closure of
the chart image, and `λᵢ` is positive there. This is the chart form McDuff–Salamon use to put `D*`
in the form of a Cauchy–Riemann operator of `∂`-type.

The proof writes `η` near the point as `∑ₖ rₖ eₖ` in the chart frame (`rₖ` the coordinates of `r`)
and applies the Leibniz rule `D* (f e) = f D* e - e (grad f)`
(`TauCeti.IsRealCauchyRiemannOperator.formalAdjoint_smul`). In real dimension two the gradient
term is `df v • e v - df (j v) • i • e v` for a unit vector `v`
(`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm.apply_mgradient`); with `v` the unit vector
in the direction read as `1`, its reading is `λᵢ⁻¹ (∂ₛ rₖ - ∂ₜ rₖ i) bₖ`.

## Main definitions

* `TauCeti.FiniteBundleAtlas.zeroOneFrame`: the chart frame of `(0,1)`-forms.
* `TauCeti.FiniteBundleAtlas.chartZeroOneZeroOrder`: the zeroth-order term in chart `i` of an
  operator from one-forms to sections, read on the chart frame of `(0,1)`-forms.
* `TauCeti.FiniteBundleAtlas.chartConformalFactor`: the conformal factor of the metric in chart `i`.

## Main results

* `TauCeti.FiniteBundleAtlas.coord_formalAdjoint_eq`: the chart form of `D*`.
* `TauCeti.FiniteBundleAtlas.eq_sum_smul_zeroOneFrame`,
  `TauCeti.FiniteBundleAtlas.formalAdjoint_eq_sum_zeroOneFrame`: a `(0,1)`-form in the chart
  frame, and the Leibniz expansion of `D*` in it.
* `TauCeti.FiniteBundleAtlas.continuousLinearMapAt_zeroOneFrame_mgradient`: the gradient term
  in a chart.
* `TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_antilinearOfOneL`: a `(0,1)`-form reads as the
  antilinear map with its value at `1`.
* `TauCeti.FiniteBundleAtlas.contDiffOn_chartZeroOneZeroOrder`,
  `TauCeti.FiniteBundleAtlas.contDiffOn_chartConformalFactor`,
  `TauCeti.FiniteBundleAtlas.chartConformalFactor_pos`: the coefficients are smooth, and the
  conformal factor is positive.
* `TauCeti.FiniteBundleAtlas.inner_eq_chartConformalFactor_mul`: for an orthogonal almost complex
  structure the metric reads as `λᵢ |dz|²`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, the formal adjoint after Lemma C.1.9.
-/

public section

noncomputable section

open Bundle Module Set Filter
open ContinuousLinearMap (antilinearOfOneL)
open scoped Manifold ContDiff Topology RealInnerProductSpace TauCeti.ComplexManifold

namespace TauCeti

namespace FiniteBundleAtlas

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneAdjoint : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [RiemannianBundle V] [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  (A : FiniteBundleAtlas ℂ M F V) (i : Fin A.n)

/-- **The chart frame of `(0,1)`-forms.** The one-form whose reading in the trivialization of
one-forms of chart `i` is the antilinear map `w ↦ conj w • bₖ` with value the `k`th vector of the
basis `Module.finBasis ℝ F` at `1`, and which vanishes off the base set of that trivialization. -/
def zeroOneFrame (k : Fin (finrank ℝ F)) : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x :=
  fun x ↦ (A.tangentHom.triv i).symmL ℝ x (antilinearOfOneL F (finBasis ℝ F k))

omit [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)] in
theorem zeroOneFrame_def (k : Fin (finrank ℝ F)) (x : M) :
    A.zeroOneFrame i k x =
      (A.tangentHom.triv i).symmL ℝ x (antilinearOfOneL F (finBasis ℝ F k)) := by
  rw [zeroOneFrame]

omit [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)] in
/-- The chart frame forms vanish off the base set of the trivialization of one-forms. -/
theorem zeroOneFrame_of_notMem (k : Fin (finrank ℝ F)) {x : M}
    (hx : x ∉ (A.tangentHom.triv i).baseSet) : A.zeroOneFrame i k x = 0 := by
  rw [zeroOneFrame_def, Trivialization.symmL_apply_of_notMem _ hx]

/-- **The zeroth-order term of an operator on one-forms in chart `i`.** For an operator `P` from
`V`-valued one-forms to sections of `V`, the map sending `v = ∑ₖ vᵏ bₖ` to `∑ₖ vᵏ • (P eₖ)ᵢ z`,
where `eₖ` is the chart frame of `(0,1)`-forms (`TauCeti.FiniteBundleAtlas.zeroOneFrame`) and
`(P eₖ)ᵢ` the reading of `P eₖ` in chart `i`. -/
def chartZeroOneZeroOrder (P : (Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) → Π x : M, V x)
    (z : ℂ) : F →L[ℝ] F :=
  ∑ k, (LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord k)).smulRight
    (A.coord i (P (A.zeroOneFrame i k)) z)

omit [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)] in
theorem chartZeroOneZeroOrder_apply
    (P : (Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) → Π x : M, V x) (z : ℂ) (v : F) :
    A.chartZeroOneZeroOrder i P z v =
      ∑ k, (finBasis ℝ F).coord k v • A.coord i (P (A.zeroOneFrame i k)) z := by
  simp [chartZeroOneZeroOrder]

omit [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)] in
/-- The chart frame of `(0,1)`-forms reads as the antilinear map with value `bₖ` at `1` at the
points read from the base set of the trivialization of one-forms. -/
theorem coord_zeroOneFrame (k : Fin (finrank ℝ F)) {y : ℂ}
    (hy : (A.chart i).symm y ∈ (A.tangentHom.triv i).baseSet) :
    A.tangentHom.coord i (A.zeroOneFrame i k) y = antilinearOfOneL F (finBasis ℝ F k) :=
  A.tangentHom.coord_symmL (i := i) hy _

omit [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)] in
/-- The chart frame of `(0,1)`-forms is smooth on the base set of the trivialization of
one-forms. -/
theorem contMDiffOn_zeroOneFrame [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (k : Fin (finrank ℝ F)) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x
        (A.zeroOneFrame i k x)) (A.tangentHom.triv i).baseSet :=
  ((A.tangentHom.triv i).contMDiffOn_section_symm (A.tangentHom.triv i).open_baseSet subset_rfl
    contMDiffOn_const).congr fun x hx ↦ by rw [zeroOneFrame_def, Trivialization.symmL_apply _ hx]

omit [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)] in
/-- The chart frame of `(0,1)`-forms consists of `(0,1)`-forms. -/
theorem isZeroOneForm_zeroOneFrame (k : Fin (finrank ℝ F)) (x : M) :
    (ofComplexManifold ℂ M).IsZeroOneForm (A.zeroOneFrame i k x) := by
  by_cases hx : x ∉ (A.tangentHom.triv i).baseSet
  · rw [A.zeroOneFrame_of_notMem i k hx]
    exact isZeroOneForm_iff.2 fun v ↦ by simp
  rw [not_not] at hx
  have hx' := A.mem_tangentHom_triv_baseSet_iff.1 hx
  have hxy : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hx'.1
  have hc := A.coord_tangentHom i (A.zeroOneFrame i k) (A.chart i x)
  rw [hxy, coord_zeroOneFrame A i k (hxy.symm ▸ hx)] at hc
  refine (isZeroOneForm_iff_inCoordinates (x₀ := A.center i) (y₀ := A.center i)
    (inTangentCoordinates_ofComplexManifold hx'.1) hx'.2).2 fun v ↦ ?_
  rw [← hc]
  exact ContinuousLinearMap.antilinearOfOneL_apply_I_smul _ v

omit [FiniteDimensional ℝ F] [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  [RiemannianBundle V] in
/-- At the points read from the base set of the trivialization of one-forms, a `(0,1)`-form reads
as the antilinear map with its value at `1`. -/
theorem coord_tangentHom_eq_antilinearOfOneL {θ : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    {y : ℂ} (hy : (A.chart i).symm y ∈ (A.tangentHom.triv i).baseSet)
    (hθ : (ofComplexManifold ℂ M).IsZeroOneForm (θ ((A.chart i).symm y))) :
    A.tangentHom.coord i θ y = antilinearOfOneL F (A.tangentHom.coord i θ y 1) := by
  have hy' := A.mem_tangentHom_triv_baseSet_iff.1 hy
  have hc := A.coord_tangentHom i θ y
  refine (ContinuousLinearMap.antilinearOfOneL_apply_eq_of_antilinear _ fun v ↦ ?_).symm
  rw [hc]
  exact (isZeroOneForm_iff_inCoordinates (x₀ := A.center i) (y₀ := A.center i)
    (inTangentCoordinates_ofComplexManifold hy'.1) hy'.2).1 hθ v

omit [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)] in
/-- **A `(0,1)`-form in the chart frame.** At a point of the base set of the trivialization of
one-forms where `θ` is a `(0,1)`-form, `θ` is `∑ₖ rₖ eₖ`, where `eₖ` is the chart frame of
`(0,1)`-forms and `rₖ` are the coordinates, in the basis `Module.finBasis ℝ F`, of the value at `1`
of the reading of `θ` at the chart point. -/
theorem eq_sum_smul_zeroOneFrame {θ : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x} {x : M}
    (hθ : (ofComplexManifold ℂ M).IsZeroOneForm (θ x)) (hx : x ∈ (A.tangentHom.triv i).baseSet) :
    θ x = (∑ k, (fun x' ↦ (finBasis ℝ F).coord k (A.tangentHom.coord i θ (A.chart i x') 1)) •
      A.zeroOneFrame i k) x := by
  have hx' := A.mem_tangentHom_triv_baseSet_iff.1 hx
  have hxy : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hx'.1
  calc θ x = (A.tangentHom.triv i).symmL ℝ x (A.tangentHom.coord i θ (A.chart i x)) :=
        (A.tangentHom.symmL_coord_chart (i := i) hx'.1 hx θ).symm
    _ = (A.tangentHom.triv i).symmL ℝ x
          (antilinearOfOneL F (A.tangentHom.coord i θ (A.chart i x) 1)) :=
        congrArg _ (coord_tangentHom_eq_antilinearOfOneL A i (hxy.symm ▸ hx) (hxy.symm ▸ hθ))
    _ = _ := by
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply', zeroOneFrame_def, ← map_smul, ← map_sum, Basis.coord_apply]
        exact congrArg _ (congrArg _ ((finBasis ℝ F).sum_repr _).symm)

/-- **The conformal factor of the metric in chart `i`.** At `z`, the squared length of the tangent
vector at the point read at `z` that the tangent trivialization at the centre of chart `i` reads as
`1`. For a metric for which `i` is orthogonal, the metric reads in chart `i` as `λᵢ z |dz|²`. -/
def chartConformalFactor (z : ℂ) : ℝ :=
  ‖(trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) (A.center i)).symmL ℝ ((A.chart i).symm z) 1‖ ^ 2

omit [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [VectorBundle ℂ F V] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, AddCommGroup (V x)] in
theorem chartConformalFactor_def (z : ℂ) :
    A.chartConformalFactor i z =
      ‖(trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) (A.center i)).symmL ℝ ((A.chart i).symm z)
        1‖ ^ 2 := by
  rw [chartConformalFactor]

omit [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [VectorBundle ℂ F V] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, AddCommGroup (V x)]
  [RiemannianBundle V] [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)] in
/-- The points read from the chart target lie in the base set of the tangent trivialization at the
centre. -/
private theorem symm_mem_tangent_baseSet {z : ℂ} (hz : z ∈ (A.chart i).target) :
    (A.chart i).symm z ∈
      (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet]
  exact (A.chart i).map_target hz

omit [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [VectorBundle ℂ F V] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, AddCommGroup (V x)] in
/-- The conformal factor is positive on the target of chart `i`. -/
theorem chartConformalFactor_pos {z : ℂ} (hz : z ∈ (A.chart i).target) :
    0 < A.chartConformalFactor i z := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)
  have hb : (A.chart i).symm z ∈ e.baseSet := A.symm_mem_tangent_baseSet i hz
  refine pow_pos (norm_pos_iff.2 fun h ↦ (one_ne_zero : (1 : ℂ) ≠ 0) ?_) 2
  have h1 := e.continuousLinearMapAt_symmL (R := ℝ) hb (1 : ℂ)
  rw [h, map_zero] at h1
  exact h1.symm

omit [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [VectorBundle ℂ F V] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, AddCommGroup (V x)]
  [RiemannianBundle V] in
/-- **The metric is conformal in a chart.** If the almost complex structure is orthogonal at the
point read at `z` in the chart target, the metric there is `λᵢ z` times the flat metric of the
readings in the tangent trivialization at the centre of chart `i`: it reads as `λᵢ z |dz|²`. -/
theorem inner_eq_chartConformalFactor_mul {z : ℂ} (hz : z ∈ (A.chart i).target)
    (hJ : ∀ u v : TangentSpace 𝓘(ℝ, ℂ) ((A.chart i).symm z),
      ⟪ofComplexManifold ℂ M _ u, ofComplexManifold ℂ M _ v⟫ = ⟪u, v⟫)
    (u w : TangentSpace 𝓘(ℝ, ℂ) ((A.chart i).symm z)) :
    ⟪u, w⟫ = A.chartConformalFactor i z *
      ⟪(trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)).continuousLinearMapAt
          ℝ ((A.chart i).symm z) u,
        (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)).continuousLinearMapAt
          ℝ ((A.chart i).symm z) w⟫ := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)
  have hb : (A.chart i).symm z ∈ e.baseSet := A.symm_mem_tangent_baseSet i hz
  have hxs : (A.chart i).symm z ∈ (chartAt ℂ (A.center i)).source := (A.chart i).map_target hz
  set a : TangentSpace 𝓘(ℝ, ℂ) ((A.chart i).symm z) := e.symmL ℝ ((A.chart i).symm z) 1
  set ja : TangentSpace 𝓘(ℝ, ℂ) ((A.chart i).symm z) := ofComplexManifold ℂ M _ a
  -- The readings `1` and `i` come from `a` and `j a`, which are orthogonal of the same length.
  have hja : e.symmL ℝ ((A.chart i).symm z) Complex.I = ja := by
    rw [← e.symmL_continuousLinearMapAt (R := ℝ) hb ja,
      continuousLinearMapAt_trivializationAt_ofComplexManifold hxs,
      e.continuousLinearMapAt_symmL (R := ℝ) hb, smul_eq_mul, mul_one]
  have hsymm (c : ℂ) : e.symmL ℝ ((A.chart i).symm z) c = c.re • a + c.im • ja := by
    have hc : c = c.re • (1 : ℂ) + c.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hc]
    rw [map_add, map_smul, map_smul, hja]
  have hjj : ⟪ja, ja⟫ = ⟪a, a⟫ := hJ a a
  have hjja : ofComplexManifold ℂ M _ ja = -a := by
    simp [ja]
  have hperp : ⟪a, ja⟫ = 0 := by
    have h := hJ a ja
    rw [hjja, inner_neg_right, real_inner_comm] at h
    linarith
  conv_lhs => rw [← e.symmL_continuousLinearMapAt (R := ℝ) hb u,
    ← e.symmL_continuousLinearMapAt (R := ℝ) hb w, hsymm, hsymm]
  rw [chartConformalFactor_def, ← real_inner_self_eq_norm_sq, Complex.inner]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hjj,
    hperp, real_inner_comm a ja, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

variable [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]

omit [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [VectorBundle ℂ F V] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, AddCommGroup (V x)] in
/-- The conformal factor is smooth on the target of chart `i`. -/
theorem contDiffOn_chartConformalFactor :
    ContDiffOn ℝ ∞ (A.chartConformalFactor i) (A.chart i).target := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)
  have hφ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (fun x ↦ ⟪e.symm x (1 : ℂ), e.symm x (1 : ℂ)⟫)
      e.baseSet := fun x hx ↦
    have hs := (e.contMDiffOn_section_symm (n := ∞) e.open_baseSet subset_rfl
      (u := fun _ ↦ (1 : ℂ)) contMDiffOn_const).contMDiffAt (e.open_baseSet.mem_nhds hx)
    (hs.inner_bundle hs).contMDiffWithinAt
  rw [← contMDiffOn_iff_contDiffOn]
  refine (hφ.comp contMDiffOn_chart_symm fun z hz ↦ A.symm_mem_tangent_baseSet i hz).congr
    fun z hz ↦ ?_
  simp only [chartConformalFactor_def, Function.comp_apply, real_inner_self_eq_norm_sq]
  rw [Trivialization.symmL_apply _ (A.symm_mem_tangent_baseSet i hz)]

/-! ### The formal adjoint in a chart -/

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V] [∀ x, ContinuousSMul ℂ (V x)] [T2Space M]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (cov : _root_.CovariantDerivative 𝓘(ℝ, ℂ) F V)

omit [T2Space M] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V]
  [∀ x, ContinuousSMul ℂ (V x)] [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x]
  [FiniteDimensional ℝ F]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x] in
/-- The value at `1` of the reading of a smooth one-form is differentiable where the
trivialization of one-forms is defined. -/
theorem differentiableAt_coord_apply_one {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
      TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    {y : ℂ} (hy : y ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.tangentHom.triv i).baseSet) :
    DifferentiableAt ℝ (fun z ↦ A.tangentHom.coord i η z 1) y :=
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  (((A.tangentHom.contDiffOn_coord hη i).clm_apply
    (contDiffOn_const (c := (1 : ℂ)))).differentiableOn (by simp)).differentiableAt
      (((A.chart i).isOpen_inter_preimage_symm (A.tangentHom.triv i).open_baseSet).mem_nhds hy)

omit [T2Space M] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V]
  [∀ x, ContinuousSMul ℂ (V x)] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x] in
/-- At the point read at `y` in the chart image, the chart frame form `eₖ` applied to a tangent
vector `w` reads as `conj (wᵢ) • bₖ`, `wᵢ` the reading of `w` in the tangent trivialization. -/
private theorem continuousLinearMapAt_zeroOneFrame_apply {y : ℂ} (hy : y ∈ A.image i)
    (k : Fin (finrank ℝ F)) (w : TangentSpace 𝓘(ℝ, ℂ) ((A.chart i).symm y)) :
    (A.triv i).continuousLinearMapAt ℝ ((A.chart i).symm y) (A.zeroOneFrame i k _ w) =
      antilinearOfOneL F (finBasis ℝ F k)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)).continuousLinearMapAt
          ℝ ((A.chart i).symm y) w) := by
  have hx : (A.chart i).symm y ∈ A.dom i := A.symm_mem_dom hy
  have h := A.coord_tangentHom_apply i (A.zeroOneFrame i k) (fun _ ↦ w) hy
  have h1 : A.tangent.coord i (fun _ ↦ w) y =
      (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)).continuousLinearMapAt
        ℝ ((A.chart i).symm y) w :=
    A.tangent.coord_eq_continuousLinearMapAt (i := i)
      (A.symm_mem_tangent_baseSet i (A.image_subset_target_inter_preimage_baseSet i hy).1) _
  have h2 : A.coord i (fun x' ↦ A.zeroOneFrame i k x' w) y =
      (A.triv i).continuousLinearMapAt ℝ ((A.chart i).symm y) (A.zeroOneFrame i k _ w) :=
    A.coord_eq_continuousLinearMapAt (i := i) (A.dom_subset_baseSet i hx) _
  rw [coord_zeroOneFrame A i k (A.tangentHom.dom_subset_baseSet i hx), h1, h2] at h
  exact h.symm

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V] [T2Space M] [∀ x, ContinuousSMul ℂ (V x)]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x] in
/-- **The gradient term in a chart.** At the point `x` read at `y` in the image of chart `i`, for a
function `g` on the chart differentiable at `y` and an orthogonal almost complex structure, the
chart frame form `eₖ` applied to the gradient of `g` read through the chart reads as
`λᵢ⁻¹ (∂ₛ g • bₖ - ∂ₜ g • i • bₖ)`, `λᵢ` the conformal factor. -/
theorem continuousLinearMapAt_zeroOneFrame_mgradient
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    {y : ℂ} (hy : y ∈ A.image i) {g : ℂ → ℝ} (hg : DifferentiableAt ℝ g y)
    (k : Fin (finrank ℝ F)) :
    (A.triv i).continuousLinearMapAt ℝ ((A.chart i).symm y)
        (A.zeroOneFrame i k ((A.chart i).symm y)
          (TauCeti.Manifold.mgradient 𝓘(ℝ, ℂ) (fun x' ↦ g (A.chart i x')) ((A.chart i).symm y))) =
      (A.chartConformalFactor i y)⁻¹ •
        (fderiv ℝ g y 1 • finBasis ℝ F k -
          fderiv ℝ g y Complex.I • Complex.I • finBasis ℝ F k) := by
  set x := (A.chart i).symm y
  set Tt := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : M → Type _) (A.center i)
  set L := (A.triv i).continuousLinearMapAt ℝ x
  have hx : x ∈ A.dom i := A.symm_mem_dom hy
  have hxs : x ∈ (A.chart i).source := A.dom_subset_chart_source i hx
  have hxT : x ∈ Tt.baseSet := by rwa [TangentBundle.trivializationAt_baseSet]
  have hxV : x ∈ (A.triv i).baseSet := A.dom_subset_baseSet i hx
  have hxe : x ∈ (A.tangentHom.triv i).baseSet := A.tangentHom.dom_subset_baseSet i hx
  have hyx : A.chart i x = y :=
    (A.chart i).right_inv (A.image_subset_target_inter_preimage_baseSet i hy).1
  -- The unit tangent vector `v` in the direction read as `1`.
  set a : TangentSpace 𝓘(ℝ, ℂ) x := Tt.symmL ℝ x 1
  have hTa : Tt.continuousLinearMapAt ℝ x a = 1 := Tt.continuousLinearMapAt_symmL hxT 1
  have ha : a ≠ 0 := fun h ↦ one_ne_zero (by rw [← hTa, h, map_zero] : (0 : ℂ) = 1).symm
  set v : TangentSpace 𝓘(ℝ, ℂ) x := ‖a‖⁻¹ • a
  have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) ha
  have hTv : Tt.continuousLinearMapAt ℝ x v = ((‖a‖⁻¹ : ℝ) : ℂ) := by
    rw [map_smul, hTa, Complex.real_smul, mul_one]
  clear_value v
  have hE := continuousLinearMapAt_zeroOneFrame_apply A i hy k
  have hI (u : V x) : L (Complex.I • u) = Complex.I • L u := by
    simp only [L]
    rw [Trivialization.coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt ℝ ℂ, map_smul]
  -- The derivatives of `g` through the chart.
  have hg' : DifferentiableAt ℝ g (chartAt ℂ (A.center i) x) := by rwa [← hyx] at hg
  have hd (w : TangentSpace 𝓘(ℝ, ℂ) x) :
      mvfderiv 𝓘(ℝ, ℂ) (fun x' ↦ g (A.chart i x')) x w =
        fderiv ℝ g y (Tt.continuousLinearMapAt ℝ x w) := by
    rw [mvfderiv_comp_chartAt_apply hxs hg', hyx]
  have hgrad := SmoothAlmostComplexStructure.IsZeroOneForm.apply_mgradient
    (A.isZeroOneForm_zeroOneFrame i k x) (hJ x)
    Complex.finrank_real_complex hv (fun x' ↦ g (A.chart i x'))
  have h1 : mvfderiv 𝓘(ℝ, ℂ) (fun x' ↦ g (A.chart i x')) x v = ‖a‖⁻¹ * fderiv ℝ g y 1 := by
    rw [hd, hTv, show ((‖a‖⁻¹ : ℝ) : ℂ) = ‖a‖⁻¹ • (1 : ℂ) by simp, map_smul, smul_eq_mul]
  have h2 : mvfderiv 𝓘(ℝ, ℂ) (fun x' ↦ g (A.chart i x')) x (ofComplexManifold ℂ M x v) =
      ‖a‖⁻¹ * fderiv ℝ g y Complex.I := by
    rw [hd, continuousLinearMapAt_trivializationAt_ofComplexManifold hxs, hTv,
      show Complex.I • ((‖a‖⁻¹ : ℝ) : ℂ) = ‖a‖⁻¹ • Complex.I by
        rw [Complex.real_smul, smul_eq_mul, mul_comm], map_smul, smul_eq_mul]
  have h3 : L (A.zeroOneFrame i k x v) = ‖a‖⁻¹ • finBasis ℝ F k := by
    rw [hE, hTv]
    simp only [ContinuousLinearMap.antilinearOfOneL_apply_apply, Complex.conj_ofReal]
    exact algebraMap_smul ℂ (‖a‖⁻¹ : ℝ) (finBasis ℝ F k)
  rw [hgrad, h1, h2, map_sub, map_smul, map_smul, hI, h3, chartConformalFactor_def, smul_sub,
    smul_comm Complex.I (‖a‖⁻¹ : ℝ), smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V] [T2Space M] in
/-- **Leibniz expansion of `D*` in the chart frame.** Over the base set of the trivialization of
one-forms, for a smooth `(0,1)`-form `η` with coordinates `rₖ` in the chart frame `eₖ`,
`D* η = ∑ₖ (rₖ D* eₖ - eₖ (grad rₖ))`. -/
theorem formalAdjoint_eq_sum_zeroOneFrame {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
      TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    (hη01 : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x)) {x : M}
    (hx : x ∈ (A.tangentHom.triv i).baseSet) :
    hD.formalAdjoint cov η x = ∑ k,
      ((finBasis ℝ F).coord k (A.tangentHom.coord i η (A.chart i x) 1) •
          hD.formalAdjoint cov (A.zeroOneFrame i k) x -
        A.zeroOneFrame i k x (TauCeti.Manifold.mgradient 𝓘(ℝ, ℂ)
          (fun x' ↦ (finBasis ℝ F).coord k (A.tangentHom.coord i η (A.chart i x') 1)) x)) := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  set R : Fin (finrank ℝ F) → M → ℝ :=
    fun k x' ↦ (finBasis ℝ F).coord k (A.tangentHom.coord i η (A.chart i x') 1)
  have hx' := A.mem_tangentHom_triv_baseSet_iff.1 hx
  -- The coordinates are differentiable at `x`, read through the chart.
  have hyU :
      A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.tangentHom.triv i).baseSet :=
    ⟨(A.chart i).map_source hx'.1, by rwa [mem_preimage, (A.chart i).left_inv hx'.1]⟩
  have hR (k : Fin (finrank ℝ F)) : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ) (R k) x := by
    have hc : DifferentiableAt ℝ (fun z ↦ (finBasis ℝ F).coord k (A.tangentHom.coord i η z 1))
        (A.chart i x) :=
      (LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord k)).differentiableAt.comp _
        (A.differentiableAt_coord_apply_one i hη hyU)
    have hch : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) (A.center i)) x :=
      mdifferentiableAt_extChartAt hx'.1
    exact (hc.mdifferentiableAt.comp x (by simpa using hch) : _)
  have hE (k : Fin (finrank ℝ F)) := ((A.contMDiffOn_zeroOneFrame i k).contMDiffAt
    ((A.tangentHom.triv i).open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hRE (k : Fin (finrank ℝ F)) := (hR k).smul_section (hE k)
  have hev : ∀ᶠ x' in 𝓝 x, η x' = (∑ k, R k • A.zeroOneFrame i k) x' :=
    eventually_of_mem ((A.tangentHom.triv i).open_baseSet.mem_nhds hx) fun x' hx'' ↦
      eq_sum_smul_zeroOneFrame A i (hη01 x') hx''
  rw [hD.formalAdjoint_congr_of_eventuallyEq cov hev,
    hD.formalAdjoint_sum cov _ fun k _ ↦ hRE k]
  exact Finset.sum_congr rfl fun k _ ↦ hD.formalAdjoint_smul cov (hR k) (hE k)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V] [T2Space M] in
/-- **The formal adjoint in a chart** (McDuff–Salamon, Appendix C.1, `D*` as an operator of
`∂`-type). For an orthogonal almost complex structure, a smooth `(0,1)`-form `η` and `y` in the
image of chart `i`, with `r z = ηᵢ(z)(1)` the values at `1` of the readings of `η`,

`(D* η)ᵢ(y) = Kᵢ(y) (r y) - λᵢ(y)⁻¹ (∂ₛ r(y) - i ∂ₜ r(y))`,

where `Kᵢ` is the zeroth-order term of `D*` in chart `i`
(`TauCeti.FiniteBundleAtlas.chartZeroOneZeroOrder`) and `λᵢ` the conformal factor of the metric
(`TauCeti.FiniteBundleAtlas.chartConformalFactor`). -/
theorem coord_formalAdjoint_eq
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
      TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    (hη01 : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x)) {y : ℂ} (hy : y ∈ A.image i) :
    A.coord i (hD.formalAdjoint cov η) y =
      A.chartZeroOneZeroOrder i (hD.formalAdjoint cov) y (A.tangentHom.coord i η y 1) -
        (A.chartConformalFactor i y)⁻¹ •
          (fderiv ℝ (fun z ↦ A.tangentHom.coord i η z 1) y 1 -
            Complex.I • fderiv ℝ (fun z ↦ A.tangentHom.coord i η z 1) y Complex.I) := by
  set x := (A.chart i).symm y
  set r : ℂ → F := fun z ↦ A.tangentHom.coord i η z 1
  set b := finBasis ℝ F
  have hx : x ∈ A.dom i := A.symm_mem_dom hy
  have hxV : x ∈ (A.triv i).baseSet := A.dom_subset_baseSet i hx
  have hxe : x ∈ (A.tangentHom.triv i).baseSet := A.tangentHom.dom_subset_baseSet i hx
  have hyt : y ∈ (A.chart i).target := (A.image_subset_target_inter_preimage_baseSet i hy).1
  have hyx : A.chart i x = y := (A.chart i).right_inv hyt
  have hrd : DifferentiableAt ℝ r y := A.differentiableAt_coord_apply_one i hη ⟨hyt, hxe⟩
  -- Each term of the Leibniz expansion, read in chart `i`.
  have hterm (k : Fin (finrank ℝ F)) :
      (A.triv i).continuousLinearMapAt ℝ x
          (b.coord k (A.tangentHom.coord i η (A.chart i x) 1) •
              hD.formalAdjoint cov (A.zeroOneFrame i k) x -
            A.zeroOneFrame i k x (TauCeti.Manifold.mgradient 𝓘(ℝ, ℂ)
              (fun x' ↦ b.coord k (A.tangentHom.coord i η (A.chart i x') 1)) x)) =
        b.coord k (r y) • A.coord i (hD.formalAdjoint cov (A.zeroOneFrame i k)) y -
          (A.chartConformalFactor i y)⁻¹ •
            (b.coord k (fderiv ℝ r y 1) • b k -
              b.coord k (fderiv ℝ r y Complex.I) • Complex.I • b k) := by
    set c := LinearMap.toContinuousLinearMap (b.coord k)
    have hg : DifferentiableAt ℝ (fun z ↦ c (r z)) y := c.differentiableAt.comp y hrd
    have hfd : fderiv ℝ (fun z ↦ c (r z)) y = c.comp (fderiv ℝ r y) :=
      (c.hasFDerivAt.comp y hrd.hasFDerivAt).fderiv
    have hgrad := A.continuousLinearMapAt_zeroOneFrame_mgradient i hJ hy hg k
    rw [hfd] at hgrad
    have hK : (A.triv i).continuousLinearMapAt ℝ x (hD.formalAdjoint cov (A.zeroOneFrame i k) x) =
        A.coord i (hD.formalAdjoint cov (A.zeroOneFrame i k)) y :=
      (A.coord_eq_continuousLinearMapAt (i := i) hxV _).symm
    have hc : A.tangentHom.coord i η (A.chart i x) 1 = r y :=
      congrArg (fun t ↦ A.tangentHom.coord i η t 1) hyx
    rw [map_sub, map_smul, hK, hc]
    exact congrArg _ hgrad
  rw [A.coord_eq_continuousLinearMapAt (i := i) hxV _,
    A.formalAdjoint_eq_sum_zeroOneFrame i hD cov hη hη01 hxe, map_sum,
    Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_sub_distrib, chartZeroOneZeroOrder_apply,
    ← Finset.smul_sum, Finset.sum_sub_distrib]
  simp only [Basis.coord_apply, b.sum_repr]
  conv_rhs => rw [← b.sum_repr (fderiv ℝ r y Complex.I), Finset.smul_sum]
  exact congrArg _ (congrArg _ (congrArg _ (Finset.sum_congr rfl fun k _ ↦ smul_comm _ _ _)))

/-- **Smoothness of the zeroth-order term of `D*`.** For compatible metrics and a smooth connection,
the zeroth-order term of the formal adjoint of a smooth real Cauchy–Riemann operator in chart `i` is
smooth on the points of the chart target read from the base set of the trivialization of
one-forms, an open set containing the closure of the chart image. -/
theorem contDiffOn_chartZeroOneZeroOrder
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    ContDiffOn ℝ ∞ (A.chartZeroOneZeroOrder i (hD.formalAdjoint cov))
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.tangentHom.triv i).baseSet) := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  refine ContDiffOn.sum fun k _ ↦ contDiffOn_const.smulRight ?_
  intro y₀ hy₀
  -- Cut the frame form off near the point; `D*` of the cut-off form is smooth, and agrees with
  -- `D*` of the frame form near the point.
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℂ))
    ((A.chart i).symm y₀)).mem_iff.mp ((A.tangentHom.triv i).open_baseSet.mem_nhds hy₀.2)
  set η₀ := (ρ : M → ℝ) • A.zeroOneFrame i k
  have hη₀ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
      TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η₀ x) :=
    ρ.contMDiff.contMDiffOn.smul_section_of_tsupport (A.tangentHom.triv i).open_baseSet hρ
      (A.contMDiffOn_zeroOneFrame i k)
  have hη₀01 (x : M) : (ofComplexManifold ℂ M).IsZeroOneForm (η₀ x) := by
    refine isZeroOneForm_iff.2 fun v ↦ ?_
    simp only [η₀, Pi.smul_apply', smul_apply,
      isZeroOneForm_iff.1 (A.isZeroOneForm_zeroOneFrame i k x) v, smul_neg,
      smul_comm (ρ x) Complex.I]
  have hc := A.contDiffOn_coord (hD.contMDiff_formalAdjoint cov hDs hJ hV hη₀ hη₀01) i
  have hb : (A.chart i).symm y₀ ∈ (A.triv i).baseSet :=
    (A.mem_tangentHom_triv_baseSet_iff.1 hy₀.2).2
  have hU : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet ∈ 𝓝 y₀ :=
    ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet).mem_nhds ⟨hy₀.1, hb⟩
  have hsymm := ((A.chart i).continuousAt_symm hy₀.1).tendsto
  have hev : A.coord i (hD.formalAdjoint cov η₀) =ᶠ[𝓝 y₀]
      A.coord i (hD.formalAdjoint cov (A.zeroOneFrame i k)) := by
    filter_upwards [hsymm.eventually ρ.eventuallyEq_one.eventually_nhds] with z hz1
    have h := hD.formalAdjoint_congr_of_eventuallyEq cov (η := η₀) (η' := A.zeroOneFrame i k)
      (hz1.mono fun x hx ↦ by simp [η₀, hx])
    rw [coord_def, coord_def, h]
  exact ((hc.contDiffAt hU).congr_of_eventuallyEq hev.symm).contDiffWithinAt


end FiniteBundleAtlas

end TauCeti
