/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Finrank

/-!
# Inhomogeneous terms in charts

Let `ν` be an inhomogeneous term for an almost complex structure `j` on a manifold `P` and a
domain-dependent almost complex structure `J` on a manifold `M`. Read in a chart `φ` of `P` with
values in `ℂ` and a chart `ψ` of `M` with values in a normed space, it becomes the map
`η(z, v) = 2 dψ (ν(φ⁻¹ z, ψ⁻¹ v)(dφ⁻¹ 1))`: twice the value of `ν` on the coordinate vector
`∂ₛ = dφ⁻¹ 1`, pushed forward along `ψ`. This is the right-hand side of the coordinate form
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` of the inhomogeneous Cauchy–Riemann equation
`du + J(z, u) ∘ du ∘ j = 2ν(z, u)`, used to define weak pseudoholomorphic maps chart by chart.

On a Riemann surface, whose tangent spaces are `ℂ` with `j` acting as multiplication by `i`, an
inhomogeneous term is determined at each point by its value on `1`, by complex antilinearity.
So the equation tested on `∂ₛ` alone loses no information.

## Main declarations

* `TauCeti.InhomogeneousTerm.chartTerm`: an inhomogeneous term read in charts, with its
  interaction with the module operations, with regularity downgrades, with replacing the
  structures by equal ones and with identity charts.
* `TauCeti.InhomogeneousTerm.chartTermExtend`: an inhomogeneous term read in an extended chart
  `φ.extend IQ` of a domain modelled on `ℂ`, possibly with corners such as a Riemann surface with
  boundary, with the same API as `chartTerm`;
  `TauCeti.InhomogeneousTerm.chartTermExtend_apply_eq_chartTerm_apply` compares it with
  `chartTerm` at interior points of the model range.
* `TauCeti.InhomogeneousTerm.chartTerm_symm_trans_apply`: under a change of chart of `M`, the
  term read in charts is transported by the derivative of the transition.
* `TauCeti.InhomogeneousTerm.chartTerm_eq_re_smul_sub_im_smul`: on a Riemann surface, under a
  change of holomorphic chart with transition derivative `a + b i`, the term read in charts
  becomes `a η - b J η`.
* `TauCeti.InhomogeneousTerm.chartTerm_apply_eq_zero_iff`: the term read in charts vanishes at a
  point exactly when the term vanishes on `∂ₛ` there.
* `TauCeti.InhomogeneousTerm.contDiffOn_chartTerm_chartAt`: over a domain modelled on `ℂ`, in
  the preferred charts and on a boundaryless target, the term read in charts is jointly `Cⁿ` on
  the product of the chart targets. It is twice the term read in the tangent trivializations,
  applied to `1` (`TauCeti.InhomogeneousTerm.chartTerm_chartAt`), and that reading is `Cⁿ` on
  the product of the chart sources (`TauCeti.DomainDependentHomSection.contMDiffOn_inCoordinates`).
* `TauCeti.InhomogeneousTerm.contDiffOn_chartTermExtend_chartAt`: over a domain modelled on `ℂ`
  with corners, such as a Riemann surface with boundary, the term read in the preferred extended
  charts is jointly `Cⁿ` on the product of the extended chart targets, which is regularity up to
  the boundary (`TauCeti.InhomogeneousTerm.chartTermExtend_chartAt` is the reading in the
  tangent trivializations).
* `TauCeti.InhomogeneousTerm.tangentHom_eq_zero_iff_apply_eq_zero`: over a two-dimensional domain,
  an inhomogeneous term vanishes at a point exactly when it vanishes on one nonzero tangent vector
  there; `TauCeti.InhomogeneousTerm.tangentHom_eq_zero_iff_apply_one_eq_zero` is the case of the
  vector `1` over a domain modelled on `ℂ`, such as a Riemann surface.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (inhomogeneous Cauchy--Riemann equations).
-/

public section

noncomputable section

open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

namespace TauCeti

namespace InhomogeneousTerm

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n m : ℕ∞}
  {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I M IP P n}

/-- An inhomogeneous term read in a chart `φ` of `P` with values in `ℂ` and a chart `ψ` of `M`
with values in a normed space `G`: at `(z, v)`, twice the value of `ν(φ⁻¹ z, ψ⁻¹ v)` on the
coordinate vector `∂ₛ = dφ⁻¹ 1`, pushed forward along `ψ` (by its derivative read in `G`,
`mvfderiv`). This is the right-hand side `η` of the coordinate equation
`∂ₛu + J(z, u) ∂ₜu = η(z, u)`. -/
def chartTerm (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) (z : ℂ) (v : G) : G :=
  (2 : ℝ) • mvfderiv I ψ (ψ.symm v)
    (ν.val.tangentHom (φ.symm z, ψ.symm v) (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ)))

/-- Evaluate an inhomogeneous term read in charts. -/
theorem chartTerm_apply (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) (z : ℂ) (v : G) :
    ν.chartTerm φ ψ z v = (2 : ℝ) • mvfderiv I ψ (ψ.symm v)
      (ν.val.tangentHom (φ.symm z, ψ.symm v) (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ))) :=
  (rfl)

/-- The zero inhomogeneous term reads as zero in all charts. -/
@[simp]
theorem chartTerm_zero (φ : OpenPartialHomeomorph P ℂ) (ψ : OpenPartialHomeomorph M G) :
    (0 : InhomogeneousTerm j J).chartTerm φ ψ = fun _ _ ↦ 0 := by
  funext z v
  -- Keep `mvfderiv`, valued in `G`, rather than `mfderiv`, valued in a tangent space of `G`,
  -- so that the module laws simp applies are those of `G`; likewise below.
  simp [chartTerm_apply, -mvfderiv_apply_eq_mfderiv_apply]

/-- Reading in charts is additive in the inhomogeneous term. -/
@[simp]
theorem chartTerm_add (ν μ : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) :
    (ν + μ).chartTerm φ ψ = ν.chartTerm φ ψ + μ.chartTerm φ ψ := by
  funext z v
  simp [chartTerm_apply, -mvfderiv_apply_eq_mfderiv_apply]

/-- Reading in charts commutes with real scalar multiplication of the inhomogeneous term. -/
@[simp]
theorem chartTerm_smul (c : ℝ) (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) :
    (c • ν).chartTerm φ ψ = c • ν.chartTerm φ ψ := by
  funext z v
  simp [chartTerm_apply, -mvfderiv_apply_eq_mfderiv_apply, smul_smul, mul_comm]

/-- Reading in charts commutes with negation of the inhomogeneous term. -/
@[simp]
theorem chartTerm_neg (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) :
    (-ν).chartTerm φ ψ = -ν.chartTerm φ ψ := by
  rw [← neg_one_smul ℝ ν, chartTerm_smul, neg_one_smul]

/-- Reading in charts commutes with subtraction of inhomogeneous terms. -/
@[simp]
theorem chartTerm_sub (ν μ : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) :
    (ν - μ).chartTerm φ ψ = ν.chartTerm φ ψ - μ.chartTerm φ ψ := by
  rw [sub_eq_add_neg, chartTerm_add, chartTerm_neg, sub_eq_add_neg]

/-- Forgetting regularity does not change an inhomogeneous term read in charts. -/
@[simp]
theorem chartTerm_ofLE (ν : InhomogeneousTerm j J) (hmn : m ≤ n)
    (φ : OpenPartialHomeomorph P ℂ) (ψ : OpenPartialHomeomorph M G) :
    (ν.ofLE hmn).chartTerm φ ψ = ν.chartTerm φ ψ := by
  funext z v
  simp [chartTerm_apply]

/-- Replacing the structures of an inhomogeneous term by equal ones does not change it read in
charts. -/
@[simp]
theorem chartTerm_ofEq (ν : InhomogeneousTerm j J) {j' : ContMDiffAlmostComplexStructure IP n P}
    {J' : ContMDiffAlmostComplexStructureFamily I M IP P n} (hj : j = j') (hJ : J = J')
    (φ : OpenPartialHomeomorph P ℂ) (ψ : OpenPartialHomeomorph M G) :
    (ν.ofEq hj hJ).chartTerm φ ψ = ν.chartTerm φ ψ := by
  funext z v
  rw [chartTerm_apply, chartTerm_apply, ofEq_val]

/-- On a normed space, read in the identity chart, an inhomogeneous term is twice its value on
`∂ₛ` at the domain point `φ⁻¹ z`. -/
@[simp]
theorem chartTerm_refl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, F) F IP P n} (ν : InhomogeneousTerm j J)
    (φ : OpenPartialHomeomorph P ℂ) :
    ν.chartTerm φ (OpenPartialHomeomorph.refl F) = fun z v ↦
      (2 : ℝ) • (ν.val.tangentHom (φ.symm z, v) (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ)) : F) := by
  funext z v
  rw [chartTerm_apply]
  generalize mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ) = w
  rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq,
    mvfderiv_eq_fderiv_apply, fderiv_id]
  -- The identity of `F` fixes the tangent vector, read as a vector of `F`.
  rfl

/-- **Changing the chart of the target.** For two charts `ψ₁` and `ψ₂` of `M` with values in
normed spaces and a point `w` of the source of the transition `Θ = ψ₂ ∘ ψ₁⁻¹`, the term read in `φ`
and `ψ₂` at `(z, Θ w)` is the derivative of `Θ` at `w` applied to the term read in `φ` and `ψ₁`
at `(z, w)`, provided `ψ₁` is differentiable at `ψ₁⁻¹ w` and `Θ` at `w`. -/
theorem chartTerm_symm_trans_apply (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (z : ℂ) {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {ψ₁ : OpenPartialHomeomorph M G} {ψ₂ : OpenPartialHomeomorph M G'} {w : G}
    (hw : w ∈ (ψ₁.symm.trans ψ₂).source)
    (hψ₁ : MDifferentiableAt I 𝓘(ℝ, G) ψ₁ (ψ₁.symm w))
    (hΘ : DifferentiableAt ℝ (ψ₁.symm.trans ψ₂) w) :
    ν.chartTerm φ ψ₂ z (ψ₁.symm.trans ψ₂ w) =
      fderiv ℝ (ψ₁.symm.trans ψ₂) w (ν.chartTerm φ ψ₁ z w) := by
  have hw' : w ∈ ψ₁.target ∧ ψ₁.symm w ∈ ψ₂.source := by simpa using hw
  have hy : ψ₂.symm (ψ₁.symm.trans ψ₂ w) = ψ₁.symm w := by simp [ψ₂.left_inv hw'.2]
  rw [chartTerm_apply, chartTerm_apply, hy, ψ₁.mvfderiv_eq_fderiv_symm_trans_comp hw hψ₁ hΘ,
    ContinuousLinearMap.comp_apply, map_smul]

/-- An inhomogeneous term read in charts vanishes at the value `ψ y` exactly when the term at
`(φ⁻¹ z, y)` vanishes on `∂ₛ = dφ⁻¹ 1`, for a chart `ψ` differentiable at `y` with inverse
differentiable at `ψ y`. -/
theorem chartTerm_apply_eq_zero_iff (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    {ψ : OpenPartialHomeomorph M G} {y : M} (hy : y ∈ ψ.source)
    (hψ : MDifferentiableAt I 𝓘(ℝ, G) ψ y) (hψs : MDifferentiableAt 𝓘(ℝ, G) I ψ.symm (ψ y))
    (z : ℂ) :
    ν.chartTerm φ ψ z (ψ y) = 0 ↔
      ν.val.tangentHom (φ.symm z, y) (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ)) = 0 := by
  -- The chart derivative is injective, with left inverse the derivative of `ψ.symm`.
  have hinv := ψ.mfderiv_symm_apply_mfderiv_apply hy hψ hψs
  rw [chartTerm_apply, ψ.left_inv hy]
  generalize ν.val.tangentHom (φ.symm z, y) (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ)) = w
  rw [smul_eq_zero, or_iff_right two_ne_zero, mvfderiv_apply_eq_mfderiv_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; exact map_zero _⟩
  rw [← hinv w, h]
  exact map_zero _

/-- Over a domain of real dimension two, an inhomogeneous term vanishes at a point exactly when
it vanishes on one nonzero tangent vector there, such as the coordinate vector `∂ₛ` of a chart. -/
theorem tangentHom_eq_zero_iff_apply_eq_zero (ν : InhomogeneousTerm j J)
    (hEP : Module.finrank ℝ EP = 2) (q : P × M) {v : TangentSpace IP q.1} (hv : v ≠ 0) :
    ν.val.tangentHom q = 0 ↔ ν.val.tangentHom q v = 0 := by
  -- The zero map vanishes on `v`.
  refine ⟨fun h ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  -- By complex antilinearity, the value on `j v` is `-J` applied to the value on `v`.
  have hjv : ν.val.tangentHom q (j.almostComplexStructureAt q.1 v) = 0 := by
    rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply, ν.tangentHom_apply_j, h,
      map_zero, neg_zero]
  -- In real dimension two, `v` and `j v` span the tangent space.
  refine ContinuousLinearMap.coe_injective (LinearMap.ext_on
    ((j.almostComplexStructureAt q.1).span_pair_eq_top_of_finrank_eq_two hEP hv) ?_)
  rintro w (rfl | rfl)
  · exact h
  · simpa using hjv

/-- Over a domain modelled on `ℂ`, such as a Riemann surface, an inhomogeneous term vanishes at a
point exactly when it vanishes on the unit vector `1` of the model tangent space there, the
coordinate vector `∂ₛ` of the preferred chart. -/
theorem tangentHom_eq_zero_iff_apply_one_eq_zero {HX X : Type*} [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ ℂ HX} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]
    {jX : ContMDiffAlmostComplexStructure IX n X}
    {J : ContMDiffAlmostComplexStructureFamily I M IX X n} (ν : InhomogeneousTerm jX J)
    (q : X × M) : ν.val.tangentHom q = 0 ↔ ν.val.tangentHom q (1 : ℂ) = 0 :=
  ν.tangentHom_eq_zero_iff_apply_eq_zero Complex.finrank_real_complex q
    (one_ne_zero : (1 : ℂ) ≠ 0)

/-! ### Extended charts of domains with corners -/

section Extend

variable {HQ Q : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ ℂ HQ} [TopologicalSpace Q]
  [ChartedSpace HQ Q] [IsManifold IQ ∞ Q] {jQ : ContMDiffAlmostComplexStructure IQ n Q}
  {JQ : ContMDiffAlmostComplexStructureFamily I M IQ Q n}

/-- An inhomogeneous term read in an extended chart `φ.extend IQ` of a domain `Q` modelled on `ℂ`,
possibly with corners, and a chart `ψ` of `M` with values in a normed space `G`: at `(z, v)`,
twice the value of `ν((φ.extend IQ)⁻¹ z, ψ⁻¹ v)` on the coordinate vector `∂ₛ`, the image of `1`
under the derivative of `(φ.extend IQ)⁻¹` within the range of the model, pushed forward along `ψ`.
At points of the interior of the range it is `chartTerm` for any chart into `ℂ` with the same
inverse near the point (`chartTermExtend_apply_eq_chartTerm_apply`). -/
def chartTermExtend (ν : InhomogeneousTerm jQ JQ) (φ : OpenPartialHomeomorph Q HQ)
    (ψ : OpenPartialHomeomorph M G) (z : ℂ) (v : G) : G :=
  (2 : ℝ) • mvfderiv I ψ (ψ.symm v)
    (ν.val.tangentHom ((φ.extend IQ).symm z, ψ.symm v)
      (mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ)))

/-- Evaluate an inhomogeneous term read in an extended chart. -/
theorem chartTermExtend_apply (ν : InhomogeneousTerm jQ JQ) (φ : OpenPartialHomeomorph Q HQ)
    (ψ : OpenPartialHomeomorph M G) (z : ℂ) (v : G) :
    ν.chartTermExtend φ ψ z v = (2 : ℝ) • mvfderiv I ψ (ψ.symm v)
      (ν.val.tangentHom ((φ.extend IQ).symm z, ψ.symm v)
        (mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ))) :=
  (rfl)

/-- The zero inhomogeneous term reads as zero in all extended charts. -/
@[simp]
theorem chartTermExtend_zero (φ : OpenPartialHomeomorph Q HQ) (ψ : OpenPartialHomeomorph M G) :
    (0 : InhomogeneousTerm jQ JQ).chartTermExtend φ ψ = fun _ _ ↦ 0 := by
  funext z v
  rw [chartTermExtend_apply]
  -- Name the domain point, so that simp does not unfold the extended chart in the tangent spaces.
  generalize mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ) = w
  generalize (φ.extend IQ).symm z = x at w ⊢
  simp [-mvfderiv_apply_eq_mfderiv_apply]

/-- Reading in extended charts is additive in the inhomogeneous term. -/
@[simp]
theorem chartTermExtend_add (ν μ : InhomogeneousTerm jQ JQ) (φ : OpenPartialHomeomorph Q HQ)
    (ψ : OpenPartialHomeomorph M G) :
    (ν + μ).chartTermExtend φ ψ = ν.chartTermExtend φ ψ + μ.chartTermExtend φ ψ := by
  funext z v
  simp only [Pi.add_apply, chartTermExtend_apply]
  -- Name the domain point, so that simp does not unfold the extended chart in the tangent spaces.
  generalize mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ) = w
  generalize (φ.extend IQ).symm z = x at w ⊢
  simp [-mvfderiv_apply_eq_mfderiv_apply]

/-- Reading in extended charts commutes with real scalar multiplication of the inhomogeneous
term. -/
@[simp]
theorem chartTermExtend_smul (c : ℝ) (ν : InhomogeneousTerm jQ JQ)
    (φ : OpenPartialHomeomorph Q HQ) (ψ : OpenPartialHomeomorph M G) :
    (c • ν).chartTermExtend φ ψ = c • ν.chartTermExtend φ ψ := by
  funext z v
  simp only [Pi.smul_apply, chartTermExtend_apply]
  -- Name the domain point, so that simp does not unfold the extended chart in the tangent spaces.
  generalize mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ) = w
  generalize (φ.extend IQ).symm z = x at w ⊢
  simp [-mvfderiv_apply_eq_mfderiv_apply, smul_smul, mul_comm]

/-- Reading in extended charts commutes with negation of the inhomogeneous term. -/
@[simp]
theorem chartTermExtend_neg (ν : InhomogeneousTerm jQ JQ) (φ : OpenPartialHomeomorph Q HQ)
    (ψ : OpenPartialHomeomorph M G) :
    (-ν).chartTermExtend φ ψ = -ν.chartTermExtend φ ψ := by
  rw [← neg_one_smul ℝ ν, chartTermExtend_smul, neg_one_smul]

/-- Reading in extended charts commutes with subtraction of inhomogeneous terms. -/
@[simp]
theorem chartTermExtend_sub (ν μ : InhomogeneousTerm jQ JQ) (φ : OpenPartialHomeomorph Q HQ)
    (ψ : OpenPartialHomeomorph M G) :
    (ν - μ).chartTermExtend φ ψ = ν.chartTermExtend φ ψ - μ.chartTermExtend φ ψ := by
  rw [sub_eq_add_neg, chartTermExtend_add, chartTermExtend_neg, sub_eq_add_neg]

/-- Forgetting regularity does not change an inhomogeneous term read in extended charts. -/
@[simp]
theorem chartTermExtend_ofLE (ν : InhomogeneousTerm jQ JQ) (hmn : m ≤ n)
    (φ : OpenPartialHomeomorph Q HQ) (ψ : OpenPartialHomeomorph M G) :
    (ν.ofLE hmn).chartTermExtend φ ψ = ν.chartTermExtend φ ψ := by
  funext z v
  simp [chartTermExtend_apply]

/-- Replacing the structures of an inhomogeneous term by equal ones does not change it read in
extended charts. -/
@[simp]
theorem chartTermExtend_ofEq (ν : InhomogeneousTerm jQ JQ)
    {jQ' : ContMDiffAlmostComplexStructure IQ n Q}
    {JQ' : ContMDiffAlmostComplexStructureFamily I M IQ Q n} (hj : jQ = jQ') (hJ : JQ = JQ')
    (φ : OpenPartialHomeomorph Q HQ) (ψ : OpenPartialHomeomorph M G) :
    (ν.ofEq hj hJ).chartTermExtend φ ψ = ν.chartTermExtend φ ψ := by
  funext z v
  rw [chartTermExtend_apply, chartTermExtend_apply, ofEq_val]

/-- On a normed space, read in the identity chart, an inhomogeneous term is twice its value on
`∂ₛ` at the domain point `(φ.extend IQ)⁻¹ z`. -/
@[simp]
theorem chartTermExtend_refl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {JQ : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, F) F IQ Q n} (ν : InhomogeneousTerm jQ JQ)
    (φ : OpenPartialHomeomorph Q HQ) :
    ν.chartTermExtend φ (OpenPartialHomeomorph.refl F) = fun z v ↦
      (2 : ℝ) • (ν.val.tangentHom ((φ.extend IQ).symm z, v)
        (mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ)) : F) := by
  funext z v
  rw [chartTermExtend_apply]
  generalize mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ) = w
  rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq,
    mvfderiv_eq_fderiv_apply, fderiv_id]
  -- The identity of `F` fixes the tangent vector, read as a vector of `F`.
  rfl

/-- An inhomogeneous term read in extended charts vanishes at the value `ψ y` exactly when the
term at `((φ.extend IQ)⁻¹ z, y)` vanishes on `∂ₛ`, for a chart `ψ` differentiable at `y` with
inverse differentiable at `ψ y`. -/
theorem chartTermExtend_apply_eq_zero_iff (ν : InhomogeneousTerm jQ JQ)
    (φ : OpenPartialHomeomorph Q HQ) {ψ : OpenPartialHomeomorph M G} {y : M} (hy : y ∈ ψ.source)
    (hψ : MDifferentiableAt I 𝓘(ℝ, G) ψ y) (hψs : MDifferentiableAt 𝓘(ℝ, G) I ψ.symm (ψ y))
    (z : ℂ) :
    ν.chartTermExtend φ ψ z (ψ y) = 0 ↔
      ν.val.tangentHom ((φ.extend IQ).symm z, y)
        (mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ)) = 0 := by
  -- The chart derivative is injective, with left inverse the derivative of `ψ.symm`.
  have hinv := ψ.mfderiv_symm_apply_mfderiv_apply hy hψ hψs
  rw [chartTermExtend_apply, ψ.left_inv hy]
  generalize ν.val.tangentHom ((φ.extend IQ).symm z, y)
    (mfderivWithin 𝓘(ℝ, ℂ) IQ (φ.extend IQ).symm (Set.range IQ) z (1 : ℂ)) = w
  rw [smul_eq_zero, or_iff_right two_ne_zero, mvfderiv_apply_eq_mfderiv_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; exact map_zero _⟩
  rw [← hinv w, h]
  exact map_zero _

/-- **Comparison at interior points.** At a point `z` in the interior of the range of the model,
an inhomogeneous term read in the extended chart `φ.extend IQ` is the term read by `chartTerm` in
any chart `φ'` into `ℂ` whose inverse agrees with `(φ.extend IQ)⁻¹` near `z`. -/
theorem chartTermExtend_apply_eq_chartTerm_apply (ν : InhomogeneousTerm jQ JQ)
    (φ : OpenPartialHomeomorph Q HQ) (φ' : OpenPartialHomeomorph Q ℂ)
    (ψ : OpenPartialHomeomorph M G) {z : ℂ} (hz : Set.range IQ ∈ 𝓝 z)
    (hφ : φ'.symm =ᶠ[𝓝 z] (φ.extend IQ).symm) (v : G) :
    ν.chartTermExtend φ ψ z v = ν.chartTerm φ' ψ z v := by
  rw [chartTermExtend_apply, chartTerm_apply, mfderivWithin_of_mem_nhds hz, hφ.mfderiv_eq,
    hφ.eq_of_nhds]
  -- The cast between tangent spaces at the same point is the identity.
  rfl

end Extend

/-! ### Preferred extended charts of a domain modelled on `ℂ` with corners -/

section PreferredChartsExtend

variable [I.Boundaryless] {HQ Q : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ ℂ HQ}
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q]
  {jQ : ContMDiffAlmostComplexStructure IQ n Q}
  {JQ : ContMDiffAlmostComplexStructureFamily I M IQ Q n}

/-- In the preferred extended charts of a domain modelled on `ℂ` with corners, an inhomogeneous
term read through `chartTermExtend` is twice its reading in the tangent trivializations at `x`
and `y`, applied to `1`. -/
theorem chartTermExtend_chartAt (ν : InhomogeneousTerm jQ JQ) (x : Q) (y : M) {z : ℂ}
    (hz : z ∈ (extChartAt IQ x).target) {v : E} (hv : v ∈ (extChartAt I y).target) :
    ν.chartTermExtend (chartAt HQ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) z v =
      (2 : ℝ) • ContinuousLinearMap.inCoordinates ℂ (TangentSpace IQ) E (TangentSpace I) x
        ((extChartAt IQ x).symm z) y ((extChartAt I y).symm v)
        (ν.val ((extChartAt IQ x).symm z, (extChartAt I y).symm v)) 1 := by
  have hx : (extChartAt IQ x).symm z ∈ (chartAt HQ x).source := by
    rw [← extChartAt_source IQ]
    exact (extChartAt IQ x).map_target hz
  have hy : (extChartAt I y).symm v ∈ (chartAt H y).source := by
    rw [← extChartAt_source I]
    exact (extChartAt I y).map_target hv
  have hψ : ⇑((chartAt H y).extendTrans I (Homeomorph.refl E)) = extChartAt I y :=
    (chartAt H y).coe_extendTrans_refl I
  have hψs : ⇑((chartAt H y).extendTrans I (Homeomorph.refl E)).symm = (extChartAt I y).symm :=
    (chartAt H y).coe_symm_extendTrans_refl I
  simp only [chartTermExtend_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy,
    TangentBundle.symmL_trivializationAt hx, hψ, hψs, (extChartAt IQ x).right_inv hz]
  rw [DomainDependentHomSection.tangentHom_apply]
  -- `mvfderiv` is `mfderiv` followed by the identification of `TangentSpace 𝓘(ℝ, E) _` with `E`,
  -- and the composite evaluates by `comp_apply`; the identification is the identity, so both
  -- sides agree by definition. Rewriting with `mvfderiv_apply_eq_mfderiv_apply` or `comp_apply`
  -- fails here, since `1 : ℂ` is read as a tangent vector only up to that identification.
  rfl

/-- In the preferred extended charts of a domain modelled on `ℂ` with corners, an inhomogeneous
term read through `chartTermExtend` is jointly `Cⁿ` on the product of the extended chart targets.
Over the closed upper half-plane this is regularity up to the boundary. -/
theorem contDiffOn_chartTermExtend_chartAt (ν : InhomogeneousTerm jQ JQ) (x : Q) (y : M) :
    ContDiffOn ℝ n (fun q : ℂ × E ↦
        ν.chartTermExtend (chartAt HQ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) q.1
          q.2)
      ((extChartAt IQ x).target ×ˢ (extChartAt I y).target) := by
  have hmaps : Set.MapsTo (extChartAt (IQ.prod I) (x, y)).symm
      (extChartAt (IQ.prod I) (x, y)).target ((chartAt HQ x).source ×ˢ (chartAt H y).source) :=
    fun q hq ↦ by
      simpa [extChartAt_source] using (extChartAt (IQ.prod I) (x, y)).map_target hq
  have h := contMDiffOn_iff_contDiffOn.1 ((ν.val.contMDiffOn_inCoordinates x y).comp
    (contMDiffOn_extChartAt_symm (x, y)) hmaps)
  rw [extChartAt_prod_target] at h
  refine ((h.clm_apply (contDiffOn_const (c := (1 : ℂ)))).const_smul (2 : ℝ)).congr
    fun q hq ↦ ?_
  have hs : (extChartAt (IQ.prod I) (x, y)).symm q =
      ((extChartAt IQ x).symm q.1, (extChartAt I y).symm q.2) :=
    extChartAt_prod_symm_apply _ _
  rw [ν.chartTermExtend_chartAt x y hq.1 hq.2]
  exact congrArg (fun r : Q × M ↦ (2 : ℝ) • ContinuousLinearMap.inCoordinates ℂ
    (TangentSpace IQ) E (TangentSpace I) x r.1 y r.2 (ν.val r) 1) hs.symm

end PreferredChartsExtend

/-! ### Preferred charts of a domain modelled on `ℂ` -/

section PreferredCharts

variable [I.Boundaryless] {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℝ, ℂ) ∞ Y] {jY : ContMDiffAlmostComplexStructure 𝓘(ℝ, ℂ) n Y}
  {JY : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) Y n}

omit [I.Boundaryless] in
/-- In the preferred chart of a domain modelled on `ℂ`, `chartTerm` is `chartTermExtend`. -/
private theorem chartTerm_chartAt_eq_chartTermExtend (ν : InhomogeneousTerm jY JY) (x : Y)
    (ψ : OpenPartialHomeomorph M G) (z : ℂ) (v : G) :
    ν.chartTerm (chartAt ℂ x) ψ z v = ν.chartTermExtend (chartAt ℂ x) ψ z v :=
  (ν.chartTermExtend_apply_eq_chartTerm_apply _ _ ψ (by simp)
    (Filter.EventuallyEq.of_eq (by simp)) v).symm

/-- In the preferred charts, an inhomogeneous term read through `chartTerm` is twice its reading
in the tangent trivializations at `x` and `y`, applied to `1`. -/
theorem chartTerm_chartAt (ν : InhomogeneousTerm jY JY) (x : Y) (y : M) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) {v : E} (hv : v ∈ (extChartAt I y).target) :
    ν.chartTerm (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) z v =
      (2 : ℝ) • ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ)) E (TangentSpace I) x
        ((chartAt ℂ x).symm z) y ((extChartAt I y).symm v)
        (ν.val ((chartAt ℂ x).symm z, (extChartAt I y).symm v)) 1 := by
  rw [chartTerm_chartAt_eq_chartTermExtend]
  simpa using ν.chartTermExtend_chartAt x y (z := z) (by simpa using hz) hv

/-- In the preferred charts, an inhomogeneous term read through `chartTerm` is jointly `Cⁿ` on
the product of the chart targets. -/
theorem contDiffOn_chartTerm_chartAt (ν : InhomogeneousTerm jY JY) (x : Y) (y : M) :
    ContDiffOn ℝ n (fun q : ℂ × E ↦
        ν.chartTerm (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) q.1 q.2)
      ((chartAt ℂ x).target ×ˢ (extChartAt I y).target) := by
  simpa [chartTerm_chartAt_eq_chartTermExtend] using ν.contDiffOn_chartTermExtend_chartAt x y

end PreferredCharts

end InhomogeneousTerm

/-! ### Changes of holomorphic chart on a Riemann surface -/

section HolomorphicChart

variable {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}

/-- The inhomogeneous term evaluated on the coordinate vector `∂ₛ` of a holomorphic chart `φ'`,
expressed through the coordinate vector `∂ₛ` of a holomorphic chart `φ`: with `a + b i` the
derivative of the transition `φ ∘ φ'⁻¹`, the vector is `a ∂ₛ + b j ∂ₛ`, and `ν` is antilinear. -/
private theorem tangentHom_mfderiv_symm_apply_one {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {z : ℂ} (hz : z ∈ (φ'.symm.trans φ).source) (y : M) :
    ν.val.tangentHom (φ'.symm z, y) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ'.symm z (1 : ℂ)) =
      (deriv (φ'.symm.trans φ) z).re •
          ν.val.tangentHom (φ.symm (φ'.symm.trans φ z), y)
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z) (1 : ℂ)) -
        (deriv (φ'.symm.trans φ) z).im •
          J.tangentEndomorphism (φ.symm (φ'.symm.trans φ z), y)
            (ν.val.tangentHom (φ.symm (φ'.symm.trans φ z), y)
              (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z) (1 : ℂ))) := by
  have hz' : z ∈ φ'.target ∧ φ'.symm z ∈ φ.source := by simpa using hz
  have hτz : φ'.symm.trans φ z ∈ φ.target := by simpa using φ.map_source hz'.2
  have hzx : φ'.symm z = φ.symm (φ'.symm.trans φ z) := by simp [φ.left_inv hz'.2]
  -- The coordinate vector `∂ₛ` of `φ'` is, in `φ`, the derivative of the transition.
  have hτ : DifferentiableAt ℂ (φ'.symm.trans φ) z :=
    (contDiffAt_symm_trans_of_mem_maximalAtlas hφ' hφ hz).differentiableAt one_ne_zero
  have hτ1 : fderiv ℝ (φ'.symm.trans φ) z 1 = deriv (F := ℂ) (φ'.symm.trans φ) z := by
    rw [(hτ.hasFDerivAt.restrictScalars ℝ).fderiv]
    exact fderiv_apply_one_eq_deriv
  have hone : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ'.symm z (1 : ℂ) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z)
        (deriv (F := ℂ) (φ'.symm.trans φ) z) :=
    (DFunLike.congr_fun (φ'.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans hz
      (mdifferentiableAt_symm_of_mem_maximalAtlas
        (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ) hτz)
      (hτ.restrictScalars ℝ)) (1 : ℂ)).trans
      (congrArg (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z)) hτ1)
  -- A real-linear map on `ℂ` is determined by its values on `1` and `i`.
  have hlin : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z)
        (deriv (F := ℂ) (φ'.symm.trans φ) z) =
      (deriv (φ'.symm.trans φ) z).re •
          mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z) (1 : ℂ) +
        (deriv (φ'.symm.trans φ) z).im •
          mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z) Complex.I :=
    ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ _
  -- The holomorphic inverse chart intertwines multiplication by `i` with `j`.
  have hI := mfderiv_symm_apply_I_of_mem_maximalAtlas hφ hτz
  have hj := ν.tangentHom_apply_j (φ.symm (φ'.symm.trans φ z), y)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z) (1 : ℂ))
  rw [SmoothAlmostComplexStructure.toContMDiff_apply] at hj
  rw [hone, hzx, hlin, hI, map_add, map_smul, map_smul, hj, smul_neg, sub_eq_add_neg]

/-- **Changing the holomorphic chart.** Let `φ` and `φ'` be holomorphic charts of `X`, let `z` lie
in the source of the transition `τ = φ ∘ φ'⁻¹`, and write `τ'(z) = a + b i`. For a chart `ψ` of
`M` with values in a normed space, differentiable at `ψ⁻¹ v` with inverse differentiable at a point
`v` of its target, the inhomogeneous term read in `φ'` and `ψ` at `(z, v)` is
`a η(τ z, v) - b J(τ z, v) η(τ z, v)`, where `η` and `J` are the term and the structure read in
`φ` and `ψ`. This is the transformation law of the planar weak equation under the biholomorphism
`τ`. -/
theorem InhomogeneousTerm.chartTerm_eq_re_smul_sub_im_smul {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {z : ℂ} (hz : z ∈ (φ'.symm.trans φ).source) {ψ : OpenPartialHomeomorph M G} {v : G}
    (hv : v ∈ ψ.target) (hψ : MDifferentiableAt I 𝓘(ℝ, G) ψ (ψ.symm v))
    (hψs : MDifferentiableAt 𝓘(ℝ, G) I ψ.symm v) :
    ν.chartTerm φ' ψ z v =
      (deriv (φ'.symm.trans φ) z).re • ν.chartTerm φ ψ (φ'.symm.trans φ z) v -
        (deriv (φ'.symm.trans φ) z).im •
          J.chartField φ ψ (φ'.symm.trans φ z) v (ν.chartTerm φ ψ (φ'.symm.trans φ z) v) := by
  -- The derivative of `ψ` intertwines `J` with the structure read in `ψ`.
  have hint := (J.freeze (φ.symm (φ'.symm.trans φ z))).mfderiv_comp_toEndomorphism ψ
    (ψ.map_target hv) hψ (by rwa [ψ.right_inv hv])
  rw [ψ.right_inv hv] at hint
  rw [InhomogeneousTerm.chartTerm_apply, InhomogeneousTerm.chartTerm_apply,
    ContMDiffAlmostComplexStructureFamily.chartField_apply,
    tangentHom_mfderiv_symm_apply_one hφ hφ' hz, map_smul, mvfderiv_apply_eq_mfderiv_apply,
    mvfderiv_apply_eq_mfderiv_apply]
  generalize (ν.val.tangentHom (φ.symm (φ'.symm.trans φ z), ψ.symm v))
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z) (1 : ℂ)) = w
  have hJ : (J.freeze (φ.symm (φ'.symm.trans φ z))).chartPushforward ψ v
      (mfderiv I 𝓘(ℝ, G) ψ (ψ.symm v) w) =
      mfderiv I 𝓘(ℝ, G) ψ (ψ.symm v)
        (J.tangentEndomorphism (φ.symm (φ'.symm.trans φ z), ψ.symm v) w) :=
    (DFunLike.congr_fun hint w).symm.trans (congrArg _ (J.freeze_apply _ _ w))
  rw [hJ, map_sub, map_smul, map_smul]
  -- What remains is an identity between vectors of `G`.
  have h2 : ∀ (a b : ℝ) (x y : G), (2 : ℝ) • (a • x - b • y) = a • (2 : ℝ) • x - b • (2 : ℝ) • y :=
    fun a b x y ↦ by module
  exact h2 _ _ _ _

end HolomorphicChart

end TauCeti
