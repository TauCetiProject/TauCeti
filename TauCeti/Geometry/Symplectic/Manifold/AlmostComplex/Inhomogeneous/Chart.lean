/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
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
* `TauCeti.InhomogeneousTerm.chartTerm_apply_eq_zero_iff`: the term read in charts vanishes at a
  point exactly when the term vanishes on `∂ₛ` there.
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

open scoped Manifold ContDiff Topology

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

end InhomogeneousTerm

end TauCeti
