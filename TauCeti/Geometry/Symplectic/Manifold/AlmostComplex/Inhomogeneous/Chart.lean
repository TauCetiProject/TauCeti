/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.LinearAlgebra.Complex.Module

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
* `TauCeti.InhomogeneousTerm.chartTerm_apply_eq_zero_iff`: the term read in charts vanishes at a
  point exactly when the term vanishes on `∂ₛ` there.
* `TauCeti.InhomogeneousTerm.tangentHom_eq_zero_iff_apply_one_eq_zero`: on a Riemann surface, an
  inhomogeneous term vanishes at a point exactly when it vanishes on `1` there.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (inhomogeneous Cauchy--Riemann equations).
-/

public section

noncomputable section

open scoped Manifold ContDiff TauCeti.ComplexManifold

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
  rw [chartTerm_apply, ZeroMemClass.coe_zero,
    DomainDependentHomSection.tangentHom_zero, zero_apply, map_zero,
    smul_zero]

/-- Reading in charts is additive in the inhomogeneous term. -/
@[simp]
theorem chartTerm_add (ν μ : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) :
    (ν + μ).chartTerm φ ψ = ν.chartTerm φ ψ + μ.chartTerm φ ψ := by
  funext z v
  rw [Pi.add_apply, Pi.add_apply, chartTerm_apply, chartTerm_apply, chartTerm_apply,
    Submodule.coe_add, DomainDependentHomSection.tangentHom_add, add_apply,
    map_add, smul_add]

/-- Reading in charts commutes with real scalar multiplication of the inhomogeneous term. -/
@[simp]
theorem chartTerm_smul (c : ℝ) (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (ψ : OpenPartialHomeomorph M G) :
    (c • ν).chartTerm φ ψ = c • ν.chartTerm φ ψ := by
  funext z v
  rw [Pi.smul_apply, Pi.smul_apply, chartTerm_apply, chartTerm_apply, Submodule.coe_smul,
    DomainDependentHomSection.tangentHom_smul, smul_apply, map_smul,
    smul_comm]

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
  rw [chartTerm_apply, chartTerm_apply]
  generalize mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ) = w
  rw [DomainDependentHomSection.tangentHom_apply, DomainDependentHomSection.tangentHom_apply,
    ofLE_val_apply]

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

/-- On a Riemann surface, an inhomogeneous term vanishes at a point exactly when it vanishes on
the unit vector `1` of the model tangent space there, the coordinate vector `∂ₛ` of the
preferred chart. -/
theorem tangentHom_eq_zero_iff_apply_one_eq_zero {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X] {ℓ : ℕ∞}
    {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (q : X × M) : ν.val.tangentHom q = 0 ↔ ν.val.tangentHom q (1 : ℂ) = 0 := by
  -- The zero map vanishes on `1`.
  refine ⟨fun h ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  -- By complex antilinearity, the value on `j 1 = i` is `-J` applied to the value on `1`.
  have hj1 : ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) q.1 (1 : ℂ) =
      Complex.I := by
    simp [SmoothAlmostComplexStructure.ofComplexManifold_apply]
    -- The two sides are `I` in `TangentSpace 𝓘(ℝ, ℂ) q.1` and in `ℂ`, equal by definition.
    rfl
  have hI := ν.tangentHom_apply_j q (1 : ℂ)
  rw [hj1, h, map_zero, neg_zero] at hI
  -- A real linear map out of `ℂ` vanishing on `1` and `i` is zero.
  have key : ∀ L : ℂ →L[ℝ] TangentSpace I q.2, L 1 = 0 → L Complex.I = 0 → L = 0 :=
    fun L h1 hI ↦ ContinuousLinearMap.ext fun a ↦ by
      simpa [h1, hI] using L.toLinearMap.apply_eq_re_smul_one_add_im_smul_I a
  -- The tangent space of `X` at `q.1` is `ℂ` by definition.
  exact key (ν.val.tangentHom q) h hI

end InhomogeneousTerm

end TauCeti
