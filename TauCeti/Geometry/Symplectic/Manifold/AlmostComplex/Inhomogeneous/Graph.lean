/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
public import TauCeti.Geometry.Symplectic.Prod.Skew
public import TauCeti.Geometry.Symplectic.Floer.Graph

/-!
# The native skew graph construction for finite-regularity forcing data

The pointwise graph structure is the existing skew product, transported through the canonical
product tangent equivalence. For an antilinear forcing term its vertical component is
`J v - 2 J ν ζ`. The square identity is inherited from the native skew construction.
This file concerns tangent-fibre algebra; a weak manifold graph equation requires its separate
Sobolev derivative and chart assembly. Standard complex model coordinates agree with the existing
arbitrary-one-form `Floer.graphStructure` by its general skew-product comparison.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.InhomogeneousTerm

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] {n : ℕ∞}
  {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I M IP P n}

/-- The existing skew graph structure in the actual product tangent fibre. -/
def graphStructureAt (ν : InhomogeneousTerm j J) (q : P × M) :
    AlmostComplexStructure (TangentSpace (IP.prod I) q) :=
  ((j.almostComplexStructureAt q.1).skewProd
    ((J.freeze q.1).almostComplexStructureAt q.2) (ν.val.tangentHom q).toLinearMap).transport
      (Manifold.tangentSpaceProdEquiv q).symm.toLinearEquiv

/-- The normalized forcing convention gives the minus sign and the factor two in the native
skew graph construction. -/
@[simp]
theorem graphStructureAt_apply (ν : InhomogeneousTerm j J) (q : P × M)
    (v : TangentSpace (IP.prod I) q) :
    ν.graphStructureAt q v = (Manifold.tangentSpaceProdEquiv q).symm
      (j q.1 (Manifold.tangentSpaceProdEquiv q v).1,
        J.tangentEndomorphism q (Manifold.tangentSpaceProdEquiv q v).2 -
          (2 : ℝ) • J.tangentEndomorphism q
            (ν.val.tangentHom q (Manifold.tangentSpaceProdEquiv q v).1)) := by
  let w := Manifold.tangentSpaceProdEquiv q v
  have hJ (a : TangentSpace I q.2) :
      (J.freeze q.1).almostComplexStructureAt q.2 a = J.tangentEndomorphism q a :=
    ((J.freeze q.1).almostComplexStructureAt_apply q.2 a).trans (J.freeze_apply q.1 q.2 a)
  have h : (j.almostComplexStructureAt q.1).skewProd
      ((J.freeze q.1).almostComplexStructureAt q.2) (ν.val.tangentHom q).toLinearMap w =
        (j q.1 w.1, J.tangentEndomorphism q w.2 -
          (2 : ℝ) • J.tangentEndomorphism q (ν.val.tangentHom q w.1)) := by
    rw [AlmostComplexStructure.skewProd_apply]
    apply Prod.ext
    · exact j.almostComplexStructureAt_apply q.1 w.1
    · simp only [ContinuousLinearMap.coe_coe]
      rw [hJ, ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply,
        ν.tangentHom_apply_j, map_sub]
      simp only [two_smul]
      abel
  unfold graphStructureAt
  rw [AlmostComplexStructure.transport_apply]
  exact congrArg (Manifold.tangentSpaceProdEquiv q).symm h

section Model

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {jC : ContMDiffAlmostComplexStructure 𝓘(ℝ, ℂ) n ℂ}
  {JC : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V 𝓘(ℝ, ℂ) ℂ n}

/-- In standard complex source coordinates, the native tangent skew graph structure agrees
with the existing Euclidean `Floer.graphStructure` through the canonical product
identifications. -/
theorem toLp_graphStructureAt_eq_graphStructure (ν : InhomogeneousTerm jC JC)
    (q : ℂ × V) (hj : ∀ w : ℂ, jC q.1 w = Complex.I * w)
    (v : TangentSpace (𝓘(ℝ, ℂ).prod 𝓘(ℝ, V)) q) :
    WithLp.toLp 2 (show ℂ × V from ν.graphStructureAt q v) =
      Floer.graphStructure (fun q ↦ (show V →L[ℝ] V from JC.toEndomorphism q))
        (fun q ↦ (show ℂ →L[ℝ] V from ν.val.tangentHom q)) (WithLp.toLp 2 q)
          (WithLp.toLp 2 (show ℂ × V from v)) := by
  let K : AlmostComplexStructure V :=
    { toLinearMap := (show V →L[ℝ] V from JC.toEndomorphism q).toLinearMap
      square_neg := by ext w; exact JC.apply_apply q w }
  rw [graphStructureAt_apply, Floer.graphStructure_toLp_eq_skewProd _ _ q
    (show ℂ × V from v) K (fun _ ↦ rfl), AlmostComplexStructure.skewProd_apply]
  simp only [AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · simp only [Manifold.tangentSpaceProdEquiv_apply,
      Manifold.tangentSpaceProdEquiv_symm_apply]
    exact hj v.1
  · let A : V →L[ℝ] V := JC.toEndomorphism q
    let N : ℂ →L[ℝ] V := ν.val.tangentHom q
    have hJ := JC.tangentEndomorphism_apply q
    have hn : N (Complex.I * v.1) = -A (N v.1) := by
      have hh := ν.tangentHom_apply_j q v.1
      erw [hJ] at hh
      exact (congrArg N (hj v.1).symm).trans hh
    simp only [Manifold.tangentSpaceProdEquiv_apply,
      Manifold.tangentSpaceProdEquiv_symm_apply, hJ]
    -- Canonical model tangents and the ambient normed spaces have the same vectors; after
    -- the public tangent getter the remaining distinction is their inherited module instances.
    change A v.2 - (2 : ℝ) • A (N v.1) = A (v.2 - N v.1) + N (Complex.I * v.1)
    rw [hn, map_sub]
    simp only [two_smul]
    abel

end Model

end TauCeti.InhomogeneousTerm
