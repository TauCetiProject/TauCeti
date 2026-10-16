/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.GlueData
public import TauCeti.Geometry.Toric.Analytic.Character.Action
public import TauCeti.Topology.Category.TopCat.GlueData

/-!
# The complex torus action on a fan realization

The coordinate-free complex torus acts on each affine chart by multiplication of monomial
values. Restriction to a face commutes with this action, so the chart actions glue to an action
on the analytic realization. The chart inclusions are equivariant, and the action is jointly
continuous for the monomial-embedding topology.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1–3.2.
-/

public section

open CategoryTheory Topology Multiplicative

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- The affine chart of a fan inherits the coordinate-free torus action on its complex points. -/
noncomputable instance analyticAffineChartMulAction (σ : Φ.cones) :
    MulAction (ComplexTorus N) ((Φ.analyticAffineChartDiagram).obj σ) := by
  -- The chart's carrier is definitionally the complex-point type of the dual semigroup.
  change MulAction (ComplexTorus N)
    (AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))
  infer_instance

/-- The map between affine charts associated to a face inclusion is equivariant for the
coordinate-free complex torus. -/
-- `analyticAffineChartDiagram_map` simplifies the left side, so this is an explicit rewrite rule.
theorem analyticAffineChartDiagram_map_smul {τ σ : Φ.cones} (f : τ ⟶ σ)
    (t : ComplexTorus N) (x : (Φ.analyticAffineChartDiagram).obj τ) :
    (Φ.analyticAffineChartDiagram).map f (t • x) =
      t • (Φ.analyticAffineChartDiagram).map f x := by
  -- Use the public map equations because the face-map definitions are not exposed.
  rw [analyticAffineChartDiagram_map_apply, analyticAffineChartDiagram_map_apply,
    ← faceAffinePointMap_def Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f))]
  exact faceAffinePointMap_smul Φ.lattice
    (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f)) t x

/-- Equal representatives in two affine charts remain equal after torus translation. -/
private theorem analyticAffineChartι_smul_eq_of_eq {σ τ : Φ.cones}
    (x : (Φ.analyticAffineChartDiagram).obj σ)
    (y : (Φ.analyticAffineChartDiagram).obj τ) (t : ComplexTorus N)
    (h : Φ.analyticAffineChartι hΦ σ x = Φ.analyticAffineChartι hΦ τ y) :
    Φ.analyticAffineChartι hΦ σ (t • x) = Φ.analyticAffineChartι hΦ τ (t • y) := by
  obtain ⟨z, hzσ, hzτ⟩ :=
    (Φ.analyticAffineChartι_eq_analyticAffineChartι_iff hΦ x y).mp h
  apply (Φ.analyticAffineChartι_eq_analyticAffineChartι_iff hΦ (t • x) (t • y)).mpr
  refine ⟨t • z, ?_, ?_⟩
  · simp only [analyticOverlapLeft_def] at hzσ ⊢
    rw [analyticAffineChartDiagram_map_smul, hzσ]
  · simp only [analyticOverlapRight_def] at hzτ ⊢
    rw [analyticAffineChartDiagram_map_smul, hzτ]

/-- The analytic realization carries the torus action obtained by translating chart points. -/
noncomputable instance : SMul (ComplexTorus N) (Φ.analyticRealization hΦ) where
  smul t x :=
    let σ := Classical.choose (Φ.exists_analyticAffineChartι_apply_eq hΦ x)
    let y := Classical.choose (Classical.choose_spec (Φ.exists_analyticAffineChartι_apply_eq hΦ x))
    Φ.analyticAffineChartι hΦ σ (t • y)

/-- The global action agrees with the affine action in every chart. -/
@[simp]
theorem smul_analyticAffineChartι (t : ComplexTorus N) (σ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj σ) :
    t • Φ.analyticAffineChartι hΦ σ x =
      Φ.analyticAffineChartι hΦ σ (t • x) := by
  let e := Φ.exists_analyticAffineChartι_apply_eq hΦ (Φ.analyticAffineChartι hΦ σ x)
  let σ' := Classical.choose e
  let y' := Classical.choose (Classical.choose_spec e)
  have h : Φ.analyticAffineChartι hΦ σ' y' = Φ.analyticAffineChartι hΦ σ x :=
    Classical.choose_spec (Classical.choose_spec e)
  exact Φ.analyticAffineChartι_smul_eq_of_eq hΦ y' x t h

/-- The glued translations satisfy the group action laws. -/
noncomputable instance : MulAction (ComplexTorus N) (Φ.analyticRealization hΦ) where
  one_smul x := by
    obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
    simp only [smul_analyticAffineChartι, one_smul]
  mul_smul t t' x := by
    obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
    simp only [smul_analyticAffineChartι, mul_smul]

/-- The coordinate-free torus acts jointly continuously on each analytic affine chart. -/
instance (σ : Φ.cones) :
    ContinuousSMul (ComplexTorus N) ((Φ.analyticAffineChartDiagram).obj σ) := by
  let g := Φ.analyticChartGenerators σ
  -- The chart topology is definitionally its chosen monomial-embedding topology.
  change letI := affinePointTopology g.2
    ContinuousSMul (ComplexTorus N)
      (AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))
  exact AffineSemigroupComplexPoint.continuousSMul_complexTorus_affinePointTopology g.2

/-- The analytic realization carries the continuous action of its complex torus. -/
instance : ContinuousSMul (ComplexTorus N) (Φ.analyticRealization hΦ) := by
  refine ⟨?_⟩
  let q : (Σ σ, (Φ.analyticAffineChartDiagram).obj σ) → Φ.analyticRealization hΦ :=
    fun x ↦ (Φ.analyticGlueData hΦ).ι x.1 x.2
  have hq : IsOpenQuotientMap q := (Φ.analyticGlueData hΦ).isOpenQuotientMap_sigma_ι
  have hId : IsOpenQuotientMap (id : ComplexTorus N → ComplexTorus N) :=
    IsOpenQuotientMap.id
  have hQ : IsOpenQuotientMap (Prod.map id q) := hId.prodMap hq
  apply hQ.isQuotientMap.continuous_iff.mpr
  rw [← ((Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib).symm.comp_continuous_iff',
    continuous_sigma_iff]
  intro σ
  simp only [Function.comp_def, Homeomorph.symm_trans_apply,
    Homeomorph.sigmaProdDistrib_symm_apply]
  simp only [Homeomorph.prodComm_symm, Homeomorph.coe_prodComm, Prod.map, id_eq, q,
    ← analyticAffineChartι_def]
  simp only [Prod.swap]
  -- The chart inclusion is definitionally the underlying map of its `TopCat` morphism.
  change Continuous (fun a : ((Φ.analyticAffineChartDiagram).obj σ) ×
    ComplexTorus N ↦ a.2 • Φ.analyticAffineChartι hΦ σ a.1)
  simp only [smul_analyticAffineChartι]
  have hmul := (continuous_smul (M := ComplexTorus N)
    (X := (Φ.analyticAffineChartDiagram).obj σ)).comp
      (Homeomorph.prodComm _ _).continuous
  exact (Φ.analyticAffineChartι hΦ σ).hom.continuous_toFun.comp hmul

end TauCeti.Toric.Fan
