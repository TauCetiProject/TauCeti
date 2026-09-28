/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.GlueData
public import TauCeti.Geometry.Toric.Analytic.Character.Action
public import TauCeti.Geometry.Toric.Analytic.Torus.Topology
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
    MulAction (ComplexTorus N) ((Φ.analyticAffineChartDiagram hΦ).obj σ) := by
  change MulAction (ComplexTorus N)
    (AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))
  infer_instance

/-- The map between affine charts associated to a face inclusion is equivariant for the
coordinate-free complex torus. -/
theorem analyticAffineChartDiagram_map_smul {τ σ : Φ.cones} (f : τ ⟶ σ)
    (t : ComplexTorus N) (x : (Φ.analyticAffineChartDiagram hΦ).obj τ) :
    (Φ.analyticAffineChartDiagram hΦ).map f (t • x) =
      t • (Φ.analyticAffineChartDiagram hΦ).map f x := by
  rw [analyticAffineChartDiagram_map_apply, analyticAffineChartDiagram_map_apply]
  exact AffineSemigroupComplexPoint.comap_inclusion_smul
    (dualSemigroup_anti Φ.lattice (leOfHom f)) t x

/-- Equal representatives in two affine charts remain equal after torus translation. -/
private theorem analyticAffineChartι_smul_eq_of_eq {σ τ : Φ.cones}
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ)
    (y : (Φ.analyticAffineChartDiagram hΦ).obj τ) (t : ComplexTorus N)
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

/-- Torus translation on the analytic realization, defined by translating a representative
in an affine chart. Independence of the representative follows from equivariance of face maps. -/
noncomputable def analyticTorusSMul (t : ComplexTorus N) (x : Φ.analyticRealization hΦ) :
    Φ.analyticRealization hΦ :=
  let σ := Classical.choose (Φ.exists_analyticAffineChartι_apply_eq hΦ x)
  let y := Classical.choose (Classical.choose_spec (Φ.exists_analyticAffineChartι_apply_eq hΦ x))
  Φ.analyticAffineChartι hΦ σ (t • y)

/-- Torus translation commutes with every affine chart inclusion. -/
private theorem analyticTorusSMul_analyticAffineChartι (t : ComplexTorus N) (σ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) :
    Φ.analyticTorusSMul hΦ t (Φ.analyticAffineChartι hΦ σ x) =
      Φ.analyticAffineChartι hΦ σ (t • x) := by
  unfold analyticTorusSMul
  let e := Φ.exists_analyticAffineChartι_apply_eq hΦ (Φ.analyticAffineChartι hΦ σ x)
  let σ' := Classical.choose e
  let y' := Classical.choose (Classical.choose_spec e)
  have h : Φ.analyticAffineChartι hΦ σ' y' = Φ.analyticAffineChartι hΦ σ x :=
    Classical.choose_spec (Classical.choose_spec e)
  exact Φ.analyticAffineChartι_smul_eq_of_eq hΦ y' x t h

/-- The glued translations satisfy the group action laws. -/
noncomputable instance : MulAction (ComplexTorus N) (Φ.analyticRealization hΦ) where
  smul := Φ.analyticTorusSMul hΦ
  one_smul x := by
    obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
    change Φ.analyticTorusSMul hΦ 1 (Φ.analyticAffineChartι hΦ σ y) = _
    rw [analyticTorusSMul_analyticAffineChartι]
    exact congrArg _ (one_smul (M := ComplexTorus N) y)
  mul_smul t t' x := by
    obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
    change Φ.analyticTorusSMul hΦ (t * t') (Φ.analyticAffineChartι hΦ σ y) =
      Φ.analyticTorusSMul hΦ t (Φ.analyticTorusSMul hΦ t'
        (Φ.analyticAffineChartι hΦ σ y))
    rw [analyticTorusSMul_analyticAffineChartι,
      analyticTorusSMul_analyticAffineChartι, analyticTorusSMul_analyticAffineChartι]
    exact congrArg _ ((Φ.analyticAffineChartMulAction hΦ σ).mul_smul t t' y)

/-- The global action agrees with the affine action in every chart. -/
@[simp]
theorem smul_analyticAffineChartι (t : ComplexTorus N) (σ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) :
    t • Φ.analyticAffineChartι hΦ σ x = Φ.analyticAffineChartι hΦ σ (t • x) :=
  Φ.analyticTorusSMul_analyticAffineChartι hΦ t σ x

/-- The torus action on each affine chart is jointly continuous in the torus point and the
affine complex point. -/
theorem continuous_analyticAffineChart_smul (σ : Φ.cones) :
    Continuous (fun p : (Φ.analyticAffineChartDiagram hΦ).obj σ × ComplexTorus N ↦
      p.2 • p.1) := by
  let hreg := (isRegular_iff.mp hΦ) σ.1 σ.2
  let g := Φ.analyticChartGenerators σ hreg
  let _ := affinePointTopology g.2
  have hc : Continuous
      (fun p : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) × ComplexTorus N ↦
        p.2 • p.1) := by
    rw [continuous_iff_forall_continuous_apply_single g.2]
    intro m
    simp only [AffineSemigroupComplexPoint.ambient_smul_apply_single]
    exact (Units.continuous_val.comp
      ((continuous_complexTorus_apply m.1).comp continuous_snd)).mul
      ((continuous_apply_single g.2 m).comp continuous_fst)
  have ht : ((Φ.analyticAffineChartDiagram hΦ).obj σ).str = affinePointTopology g.2 :=
    Φ.analyticAffineChart_str_eq σ hreg g.2
  cases ht
  exact hc

/-- The torus action on the fan realization is jointly continuous. -/
theorem continuous_smul_analyticRealization :
    Continuous (fun p : ComplexTorus N × Φ.analyticRealization hΦ ↦ p.1 • p.2) := by
  let q : (Σ σ, (Φ.analyticAffineChartDiagram hΦ).obj σ) → Φ.analyticRealization hΦ :=
    fun x ↦ (Φ.analyticGlueData hΦ).ι x.1 x.2
  have hq : IsOpenQuotientMap q := (Φ.analyticGlueData hΦ).isOpenQuotientMap_sigma_ι
  have hId : IsOpenQuotientMap (id : ComplexTorus N → ComplexTorus N) :=
    IsOpenQuotientMap.id
  have hQ : IsOpenQuotientMap (Prod.map id q) := hId.prodMap hq
  apply hQ.isQuotientMap.continuous_iff.mpr
  have hcσ : Continuous (fun p : Σ σ, ((Φ.analyticAffineChartDiagram hΦ).obj σ) ×
      ComplexTorus N ↦ p.2.2 • Φ.analyticAffineChartι hΦ p.1 p.2.1) := by
    apply continuous_sigma
    intro σ
    have hc := ((Φ.analyticAffineChartι hΦ σ).hom.continuous_toFun).comp
      (Φ.continuous_analyticAffineChart_smul hΦ σ)
    convert hc using 1
    funext x
    simp [smul_analyticAffineChartι]
  have hc : Continuous (fun p : (Σ σ, (Φ.analyticAffineChartDiagram hΦ).obj σ) ×
      ComplexTorus N ↦ p.2 • q p.1) := by
    let e : ((Σ σ, (Φ.analyticAffineChartDiagram hΦ).obj σ) × ComplexTorus N) ≃ₜ
        (Σ σ, ((Φ.analyticAffineChartDiagram hΦ).obj σ) × ComplexTorus N) :=
      Homeomorph.sigmaProdDistrib
    have h := hcσ.comp e.continuous
    convert h using 1
    funext p
    simp [e, q, analyticAffineChartι_def, Homeomorph.sigmaProdDistrib,
      Equiv.sigmaProdDistrib]; rfl
  have h := hc.comp (Homeomorph.prodComm _ _).continuous
  convert h using 1
  funext p
  rfl

/-- The analytic realization carries the continuous action of its complex torus. -/
instance : ContinuousSMul (ComplexTorus N) (Φ.analyticRealization hΦ) :=
  ⟨Φ.continuous_smul_analyticRealization hΦ⟩

end TauCeti.Toric.Fan
