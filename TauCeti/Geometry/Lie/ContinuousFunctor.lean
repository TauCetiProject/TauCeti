/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.Faithfulness

/-!
# The Lie functor on continuous homomorphisms

Every continuous homomorphism between finite-dimensional real Lie groups is smooth. This file
uses that automatic smoothness result to expose the Lie functor directly on bundled continuous
homomorphisms. Its identity, composition, exponential, and faithfulness laws are inherited from
the smooth Lie functor.

## Main results

* `ContinuousMonoidHom.lieMap` is the Lie map of a continuous homomorphism.
* `ContinuousMonoidHom.lieMap_comp` gives its composition law.
* `ContinuousMonoidHom.lieMap_injective` gives faithfulness on preconnected sources.
-/

public section

noncomputable section

open Topology
open scoped ContDiff Manifold

namespace ContinuousMonoidHom

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [LieGroup I ∞ G] [LieGroup I' ∞ G']

/-- The Lie-algebra homomorphism induced by a continuous homomorphism between finite-dimensional
real Lie groups. -/
public noncomputable def lieMap (f : G →ₜ* G') :
    LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G' :=
  _root_.lieMap (f.toContMDiffMonoidMorphism I I')

/-- The Lie map of a continuous homomorphism is the smooth Lie map obtained by automatic
smoothness. -/
theorem lieMap_def (f : G →ₜ* G') :
    lieMap (I := I) (I' := I') f =
      _root_.lieMap (f.toContMDiffMonoidMorphism I I') :=
  (rfl)

/-- The Lie map of the identity continuous homomorphism is the identity. -/
@[simp]
theorem lieMap_id :
    lieMap (I := I) (I' := I) (ContinuousMonoidHom.id G) = 1 := by
  have h : (ContinuousMonoidHom.id G).toContMDiffMonoidMorphism I I =
      ContMDiffMonoidMorphism.id := by
    apply DFunLike.coe_injective
    rw [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
      ContMDiffMonoidMorphism.coe_id, ContinuousMonoidHom.coe_id]
  rw [lieMap, h, _root_.lieMap_id]

/-- The Lie map of a composite of continuous homomorphisms is the composite of their Lie maps. -/
theorem lieMap_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [FiniteDimensional ℝ E''] [LieGroup I'' ∞ G'']
    (f : G →ₜ* G') (g : G' →ₜ* G'') :
    lieMap (I := I) (I' := I'') (g.comp f) =
      (lieMap (I := I') (I' := I'') g).comp (lieMap (I := I) (I' := I') f) := by
  have h : (g.comp f).toContMDiffMonoidMorphism I I'' =
      (g.toContMDiffMonoidMorphism I' I'').comp
        (f.toContMDiffMonoidMorphism I I') := by
    apply DFunLike.coe_injective
    rw [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
      ContMDiffMonoidMorphism.coe_comp,
      ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
      ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
      ContinuousMonoidHom.coe_comp]
  rw [lieMap, lieMap, lieMap, h, _root_.lieMap_comp]

/-- A continuous homomorphism intertwines Lie-group exponentials through its Lie map. -/
theorem map_lieExp (f : G →ₜ* G') (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : T2Space G' := t2Space_of_lieGroup (I := I') (n := ∞)
    f (_root_.lieExp X) = _root_.lieExp (lieMap (I := I) (I' := I') f X) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : T2Space G' := t2Space_of_lieGroup (I := I') (n := ∞)
  dsimp only
  rw [lieMap, ← ContinuousMonoidHom.coe_toContMDiffMonoidMorphism
    (I := I) (I' := I') f]
  exact _root_.map_lieExp (f.toContMDiffMonoidMorphism I I') X

/-- The Lie map is injective on continuous homomorphisms out of a preconnected Lie group. -/
@[grind inj]
theorem lieMap_injective [PreconnectedSpace G] :
    Function.Injective (lieMap (I := I) (I' := I') :
      (G →ₜ* G') → LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') := by
  intro f g h
  have hsmooth : f.toContMDiffMonoidMorphism I I' =
      g.toContMDiffMonoidMorphism I I' := by
    apply _root_.lieMap_injective
    exact h
  ext x
  simpa only [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism] using
    congrArg (fun k : ContMDiffMonoidMorphism I I' ∞ G G' ↦ k x) hsmooth

end ContinuousMonoidHom
