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
* `ContinuousMonoidHom.lieMap_one`, `ContinuousMonoidHom.lieMap_comp`, and
  `ContinuousMonoidHom.lieMap_comp_apply` give its trivial-morphism and composition laws.
* `ContinuousMonoidHom.lieMap_injective` gives faithfulness on preconnected sources.
* `ContinuousMonoidHom.isLocalDiffeomorph_iff_lieMap_bijective` characterizes smooth local
  diffeomorphisms via bijectivity of `lieMap`.
* `ContinuousMulEquiv.lieEquiv` is the Lie-algebra equivalence induced by a continuous
  multiplicative equivalence.
-/

public section

noncomputable section

open Topology
open scoped ContDiff Manifold

namespace ContinuousMonoidHom

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
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

/-- The Lie map of the trivial continuous homomorphism is zero. -/
@[simp]
theorem lieMap_one :
    lieMap (I := I) (I' := I') (1 : G →ₜ* G') = 0 := by
  have h : (1 : G →ₜ* G').toContMDiffMonoidMorphism I I' = 1 := by
    apply DFunLike.coe_injective
    rw [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
    rfl
  rw [lieMap, h, _root_.lieMap_one]

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

/-- Pointwise, the Lie map of a composite of continuous homomorphisms applies the Lie maps in
sequence. -/
theorem lieMap_comp_apply
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [FiniteDimensional ℝ E''] [LieGroup I'' ∞ G'']
    (f : G →ₜ* G') (g : G' →ₜ* G'') (X : LeftInvariantDerivation I G) :
    lieMap (I := I) (I' := I'') (g.comp f) X =
      lieMap (I := I') (I' := I'') g (lieMap (I := I) (I' := I') f X) :=
  (LieHom.congr_fun (lieMap_comp (I := I) (I' := I') (I'' := I'') f g) X).trans
    (LieHom.comp_apply _ _ X)

/-- A continuous homomorphism intertwines Lie-group exponentials through its Lie map. -/
theorem map_lieExp (f : G →ₜ* G') (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
    f (_root_.lieExp X) = _root_.lieExp (lieMap (I := I) (I' := I') f X) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
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

/-- A continuous homomorphism that is a smooth local diffeomorphism at the identity has bijective
Lie map. -/
theorem lieMap_bijective_of_isLocalDiffeomorphAt (f : G →ₜ* G')
    (hf : IsLocalDiffeomorphAt I I' ∞ f 1) :
    Function.Bijective (lieMap (I := I) (I' := I') f) := by
  rw [lieMap_def]
  apply ContMDiffMonoidMorphism.lieMap_bijective_of_isLocalDiffeomorphAt
  rwa [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]

/-- A continuous homomorphism with bijective Lie map is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_of_lieMap_bijective (f : G →ₜ* G')
    (hf : Function.Bijective (lieMap (I := I) (I' := I') f)) :
    IsLocalDiffeomorph I I' ∞ f := by
  rw [← ContinuousMonoidHom.coe_toContMDiffMonoidMorphism (I := I) (I' := I') f]
  exact (f.toContMDiffMonoidMorphism I I').isLocalDiffeomorph_of_lieMap_bijective hf

/-- A continuous homomorphism of finite-dimensional real Lie groups is a smooth local
diffeomorphism if and only if its Lie map is bijective. -/
theorem isLocalDiffeomorph_iff_lieMap_bijective (f : G →ₜ* G') :
    IsLocalDiffeomorph I I' ∞ f ↔ Function.Bijective (lieMap (I := I) (I' := I') f) :=
  ⟨fun hf ↦ lieMap_bijective_of_isLocalDiffeomorphAt f (hf 1),
    isLocalDiffeomorph_of_lieMap_bijective f⟩

/-- A left inverse pair of continuous homomorphisms induces a left inverse pair of Lie maps. -/
theorem leftInverse_lieMap (f : G →ₜ* G') (g : G' →ₜ* G)
    (h : g.comp f = ContinuousMonoidHom.id G) :
    Function.LeftInverse
      (lieMap (I := I') (I' := I) g) (lieMap (I := I) (I' := I') f) := by
  intro X
  rw [← lieMap_comp_apply (I := I) (I' := I') (I'' := I) f g X, h, lieMap_id, one_apply_eq_self]

end ContinuousMonoidHom

namespace ContinuousMulEquiv

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [LieGroup I ∞ G] [LieGroup I' ∞ G']

/-- The Lie-algebra equivalence induced by a continuous multiplicative equivalence between
finite-dimensional real Lie groups. -/
public noncomputable def lieEquiv (e : G ≃ₜ* G') :
    LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I' G' :=
  LieEquiv.mk
    (ContinuousMonoidHom.lieMap (I := I) (I' := I') (e : G →ₜ* G'))
    (ContinuousMonoidHom.lieMap (I := I') (I' := I) (e.symm : G' →ₜ* G))
    (ContinuousMonoidHom.leftInverse_lieMap (I := I) (I' := I')
      (e : G →ₜ* G') (e.symm : G' →ₜ* G)
      (ContinuousMonoidHom.ext fun x ↦ e.symm_apply_apply x))
    (ContinuousMonoidHom.leftInverse_lieMap (I := I') (I' := I)
      (e.symm : G' →ₜ* G) (e : G →ₜ* G')
      (ContinuousMonoidHom.ext fun y ↦ e.apply_symm_apply y))

/-- The forward map of `ContinuousMulEquiv.lieEquiv` is the Lie map of the equivalence. -/
@[simp]
theorem lieEquiv_apply (e : G ≃ₜ* G') (X : LeftInvariantDerivation I G) :
    lieEquiv (I := I) (I' := I') e X =
      ContinuousMonoidHom.lieMap (I := I) (I' := I') (e : G →ₜ* G') X :=
  (rfl)

/-- The inverse map of `ContinuousMulEquiv.lieEquiv` is the Lie map of the inverse equivalence. -/
@[simp]
theorem lieEquiv_symm_apply (e : G ≃ₜ* G') (Y : LeftInvariantDerivation I' G') :
    (lieEquiv (I := I) (I' := I') e).symm Y =
      ContinuousMonoidHom.lieMap (I := I') (I' := I) (e.symm : G' →ₜ* G) Y :=
  (rfl)

end ContinuousMulEquiv
