/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Geometry.Lie.Prod
public import TauCeti.Geometry.Lie.Subgroup.Immersed.Existence
import TauCeti.Geometry.Lie.Covering
import TauCeti.Geometry.Lie.Faithfulness
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Integrating Lie-algebra homomorphisms out of simply connected Lie groups

Let `G` and `G'` be finite-dimensional real Lie groups with Lie algebras `𝔤` and `𝔤'`. If `G` is
simply connected, every Lie-algebra homomorphism `φ : 𝔤 → 𝔤'` is the differential of a unique
smooth homomorphism `G → G'`, `LieHom.integrate φ`. Together with the faithfulness of the Lie
functor on preconnected groups (`lieMap_injective`), this says that differentiation is a bijection
from the smooth homomorphisms `G → G'` onto the Lie-algebra homomorphisms `𝔤 → 𝔤'`
(`TauCeti.Lie.lieMapEquiv`).

The proof integrates the graph of `φ`. Its graph `{(X, φ X)}` is a Lie subalgebra of the Lie
algebra `𝔤 × 𝔤'` of `G × G'` (`TauCeti.Lie.prodLieEquiv`), so it is the Lie algebra of a
connected immersed Lie subgroup `Γ ⊆ G × G'`
(`LieSubalgebra.integralLeafSubgroupData`). The first projection `Γ → G` has bijective
differential, since the graph meets the second factor only in `0` and projects onto the first.
It is therefore a covering map of the connected group `Γ` onto the simply connected group `G`
(`ContMDiffMonoidMorphism.bijective_of_lieMap_bijective_of_simplyConnectedSpace`), hence a
bijective local diffeomorphism, hence a diffeomorphism. Following its inverse by the second
projection gives the integrating homomorphism, whose differential is `φ` because the differential
of the inclusion of `Γ` has range the graph of `φ`.

The integral leaf subgroup is available for second-countable Lie groups modelled without boundary
on spaces in the lowest universe, so these hypotheses are carried by the statements.

## Main definitions

* `LieHom.integrate`: the smooth homomorphism out of a simply connected Lie group integrating a
  Lie-algebra homomorphism.
* `TauCeti.Lie.lieMapEquiv`: differentiation identifies smooth homomorphisms out of a simply
  connected Lie group with Lie-algebra homomorphisms.

## Main results

* `LieHom.lieMap_integrate`: the differential of `φ.integrate` is `φ`.
* `ContMDiffMonoidMorphism.integrate_lieMap`: a smooth homomorphism is the integral of its
  differential.
* `ContMDiffMonoidMorphism.eq_integrate_iff`: a smooth homomorphism is the integral of `φ` exactly
  when its differential is `φ`.
* `TauCeti.Lie.lieMap_bijective`: **Lie's second theorem**, differentiation is bijective on
  smooth homomorphisms out of a simply connected Lie group.
* `LieHom.integrate_comp`: integration is functorial.
* `LieHom.integrate_bijective`: a Lie-algebra isomorphism between the Lie algebras of two simply
  connected Lie groups integrates to a bijective homomorphism.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113, Cambridge University Press (2008), Theorem 3.41.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer (2013), Theorem 20.19.
-/

public section

noncomputable section

open Function
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

attribute [local instance] TauCeti.Lie.ImmersedLieSubgroupData.group
  TauCeti.Lie.ImmersedLieSubgroupData.topologicalSpace
  TauCeti.Lie.ImmersedLieSubgroupData.normedAddCommGroup
  TauCeti.Lie.ImmersedLieSubgroupData.normedSpace
  TauCeti.Lie.ImmersedLieSubgroupData.finiteDimensional
  TauCeti.Lie.ImmersedLieSubgroupData.modelTopology
  TauCeti.Lie.ImmersedLieSubgroupData.chartedSpace TauCeti.Lie.ImmersedLieSubgroupData.lieGroup
  TauCeti.Lie.ImmersedLieSubgroupData.connectedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

namespace TauCeti.Lie

/-! ### The graph of a Lie-algebra homomorphism -/

/-- The graph `X ↦ (X, φ X)` of a Lie-algebra homomorphism, read in the Lie algebra of the
product group through `TauCeti.Lie.prodLieEquiv`. -/
private def graphLieHom (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation (I.prod I') (G × G') :=
  prodLieEquiv.symm.toLieHom.comp ((1 : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ _).prod φ)

private theorem lieMap_fst_graphLieHom
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G')
    (X : LeftInvariantDerivation I G) :
    lieMap ContMDiffMonoidMorphism.fst (graphLieHom φ X) = X := by
  simp [graphLieHom]

private theorem lieMap_snd_graphLieHom
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G')
    (X : LeftInvariantDerivation I G) :
    lieMap ContMDiffMonoidMorphism.snd (graphLieHom φ X) = φ X := by
  simp [graphLieHom]

variable [I.Boundaryless] [SecondCountableTopology G] [I'.Boundaryless]
  [SecondCountableTopology G']

/-- The connected immersed Lie subgroup of `G × G'` whose Lie algebra is the graph of `φ`. -/
private abbrev graphData (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :=
  (graphLieHom φ).range.integralLeafSubgroupData (I := I.prod I')

/-- The first projection from the integrated graph of `φ` to `G`. -/
private def graphFst (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    ContMDiffMonoidMorphism (graphData φ).I' I ∞ (graphData φ).X G :=
  ContMDiffMonoidMorphism.fst.comp (graphData φ).toContMDiffMonoidMorphism

/-- The differential of the inclusion of the integrated graph is the graph of `φ`, evaluated at the
differential of the first projection. -/
private theorem lieMapToHom_graphData
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G')
    (Y : LeftInvariantDerivation (graphData φ).I' (graphData φ).X) :
    (graphData φ).lieMapToHom Y = graphLieHom φ (lieMap (graphFst φ) Y) := by
  obtain ⟨X, hX⟩ := (LieHom.mem_range _ _).1 <|
    (LieSubalgebra.range_lieMapToHom_integralLeafSubgroupData (graphLieHom φ).range).le
      (LieHom.mem_range_self _ Y)
  simp only [← hX, graphFst, lieMap_comp, LieHom.comp_apply,
    ImmersedLieSubgroupData.lieMap_toContMDiffMonoidMorphism, lieMap_fst_graphLieHom]

private theorem lieMap_graphFst_bijective
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    Bijective (lieMap (graphFst φ)) := by
  refine ⟨fun Y Y' h ↦ (graphData φ).injective_lieMapToHom ?_, fun X ↦ ?_⟩
  · rw [lieMapToHom_graphData, lieMapToHom_graphData, h]
  · obtain ⟨Y, hY⟩ : graphLieHom φ X ∈ (graphData φ).lieMapToHom.range := by
      rw [LieSubalgebra.range_lieMapToHom_integralLeafSubgroupData]
      exact LieHom.mem_range_self _ X
    refine ⟨Y, ?_⟩
    rw [LieHom.coe_toLinearMap, lieMapToHom_graphData] at hY
    simpa only [lieMap_fst_graphLieHom] using congrArg (lieMap ContMDiffMonoidMorphism.fst) hY

variable [SimplyConnectedSpace G]

/-- The first projection from the integrated graph of `φ` onto the simply connected group `G`,
as a diffeomorphism. -/
private def graphFstDiffeomorph
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    Diffeomorph (graphData φ).I' I (graphData φ).X G ∞ :=
  IsLocalDiffeomorph.diffeomorphOfBijective
    ((graphFst φ).isLocalDiffeomorph_of_lieMap_bijective (lieMap_graphFst_bijective φ))
    ((graphFst φ).bijective_of_lieMap_bijective_of_simplyConnectedSpace
      (lieMap_graphFst_bijective φ))

private theorem coe_graphFstDiffeomorph
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    ⇑(graphFstDiffeomorph φ) = graphFst φ :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

private theorem graphFst_graphFstDiffeomorph_symm
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') (g : G) :
    graphFst φ ((graphFstDiffeomorph φ).symm g) = g := by
  rw [← coe_graphFstDiffeomorph]
  exact (graphFstDiffeomorph φ).apply_symm_apply g

/-- The inverse of the first projection from the integrated graph of `φ`, as a smooth
homomorphism. -/
private def graphFstInv (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    ContMDiffMonoidMorphism I (graphData φ).I' ∞ G (graphData φ).X where
  toFun := (graphFstDiffeomorph φ).symm
  map_one' := (graphFstDiffeomorph φ).injective <| by
    simp [coe_graphFstDiffeomorph]
  map_mul' g h := (graphFstDiffeomorph φ).injective <| by
    simp [coe_graphFstDiffeomorph, graphFst_graphFstDiffeomorph_symm]
  contMDiff_toFun := (graphFstDiffeomorph φ).symm.contMDiff

private theorem graphFst_comp_graphFstInv
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    (graphFst φ).comp (graphFstInv φ) = ContMDiffMonoidMorphism.id :=
  DFunLike.ext _ _ fun g ↦ by
    simp only [ContMDiffMonoidMorphism.coe_comp, ContMDiffMonoidMorphism.coe_id, comp_apply, id]
    exact graphFst_graphFstDiffeomorph_symm φ g

end TauCeti.Lie

open TauCeti TauCeti.Lie

variable [I.Boundaryless] [SecondCountableTopology G] [SimplyConnectedSpace G] [I'.Boundaryless]
  [SecondCountableTopology G']

namespace LieHom

/-- **Integration of a Lie-algebra homomorphism.** The smooth homomorphism out of a simply
connected Lie group `G` whose differential is a given Lie-algebra homomorphism `φ`
(`LieHom.lieMap_integrate`). It is the second projection of the connected immersed subgroup of
`G × G'` integrating the graph of `φ`, composed with the inverse of its first projection. -/
def integrate (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    ContMDiffMonoidMorphism I I' ∞ G G' :=
  ContMDiffMonoidMorphism.snd.comp
    ((graphData φ).toContMDiffMonoidMorphism.comp (graphFstInv φ))

/-- The differential of the integral of a Lie-algebra homomorphism is that homomorphism. -/
@[simp]
theorem lieMap_integrate (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    lieMap φ.integrate = φ := by
  ext X
  have hinv := (graphFstInv φ).leftInverse_lieMap (graphFst φ) (graphFst_comp_graphFstInv φ) X
  simp only [integrate, lieMap_comp, LieHom.comp_apply,
    ImmersedLieSubgroupData.lieMap_toContMDiffMonoidMorphism, lieMapToHom_graphData, hinv,
    lieMap_snd_graphLieHom]

/-- The identity of the Lie algebra integrates to the identity homomorphism. -/
@[simp]
theorem integrate_one :
    (1 : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I G).integrate =
      ContMDiffMonoidMorphism.id :=
  lieMap_injective (by rw [lieMap_integrate, lieMap_id])

/-- Integration is functorial: the integral of a composite of Lie-algebra homomorphisms between
the Lie algebras of simply connected groups is the composite of the integrals. -/
theorem integrate_comp [SimplyConnectedSpace G']
    {E'' : Type} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [I''.Boundaryless]
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G''] [LieGroup I'' ∞ G'']
    [SecondCountableTopology G'']
    (ψ : LeftInvariantDerivation I' G' →ₗ⁅ℝ⁆ LeftInvariantDerivation I'' G'')
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    (ψ.comp φ).integrate = ψ.integrate.comp φ.integrate :=
  lieMap_injective (by rw [lieMap_integrate, lieMap_comp, lieMap_integrate, lieMap_integrate])

/-- A bijective homomorphism between the Lie algebras of two simply connected Lie groups
integrates to a bijective homomorphism of the groups. -/
theorem integrate_bijective [SimplyConnectedSpace G']
    {φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G'} (hφ : Bijective φ) :
    Bijective φ.integrate :=
  φ.integrate.bijective_of_lieMap_bijective_of_simplyConnectedSpace (by rwa [lieMap_integrate])

end LieHom

namespace ContMDiffMonoidMorphism

/-- A smooth homomorphism out of a simply connected Lie group is the integral of its
differential. -/
@[simp]
theorem integrate_lieMap (f : ContMDiffMonoidMorphism I I' ∞ G G') :
    (lieMap f).integrate = f :=
  lieMap_injective (lieMap f).lieMap_integrate

/-- `LieHom.integrate` is characterized by its universal property: a smooth homomorphism out of a
simply connected Lie group is the integral of `φ` exactly when its differential is `φ`. -/
@[simp]
theorem eq_integrate_iff {f : ContMDiffMonoidMorphism I I' ∞ G G'}
    {φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G'} :
    f = φ.integrate ↔ lieMap f = φ :=
  ⟨fun h ↦ h ▸ φ.lieMap_integrate, fun h ↦ h ▸ (integrate_lieMap f).symm⟩

end ContMDiffMonoidMorphism

namespace TauCeti.Lie

/-- **Lie's second theorem.** Differentiation is a bijection from the smooth homomorphisms out of
a simply connected Lie group onto the homomorphisms of Lie algebras. -/
theorem lieMap_bijective :
    Bijective (lieMap : ContMDiffMonoidMorphism I I' ∞ G G' →
      LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :=
  ⟨lieMap_injective, fun φ ↦ ⟨φ.integrate, φ.lieMap_integrate⟩⟩

variable (I G I' G') in
/-- Differentiation identifies the smooth homomorphisms out of a simply connected Lie group with
the homomorphisms of Lie algebras; the inverse is `LieHom.integrate`. -/
def lieMapEquiv :
    ContMDiffMonoidMorphism I I' ∞ G G' ≃
      (LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') where
  toFun := lieMap
  invFun := LieHom.integrate
  left_inv := ContMDiffMonoidMorphism.integrate_lieMap
  right_inv := LieHom.lieMap_integrate

/-- `TauCeti.Lie.lieMapEquiv` is differentiation. -/
@[simp]
theorem lieMapEquiv_apply (f : ContMDiffMonoidMorphism I I' ∞ G G') :
    lieMapEquiv I G I' G' f = lieMap f :=
  (rfl)

/-- The inverse of `TauCeti.Lie.lieMapEquiv` is integration. -/
@[simp]
theorem lieMapEquiv_symm_apply
    (φ : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') :
    (lieMapEquiv I G I' G').symm φ = φ.integrate :=
  (rfl)

end TauCeti.Lie
