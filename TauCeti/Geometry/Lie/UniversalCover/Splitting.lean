/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Geometry.Lie.Covering
public import TauCeti.Geometry.Lie.Prod
public import TauCeti.Geometry.Lie.Subgroup.Immersed.Existence
import Mathlib.Algebra.Lie.IdealOperations
import TauCeti.Geometry.Lie.Exponential.Commute

/-!
# Splitting a simply connected Lie group along complementary ideals

Let `G` be a simply connected Lie group whose Lie algebra `𝔤` is the direct sum of two ideals,
`𝔤 = 𝔞 ⊕ 𝔨`. Then `G` is the direct product of the connected Lie subgroups integrating `𝔞` and
`𝔨`, as a topological group (`TauCeti.Lie.idealProdContinuousMulEquiv`). In particular, if the
centre `𝔷` and the derived algebra `[𝔤, 𝔤]` of `𝔤` are complementary, as they are for the Lie
algebra of a compact Lie group, then `G` is the product of the commutative subgroup integrating `𝔷`
and the subgroup `K` integrating `[𝔤, 𝔤]` (`TauCeti.Lie.centerProdDerivedContinuousMulEquiv`).
Applied to the universal cover of a compact connected Lie group, this is a step towards the finite
cover `T × K → G` by a torus times a simply connected semisimple group; transferring the
complementarity to the universal cover and the semisimplicity of `[𝔤, 𝔤]` are not proved here.

The splitting rests on a general criterion. Let `φ : A → G` and `ψ : K → G` be smooth
homomorphisms out of connected Lie groups.

* If the images of their Lie maps commute, so do their images
  (`TauCeti.Lie.commute_of_lie_lieMap_eq_zero`, in `TauCeti/Geometry/Lie/Exponential/Commute.lean`).
* In that case `(a, k) ↦ φ a * ψ k` is a smooth homomorphism `A × K → G`
  (`ContMDiffMonoidMorphism.noncommCoprod`), whose Lie map is `(X, Y) ↦ dφ X + dψ Y`
  (`TauCeti.Lie.lieMap_noncommCoprod`). It is bijective as soon as `dφ` and `dψ` are injective
  with complementary ranges (`TauCeti.Lie.bijective_lieMap_noncommCoprod`).
* A smooth homomorphism with bijective Lie map from a connected group to a simply connected one is
  a covering map onto a simply connected space, hence bijective, and it is a local
  diffeomorphism, hence open. So `A × K → G` is an isomorphism of topological groups
  (`TauCeti.Lie.noncommCoprodContinuousMulEquiv`).

For the splitting along ideals, `A` and `K` are the integral leaf subgroups of `𝔞` and `𝔨` with
their intrinsic Lie group structures (`LieSubalgebra.integralLeafSubgroupData`). The ideals bracket
to zero against each other, since `⁅𝔞, 𝔨⁆ ⊆ 𝔞 ⊓ 𝔨 = 0`. The factors are only required to be
connected, not simply connected: the covering argument needs simple connectivity of `G` alone.

## Main definitions

* `TauCeti.Lie.noncommCoprodContinuousMulEquiv`: the product of two commuting smooth homomorphisms
  with complementary Lie algebras, as an isomorphism of topological groups onto a simply connected
  Lie group.
* `TauCeti.Lie.idealProdContinuousMulEquiv`: a simply connected Lie group is the product of the
  integral leaf subgroups of two complementary ideals.
* `TauCeti.Lie.centerProdDerivedContinuousMulEquiv`: the case of the centre and the derived
  algebra.

## Main results

* `TauCeti.Lie.bijective_lieMap_noncommCoprod`: the Lie map of the product is bijective for
  complementary Lie algebras.
* `TauCeti.Lie.commute_integralLeafSubgroupData_center`: the integral leaf subgroup of the centre
  is commutative, by `LieSubalgebra.commute_integralLeafSubgroupData_of_isLieAbelian`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter V, Theorem 8.1 and its proof (the finite cover `T × K → G`).
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Proposition 11.1.3 and Theorem 12.1.17.
-/

public section

noncomputable section

open Function Set
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace TauCeti.Lie

section Criterion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [Group A] [LieGroup I ∞ A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H' K] [Group K] [LieGroup I' ∞ K]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HF : Type*} [TopologicalSpace HF] {J : ModelWithCorners ℝ F HF}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HF G] [Group G] [LieGroup J ∞ G]

/-- The Lie map of the product `(a, k) ↦ φ a * ψ k` of two commuting smooth homomorphisms is
bijective when the Lie maps of `φ` and `ψ` are injective with complementary ranges. -/
theorem bijective_lieMap_noncommCoprod
    (φ : ContMDiffMonoidMorphism I J ∞ A G) (ψ : ContMDiffMonoidMorphism I' J ∞ K G)
    (h : ∀ a k, Commute (φ a) (ψ k)) (hφ : Injective (lieMap φ)) (hψ : Injective (lieMap ψ))
    (hc : IsCompl (LinearMap.range (lieMap φ).toLinearMap)
      (LinearMap.range (lieMap ψ).toLinearMap)) :
    Bijective (lieMap (φ.noncommCoprod ψ h)) := by
  let s := (lieMap φ).toLinearMap.coprod (lieMap ψ).toLinearMap
  have hs : Bijective s := by
    refine ⟨LinearMap.ker_eq_bot.mp ?_, LinearMap.range_eq_top.mp ?_⟩
    · rw [LinearMap.ker_coprod_of_disjoint_range _ _ hc.disjoint, LinearMap.ker_eq_bot.mpr hφ,
        LinearMap.ker_eq_bot.mpr hψ, Submodule.prod_bot]
    · rw [LinearMap.range_coprod, hc.sup_eq_top]
  have heq : ⇑(lieMap (φ.noncommCoprod ψ h)) = s ∘ prodLieEquiv := by
    ext D
    simp only [comp_apply, prodLieEquiv_apply, s, LinearMap.coprod_apply, LieHom.coe_toLinearMap,
      lieMap_noncommCoprod]
  rw [heq]
  exact hs.comp prodLieEquiv.bijective

variable [PreconnectedSpace A] [PreconnectedSpace K] [SimplyConnectedSpace G]

/-- **Splitting a simply connected Lie group into two commuting subgroups.** Let `φ : A → G` and
`ψ : K → G` be smooth homomorphisms out of connected Lie groups into a simply connected Lie group,
with commuting images, whose Lie maps are injective with complementary ranges. Then
`(a, k) ↦ φ a * ψ k` is an isomorphism of topological groups `A × K ≃ₜ* G`. -/
def noncommCoprodContinuousMulEquiv
    (φ : ContMDiffMonoidMorphism I J ∞ A G) (ψ : ContMDiffMonoidMorphism I' J ∞ K G)
    (h : ∀ a k, Commute (φ a) (ψ k)) (hφ : Injective (lieMap φ)) (hψ : Injective (lieMap ψ))
    (hc : IsCompl (LinearMap.range (lieMap φ).toLinearMap)
      (LinearMap.range (lieMap ψ).toLinearMap)) :
    A × K ≃ₜ* G :=
  have hL := bijective_lieMap_noncommCoprod φ ψ h hφ hψ hc
  let μ := φ.noncommCoprod ψ h
  ContinuousMulEquiv.mk'
    ((Equiv.ofBijective μ (μ.bijective_of_lieMap_bijective_of_simplyConnectedSpace hL)
      ).toHomeomorphOfContinuousOpen (map_continuous μ)
      (μ.isLocalDiffeomorph_of_lieMap_bijective hL).isLocalHomeomorph.isOpenMap)
    (map_mul μ)

@[simp]
theorem noncommCoprodContinuousMulEquiv_apply
    (φ : ContMDiffMonoidMorphism I J ∞ A G) (ψ : ContMDiffMonoidMorphism I' J ∞ K G)
    (h : ∀ a k, Commute (φ a) (ψ k)) (hφ : Injective (lieMap φ)) (hψ : Injective (lieMap ψ))
    (hc : IsCompl (LinearMap.range (lieMap φ).toLinearMap)
      (LinearMap.range (lieMap ψ).toLinearMap)) (p : A × K) :
    noncommCoprodContinuousMulEquiv φ ψ h hφ hψ hc p = φ p.1 * ψ p.2 :=
  φ.noncommCoprod_apply ψ h p

end Criterion

section Ideal

attribute [local instance] ImmersedLieSubgroupData.group
  ImmersedLieSubgroupData.topologicalSpace ImmersedLieSubgroupData.normedAddCommGroup
  ImmersedLieSubgroupData.normedSpace ImmersedLieSubgroupData.finiteDimensional
  ImmersedLieSubgroupData.modelTopology ImmersedLieSubgroupData.chartedSpace
  ImmersedLieSubgroupData.lieGroup ImmersedLieSubgroupData.connectedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [SecondCountableTopology G]

variable [SimplyConnectedSpace G]

/-- **A simply connected Lie group is the product of the subgroups integrating two complementary
ideals.** If the Lie algebra `𝔤` of a simply connected Lie group `G` is the direct sum of two ideals
`𝔞` and `𝔨`, then `(a, k) ↦ a * k` identifies the product of their integral leaf subgroups, each
with its intrinsic Lie group structure, with `G` as a topological group. -/
def idealProdContinuousMulEquiv (𝔞 𝔨 : LieIdeal ℝ (LeftInvariantDerivation I G))
    (hc : IsCompl 𝔞 𝔨) :
    ((𝔞 : LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X ×
      ((𝔨 : LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X
      ≃ₜ* G :=
  noncommCoprodContinuousMulEquiv
    ((𝔞 : LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
      (I := I)).toContMDiffMonoidMorphism
    ((𝔨 : LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
      (I := I)).toContMDiffMonoidMorphism
    (commute_of_lie_lieMap_eq_zero _ _ fun X Y ↦ (LieSubmodule.lie_eq_bot_iff (I := 𝔞) (N := 𝔨)).mp
      (eq_bot_iff.mpr ((LieSubmodule.lie_le_inf 𝔞 𝔨).trans hc.disjoint.le_bot)) _
      ((LieIdeal.mem_toLieSubalgebra ℝ _ 𝔞 _).mp
        (LieSubalgebra.lieMap_integralLeafSubgroupData_mem _ X)) _
      ((LieIdeal.mem_toLieSubalgebra ℝ _ 𝔨 _).mp
        (LieSubalgebra.lieMap_integralLeafSubgroupData_mem _ Y)))
    (by
      rw [ImmersedLieSubgroupData.lieMap_toContMDiffMonoidMorphism]
      exact ImmersedLieSubgroupData.injective_lieMapToHom _)
    (by
      rw [ImmersedLieSubgroupData.lieMap_toContMDiffMonoidMorphism]
      exact ImmersedLieSubgroupData.injective_lieMapToHom _)
    (by
      rw [LieSubalgebra.range_lieMap_integralLeafSubgroupData,
        LieSubalgebra.range_lieMap_integralLeafSubgroupData,
        LieIdeal.toLieSubalgebra_toSubmodule, LieIdeal.toLieSubalgebra_toSubmodule,
        LieSubmodule.isCompl_toSubmodule]
      exact hc)

@[simp]
theorem idealProdContinuousMulEquiv_apply (𝔞 𝔨 : LieIdeal ℝ (LeftInvariantDerivation I G))
    (hc : IsCompl 𝔞 𝔨)
    (p : ((𝔞 : LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
      (I := I)).X ×
      ((𝔨 : LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X) :
    idealProdContinuousMulEquiv 𝔞 𝔨 hc p =
      ((𝔞 : LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
        (I := I)).toHom p.1 *
        ((𝔨 : LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
          (I := I)).toHom p.2 := by
  rw [idealProdContinuousMulEquiv, noncommCoprodContinuousMulEquiv_apply,
    ImmersedLieSubgroupData.toContMDiffMonoidMorphism_apply,
    ImmersedLieSubgroupData.toContMDiffMonoidMorphism_apply]

/-- **A simply connected Lie group splits along its centre and derived algebra.** If the centre
`𝔷` and the derived algebra `[𝔤, 𝔤]` of the Lie algebra of a simply connected Lie group `G` are
complementary, as they are for the Lie algebra of a compact Lie group
(`TauCeti.Lie.isCompl_center_derivedSeries_one_of_compactSpace`), then `G` is, as a topological
group, the product of the commutative subgroup integrating the centre `𝔷` of the Lie algebra
(`TauCeti.Lie.commute_integralLeafSubgroupData_center`) and the subgroup integrating
`[𝔤, 𝔤]`. -/
def centerProdDerivedContinuousMulEquiv
    (hc : IsCompl (LieAlgebra.center ℝ (LeftInvariantDerivation I G))
      (LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I G) 1)) :
    ((LieAlgebra.center ℝ (LeftInvariantDerivation I G) :
        LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X ×
      ((LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
        LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X
      ≃ₜ* G :=
  idealProdContinuousMulEquiv _ _ hc

@[simp]
theorem centerProdDerivedContinuousMulEquiv_apply
    (hc : IsCompl (LieAlgebra.center ℝ (LeftInvariantDerivation I G))
      (LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I G) 1))
    (p : ((LieAlgebra.center ℝ (LeftInvariantDerivation I G) :
        LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X ×
      ((LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
        LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X) :
    centerProdDerivedContinuousMulEquiv hc p =
      ((LieAlgebra.center ℝ (LeftInvariantDerivation I G) :
        LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
          (I := I)).toHom p.1 *
        ((LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
          LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
            (I := I)).toHom p.2 :=
  idealProdContinuousMulEquiv_apply _ _ hc p

omit [SimplyConnectedSpace G] in
/-- The integral leaf subgroup of the centre `𝔷` of the Lie algebra, the first factor of
`TauCeti.Lie.centerProdDerivedContinuousMulEquiv`, is commutative. -/
theorem commute_integralLeafSubgroupData_center
    (x y : ((LieAlgebra.center ℝ (LeftInvariantDerivation I G) :
      LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X) :
    Commute x y :=
  have : IsLieAbelian ↥(LieAlgebra.center ℝ (LeftInvariantDerivation I G) :
      LieSubalgebra ℝ (LeftInvariantDerivation I G)) :=
    inferInstanceAs (IsLieAbelian (LieAlgebra.center ℝ (LeftInvariantDerivation I G)))
  LieSubalgebra.commute_integralLeafSubgroupData_of_isLieAbelian _ x y

end Ideal

end TauCeti.Lie
