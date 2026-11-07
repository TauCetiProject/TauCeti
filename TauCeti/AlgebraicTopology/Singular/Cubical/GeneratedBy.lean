/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.Topology.Convenient.CompactlyGenerated
public import Mathlib.Topology.Convenient.Category
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Cubical chains and generated topologies

Refining a space by a family of generators that generates every finite cube does not change
its normalized cubical chain complex. Every cube lifts uniquely through the counit, and the
counit reflects degeneracy. The resulting chain isomorphism is natural in the space.

`TauCeti.normalizedCubicalChainComplexGeneratedByIso` uses Mathlib's actual generated-topology
counit, rather than an independently chosen homology comparison. The compact Hausdorff family
satisfies the hypotheses, so the result applies to compact generation of arbitrary spaces,
including compact-open mapping spaces and stopped Moore path spaces. No separation or
compact-generation condition on the original space is needed.

## References

* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory* (1971).
* W. S. Massey, *Singular Homology Theory*, Chapter II (normalized cubical chains).

The generated-space functor and counit are Mathlib's `TopCat.toGeneratedByTopCat` and
`GeneratedByTopCat.adjCounit`.
-/

public section

noncomputable section

universe t u v

open CategoryTheory Topology unitInterval

namespace TauCeti

variable {ι : Type t} (G : ι → Type v) [∀ i, TopologicalSpace (G i)]

namespace NormalizedCubicalChain

variable (R : Type u) [Ring R] (X : Type*) [TopologicalSpace X]

/-- The generated-topology counit is bijective on normalized cubical chains. -/
theorem bijective_map_generatedByCounit (n : ℕ) [IsGeneratedBy G (Fin n → I)] :
    Function.Bijective (map R
      (⟨WithGeneratedByTopology.equiv, WithGeneratedByTopology.continuous_equiv⟩ :
        C(WithGeneratedByTopology G X, X)) n) := by
  let ε : C(WithGeneratedByTopology G X, X) :=
    ⟨WithGeneratedByTopology.equiv, WithGeneratedByTopology.continuous_equiv⟩
  refine ⟨map_injective R ε WithGeneratedByTopology.equiv.injective n, ?_⟩
  rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
  intro c
  induction c using NormalizedCubicalChain.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | smul r a ha => exact Submodule.smul_mem _ r ha
  | ofCube c =>
    exact ⟨ofCube _ R (c.toGeneratedBy G), by simp⟩

end NormalizedCubicalChain

variable [∀ n : ℕ, IsGeneratedBy G (Fin n → I)] (R : Type u) [Ring R]

/-- The actual generated-topology counit induces an isomorphism of normalized cubical
chain complexes. -/
instance isIso_normalizedCubicalChainComplex_map_generatedByCounit (X : TopCat.{u}) :
    IsIso ((normalizedCubicalChainComplex R).map
      ((GeneratedByTopCat.adjCounit (X := G)).app X)) := by
  have (n : ℕ) : IsIso (((normalizedCubicalChainComplex R).map
      ((GeneratedByTopCat.adjCounit (X := G)).app X)).f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact NormalizedCubicalChain.bijective_map_generatedByCounit G R X n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Normalized cubical chains are naturally unchanged by a generated refinement whose
generators generate every finite cube. In particular, this applies to compact generation. -/
def normalizedCubicalChainComplexGeneratedByIso :
    (TopCat.toGeneratedByTopCat (X := G) ⋙ GeneratedByTopCat.toTopCat) ⋙
        normalizedCubicalChainComplex R ≅ normalizedCubicalChainComplex R :=
  NatIso.ofComponents
    (fun X ↦ asIso ((normalizedCubicalChainComplex R).map
      ((GeneratedByTopCat.adjCounit (X := G)).app X)))
    (fun f ↦ by
      simpa only [asIso_hom, Functor.comp_map, Functor.id_map, ← Functor.map_comp] using
        congrArg ((normalizedCubicalChainComplex R).map)
          ((GeneratedByTopCat.adjCounit (X := G)).naturality f))

/-- The forward comparison is the chain map induced by the counit. -/
@[simp]
theorem normalizedCubicalChainComplexGeneratedByIso_hom_app (X : TopCat.{u}) :
    (normalizedCubicalChainComplexGeneratedByIso G R).hom.app X =
      (normalizedCubicalChainComplex R).map
        ((GeneratedByTopCat.adjCounit (X := G)).app X) :=
  (rfl)

/-- On generators, the inverse comparison lifts the same cube to the generated topology. -/
theorem normalizedCubicalChainComplexGeneratedByIso_inv_app_f_ofCube (X : TopCat.{u})
    {n : ℕ} (c : SingularCube X n) :
    ((normalizedCubicalChainComplexGeneratedByIso G R).inv.app X).f n
        (NormalizedCubicalChain.ofCube X R c) =
      NormalizedCubicalChain.ofCube _ R (c.toGeneratedBy G) := by
  apply (NormalizedCubicalChain.bijective_map_generatedByCounit G R X n).injective
  let e := (normalizedCubicalChainComplexGeneratedByIso G R).app X
  have h := (HomologicalComplex.Hom.isoApp e n).inv_hom_id_apply
    ((normalizedCubicalChainComplexXEquiv X n).symm (NormalizedCubicalChain.ofCube X R c))
  have hc := congrArg (normalizedCubicalChainComplexXEquiv X n) h
  simp only [HomologicalComplex.Hom.isoApp_hom, HomologicalComplex.Hom.isoApp_inv,
    e, Iso.app_hom, Iso.app_inv] at hc
  rw [normalizedCubicalChainComplexGeneratedByIso_hom_app,
    normalizedCubicalChainComplexXEquiv_map_f_apply] at hc
  have hε : ((GeneratedByTopCat.adjCounit (X := G)).app X).hom =
      (⟨WithGeneratedByTopology.equiv, WithGeneratedByTopology.continuous_equiv⟩ :
        C(WithGeneratedByTopology G X, X)) := (rfl)
  rw [hε] at hc
  -- Align the native functor's object with the explicit generated-topology carrier.
  simpa only [normalizedCubicalChainComplexXEquiv_apply,
    normalizedCubicalChainComplexXEquiv_symm_apply, NormalizedCubicalChain.map_ofCube,
    ContinuousMap.equiv_comp_toGeneratedBy] using! hc

end TauCeti
