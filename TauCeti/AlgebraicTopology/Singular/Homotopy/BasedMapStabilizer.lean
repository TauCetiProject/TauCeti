/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import TauCeti.Topology.MappingSpace.Action

/-!
# The identity path component of a stabilizer acts trivially on the homology of based maps

Let a group `G` act continuously on `X`, and let `x ∈ X`. The stabilizer of `x` acts on the based
mapping space `Map_*(B, X)` by postcomposition (`TauCeti.BasedMap.instMulActionStabilizer`). A path
from `1` to `h` in the stabilizer is a homotopy from the identity of `Map_*(B, X)` to the action of
`h`, so such an `h` fixes every class of the singular homology of `Map_*(B, X)`, with any
coefficients. When the stabilizer is path connected, this applies to all of its elements.

## Main results

* `JoinedIn.homologyMap_stabilizer_smul_apply`: an element of the stabilizer joined to `1` by a
  path in the stabilizer fixes every class of the singular homology of the based mapping space.
-/

public section

open CategoryTheory

universe u

/-- **The identity path component of a stabilizer fixes the homology of based maps.** If `h` is
joined to `1` by a path in the stabilizer of `x`, that path is a homotopy from the identity of the
based mapping space `Map_*(B, X)` to the action of `h`, so `h` fixes every class of its singular
homology. For a path-connected stabilizer `hstab`, apply it to
`hstab.joinedIn 1 (one_mem _) h h.property`; this supplies the hypothesis of
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero` for a group action with
path-connected stabilizer. -/
theorem JoinedIn.homologyMap_stabilizer_smul_apply {G : Type*} {X B : Type u} [Group G]
    [TopologicalSpace G] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    [TopologicalSpace B] {b₀ : B} {x : X} {h : MulAction.stabilizer G x}
    (hh : JoinedIn (MulAction.stabilizer G x : Set G) 1 (h : G)) {Λ : Type*} [Ring Λ]
    (R : ModuleCat.{u} Λ) (k : ℕ)
    (α : ((TopCat.toSSet.obj (TopCat.of (TauCeti.BasedMap B X b₀ x))).homology R k :
      ModuleCat.{u} Λ)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : TauCeti.BasedMap B X b₀ x →
      TauCeti.BasedMap B X b₀ x), continuous_const_smul h⟩)) R k).hom α = α := by
  let γ := hh.joined_subtype.somePath
  let H : ContinuousMap.Homotopy (ContinuousMap.id (TauCeti.BasedMap B X b₀ x))
      ⟨(h • · : TauCeti.BasedMap B X b₀ x → TauCeti.BasedMap B X b₀ x), continuous_const_smul h⟩ :=
    { toFun := fun p ↦ (⟨(γ p.1 : G), (γ p.1).property⟩ : MulAction.stabilizer G x) • p.2
      continuous_toFun := continuous_smul.comp
        (((continuous_subtypeVal.comp (γ.continuous.comp continuous_fst)).subtype_mk _).prodMk
          continuous_snd)
      map_zero_left := fun u ↦ by
        simp only [Path.source, ContinuousMap.id_apply]
        exact one_smul _ u
      map_one_left := fun u ↦ by simp }
  have hH := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom (ContinuousMap.id _)) (g := TopCat.ofHom _) H R k
  rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at hH
  exact (ConcreteCategory.congr_hom hH.symm α).trans (ConcreteCategory.id_apply α)
