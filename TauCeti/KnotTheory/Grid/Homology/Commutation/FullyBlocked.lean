/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Grading.Map
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.FullyBlocked
public import TauCeti.KnotTheory.Grid.Homology.FullyBlockedBigraded
import TauCeti.Algebra.CharP.Two

/-!
# Commutation invariance of fully blocked grid homology

The fully blocked pentagon chain map `Φ~` of a validated column commutation induces a specified map
on fully blocked homology: the class of a cycle is sent to the class of its pentagon image. This
uses `LinearMap.homologyMap` through the identification with the kernel modulo the image of the
differential.

The fully blocked homotopy equations
(`GridDiagram.fullyBlockedDifferential_fullyBlockedCommutationHomotopy_add_eq` and its `_reverse_`
form) show that `Φ~` and the pentagon map `Ψ~` of the reverse commutation are inverse to each other
up to boundaries on cycles, so the induced map on `GH~` (written $\widetilde{GH}$ in the
literature) is bijective. The fully blocked pentagons carry no markings, so `Φ~` preserves the
`(O-Maslov, Alexander)` bidegree of every state; hence the induced equivalence commutes with the
homogeneous projections, and the bigraded Poincaré series of `GH~` is unchanged by a column
commutation.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedHomologyCommutationMap`: the map induced on fully blocked
  homology by the fully blocked pentagon map.
* `TauCeti.GridDiagram.fullyBlockedHomologyCommutationEquiv`: the same map, as a linear
  equivalence.

## Main results

* `TauCeti.GridDiagram.fullyBlockedHomologyCommutationMap_bijective`: **commutation invariance of
  `GH~`**, the induced map is bijective.
* `fullyBlockedHomologyCommutationMap_bigradedFullyBlockedHomologyProjection`: for a diagram with
  an odd number of components, the induced map commutes with the homogeneous projections.
* `TauCeti.OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_swapColumns` and
  `bigradedFullyBlockedHomologyPoincareSeries_eq_of_isColumnCommutation`: a column commutation
  does not change the bigraded Poincaré series of `GH~`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The bijectivity argument is that of
`GridDiagram.unblockedHomologyCommutationMap_bijective` for `GH⁻`.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "G'" => G.swapColumns C.column (finRotate n C.column)

/-- The fully blocked pentagon map sends cycles to cycles. -/
theorem fullyBlockedCommutationMap_mem_cycles {z : GridChain (ZMod 2) n}
    (hz : z ∈ G.fullyBlockedCycles) :
    G.fullyBlockedCommutationMap (ZMod 2) C z ∈ (G').fullyBlockedCycles := by
  rw [mem_fullyBlockedCycles] at hz ⊢
  have h := LinearMap.congr_fun (G.fullyBlockedCommutationMap_comp_fullyBlockedDifferential C) z
  simpa only [LinearMap.comp_apply, hz, map_zero] using h.symm

/-- The fully blocked pentagon map of the reverse commutation sends cycles of the commuted diagram
to cycles of `G`. -/
theorem fullyBlockedCommutationMap_reverse_mem_cycles {z : GridChain (ZMod 2) n}
    (hz : z ∈ (G').fullyBlockedCycles) :
    (G').fullyBlockedCommutationMap (ZMod 2) C.reverse z ∈ G.fullyBlockedCycles := by
  rw [mem_fullyBlockedCycles] at hz ⊢
  have h := LinearMap.congr_fun
    (G.fullyBlockedCommutationMap_reverse_comp_fullyBlockedDifferential C) z
  simpa only [LinearMap.comp_apply, hz, map_zero] using h.symm

/-- The specified map on fully blocked homology induced by counting empty pentagons avoiding
all markings. -/
noncomputable def fullyBlockedHomologyCommutationMap :
    G.fullyBlockedHomology →ₗ[ZMod 2] (G').fullyBlockedHomology :=
  (G').fullyBlockedHomologyEquivLinearMapHomology.symm.toLinearMap.comp
    ((LinearMap.homologyMap (G.fullyBlockedCommutationMap (ZMod 2) C)
      G.fullyBlockedDifferential_comp_self_eq_zero
      (G').fullyBlockedDifferential_comp_self_eq_zero
      (G.fullyBlockedCommutationMap_comp_fullyBlockedDifferential C)).comp
        G.fullyBlockedHomologyEquivLinearMapHomology.toLinearMap)

/-- A cycle class is sent to the class of its fully blocked pentagon image. -/
@[simp]
theorem fullyBlockedHomologyCommutationMap_mk (z : G.fullyBlockedCycles) :
    G.fullyBlockedHomologyCommutationMap C (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (⟨G.fullyBlockedCommutationMap (ZMod 2) C z,
          G.fullyBlockedCommutationMap_mem_cycles C z.2⟩ : (G').fullyBlockedCycles) := by
  simp only [fullyBlockedHomologyCommutationMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    fullyBlockedHomologyEquivLinearMapHomology_mk, LinearMap.homologyMap_mk,
    fullyBlockedHomologyEquivLinearMapHomology_symm_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp only [LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]

/-- **Commutation invariance of `GH~`.** The map induced on fully blocked grid homology by the
fully blocked pentagon map of a validated column commutation is bijective. -/
theorem fullyBlockedHomologyCommutationMap_bijective :
    Function.Bijective (G.fullyBlockedHomologyCommutationMap C) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, fun y => ?_⟩
  · -- If `Φ~ z = ∂~' w`, then `z = Ψ~ Φ~ z + ∂~ H~ z = ∂~ (Ψ~ w + H~ z)`.
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      rw [fullyBlockedHomologyCommutationMap_mk, fullyBlockedHomology_mk_eq_zero_iff,
        mem_fullyBlockedBoundaries] at hy
      obtain ⟨w, hw⟩ := hy
      rw [fullyBlockedHomology_mk_eq_zero_iff, mem_fullyBlockedBoundaries]
      refine ⟨(G').fullyBlockedCommutationMap (ZMod 2) C.reverse w +
        G.fullyBlockedCommutationHomotopy (ZMod 2) C z, ?_⟩
      have hΨ := LinearMap.congr_fun
        (G.fullyBlockedCommutationMap_reverse_comp_fullyBlockedDifferential C) w
      have hH := G.fullyBlockedDifferential_fullyBlockedCommutationHomotopy_add_eq C z
      rw [(mem_fullyBlockedCycles _ _).mp z.2, map_zero, add_zero] at hH
      simp only [LinearMap.comp_apply, hw] at hΨ
      rw [map_add, ← hΨ, hH, add_left_comm, add_self_eq_zero_of_charTwo (ZMod 2), add_zero]
  · -- The class of a cycle `z` of `GC~(G')` is the image of the class of `Ψ~ z`, since
    -- `Φ~ Ψ~ z - z = ∂~' H~' z`.
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk
        ⟨_, G.fullyBlockedCommutationMap_reverse_mem_cycles C z.2⟩, ?_⟩
      rw [fullyBlockedHomologyCommutationMap_mk, fullyBlockedHomology_mk_eq_iff,
        mem_fullyBlockedBoundaries]
      refine ⟨(G').fullyBlockedCommutationHomotopy (ZMod 2) C.reverse z, ?_⟩
      have hH := G.fullyBlockedDifferential_fullyBlockedCommutationHomotopy_reverse_add_eq C z
      rw [(mem_fullyBlockedCycles _ _).mp z.2, map_zero, add_zero] at hH
      rw [hH, sub_eq_add_neg, neg_eq_of_add_eq_zero_left
        (add_self_eq_zero_of_charTwo (ZMod 2) (z : GridChain (ZMod 2) n))]
      exact add_comm _ _

/-- **Commutation invariance of `GH~`**, as a linear equivalence: the map induced on fully blocked
grid homology by the fully blocked pentagon map of a validated column commutation. -/
noncomputable def fullyBlockedHomologyCommutationEquiv :
    G.fullyBlockedHomology ≃ₗ[ZMod 2] (G').fullyBlockedHomology :=
  LinearEquiv.ofBijective _ (G.fullyBlockedHomologyCommutationMap_bijective C)

/-- The commutation equivalence of `GH~` is the map induced by the fully blocked pentagon map. -/
@[simp]
theorem coe_fullyBlockedHomologyCommutationEquiv :
    ⇑(G.fullyBlockedHomologyCommutationEquiv C) = G.fullyBlockedHomologyCommutationMap C :=
  (rfl)

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (C : GridDiagram.ColumnCommutationData G.1)

/-- The map induced on fully blocked homology by a column commutation commutes with the
homogeneous projections. -/
theorem fullyBlockedHomologyCommutationMap_bigradedFullyBlockedHomologyProjection (g : ℤ × ℤ)
    (y : G.1.fullyBlockedHomology) :
    G.1.fullyBlockedHomologyCommutationMap C (G.bigradedFullyBlockedHomologyProjection g y) =
      (G.swapColumns C).bigradedFullyBlockedHomologyProjection g
        (G.1.fullyBlockedHomologyCommutationMap C y) := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    rw [bigradedFullyBlockedHomologyProjection_mk,
      GridDiagram.fullyBlockedHomologyCommutationMap_mk,
      GridDiagram.fullyBlockedHomologyCommutationMap_mk]
    -- The projection lemma is stated at `(G.swapColumns C).1`, which is only definitionally the
    -- commuted diagram in the type of the class, so it is applied explicitly rather than by `rw`.
    refine Eq.trans ?_ (bigradedFullyBlockedHomologyProjection_mk (G.swapColumns C) g
      ⟨_, G.1.fullyBlockedCommutationMap_mem_cycles C z.2⟩).symm
    congr 1
    ext1
    have h := G.map_bigradedChainInclusion_bigradedChainProjection (G.swapColumns C)
      (G.1.fullyBlockedCommutationMap (ZMod 2) C) 0
      (fun x y hy => G.fullyBlockedCommutationMap_single_apply_eq_zero_of_bidegree_ne C (ZMod 2)
        (by rwa [add_zero] at hy)) g z
    rw [add_zero] at h
    exact h

/-- **A column commutation preserves the Poincaré series of `GH~`.** -/
theorem bigradedFullyBlockedHomologyPoincareSeries_swapColumns :
    (G.swapColumns C).bigradedFullyBlockedHomologyPoincareSeries =
      G.bigradedFullyBlockedHomologyPoincareSeries :=
  (G.bigradedFullyBlockedHomologyPoincareSeries_eq_of_linearEquiv
    (G.1.fullyBlockedHomologyCommutationEquiv C)
    (G.fullyBlockedHomologyCommutationMap_bigradedFullyBlockedHomologyProjection C)).symm

/-- Grid diagrams with an odd number of components related by an elementary column commutation
have the same Poincaré series of fully blocked homology. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_eq_of_isColumnCommutation
    {G G' : OddComponentGridDiagram n} (h : GridDiagram.IsColumnCommutation G.1 G'.1) :
    G.bigradedFullyBlockedHomologyPoincareSeries =
      G'.bigradedFullyBlockedHomologyPoincareSeries := by
  obtain ⟨C, hC⟩ := GridDiagram.isColumnCommutation_iff_exists_columnCommutationData.mp h
  obtain rfl : G' = G.swapColumns C := Subtype.ext hC
  exact (G.bigradedFullyBlockedHomologyPoincareSeries_swapColumns C).symm

end TauCeti.OddComponentGridDiagram
