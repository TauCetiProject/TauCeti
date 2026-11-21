/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Convenient.HomSpace

/-!
# Comparison between `G`-probed mapping spaces and the compact-open topology

Given a family of topological spaces `G : ι → Type u`, Mathlib equips the type
`ContinuousMapGeneratedBy G Y Z` of `G`-continuous maps `Y → Z` with the initial topology induced
by precomposition along continuous maps `G i → Y` into compact-open mapping spaces `C(G i, Z)`.

This file compares `ContinuousMapGeneratedBy G Y Z` with the compact-open mapping space `C(Y, Z)`:

* Every continuous map `Y → Z` is `G`-continuous (`ContinuousMap.toContinuousMapGeneratedBy`), and
  the resulting inclusion `C(Y, Z) → ContinuousMapGeneratedBy G Y Z` is continuous
  (`ContinuousMap.continuous_toContinuousMapGeneratedBy`).
* When `Y` is `G`-generated, `ContinuousMapGeneratedBy G Y Z` has the same underlying maps as
  `C(Y, Z)` (`Topology.ContinuousMapGeneratedBy.toContinuousMap`,
  `Topology.ContinuousMapGeneratedBy.equivContinuousMap`).
* When, in addition, every compact subset of `Y` is the continuous image of a compact subset of
  some generator `G i`, the two topologies coincide
  (`Topology.ContinuousMapGeneratedBy.continuous_toContinuousMap`,
  `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMap`).

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
-/

public section

open Topology

universe v v' t u

variable {ι : Type t} {G : ι → Type u} [∀ i, TopologicalSpace (G i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace ContinuousMap

/-- Every continuous map `Y → Z` is `G`-continuous. -/
@[expose]
def toContinuousMapGeneratedBy (G : ι → Type u) [∀ i, TopologicalSpace (G i)] (f : C(Y, Z)) :
    ContinuousMapGeneratedBy G Y Z :=
  ⟨f, f.continuous.continuousGeneratedBy⟩

@[simp]
theorem toContinuousMapGeneratedBy_apply (f : C(Y, Z)) (y : Y) :
    f.toContinuousMapGeneratedBy G y = f y := rfl

/-- The canonical inclusion from the compact-open mapping space `C(Y, Z)` to
`ContinuousMapGeneratedBy G Y Z` is continuous. -/
@[continuity, fun_prop]
theorem continuous_toContinuousMapGeneratedBy :
    Continuous (toContinuousMapGeneratedBy G : C(Y, Z) → ContinuousMapGeneratedBy G Y Z) :=
  ContinuousMapGeneratedBy.continuous_iff.2 fun _ p ↦ p.continuous_precomp

end ContinuousMap

namespace Topology.ContinuousMapGeneratedBy

/-- When the source `Y` is `G`-generated, every `G`-continuous map `Y → Z` is continuous. -/
@[expose]
def toContinuousMap [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) : C(Y, Z) :=
  ⟨f, (IsGeneratedBy.continuous_iff G f).2 f.prop⟩

@[simp]
theorem toContinuousMap_apply [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) (y : Y) :
    f.toContinuousMap y = f y := rfl

@[simp]
theorem coe_toContinuousMap [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) :
    (f.toContinuousMap : Y → Z) = f := rfl

/-- When `Y` is `G`-generated, `G`-continuous maps `Y → Z` coincide with continuous maps `Y → Z`. -/
@[expose]
def equivContinuousMap [IsGeneratedBy G Y] : ContinuousMapGeneratedBy G Y Z ≃ C(Y, Z) where
  toFun := toContinuousMap
  invFun := ContinuousMap.toContinuousMapGeneratedBy G
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

@[simp]
theorem equivContinuousMap_apply [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) :
    equivContinuousMap f = f.toContinuousMap := (rfl)

@[simp]
theorem equivContinuousMap_symm_apply [IsGeneratedBy G Y] (f : C(Y, Z)) :
    (equivContinuousMap (G := G)).symm f = f.toContinuousMapGeneratedBy G := (rfl)

/-- If every compact subset of `Y` is the image of a compact subset of some generator `G i` along a
continuous map `G i → Y`, then `toContinuousMap` is continuous into the compact-open topology on
`C(Y, Z)`. -/
theorem continuous_toContinuousMap [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) :
    Continuous (toContinuousMap : ContinuousMapGeneratedBy G Y Z → C(Y, Z)) := by
  refine ContinuousMap.continuous_compactOpen.2 fun K hK U hU ↦ ?_
  obtain ⟨i, L, p, hL, rfl⟩ := hG hK
  have hpre : {f : ContinuousMapGeneratedBy G Y Z | Set.MapsTo f.toContinuousMap (p '' L) U} =
      precomp p ⁻¹' {g : C(G i, Z) | Set.MapsTo g L U} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, coe_toContinuousMap, precomp_apply,
      Set.mapsTo_image_iff]
  rw [hpre]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hL hU).preimage (continuous_precomp p)

/-- When `Y` is `G`-generated and every compact subset of `Y` is the continuous image of a compact
subset of some generator `G i`, the `G`-probed mapping space `ContinuousMapGeneratedBy G Y Z` is
homeomorphic to `C(Y, Z)` with the compact-open topology. -/
@[expose]
def homeomorphContinuousMap [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) :
    ContinuousMapGeneratedBy G Y Z ≃ₜ C(Y, Z) where
  toEquiv := equivContinuousMap
  continuous_toFun := continuous_toContinuousMap hG
  continuous_invFun := ContinuousMap.continuous_toContinuousMapGeneratedBy

@[simp]
theorem homeomorphContinuousMap_apply [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K)
    (f : ContinuousMapGeneratedBy G Y Z) :
    homeomorphContinuousMap hG f = f.toContinuousMap := (rfl)

@[simp]
theorem homeomorphContinuousMap_symm_apply [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) (f : C(Y, Z)) :
    (homeomorphContinuousMap (Z := Z) hG).symm f = f.toContinuousMapGeneratedBy G := (rfl)

end Topology.ContinuousMapGeneratedBy
