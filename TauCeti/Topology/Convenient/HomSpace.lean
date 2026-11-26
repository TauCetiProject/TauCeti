/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Convenient.HomSpace
public import TauCeti.Topology.Convenient.GeneratedBy

/-!
# Comparison between `G`-probed mapping spaces and the compact-open topology

Given a family of topological spaces `G : ι → Type u`, Mathlib equips the type
`ContinuousMapGeneratedBy G Y Z` of `G`-continuous maps `Y → Z` with the initial topology induced
by precomposition along continuous maps `G i → Y` into compact-open mapping spaces `C(G i, Z)`.

This file compares `ContinuousMapGeneratedBy G Y Z` with the compact-open mapping space `C(Y, Z)`:

* Every continuous map `Y → Z` is `G`-continuous (`ContinuousMap.toContinuousMapGeneratedBy`), and
  the resulting inclusion `C(Y, Z) → ContinuousMapGeneratedBy G Y Z` is continuous
  (`ContinuousMap.continuous_toContinuousMapGeneratedBy`).
* When `Y` is nonempty and `Z` is nontrivial, `ContinuousMapGeneratedBy G Y Z` is nontrivial
  (`Topology.ContinuousMapGeneratedBy.instNontrivial`).
* When `Y` is `G`-generated, `ContinuousMapGeneratedBy G Y Z` has the same underlying maps as
  `C(Y, Z)` (`Topology.ContinuousMapGeneratedBy.toContinuousMap`,
  `Topology.ContinuousMapGeneratedBy.equivContinuousMap`).
* When every `G i` is locally compact and every `G i × G j` is `G`-generated, the `G`-generated
  refinements `WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y Z)` and
  `WithGeneratedByTopology G C(Y, Z)` are homeomorphic for every `G`-generated source `Y`
  (`Topology.ContinuousMapGeneratedBy.generatedByHomeomorphContinuousMap`), with no local
  compactness, separation, or size assumption on `Y`.
* When, in addition, every compact subset of `Y` is the continuous image of a compact subset of
  some generator `G i`, the unrefined topologies already coincide
  (`Topology.ContinuousMapGeneratedBy.continuous_toContinuousMap`,
  `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMap`).

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Proposition A.16.
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

instance instNontrivial [Nonempty Y] [Nontrivial Z] :
    Nontrivial (ContinuousMapGeneratedBy G Y Z) := by
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  obtain ⟨z₁, z₂, hz⟩ := exists_pair_ne Z
  exact ⟨(ContinuousMap.const Y z₁).toContinuousMapGeneratedBy G,
    (ContinuousMap.const Y z₂).toContinuousMapGeneratedBy G,
    fun h ↦ hz (by simpa using congr($h y₀))⟩

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

@[simp]
theorem toContinuousMap_toContinuousMapGeneratedBy [IsGeneratedBy G Y] (f : C(Y, Z)) :
    (f.toContinuousMapGeneratedBy G).toContinuousMap = f := by ext; rfl

@[simp]
theorem toContinuousMapGeneratedBy_toContinuousMap [IsGeneratedBy G Y]
    (g : ContinuousMapGeneratedBy G Y Z) :
    g.toContinuousMap.toContinuousMapGeneratedBy G = g := by ext; rfl

/-- When `Y` is `G`-generated, `G`-continuous maps `Y → Z` coincide with continuous maps `Y → Z`. -/
@[expose]
def equivContinuousMap [IsGeneratedBy G Y] : ContinuousMapGeneratedBy G Y Z ≃ C(Y, Z) where
  toFun := toContinuousMap
  invFun := ContinuousMap.toContinuousMapGeneratedBy G
  left_inv := toContinuousMapGeneratedBy_toContinuousMap
  right_inv := toContinuousMap_toContinuousMapGeneratedBy

@[simp]
theorem equivContinuousMap_apply [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) :
    equivContinuousMap f = f.toContinuousMap := (rfl)

@[simp]
theorem equivContinuousMap_symm_apply [IsGeneratedBy G Y] (f : C(Y, Z)) :
    (equivContinuousMap (G := G)).symm f = f.toContinuousMapGeneratedBy G := (rfl)

/-- Suppose `[∀ i, LocallyCompactSpace (G i)]` and `[∀ i j, IsGeneratedBy G (G i × G j)]`. For any
`G`-generated source `Y` (with no local compactness, Hausdorffness, or smallness assumption on
`Y`), the `G`-generated refinements `WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y Z)`
and `WithGeneratedByTopology G C(Y, Z)` are homeomorphic via `equivContinuousMap`. -/
def generatedByHomeomorphContinuousMap [IsGeneratedBy G Y]
    [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)] :
    WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y Z) ≃ₜ
      WithGeneratedByTopology G C(Y, Z) where
  toEquiv := WithGeneratedByTopology.equiv.trans
    (equivContinuousMap.trans WithGeneratedByTopology.equiv.symm)
  continuous_toFun := (WithGeneratedByTopology.continuous_from_iff _).2 fun i f ↦ by
    simp only [Equiv.toFun_as_coe, Equiv.coe_trans, Function.comp_def, Equiv.apply_symm_apply]
    refine (IsGeneratedBy.equiv_symm_comp_continuous_iff G
      (fun x : G i ↦ equivContinuousMap (f x))).2 ?_
    have hf := (continuousGeneratedBy_iff_uncurry _).1 f.continuous.continuousGeneratedBy
    have : IsGeneratedBy G (G i × Y) := IsGeneratedBy.prod_of_locallyCompactSpace_left
    exact (ContinuousMap.curry ⟨fun p : G i × Y ↦ f p.1 p.2, (IsGeneratedBy.continuous_iff G _).2
      fun _ r ↦ (hf (ContinuousMap.fst.comp r) (ContinuousMap.snd.comp r)).comp
        (continuous_id.prodMk continuous_id)⟩).continuous
  continuous_invFun := (WithGeneratedByTopology.continuous_from_iff _).2 fun _ f ↦ by
    simp only [Equiv.invFun_as_coe, Equiv.symm_trans_apply, Equiv.symm_symm, Function.comp_def,
      Equiv.apply_symm_apply]
    exact (IsGeneratedBy.equiv_symm_comp_continuous_iff G
      (fun x ↦ (equivContinuousMap (G := G)).symm (f x))).2
      (ContinuousMap.continuous_toContinuousMapGeneratedBy.comp f.continuous)

@[simp]
theorem generatedByHomeomorphContinuousMap_apply [IsGeneratedBy G Y]
    [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]
    (g : WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y Z)) :
    WithGeneratedByTopology.equiv (generatedByHomeomorphContinuousMap g) =
      (WithGeneratedByTopology.equiv g).toContinuousMap := (rfl)

@[simp]
theorem generatedByHomeomorphContinuousMap_symm_apply [IsGeneratedBy G Y]
    [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]
    (f : WithGeneratedByTopology G C(Y, Z)) :
    WithGeneratedByTopology.equiv (generatedByHomeomorphContinuousMap.symm f) =
      (WithGeneratedByTopology.equiv f).toContinuousMapGeneratedBy G := (rfl)

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
