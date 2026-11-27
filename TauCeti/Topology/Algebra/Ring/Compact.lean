/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Compact
public import TauCeti.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Filtration
import Mathlib.Topology.Algebra.Module.Compact
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# The topology of a compact Hausdorff noetherian local ring is adic

Let `R` be a compact Hausdorff noetherian local ring with maximal ideal `m`, for instance the
valuation ring of a nonarchimedean local field or a complete noetherian local ring with finite
residue field and its `m`-adic topology. Mathlib shows that every power `m ^ n` is open
(`IsLocalRing.isOpen_maximalIdeal_pow`). Conversely, the powers `m ^ n` are compact, they decrease,
and they meet only in `0` by the Krull intersection theorem, so every neighbourhood of `0`
contains one of them. Hence the topology of `R` is its `m`-adic topology, with no completeness
or discreteness hypothesis. This identifies the neighbourhoods of the identity in the groups of
points over `R` of an affine group of finite type with its congruence subgroups.

More generally, whenever the maximal ideal of a local ring with continuous translations (for
instance a topological ring) is open, as it is for a compact Hausdorff noetherian local ring
(`IsLocalRing.isOpen_maximalIdeal`), the residue map is continuous for every topology on the
residue field, being constant on the open cosets of the maximal ideal.

## Main results

* `IsLocalRing.isAdic_maximalIdeal`: the topology of a compact Hausdorff noetherian local ring is
  its `m`-adic topology.
* `IsLocalRing.totallyDisconnectedSpace_of_compactSpace`,
  `IsLocalRing.isAdicComplete_maximalIdeal_of_compactSpace`: `R` is totally disconnected and
  `m`-adically complete.
* `IsLocalRing.continuous_residue`: the residue map of a local ring with continuous translations
  and open maximal ideal is continuous for every topology on its residue field.
-/

public section

open Topology

namespace IsLocalRing

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R]

/-- **The topology of a compact Hausdorff noetherian local ring is its `m`-adic topology**: the
powers of the maximal ideal are open, and every neighbourhood of `0` contains one of them. -/
theorem isAdic_maximalIdeal : IsAdic (maximalIdeal R) := by
  refine isAdic_iff.mpr ⟨isOpen_maximalIdeal_pow R, fun s hs ↦ ?_⟩
  -- The powers `m ^ n` are compact, decreasing, and meet in `{0}` by Krull's intersection theorem.
  have hinter : (⋂ n : ℕ, ((maximalIdeal R ^ n : Ideal R) : Set R)) = {0} := by
    rw [← Submodule.coe_iInf,
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Submodule.bot_coe]
  refine exists_subset_nhds_of_isCompact (fun i j ↦ ⟨max i j, ?_, ?_⟩)
    (fun n ↦ Ideal.isCompact_of_fg (IsNoetherian.noetherian _)) (by rwa [hinter, nhdsSet_singleton])
  · exact Ideal.pow_le_pow_right (le_max_left i j)
  · exact Ideal.pow_le_pow_right (le_max_right i j)

/-- A compact Hausdorff noetherian local ring is totally disconnected. -/
theorem totallyDisconnectedSpace_of_compactSpace : TotallyDisconnectedSpace R :=
  (isAdic_maximalIdeal R).totallyDisconnectedSpace

/-- **A compact Hausdorff noetherian local ring is `m`-adically complete and separated.** -/
theorem isAdicComplete_maximalIdeal_of_compactSpace : IsAdicComplete (maximalIdeal R) R :=
  (isAdic_maximalIdeal R).isAdicComplete_of_compactSpace

/-- **The residue map is continuous when translations are continuous and the maximal ideal is
open**, for every topology on the residue field. -/
theorem continuous_residue {S : Type*} [CommRing S] [IsLocalRing S] [TopologicalSpace S]
    [ContinuousConstVAdd S S] [TopologicalSpace (ResidueField S)]
    (h : IsOpen (maximalIdeal S : Set S)) : Continuous (residue S) :=
  (residue S).toAddMonoidHom.continuous_of_isOpen_ker <| by
    convert h using 1
    ext x
    simp

end IsLocalRing
