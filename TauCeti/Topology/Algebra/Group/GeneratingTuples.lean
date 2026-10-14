/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# Generating tuples in quotients by open normal subgroups

A tuple in a group generates a quotient when its image generates that quotient. For a group
with separately continuous multiplication, the set of tuples indexed by a finite type that
generate the quotient by an open normal subgroup is closed. Generation descends along quotient
maps for arbitrary index types.

For compact groups these quotients are finite, and compactness produces a single tuple that
generates every quotient by an open normal subgroup containing a fixed subgroup `N`, as soon as
each such quotient has a generating tuple indexed by the same finite type
(`TauCeti.iInter_generatingTuples_nonempty`). No compatibility between the generating tuples of
different quotients is needed.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The `ι`-indexed tuples whose images generate the quotient by an open normal subgroup.
Repetitions are allowed; use `ι := Fin n` for tuples of length `n`. -/
def generatingTuples (ι : Type*) (U : OpenNormalSubgroup G) : Set (ι → G) :=
  {x | Subgroup.closure (Set.range fun i ↦ (QuotientGroup.mk (x i) : G ⧸ U.toSubgroup)) = ⊤}

/-- Membership in `generatingTuples` means that the images of the tuple generate the quotient. -/
@[simp]
theorem mem_generatingTuples (ι : Type*) (U : OpenNormalSubgroup G) (x : ι → G) :
    x ∈ generatingTuples ι U ↔
      Subgroup.closure (Set.range fun i ↦ (QuotientGroup.mk (x i) : G ⧸ U.toSubgroup)) = ⊤ :=
  Iff.rfl

/-- A tuple generates the quotient exactly when the image of the subgroup it generates is the
whole quotient. -/
theorem mem_generatingTuples_iff_map_closure (ι : Type*) (U : OpenNormalSubgroup G) (x : ι → G) :
    x ∈ generatingTuples ι U ↔
      (Subgroup.closure (Set.range x)).map (QuotientGroup.mk' U.toSubgroup) = ⊤ := by
  rw [mem_generatingTuples, MonoidHom.map_closure, ← Set.range_comp]
  simp only [Function.comp_def, QuotientGroup.mk'_apply]

/-- The finite tuples generating a quotient by an open normal subgroup form a closed set: the
condition depends only on their image in a discrete quotient. -/
theorem isClosed_generatingTuples [SeparatelyContinuousMul G] (ι : Type*) [Finite ι]
    (U : OpenNormalSubgroup G) : IsClosed (generatingTuples ι U) := by
  let q : (ι → G) → (ι → G ⧸ U.toSubgroup) := fun x i ↦ QuotientGroup.mk (x i)
  have hq : Continuous q := by
    apply continuous_pi
    intro i
    exact continuous_quotient_mk'.comp (continuous_apply i)
  let S : Set (ι → G ⧸ U.toSubgroup) := {y | Subgroup.closure (Set.range y) = ⊤}
  have : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
  have hS : IsClosed S := isClosed_discrete S
  have hEq : generatingTuples ι U = q ⁻¹' S := by
    ext x
    rfl
  rw [hEq]
  exact hS.preimage hq

/-- If `U' ≤ U`, every tuple generating the finer quotient by `U'` also generates the quotient
by `U`. -/
theorem generatingTuples_mono (ι : Type*) {U U' : OpenNormalSubgroup G}
    (h : U' ≤ U) : generatingTuples ι U' ⊆ generatingTuples ι U :=
  fun _ hx ↦ (mem_generatingTuples ι U _).mpr
    (QuotientGroup.closure_range_quotient_mk_eq_top_of_le h ((mem_generatingTuples ι U' _).mp hx))

/-- Some tuple of the group generates the quotient by an open normal subgroup exactly when the
quotient has a generating tuple with the same index type. -/
@[simp]
theorem generatingTuples_nonempty_iff (ι : Type*) (U : OpenNormalSubgroup G) :
    (generatingTuples ι U).Nonempty ↔
      ∃ x : ι → G ⧸ U.toSubgroup, Subgroup.closure (Set.range x) = ⊤ := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨fun i ↦ x i, (mem_generatingTuples ι U x).mp hx⟩,
    fun ⟨x, hx⟩ ↦ ?_⟩
  choose y hy using fun i ↦ QuotientGroup.mk_surjective (x i)
  have hyx : (fun i ↦ (y i : G ⧸ U.toSubgroup)) = x := funext hy
  exact ⟨y, by rwa [mem_generatingTuples, hyx]⟩

/-- **Compactness.** In a compact group, suppose that every quotient by an open normal subgroup
containing `N` has a generating tuple indexed by the finite type `ι`. Then a single `ι`-tuple of
the group generates all of these quotients at once. -/
theorem iInter_generatingTuples_nonempty [CompactSpace G] [SeparatelyContinuousMul G]
    (ι : Type*) [Finite ι] (N : Subgroup G)
    (h : ∀ U : OpenNormalSubgroup G, N ≤ U.toSubgroup → (generatingTuples ι U).Nonempty) :
    (⋂ U : {U : OpenNormalSubgroup G // N ≤ U.toSubgroup}, generatingTuples ι U.1).Nonempty := by
  -- The admissible `U` are directed downwards, and `generatingTuples` is monotone in `U`.
  have : Nonempty {U : OpenNormalSubgroup G // N ≤ U.toSubgroup} :=
    ⟨⟨openNormalSubgroupTop G,
      (le_top (a := N)).trans_eq (openNormalSubgroupTop_toSubgroup G).symm⟩⟩
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (fun U V ↦ ⟨⟨U.1 ⊓ V.1, le_inf U.2 V.2⟩, generatingTuples_mono ι inf_le_left,
      generatingTuples_mono ι inf_le_right⟩)
    (fun U ↦ h U.1 U.2) (fun U ↦ (isClosed_generatingTuples ι U.1).isCompact)
    (fun U ↦ isClosed_generatingTuples ι U.1)

end TauCeti
