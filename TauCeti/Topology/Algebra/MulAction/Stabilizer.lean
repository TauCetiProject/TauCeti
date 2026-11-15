/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.CompactOpen

/-!
# Open and compact set-stabilizers of continuous group actions

For a continuous action of a topological space `M` on `X`, the elements carrying a compact subset
`K ⊆ X` into an open subset `U ⊆ X` form an open subset of `M`: this is the preimage of a subbasic
open set in `C(X, X)` under the curried action map `M → C(X, X)`. No local compactness or separation
is needed.

When a group `G` with continuous inversion acts continuously on `X`, the set-stabilizer
`MulAction.stabilizer G C = {g : G | g • C = C}` of a compact open subset `C ⊆ X` is the
intersection of `{g | MapsTo (g • ·) C C}` with its inverse image under inversion, and is therefore
an open subgroup (`TauCeti.openStabilizer`). When `G` is a topological group acting on itself by
left translation and `C` is nonempty, `MulAction.stabilizer G C` lies inside `(· * a⁻¹) '' C` for
any `a ∈ C`; being closed (as an open subgroup) inside a compact set, it is itself compact. Applied
to a compact clopen neighbourhood of the identity, this produces the compact open subgroups in van
Dantzig's theorem.

## Main definitions

* `TauCeti.openStabilizer`, `TauCeti.openAddStabilizer`: the stabilizer of a compact open set under
  a continuous group action, bundled as an `OpenSubgroup` (resp. `OpenAddSubgroup`).

## Main results

* `IsCompact.isOpen_setOf_mapsTo_smul`, `IsCompact.isOpen_setOf_mapsTo_vadd`:
  `{m | MapsTo (m • ·) K U}` is open when `K` is compact and `U` is open.
* `IsCompact.isOpen_stabilizer_of_isOpen`, `IsCompact.isOpen_addStabilizer_of_isOpen`: the
  set-stabilizer of a compact open set under a continuous group action is open.
* `IsCompact.isCompact_stabilizer_of_isOpen`, `IsCompact.isCompact_addStabilizer_of_isOpen`: in a
  topological group, the left-translation stabilizer of a nonempty compact open subset is compact.

## References

* L. Kramer, *Locally Profinite Groups and Bruhat–Tits Buildings*, Lemma 1.41.
-/

public section

open Set
open scoped Pointwise

namespace IsCompact

/-- **Scalar multiplications carrying a compact set into an open set form an open set.** For a
continuous action of `M` on `X`, the set of `m : M` mapping a compact `K` into an open `U` is open.
Compare `IsCompact.isOpen_setOf_mapsTo_mul` for right multiplication in a topological magma. -/
@[to_additive /-- **Translations carrying a compact set into an open set form an open set.** For a
continuous additive action of `M` on `X`, the set of `m : M` mapping a compact `K` into an open `U`
is open. -/]
theorem isOpen_setOf_mapsTo_smul {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
    [SMul M X] [ContinuousSMul M X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) :
    IsOpen {m : M | MapsTo (m • ·) K U} :=
  (ContinuousMap.isOpen_setOfPred_mapsTo hK hU).preimage
    (ContinuousMap.curry ⟨fun p : M × X ↦ p.1 • p.2, continuous_smul⟩).continuous

/-- **The set-stabilizer of a compact open set is open.** If a group `G` with continuous inversion
acts continuously on `X`, then `{g : G | g • C = C}` is open in `G` for every compact open set
`C ⊆ X`. -/
@[to_additive isOpen_addStabilizer_of_isOpen
/-- **The set-stabilizer of a compact open set is open.** If an additive group `G` with continuous
negation acts continuously on `X`, then `{g : G | g +ᵥ C = C}` is open in `G` for every compact open
set `C ⊆ X`. -/]
theorem isOpen_stabilizer_of_isOpen {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] {C : Set X}
    (hCc : IsCompact C) (hCo : IsOpen C) :
    IsOpen (MulAction.stabilizer G C : Set G) := by
  -- `g • C = C` holds iff both `g` and `g⁻¹` map `C` into `C`.
  have hstab : (MulAction.stabilizer G C : Set G) =
      {g : G | MapsTo (g • ·) C C} ∩ (·⁻¹) ⁻¹' {g : G | MapsTo (g • ·) C C} := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_set, mem_inter_iff, mem_preimage,
      mem_ofPred_eq, MapsTo]
    exact ⟨fun h ↦ ⟨fun x hx ↦ (h x).mpr hx, fun x hx ↦ (h _).mp (by simpa using hx)⟩,
      fun ⟨h₁, h₂⟩ x ↦ ⟨fun hx ↦ by simpa using h₂ hx, fun hx ↦ h₁ hx⟩⟩
  rw [hstab]
  exact (hCc.isOpen_setOf_mapsTo_smul hCo).inter
    ((hCc.isOpen_setOf_mapsTo_smul hCo).preimage continuous_inv)

/-- **The left-translation stabilizer of a nonempty compact open subset of a topological group is
compact.** -/
@[to_additive isCompact_addStabilizer_of_isOpen
/-- **The left-translation stabilizer of a nonempty compact open subset of a topological additive
group is compact.** -/]
theorem isCompact_stabilizer_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {C : Set G} (hCc : IsCompact C) (hCo : IsOpen C) (hC₀ : C.Nonempty) :
    IsCompact (MulAction.stabilizer G C : Set G) := by
  obtain ⟨a, ha⟩ := hC₀
  let H : OpenSubgroup G := ⟨MulAction.stabilizer G C, hCc.isOpen_stabilizer_of_isOpen hCo⟩
  refine (hCc.image (continuous_mul_const a⁻¹)).of_isClosed_subset H.isClosed fun g hg ↦ ?_
  refine ⟨g * a, ?_, mul_inv_cancel_right g a⟩
  rw [← smul_eq_mul, ← MulAction.mem_stabilizer_iff.mp hg]
  exact smul_mem_smul_set ha

end IsCompact

namespace TauCeti

section Action

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- The set-stabilizer `{g : G | g • C = C}` of a compact open subset `C ⊆ X` under a continuous
group action, bundled as an `OpenSubgroup G`. -/
@[to_additive openAddStabilizer
/-- The set-stabilizer `{g : G | g +ᵥ C = C}` of a compact open subset `C ⊆ X` under a continuous
additive group action, bundled as an `OpenAddSubgroup G`. -/]
def openStabilizer (C : Set X) (hCc : IsCompact C) (hCo : IsOpen C) : OpenSubgroup G where
  toSubgroup := MulAction.stabilizer G C
  isOpen' := hCc.isOpen_stabilizer_of_isOpen hCo

/-- Coercing `openStabilizer` to `Subgroup G` recovers `MulAction.stabilizer G C`. -/
@[to_additive (attr := simp, norm_cast) toAddSubgroup_openAddStabilizer
/-- Coercing `openAddStabilizer` to `AddSubgroup G` recovers `AddAction.stabilizer G C`. -/]
theorem toSubgroup_openStabilizer (C : Set X) (hCc : IsCompact C) (hCo : IsOpen C) :
    ((openStabilizer G C hCc hCo : OpenSubgroup G) : Subgroup G) = MulAction.stabilizer G C :=
  (rfl)

/-- Coercing `openStabilizer` to `Set G` gives the carrier of `MulAction.stabilizer G C`. -/
@[to_additive (attr := simp) coe_openAddStabilizer
/-- Coercing `openAddStabilizer` to `Set G` gives the carrier of `AddAction.stabilizer G C`. -/]
theorem coe_openStabilizer (C : Set X) (hCc : IsCompact C) (hCo : IsOpen C) :
    (openStabilizer G C hCc hCo : Set G) = (MulAction.stabilizer G C : Set G) :=
  (rfl)

variable {G} in
/-- An element belongs to `openStabilizer G C hCc hCo` if and only if it stabilizes `C` setwise. -/
@[to_additive (attr := simp) mem_openAddStabilizer
/-- An element belongs to `openAddStabilizer G C hCc hCo` if and only if it stabilizes `C`
setwise. -/]
theorem mem_openStabilizer {C : Set X} {hCc : IsCompact C} {hCo : IsOpen C} {g : G} :
    g ∈ openStabilizer G C hCc hCo ↔ g • C = C :=
  MulAction.mem_stabilizer_iff

end Action

section Group

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- When `1 ∈ C`, the left-translation open stabilizer of `C` is contained in `C`. -/
@[to_additive openAddStabilizer_subset_of_zero_mem
/-- When `0 ∈ C`, the left-translation open additive stabilizer of `C` is contained in `C`. -/]
theorem openStabilizer_subset_of_one_mem [ContinuousInv G] [ContinuousSMul G G] {C : Set G}
    (hCc : IsCompact C) (hCo : IsOpen C) (h1 : (1 : G) ∈ C) :
    (openStabilizer G C hCc hCo : Set G) ⊆ C := by
  simpa only [coe_openStabilizer, div_singleton, div_one, Set.image_id'] using
    MulAction.stabilizer_subset_div_right h1

/-- The left-translation open stabilizer of a compact open subgroup is the subgroup itself. -/
@[to_additive (attr := simp) openAddStabilizer_coe_openAddSubgroup
/-- The left-translation open additive stabilizer of a compact open additive subgroup is the
subgroup itself. -/]
theorem openStabilizer_coe_openSubgroup [ContinuousInv G] [ContinuousSMul G G]
    (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    openStabilizer G (U : Set G) hU U.isOpen = U :=
  OpenSubgroup.toSubgroup_injective (MulAction.stabilizer_subgroup U.toSubgroup)

/-- In a topological group, `openStabilizer G C hCc hCo` is compact whenever `C` is nonempty. -/
@[to_additive isCompact_openAddStabilizer
/-- In a topological additive group, `openAddStabilizer G C hCc hCo` is compact whenever `C` is
nonempty. -/]
theorem isCompact_openStabilizer [IsTopologicalGroup G] {C : Set G} (hCc : IsCompact C)
    (hCo : IsOpen C) (hC₀ : C.Nonempty) :
    IsCompact (openStabilizer G C hCc hCo : Set G) :=
  hCc.isCompact_stabilizer_of_isOpen hCo hC₀

end Group

end TauCeti
