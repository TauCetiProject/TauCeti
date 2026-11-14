/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Separation.Regular
import TauCeti.Topology.Algebra.Group.Pointwise

/-!
# Van Dantzig's theorem and locally profinite groups

A Hausdorff topological group `G` is *locally profinite* (an *l-group*) if every neighbourhood of
the identity contains a compact open subgroup. Van Dantzig's theorem identifies the locally
profinite groups among Hausdorff topological groups by three equivalent conditions:

1. `G` is locally compact and totally disconnected (`LocallyCompactSpace G` and
   `TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean (`LocallyCompactSpace G` and `NonarchimedeanGroup G`);
3. every neighbourhood of `1` contains a compact open subgroup.

Mathlib's `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one` constructs open subgroups
inside clopen neighbourhoods of `1` only when the ambient group `G` is compact. For a locally
compact ambient group one instead works directly on a compact open subset `C ⊆ G`: its left
translation stabilizer `{g : G | g • C = C}` (`MulAction.stabilizer G C` for the pointwise action)
is an open subgroup (`IsCompact.stabilizerOpenSubgroup`), and when `1 ∈ C` it is contained in `C`
and therefore compact, since open subgroups are closed. In a locally compact Hausdorff totally
disconnected group, the clopen basis at `1` inside a compact neighbourhood supplies such a `C`
inside any given neighbourhood of `1`.

Consequences recorded here for locally profinite groups include:
* every compact open subgroup is profinite (`CompactSpace`, `TotallyDisconnectedSpace`, `T2Space`,
  and `IsTopologicalGroup`);
* the compact open subgroups form a filter basis of `𝓝 1`
  (`TauCeti.nhds_one_hasBasis_isCompact_openSubgroup`), and those contained in a given open
  subgroup `U₀` form a cofinal downward-directed family
  (`TauCeti.nhds_one_hasBasis_isCompact_openSubgroup_le`,
  `TauCeti.directedOn_isCompact_openSubgroup_le`).

Every result carries `@[to_additive]` so additive groups such as `ℚ_[p]` and local fields inherit
the corresponding compact open additive subgroup basis.

## Main definitions

* `IsCompact.stabilizerOpenSubgroup`: the left translation stabilizer of a compact open subset `C`
  of a topological group, bundled as an `OpenSubgroup G` (with additive counterpart
  `IsCompact.addStabilizerOpenAddSubgroup`).

## Main results

* `IsCompact.isOpen_stabilizer`: the left translation stabilizer of a compact open subset is open.
* `IsCompact.stabilizerOpenSubgroup_subset` and `IsCompact.isCompact_stabilizerOpenSubgroup`: when
  `1 ∈ C`, the translation stabilizer lies in `C` and is compact.
* `TauCeti.exists_isCompact_openSubgroup_subset` and
  `TauCeti.nhds_one_hasBasis_isCompact_openSubgroup`: compact open subgroups form a basis of `𝓝 1`
  in any locally compact Hausdorff totally disconnected topological group.
* `TauCeti.vanDantzig_tfae`,
  `TauCeti.locallyCompact_and_totallyDisconnected_iff_exists_isCompact_openSubgroup`,
  `TauCeti.totallyDisconnectedSpace_iff_nonarchimedeanGroup`: van Dantzig's equivalence theorem.

## References

* J. Bernstein, *Representations of p-adic Groups* (Harvard lecture notes by K. E. Rumelhart,
  1992), Chapter I, Section 1.1, Definition 1, p. 7.
* L. Kramer, *Bruhat-Tits Buildings*, Lemma 1.41, Proposition 1.43, and Theorem 1.44, pp. 17-19.
-/

public section

open Filter Set Topology
open scoped Pointwise

section TranslationStabilizer

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Kramer's translation-stabilizer lemma.** In a topological group, the left translation
stabilizer `{g : G | g • C = C}` of any compact open subset `C` is open. Neither `1 ∈ C` nor
Hausdorffness of `G` is required. -/
@[to_additive IsCompact.isOpen_addStabilizer
/-- In a topological additive group, the translation stabilizer `{g : G | g +ᵥ C = C}` of any
compact open subset `C` is open. Neither `0 ∈ C` nor Hausdorffness of `G` is required. -/]
theorem IsCompact.isOpen_stabilizer {C : Set G} (hC : IsCompact C) (hC_open : IsOpen C) :
    IsOpen (MulAction.stabilizer G C : Set G) := by
  obtain ⟨V, hV_open, h1V, hVC⟩ := hC.exists_isOpen_superset_mul_subset hC_open
    (by simp : ({(1 : G)} : Set G) * C ⊆ C)
  have h1 : (1 : G) ∈ V := h1V (mem_singleton 1)
  have hW_mem : V ∩ V⁻¹ ∈ 𝓝 (1 : G) :=
    (hV_open.inter hV_open.inv).mem_nhds ⟨h1, by simpa using h1⟩
  refine Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hW_mem ?_)
  rintro g ⟨hgV, hgVinv⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_set]
  exact fun x ↦ ⟨fun hx ↦ by simpa using hVC ⟨g⁻¹, mem_inv.mp hgVinv, g * x, hx, rfl⟩,
    fun hx ↦ hVC ⟨g, hgV, x, hx, rfl⟩⟩

/-- The left translation stabilizer `{g : G | g • C = C}` of a compact open subset `C` of a
topological group, bundled as an `OpenSubgroup G`. -/
@[to_additive IsCompact.addStabilizerOpenAddSubgroup
/-- The translation stabilizer `{g : G | g +ᵥ C = C}` of a compact open subset `C` of a topological
additive group, bundled as an `OpenAddSubgroup G`. -/]
def IsCompact.stabilizerOpenSubgroup {C : Set G} (hC : IsCompact C) (hC_open : IsOpen C) :
    OpenSubgroup G :=
  ⟨MulAction.stabilizer G C, hC.isOpen_stabilizer hC_open⟩

/-- The underlying set of `hC.stabilizerOpenSubgroup hC_open` is the pointwise stabilizer of `C`. -/
@[to_additive (attr := simp) IsCompact.coe_addStabilizerOpenAddSubgroup
/-- The underlying set of `hC.addStabilizerOpenAddSubgroup hC_open` is the pointwise additive
stabilizer of `C`. -/]
theorem IsCompact.coe_stabilizerOpenSubgroup {C : Set G} (hC : IsCompact C) (hC_open : IsOpen C) :
    ((hC.stabilizerOpenSubgroup hC_open : OpenSubgroup G) : Set G) =
      (MulAction.stabilizer G C : Set G) :=
  (rfl)

/-- The underlying subgroup of `hC.stabilizerOpenSubgroup hC_open` is `MulAction.stabilizer G C`. -/
@[to_additive (attr := simp) IsCompact.toAddSubgroup_addStabilizerOpenAddSubgroup
/-- The underlying additive subgroup of `hC.addStabilizerOpenAddSubgroup hC_open` is
`AddAction.stabilizer G C`. -/]
theorem IsCompact.toSubgroup_stabilizerOpenSubgroup {C : Set G} (hC : IsCompact C)
    (hC_open : IsOpen C) :
    (hC.stabilizerOpenSubgroup hC_open).toSubgroup = MulAction.stabilizer G C :=
  (rfl)

/-- An element belongs to `hC.stabilizerOpenSubgroup hC_open` precisely when left translation by it
preserves `C`. -/
@[to_additive (attr := simp, grind =) IsCompact.mem_addStabilizerOpenAddSubgroup
/-- An element belongs to `hC.addStabilizerOpenAddSubgroup hC_open` precisely when translation by it
preserves `C`. -/]
theorem IsCompact.mem_stabilizerOpenSubgroup {C : Set G} (hC : IsCompact C) (hC_open : IsOpen C)
    {g : G} : g ∈ hC.stabilizerOpenSubgroup hC_open ↔ g • C = C :=
  MulAction.mem_stabilizer_iff

/-- When `1 ∈ C`, the open translation stabilizer `hC.stabilizerOpenSubgroup hC_open` is contained
in `C`. -/
@[to_additive IsCompact.addStabilizerOpenAddSubgroup_subset
/-- When `0 ∈ C`, the open translation stabilizer `hC.addStabilizerOpenAddSubgroup hC_open` is
contained in `C`. -/]
theorem IsCompact.stabilizerOpenSubgroup_subset {C : Set G} (hC : IsCompact C) (hC_open : IsOpen C)
    (h1 : (1 : G) ∈ C) : (hC.stabilizerOpenSubgroup hC_open : Set G) ⊆ C := by
  simpa using MulAction.stabilizer_subset_div_right h1

/-- When `1 ∈ C`, the open translation stabilizer `hC.stabilizerOpenSubgroup hC_open` is compact,
being a closed subgroup contained in the compact set `C`. -/
@[to_additive IsCompact.isCompact_addStabilizerOpenAddSubgroup
/-- When `0 ∈ C`, the open translation stabilizer `hC.addStabilizerOpenAddSubgroup hC_open` is
compact, being a closed additive subgroup contained in the compact set `C`. -/]
theorem IsCompact.isCompact_stabilizerOpenSubgroup {C : Set G} (hC : IsCompact C)
    (hC_open : IsOpen C) (h1 : (1 : G) ∈ C) :
    IsCompact (hC.stabilizerOpenSubgroup hC_open : Set G) :=
  hC.of_isClosed_subset (hC.stabilizerOpenSubgroup hC_open).isClosed
    (hC.stabilizerOpenSubgroup_subset hC_open h1)

end TranslationStabilizer

namespace TauCeti

section LocallyProfinite

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The compact open subgroups of `G` contained in a given open subgroup `U₀` form a
downward-directed family (directed under reverse inclusion). -/
@[to_additive
/-- The compact open additive subgroups of `G` contained in a given open additive subgroup `U₀`
form a downward-directed family (directed under reverse inclusion). -/]
theorem directedOn_isCompact_openSubgroup_le [SeparatelyContinuousMul G] (U₀ : OpenSubgroup G) :
    DirectedOn (· ≥ ·) {H : OpenSubgroup G | IsCompact (H : Set G) ∧ H ≤ U₀} :=
  fun H₁ ⟨hH₁, h₁⟩ _ ⟨_, _⟩ ↦
    ⟨H₁ ⊓ _, ⟨H₁.isCompact_inf_left hH₁ _, inf_le_of_left_le h₁⟩, inf_le_left, inf_le_right⟩

/-- The compact open subgroups of `G` form a downward-directed family under reverse inclusion. -/
@[to_additive
/-- The compact open additive subgroups of `G` form a downward-directed family under reverse
inclusion. -/]
theorem directedOn_isCompact_openSubgroup [SeparatelyContinuousMul G] :
    DirectedOn (· ≥ ·) {H : OpenSubgroup G | IsCompact (H : Set G)} :=
  fun H₁ hH₁ H₂ _ ↦ ⟨H₁ ⊓ H₂, H₁.isCompact_inf_left hH₁ H₂, inf_le_left, inf_le_right⟩

section VanDantzig

variable [IsTopologicalGroup G] [T2Space G]

/-- **Van Dantzig's theorem (existence form).** In a locally compact Hausdorff totally disconnected
topological group, every identity neighbourhood contains a compact open subgroup. -/
@[to_additive
/-- **Van Dantzig's theorem (additive existence form).** In a locally compact Hausdorff totally
disconnected topological additive group, every neighbourhood of `0` contains a compact open additive
subgroup. -/]
theorem exists_isCompact_openSubgroup_subset [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hK_cpt, hK_nhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨C, ⟨hC_clopen, h1C⟩, hCUK⟩ :=
    (nhds_basis_isClopen (1 : G)).mem_iff.mp (inter_mem hU hK_nhds)
  have hC_cpt : IsCompact C :=
    hK_cpt.of_isClosed_subset hC_clopen.isClosed (hCUK.trans inter_subset_right)
  exact ⟨hC_cpt.stabilizerOpenSubgroup hC_clopen.isOpen,
    hC_cpt.isCompact_stabilizerOpenSubgroup hC_clopen.isOpen h1C,
    (hC_cpt.stabilizerOpenSubgroup_subset hC_clopen.isOpen h1C).trans
      (hCUK.trans inter_subset_left)⟩

/-- A locally compact Hausdorff totally disconnected topological group is nonarchimedean. -/
@[to_additive
/-- A locally compact Hausdorff totally disconnected topological additive group is
nonarchimedean. -/]
theorem nonarchimedeanGroup_of_locallyCompactSpace [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] : NonarchimedeanGroup G where
  is_nonarchimedean _ hU :=
    let ⟨H, _, hHU⟩ := exists_isCompact_openSubgroup_subset hU
    ⟨H, hHU⟩

/-- **Compact open subgroups form a basis of `𝓝 1`.** In a locally compact Hausdorff totally
disconnected topological group, the compact open subgroups form a filter basis of the identity
neighbourhood filter. -/
@[to_additive
/-- **Compact open additive subgroups form a basis of `𝓝 0`.** In a locally compact Hausdorff
totally disconnected topological additive group, the compact open additive subgroups form a filter
basis of the neighbourhoods of `0`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
      fun H ↦ (H : Set G) :=
  ⟨fun _ ↦ ⟨exists_isCompact_openSubgroup_subset,
    fun ⟨H, _, hH⟩ ↦ mem_of_superset H.mem_nhds_one hH⟩⟩

/-- **Cofinality of compact open subgroups inside a given open subgroup.** In a locally compact
Hausdorff totally disconnected topological group, the compact open subgroups contained in a fixed
open subgroup `U₀` form a filter basis of `𝓝 1`. -/
@[to_additive
/-- In a locally compact Hausdorff totally disconnected topological additive group, the compact open
additive subgroups contained in a fixed open additive subgroup `U₀` form a filter basis of
`𝓝 0`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup_le [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] (U₀ : OpenSubgroup G) :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G) ∧ H ≤ U₀)
      fun H ↦ (H : Set G) := by
  refine ⟨fun W ↦ ⟨fun hW ↦ ?_, fun ⟨H, _, hHW⟩ ↦ mem_of_superset H.mem_nhds_one hHW⟩⟩
  obtain ⟨H, hHcpt, hH⟩ := exists_isCompact_openSubgroup_subset (inter_mem hW U₀.mem_nhds_one)
  exact ⟨H, ⟨hHcpt, hH.trans inter_subset_right⟩, hH.trans inter_subset_left⟩

/-- Every open subgroup of a locally compact Hausdorff totally disconnected topological group
contains a compact open subgroup. -/
@[to_additive
/-- Every open additive subgroup of a locally compact Hausdorff totally disconnected topological
additive group contains a compact open additive subgroup. -/]
theorem exists_isCompact_openSubgroup_le [WeaklyLocallyCompactSpace G]
    [TotallyDisconnectedSpace G] (U₀ : OpenSubgroup G) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ H ≤ U₀ := by
  obtain ⟨H, hHcpt, hH⟩ := exists_isCompact_openSubgroup_subset U₀.mem_nhds_one
  exact ⟨H, hHcpt, hH⟩

variable (G) in
/-- **Van Dantzig's theorem.** For a Hausdorff topological group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and `NonarchimedeanGroup` (every neighbourhood of `1` contains an open
   subgroup);
3. every neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive vanDantzig_addGroup_tfae
/-- **Van Dantzig's theorem (additive form).** For a Hausdorff topological additive group `G`, the
following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and `NonarchimedeanAddGroup` (every neighbourhood of `0` contains an open
   additive subgroup);
3. every neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem vanDantzig_tfae :
    List.TFAE
      [LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
       LocallyCompactSpace G ∧ NonarchimedeanGroup G,
       ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U] := by
  tfae_have 1 → 3 := fun ⟨_, _⟩ _ hU ↦ exists_isCompact_openSubgroup_subset hU
  tfae_have 3 → 2 := fun h ↦ by
    obtain ⟨H, hHcpt, -⟩ := h univ univ_mem
    exact ⟨hHcpt.locallyCompactSpace_of_mem_nhds_of_group H.mem_nhds_one,
      ⟨fun U hU ↦ let ⟨K, _, hKU⟩ := h U hU; ⟨K, hKU⟩⟩⟩
  tfae_have 2 → 1 := fun ⟨hLC, hNA⟩ ↦ ⟨hLC, inferInstance⟩
  tfae_finish

/-- A Hausdorff topological group is locally compact and totally disconnected if and only if every
identity neighbourhood contains a compact open subgroup. -/
@[to_additive
/-- A Hausdorff topological additive group is locally compact and totally disconnected if and only
if every neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem locallyCompact_and_totallyDisconnected_iff_exists_isCompact_openSubgroup :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U :=
  (vanDantzig_tfae G).out 1 3

/-- A Hausdorff topological group is locally compact and nonarchimedean if and only if every
identity neighbourhood contains a compact open subgroup. -/
@[to_additive
/-- A Hausdorff topological additive group is locally compact and nonarchimedean if and only if
every neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem locallyCompact_and_nonarchimedeanGroup_iff_exists_isCompact_openSubgroup :
    LocallyCompactSpace G ∧ NonarchimedeanGroup G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U :=
  (vanDantzig_tfae G).out 2 3

/-- A locally compact Hausdorff topological group is totally disconnected if and only if it is
nonarchimedean. -/
@[to_additive
/-- A locally compact Hausdorff topological additive group is totally disconnected if and only if it
is nonarchimedean. -/]
theorem totallyDisconnectedSpace_iff_nonarchimedeanGroup [WeaklyLocallyCompactSpace G] :
    TotallyDisconnectedSpace G ↔ NonarchimedeanGroup G :=
  ⟨fun _ ↦ nonarchimedeanGroup_of_locallyCompactSpace, fun _ ↦ inferInstance⟩

end VanDantzig

end LocallyProfinite

end TauCeti

end

/-! ### Examples and sanity checks -/

section Examples

open Filter Set Topology
open scoped Pointwise

-- Every compact open subgroup of a Hausdorff totally disconnected topological group is profinite
-- (`CompactSpace`, `TotallyDisconnectedSpace`, `T2Space`, and `IsTopologicalGroup`).
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TotallyDisconnectedSpace G] (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    CompactSpace U ∧ TotallyDisconnectedSpace U ∧ T2Space U ∧ IsTopologicalGroup U :=
  ⟨isCompact_iff_compactSpace.mp hU, inferInstance, inferInstance, inferInstance⟩

-- Every trivial topological group (`Subsingleton G`, e.g. `{1}`) has the singleton compact open
-- subgroup basis.
example (G : Type*) [Group G] [TopologicalSpace G] [Subsingleton G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
      fun H ↦ (H : Set G) :=
  TauCeti.nhds_one_hasBasis_isCompact_openSubgroup

-- In `ℝ`, the interval `(-1, 1)` contains no open additive subgroup.
example : ¬ ∃ H : OpenAddSubgroup ℝ, (H : Set ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  rintro ⟨H, hH⟩
  rw [H.eq_top_of_preconnectedSpace] at hH
  have h2 : (2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := hH trivial
  norm_num at h2

-- In the noncompact additive group `ℚ_[2]`, `ℤ_[2]` (`closedBall 0 1`) and `2ℤ_[2]`
-- (`closedBall 0 2⁻¹`) are compact open additive subgroups equal to their own translation
-- stabilizers, and the balls `2^m ℤ_[2]` (`closedBall 0 (2 ^ (-m))`, `m : ℤ`) form a compact open
-- additive subgroup basis of `𝓝 (0 : ℚ_[2])`.
section PadicTwo

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

example :
    let z2 : OpenAddSubgroup ℚ_[2] := IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2] zero_lt_one
    let twoZ2 : OpenAddSubgroup ℚ_[2] :=
      IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2] (by norm_num : (0 : ℝ) < 2⁻¹)
    IsCompact (z2 : Set ℚ_[2]) ∧ IsCompact (twoZ2 : Set ℚ_[2]) ∧
      AddAction.stabilizer ℚ_[2] (z2 : Set ℚ_[2]) = z2.toAddSubgroup ∧
      AddAction.stabilizer ℚ_[2] (twoZ2 : Set ℚ_[2]) = twoZ2.toAddSubgroup ∧
      (𝓝 (0 : ℚ_[2])).HasBasis (fun _ : ℤ ↦ True)
        (fun m : ℤ ↦ (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2]
          (zpow_pos (by norm_num : (0 : ℝ) < 2) (-m)) : Set ℚ_[2])) := by
  refine ⟨isCompact_closedBall (0 : ℚ_[2]) 1, isCompact_closedBall (0 : ℚ_[2]) 2⁻¹,
    AddAction.stabilizer_addSubgroup _, AddAction.stabilizer_addSubgroup _,
    ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨m, _, hmU⟩ ↦ mem_of_superset
      (Metric.closedBall_mem_nhds 0 (zpow_pos (by norm_num : (0 : ℝ) < 2) (-m))) hmU⟩⟩⟩
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨(n : ℤ) + 1, trivial, fun x hx ↦ hrU (Metric.mem_ball.mpr ?_)⟩
  have hlt : (2 : ℝ) ^ (-((n : ℤ) + 1)) < (2⁻¹ : ℝ) ^ n := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega)
  exact (hx : dist x 0 ≤ _).trans_lt (hlt.trans hn)

end PadicTwo

-- In discrete `S₃`, `C = {1, swap 0 1, swap 0 2}` is compact and clopen with `1 ∈ C`, is not a
-- subgroup (`swap 0 1 * swap 0 2` lies outside `C`), and has trivial left translation stabilizer.
section PermFin3

open Equiv

private local instance : TopologicalSpace (Perm (Fin 3)) := ⊥
private local instance : DiscreteTopology (Perm (Fin 3)) := ⟨rfl⟩

private abbrev s3Clopen : Set (Perm (Fin 3)) :=
  {1, swap 0 1, swap 0 2}

example :
    IsCompact s3Clopen ∧ IsClopen s3Clopen ∧ (1 : Perm (Fin 3)) ∈ s3Clopen ∧
      swap (0 : Fin 3) 1 * swap 0 2 ∉ s3Clopen ∧
      MulAction.stabilizer (Perm (Fin 3)) s3Clopen = ⊥ := by
  refine ⟨s3Clopen.toFinite.isCompact, isClopen_discrete _, by simp [s3Clopen], by decide, ?_⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hg1 : g ∈ s3Clopen :=
    s3Clopen.toFinite.isCompact.stabilizerOpenSubgroup_subset (isOpen_discrete _)
      (by simp [s3Clopen]) hg
  rcases hg1 with rfl | rfl | rfl
  · rfl
  · have hmem : swap (0 : Fin 3) 1 * swap 0 2 ∈ s3Clopen := by
      rw [← MulAction.mem_stabilizer_iff.mp hg]
      exact Set.smul_mem_smul_set (by simp [s3Clopen])
    exact absurd hmem (by decide)
  · have hmem : swap (0 : Fin 3) 2 * swap 0 1 ∈ s3Clopen := by
      rw [← MulAction.mem_stabilizer_iff.mp hg]
      exact Set.smul_mem_smul_set (by simp [s3Clopen])
    exact absurd hmem (by decide)

end PermFin3

end Examples
