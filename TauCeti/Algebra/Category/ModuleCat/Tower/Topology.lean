/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic

/-!
# The inverse limit topology on the limit of a tower of modules

The limit `lim A` of a tower of modules `A₀ ← A₁ ← A₂ ← ⋯` is the module of compatible families
(`TauCeti.ModuleTower.lim`). Regarding every term `Aₙ` as a discrete space, it carries the inverse
limit topology: the kernels of the projections `lim A → Aₙ` form a basis of neighbourhoods of zero,
so two families are close when they agree in many coordinates. This file puts this topology on
`lim A`, together with the uniform structure of its additive group.

The topology is Hausdorff, since a compatible family with all coordinates zero is zero, and it is
complete: a Cauchy sequence has eventually constant coordinates, and these constant values form a
compatible family. It is linear over the ring of scalars, and every projection is locally constant.
A map into `lim A` has dense range exactly when every point of `lim A` agrees in each coordinate
with a point of its range. This is the setting for completions `lim M ⧸ Jₙ` of a module along a
decreasing family of submodules, such as completed enveloping algebras of affine Lie algebras.

## Main definitions

* `TauCeti.ModuleTower.limFilterBasis`: the kernels of the projections, as a filter basis.
* The instances `TopologicalSpace`, `UniformSpace`, `IsTopologicalAddGroup`, `IsUniformAddGroup`
  and `IsLinearTopology` on `lim A`.

## Main results

* `TauCeti.ModuleTower.hasBasis_nhds_zero`: the kernels of the projections form a basis of
  neighbourhoods of zero.
* `TauCeti.ModuleTower.tendsto_nhds_iff`: convergence is eventual agreement in every coordinate.
* `TauCeti.ModuleTower.isLocallyConstant_limπ`: the projections are locally constant.
* `TauCeti.ModuleTower.instT2Space`, `TauCeti.ModuleTower.instCompleteSpace`: the limit is
  Hausdorff and complete.
* `TauCeti.ModuleTower.denseRange_iff`: a map has dense range when its range meets every coordinate
  class of the limit.

## References

* N. Bourbaki, *General Topology*, Chapter III, §7, for inverse limits of topological groups.
-/

public section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite Filter Topology Uniformity

universe v u

variable {R : Type u} [Ring R] (F : ModuleTower.{v} R)

/-- The kernels of the projections `lim A → Aₙ`, as a filter basis of the additive group
`lim A`. -/
@[instance_reducible]
def limFilterBasis : AddGroupFilterBasis F.lim :=
  addGroupFilterBasisOfComm (Set.range fun n : ℕ ↦ (LinearMap.ker (F.limπ n) : Set F.lim))
    (Set.range_nonempty _)
    (by
      rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
      exact ⟨_, ⟨max m n, rfl⟩, Set.subset_inter (F.ker_limπ_antitone (le_max_left m n))
        (F.ker_limπ_antitone (le_max_right m n))⟩)
    (by
      rintro _ ⟨n, rfl⟩
      exact zero_mem _)
    (by
      rintro _ ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, Set.add_subset_iff.mpr fun _ hx _ hy ↦ add_mem hx hy⟩)
    (by
      rintro _ ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, fun _ hx ↦ neg_mem hx⟩)

/-- The limit of a tower carries the inverse limit topology of its discrete terms, in which the
kernels of the projections form a basis of neighbourhoods of zero. -/
instance : TopologicalSpace F.lim :=
  F.limFilterBasis.topology

instance : IsTopologicalAddGroup F.lim :=
  F.limFilterBasis.isTopologicalAddGroup

/-- The kernels of the projections `lim A → Aₙ` form a basis of neighbourhoods of zero. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : F.lim)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (LinearMap.ker (F.limπ n) : Set F.lim)) := by
  refine F.limFilterBasis.nhds_zero_hasBasis.to_hasBasis ?_ ?_
  · rintro _ ⟨n, rfl⟩
    exact ⟨n, trivial, subset_rfl⟩
  · exact fun n _ ↦ ⟨_, ⟨n, rfl⟩, subset_rfl⟩

/-- The families agreeing with `x` in the `n`-th coordinate form a basis of neighbourhoods of
`x`. -/
theorem hasBasis_nhds (x : F.lim) :
    (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ {y | F.limπ n y = F.limπ n x}) := by
  rw [← nhds_translation_sub x]
  convert F.hasBasis_nhds_zero.comap (· - x) using 2 with n
  ext y
  simp [sub_eq_zero]

variable {F} in
/-- A family of points of the limit converges to `x` exactly when, in every coordinate, it
eventually agrees with `x`. -/
theorem tendsto_nhds_iff {ι : Type*} {l : Filter ι} {f : ι → F.lim} {x : F.lim} :
    Tendsto f l (𝓝 x) ↔ ∀ n : ℕ, ∀ᶠ i in l, F.limπ n (f i) = F.limπ n x := by
  simp [(F.hasBasis_nhds x).tendsto_right_iff]

/-- The kernel of every projection is a neighbourhood of zero. -/
theorem ker_limπ_mem_nhds_zero (n : ℕ) : (LinearMap.ker (F.limπ n) : Set F.lim) ∈ 𝓝 0 :=
  F.hasBasis_nhds_zero.mem_of_mem trivial

/-- The kernel of every projection is open. -/
theorem isOpen_ker_limπ (n : ℕ) : IsOpen (LinearMap.ker (F.limπ n) : Set F.lim) :=
  (LinearMap.ker (F.limπ n)).toAddSubgroup.isOpen_of_mem_nhds (F.ker_limπ_mem_nhds_zero n)

/-- The projections `lim A → Aₙ` are locally constant: they are continuous for the discrete
topology on `Aₙ`. -/
theorem isLocallyConstant_limπ (n : ℕ) : IsLocallyConstant (F.limπ n) :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ (F.hasBasis_nhds x).mem_of_mem (i := n) trivial

/-- The inverse limit topology is linear: the kernels of the projections are open submodules. -/
instance : IsLinearTopology R F.lim :=
  IsLinearTopology.mk_of_hasBasis R F.hasBasis_nhds_zero

/-- The inverse limit topology is Hausdorff: a compatible family whose coordinates all vanish is
zero. -/
instance instT2Space : T2Space F.lim := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx ↦ ?_
  obtain ⟨n, hn⟩ : ∃ n, F.limπ n x ≠ 0 := by
    by_contra! h
    exact hx (Subtype.ext <| funext fun n ↦ by simpa using h n)
  exact ⟨_, F.ker_limπ_mem_nhds_zero n, hn⟩

/-- The limit of a tower carries the uniform structure of its topological additive group. -/
instance : UniformSpace F.lim :=
  IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup F.lim :=
  isUniformAddGroup_of_addCommGroup

/-- In a Cauchy sequence of the limit, every coordinate is eventually constant. -/
private theorem exists_limπ_eq_of_cauchySeq {x : ℕ → F.lim} (hx : CauchySeq x) (n : ℕ) :
    ∃ k, ∀ m ≥ k, F.limπ n (x m) = F.limπ n (x k) := by
  have hbasis := (uniformity_eq_comap_nhds_zero F.lim) ▸
    F.hasBasis_nhds_zero.comap fun p : F.lim × F.lim ↦ p.2 - p.1
  obtain ⟨k, hk⟩ := hbasis.cauchySeq_iff.mp hx n trivial
  exact ⟨k, fun m hm ↦ (sub_eq_zero.mp (by simpa using hk k le_rfl m hm))⟩

/-- The inverse limit topology is complete. -/
instance instCompleteSpace : CompleteSpace F.lim := by
  have : (𝓤 F.lim).IsCountablyGenerated :=
    have : (𝓝 (0 : F.lim)).IsCountablyGenerated := F.hasBasis_nhds_zero.isCountablyGenerated
    IsUniformAddGroup.uniformity_countably_generated
  refine UniformSpace.complete_of_cauchySeq_tendsto fun x hx ↦ ?_
  choose k hk using F.exists_limπ_eq_of_cauchySeq hx
  -- The `n`-th coordinate of the limit is the value on which the `n`-th coordinates stabilise.
  have hlim (n m : ℕ) (hm : k n ≤ m) : F.limπ n (x m) = F.limπ n (x (k n)) := hk n m hm
  let y : F.lim := ⟨fun n ↦ F.limπ n (x (k n)), F.mem_lim.mpr fun n ↦ by
    rw [← hlim (n + 1) (max (k n) (k (n + 1))) (le_max_right _ _), ← LinearMap.comp_apply,
      transition_comp_limπ, hlim n _ (le_max_left _ _)]⟩
  exact ⟨y, tendsto_nhds_iff.mpr fun n ↦ eventually_atTop.mpr ⟨k n, fun m hm ↦
    (hlim n m hm).trans (F.limπ_apply n y).symm⟩⟩

variable {F} in
/-- A map into the limit of a tower has dense range exactly when every point of the limit agrees in
each coordinate with some point of its range. -/
theorem denseRange_iff {α : Type*} {f : α → F.lim} :
    DenseRange f ↔ ∀ (x : F.lim) (n : ℕ), ∃ a, F.limπ n (f a) = F.limπ n x := by
  refine forall_congr' fun x ↦ ?_
  simp [mem_closure_iff_nhds_basis (F.hasBasis_nhds x)]

end TauCeti.ModuleTower
