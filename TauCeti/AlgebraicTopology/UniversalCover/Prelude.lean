/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Path
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Universal-cover prelude

Declarations from the universal-cover work in
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292) (Kim Morrison) that
are not yet in the pinned Mathlib. Several supporting declarations also come from
[mathlib4#31449](https://github.com/leanprover-community/mathlib4/pull/31449) (Kim Morrison).

When the pinned Mathlib advances past these upstream declarations, this shim should be removed
declaration-by-declaration in the same bump PR that switches downstream imports to Mathlib's
versions.
-/

public section

open scoped unitInterval
open Topology Set

namespace unitInterval
/-- The midpoint of the unit interval. -/
@[expose]
noncomputable def half : I := ⟨1 / 2, by constructor <;> linarith⟩

@[simp]
theorem coe_half : (half : ℝ) = 1 / 2 := rfl

end unitInterval

/-- Finite-`Fin` partition variant: Any open cover of `[a, b]` can be refined to a monotone
partition indexed by `Fin (n + 1)`. -/
lemma exists_monotone_partition_Icc {ι} {a b : ℝ} (h : a ≤ b) {c : ι → Set (Icc a b)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → Icc a b),
      Monotone t ∧ t 0 = a ∧ t (Fin.last n) = b ∧
      ∀ i : Fin n, ∃ j : ι, Icc (t i.castSucc) (t i.succ) ⊆ c j := by
  obtain ⟨t, ht0, ht_mono, ⟨N, hN⟩, ht_cover⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc h hc₁ hc₂
  refine ⟨N, fun k ↦ t (k : ℕ), fun _ _ hij ↦ ht_mono hij, ?_, ?_, fun i ↦ ?_⟩
  · simpa using ht0
  · simpa using hN N le_rfl
  · obtain ⟨j, hj⟩ := ht_cover i
    exact ⟨j, by simpa [Fin.val_succ, Fin.val_castSucc] using hj⟩

/-- Finite-`Fin` partition variant for the unit interval. -/
lemma exists_monotone_partition_unitInterval {ι} {c : ι → Set I}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I),
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ i : Fin n, ∃ j : ι, Icc (t i.castSucc) (t i.succ) ⊆ c j := by
  obtain ⟨N, t, ht_mono, ht0, htN, ht_cover⟩ :=
    exists_monotone_partition_Icc zero_le_one hc₁ hc₂
  exact ⟨N, t, ht_mono, Subtype.ext ht0, Subtype.ext htN, ht_cover⟩


/-- In a path-connected set `U`, two points of `U` are joined by a path with range in `U`. -/
theorem IsPathConnected.exists_path {X : Type*} [TopologicalSpace X] {a b : X} {U : Set X}
    (hU : IsPathConnected U) (ha : a ∈ U) (hb : b ∈ U) : ∃ p : Path a b, Set.range p ⊆ U :=
  let hab : JoinedIn U a b := hU.joinedIn _ ha _ hb
  ⟨hab.somePath, Set.range_subset_iff.mpr hab.somePath_mem⟩

namespace Path
variable {X : Type*} [TopologicalSpace X]

/-- Restrict a path whose image lies in a subset to a path in the corresponding subtype.
The source and target are the given subtype endpoints, and coercing the restricted path back to
`X` recovers the original path pointwise. -/
@[expose]
def codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) :
    Path x y where
  toFun := s.codRestrict γ hmem
  continuous_toFun := γ.continuous.codRestrict hmem
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp]
theorem codRestrict_coe {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) (t : I) :
    (γ.codRestrict hmem t : X) = γ t := rfl

@[simp]
theorem map_codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) :
    (γ.codRestrict hmem).map continuous_subtype_val = γ := rfl


/-- Generic Lebesgue partition lemma for paths: Given an open cover of a path's range,
there exists a finite partition of [0,1] such that each segment lies entirely in one set
from the cover. -/
theorem exists_partition_in_cover
    {ι : Type*} (U : ι → Set X) (hU_open : ∀ i, IsOpen (U i))
    {x y : X} (γ : Path x y) (hU_cover : ∀ s : unitInterval, ∃ i, γ s ∈ U i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (∀ i : Fin n, ∃ j : ι,
        ∀ s : unitInterval, (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U j) := by
  -- Pull back the cover along `γ`; the result is an open cover of `unitInterval`.
  obtain ⟨n, t, ht_mono, ht0, htn, ht_cover⟩ :=
    exists_monotone_partition_unitInterval
      (fun i ↦ (hU_open i).preimage γ.continuous)
      (fun s _ ↦ by
        obtain ⟨i, hi⟩ := hU_cover s
        exact Set.mem_iUnion.2 ⟨i, hi⟩)
  refine ⟨n, t, ht_mono, ht0, htn, fun i ↦ ?_⟩
  obtain ⟨j, hj⟩ := ht_cover i
  exact ⟨j, fun s hs ↦ hj ⟨hs.1, hs.2⟩⟩

/-- Generic Lebesgue partition lemma for paths, neighborhood version: If every point on a path
has a neighborhood with property P, then there exists a partition such that each segment lies
in an open set with property P. This follows immediately from the cover version. -/
theorem exists_partition_with_property {x y : X} (γ : Path x y) (P : Set X → Prop)
    (h : ∀ z ∈ Set.range γ, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ P U) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (∀ i : Fin n, ∃ U : Set X, IsOpen U ∧ P U ∧
        ∀ s : unitInterval, (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U) := by
  choose U hU_open hU_mem hU_P using h
  obtain ⟨n, t, h_mono, h_start, h_end, h_segments⟩ :=
    exists_partition_in_cover (fun z : Set.range γ ↦ U z.val z.property)
      (fun z ↦ hU_open z.val z.property) γ fun s ↦
        ⟨⟨γ s, ⟨s, rfl⟩⟩, hU_mem (γ s) ⟨s, rfl⟩⟩
  refine ⟨n, t, h_mono, h_start, h_end, fun i ↦ ?_⟩
  obtain ⟨⟨z, hz⟩, h_seg⟩ := h_segments i
  exact ⟨U z hz, hU_open z hz, hU_P z hz, h_seg⟩

end Path

namespace Path
variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace Homotopic.Quotient

@[simp]
theorem subpath_trans {x y : X} (p : Path x y)
    (a b c : unitInterval) (_hab : a ≤ b) (_hbc : b ≤ c) :
    trans (mk (p.subpath a b)) (mk (p.subpath b c)) =
      mk (p.subpath a c) := by
  simp only [← mk_trans, eq]
  exact ⟨Path.Homotopy.subpathTransSubpath p a b c⟩

@[simp]
theorem subpath_self {x y : X} (p : Path x y) (a : unitInterval) :
    mk (p.subpath a a) = refl (p a) := by
  simp only [← mk_refl, eq]
  rw [Path.subpath_self]

@[simp]
theorem subpath_zero_one {x y : X} (p : Path x y) :
    mk (p.subpath 0 1) = (mk p).cast (by simp) (by simp) := by
  simp only [← mk_cast, eq]
  rw [Path.subpath_zero_one]

end Homotopic.Quotient

end Path

namespace Path.Homotopic
variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- Composing on the left with a null-homotopic loop does not change the homotopy class. -/
theorem trans_left_of_nullhomotopic {γ₀ : Path x₀ x₀} {γ₁ : Path x₀ x₁}
    (hγ₀ : γ₀.Homotopic (Path.refl x₀)) : (γ₀.trans γ₁).Homotopic γ₁ :=
  (hcomp hγ₀ (.refl γ₁)).trans (refl_trans γ₁)

/-- Composing on the right with a null-homotopic loop does not change the homotopy class. -/
theorem trans_right_of_nullhomotopic {γ₀ : Path x₀ x₁} {γ₁ : Path x₁ x₁}
    (hγ₁ : γ₁.Homotopic (Path.refl x₁)) : (γ₀.trans γ₁).Homotopic γ₀ :=
  (hcomp (.refl γ₀) hγ₁).trans (trans_refl γ₀)

/-- If `γ.trans γ'.symm` is nullhomotopic, then `γ` and `γ'` are homotopic.
This is the path-homotopy analogue of `a * b⁻¹ = 1 → a = b`. -/
theorem of_trans_symm {γ γ' : Path x₀ x₁}
    (h : (γ.trans γ'.symm).Homotopic (Path.refl x₀)) : γ.Homotopic γ' :=
  (trans_refl γ).symm |>.trans <|
  (hcomp (.refl γ) (symm_trans γ').symm) |>.trans <|
  (trans_assoc γ γ'.symm γ').symm |>.trans <|
  (hcomp h (.refl γ')) |>.trans <|
  refl_trans γ'
namespace Quotient
variable {x₀ x₁ : X}

@[simp, grind =]
theorem refl_cast {x y : X} (h : y = x) : (refl x).cast h h = refl y := by
  cases h; rfl
/-- If `trans γ (symm γ') = refl`, then `γ = γ'`.
This is the quotient analogue of `a * b⁻¹ = 1 → a = b`. -/
theorem of_trans_symm {γ γ' : Homotopic.Quotient x₀ x₁}
    (h : trans γ (symm γ') = refl x₀) : γ = γ' := by
  induction γ using Quotient.ind with | mk γ =>
  induction γ' using Quotient.ind with | mk γ' =>
  simp only [← mk_trans, ← mk_symm, ← mk_refl] at h
  exact Quotient.sound (Homotopic.of_trans_symm (Quotient.exact h))

end Quotient
end Path.Homotopic
