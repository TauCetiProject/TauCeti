/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Topology.ClusterSet

import Mathlib.Order.Fin.Tuple
import TauCeti.Geometry.RealAlgebraic.Stack.Frontier.Lifting

/-!
# Clipped stack cells over open height intervals

Given a stack `θ : Fin m → S → ℝ` over `S ⊆ ℝⁿ` and an open height interval `Ioo a b`, clipping
every cell of `stackCells S θ` to `{v | v 0 ∈ Ioo a b}` yields `TauCeti.boundedStackCells a b S θ`.
When `a < b`, `θ` is strictly increasing on each fibre, and all values of `θ` lie in `Ioo a b`,
augmenting `θ` internally by the constant lower and upper bounds `a` and `b` identifies the clipped
cells with the inner sections and inner sectors of the augmented stack. Consequently every clipped
cell projects onto `S`, is connected over a connected base, and inherits preconnected approach
regions (`TauCeti.IsPreconnectedApproachAt`) at every ambient point `v₀ ∈ ℝⁿ⁺¹` whenever the base
has preconnected approach regions at `Fin.tail v₀` and all sections of `θ` admit finite limits along
`S` at `Fin.tail v₀` — including at points on the horizontal boundary caps `v₀ 0 = a` and
`v₀ 0 = b`.

## Main declarations

* `TauCeti.boundedStackCells`: stack cells clipped to the open height interval `Ioo a b`, with
  unfolding equation `TauCeti.boundedStackCells_def`, membership characterization
  `TauCeti.mem_boundedStackCells`, and clipping introduction `TauCeti.inter_mem_boundedStackCells`.
* `TauCeti.finite_boundedStackCells`, `TauCeti.sUnion_boundedStackCells`,
  `TauCeti.pairwiseDisjoint_boundedStackCells`: finiteness, covering of the bounded cylinder
  `{v | Fin.tail v ∈ S ∧ v 0 ∈ Ioo a b}`, and pairwise disjointness.
* `TauCeti.Delineation.signInvariant_eval_of_mem_boundedStackCells`: sign-invariance of delineated
  polynomial evaluations on clipped stack cells.
* `TauCeti.image_tail_of_mem_boundedStackCells`: every clipped cell of a bounded strictly increasing
  stack projects onto the base `S` under `Fin.tail`.
* `TauCeti.isConnected_of_mem_boundedStackCells`,
  `TauCeti.isPreconnectedApproachAt_of_mem_boundedStackCells`: connectedness and lifting of
  preconnected approach regions to clipped stack cells at every ambient point of `ℝⁿ⁺¹`.

## References

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 2.3.
* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS lecture notes, 1965, §16–17.
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

/-- The cells of a stack `θ` over `S ⊆ ℝⁿ` clipped to the height interval `Ioo a b`. When all
values of `θ` lie in `Ioo a b`, sections are unchanged and sectors become bounded open bands. -/
noncomputable def boundedStackCells {n m : ℕ} (a b : ℝ) (S : Set (Fin n → ℝ)) (θ : Fin m → S → ℝ) :
    Set (Set (Fin (n + 1) → ℝ)) :=
  (· ∩ {v | v 0 ∈ Ioo a b}) '' stackCells S θ

/-- Defining equation of `TauCeti.boundedStackCells`, expressing it as the image of
`TauCeti.stackCells` under clipping to the open height interval `Ioo a b`. -/
theorem boundedStackCells_def {n m : ℕ} (a b : ℝ) (S : Set (Fin n → ℝ)) (θ : Fin m → S → ℝ) :
    boundedStackCells a b S θ = (· ∩ {v | v 0 ∈ Ioo a b}) '' stackCells S θ :=
  (rfl)

/-- Unconditional membership characterization of `TauCeti.boundedStackCells`: a set lies in
`boundedStackCells a b S θ` iff it is obtained by clipping some cell of `stackCells S θ` to
`v 0 ∈ Ioo a b`.

Left untagged for `@[simp]` because `TauCeti.mem_stackCells` simplifies `T ∈ stackCells S θ`
further. -/
theorem mem_boundedStackCells {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)} {θ : Fin m → S → ℝ}
    {E : Set (Fin (n + 1) → ℝ)} :
    E ∈ boundedStackCells a b S θ ↔ ∃ T ∈ stackCells S θ, T ∩ {v | v 0 ∈ Ioo a b} = E :=
  (Iff.rfl)

/-- Clipping any cell of `stackCells S θ` to `Ioo a b` produces a member of
`boundedStackCells a b S θ`. -/
theorem inter_mem_boundedStackCells {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} {T : Set (Fin (n + 1) → ℝ)} (hT : T ∈ stackCells S θ) :
    T ∩ {v | v 0 ∈ Ioo a b} ∈ boundedStackCells a b S θ :=
  mem_boundedStackCells.mpr ⟨T, hT, rfl⟩

/-- A clipped stack has finitely many cells. -/
theorem finite_boundedStackCells {n m : ℕ} (a b : ℝ) (S : Set (Fin n → ℝ)) (θ : Fin m → S → ℝ) :
    (boundedStackCells a b S θ).Finite :=
  (finite_stackCells S θ).image _

/-- For a monotone stack `θ` over `S`, the clipped stack cells cover the bounded cylinder
`{v | Fin.tail v ∈ S ∧ v 0 ∈ Ioo a b}`. -/
theorem sUnion_boundedStackCells {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)} {θ : Fin m → S → ℝ}
    (hθ : ∀ x, Monotone fun i ↦ θ i x) :
    ⋃₀ boundedStackCells a b S θ = {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ v 0 ∈ Ioo a b} := by
  ext v
  simp only [mem_sUnion, mem_boundedStackCells, mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨T, hT, rfl⟩, hvT, hvI⟩
    have hvS : v ∈ Fin.tail ⁻¹' S := by
      rw [← sUnion_stackCells hθ]
      exact ⟨T, hT, hvT⟩
    exact ⟨hvS, hvI⟩
  · rintro ⟨hvS, hvI⟩
    have hv : v ∈ ⋃₀ stackCells S θ := by
      rw [sUnion_stackCells hθ]
      exact hvS
    obtain ⟨T, hT, hvT⟩ := hv
    exact ⟨_, ⟨T, hT, rfl⟩, hvT, hvI⟩

/-- The clipped cells of a stack with pairwise distinct functions on each fibre are pairwise
disjoint. -/
theorem pairwiseDisjoint_boundedStackCells {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hθ : ∀ x, Injective fun i ↦ θ i x) :
    (boundedStackCells a b S θ).PairwiseDisjoint id := by
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
  exact (pairwiseDisjoint_stackCells hθ hA hB fun h ↦ hAB (h ▸ rfl)).mono
    inter_subset_left inter_subset_left

/-- Polynomial evaluations of a delineation remain sign-invariant on every clipped stack cell. -/
theorem Delineation.signInvariant_eval_of_mem_boundedStackCells {n : ℕ} {ι : Type*} {a b : ℝ}
    {S : Set (Fin n → ℝ)} {P : ι → (Fin n → ℝ) → ℝ[X]}
    (D : Delineation fun k (x : S) ↦ P k x) (k : ι) {E : Set (Fin (n + 1) → ℝ)}
    (hE : E ∈ boundedStackCells a b S D.root) :
    SignInvariant (fun v ↦ (P k (Fin.tail v)).eval (v 0)) E := by
  obtain ⟨T, hT, rfl⟩ := mem_boundedStackCells.mp hE
  exact (D.signInvariant_eval_of_mem_stackCells k hT).mono inter_subset_left

/-- When all section values of a continuous strictly increasing stack over a connected base `S` lie
in `Ioo a b` (`a < b`), every clipped stack cell in `boundedStackCells a b S θ` is connected. -/
theorem isConnected_of_mem_boundedStackCells {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hS : IsConnected S) (hc : ∀ i, Continuous (θ i))
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hab : a < b) (hbnd : ∀ i x, θ i x ∈ Ioo a b)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ boundedStackCells a b S θ) :
    IsConnected E := by
  obtain ⟨T, hT, rfl⟩ := mem_boundedStackCells.mp hE
  exact isConnected_inter_Ioo_of_mem_stackCells hS hc hθ hab hbnd hT

/-! ### Internal augmented-stack representation -/

private def augmentedStack {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ) :
    Fin (m + 2) → X → ℝ :=
  Fin.cons (fun _ ↦ a) (Fin.snoc θ (fun _ ↦ b))

private theorem augmentedStack_eval {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ) (x : X) :
    (fun r ↦ augmentedStack a b θ r x) = Fin.cons a (Fin.snoc (fun i ↦ θ i x) b) := by
  ext r
  refine r.cases rfl fun s ↦ s.lastCases ?_ fun i ↦ ?_
  · simp [augmentedStack, Fin.succ_last]
  · simp [augmentedStack]

private theorem augmentedStack_zero {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ) (x : X) :
    augmentedStack a b θ 0 x = a :=
  rfl

private theorem augmentedStack_inner {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ)
    (i : Fin m) (x : X) :
    augmentedStack a b θ i.castSucc.succ x = θ i x := by
  simp [augmentedStack]

private theorem augmentedStack_last {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ) (x : X) :
    augmentedStack a b θ (Fin.last (m + 1)) x = b := by
  rw [← Fin.succ_last m]
  simp [augmentedStack]

private theorem continuous_augmentedStack {X : Type*} [TopologicalSpace X] {a b : ℝ} {m : ℕ}
    {θ : Fin m → X → ℝ} (hc : ∀ i, Continuous (θ i)) (r : Fin (m + 2)) :
    Continuous (augmentedStack a b θ r) := by
  induction r using Fin.cases with
  | zero => exact continuous_const
  | succ s =>
    induction s using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, funext (augmentedStack_last a b θ)]
      exact continuous_const
    | cast i => simpa [augmentedStack] using hc i

private theorem strictMono_augmentedStack {X : Type*} {a b : ℝ} {m : ℕ} {θ : Fin m → X → ℝ}
    (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hbnd : ∀ i x, θ i x ∈ Ioo a b) (x : X) :
    StrictMono fun r ↦ augmentedStack a b θ r x := by
  rw [augmentedStack_eval, Fin.strictMono_cons, ← Fin.insertNth_last', Fin.strictMono_insertNth_iff]
  refine ⟨fun s ↦ s.lastCases ?_ fun i ↦ ?_, hθ x, fun i _ ↦ (mem_Ioo.mp (hbnd i x)).right,
    fun i hi ↦ absurd hi (not_le_of_gt (Fin.castSucc_lt_last i))⟩
  · simpa using hab
  · simpa using (mem_Ioo.mp (hbnd i x)).left

private theorem sectionSet_inter_Ioo_eq {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hbnd : ∀ i x, θ i x ∈ Ioo a b) (i : Fin m) :
    cylinder S '' sectionSet θ i ∩ {v | v 0 ∈ Ioo a b} =
      cylinder S '' sectionSet (augmentedStack a b θ) i.castSucc.succ := by
  ext v
  simp only [mem_inter_iff, mem_image_cylinder, mem_sectionSet, mem_ofPred_eq, augmentedStack_inner]
  refine ⟨fun ⟨⟨hx, hv0⟩, _⟩ ↦ ⟨hx, hv0⟩, fun ⟨hx, hv0⟩ ↦ ⟨⟨hx, hv0⟩, ?_⟩⟩
  rw [← hv0]
  exact hbnd i ⟨Fin.tail v, hx⟩

private theorem sectorLower_iff {X : Type*} {a b : ℝ} {m : ℕ} {θ : Fin m → X → ℝ}
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) (j : Fin (m + 1)) (x : X) (t : ℝ) :
    ((∀ i : Fin m, i.succ = j → θ i x < t) ∧ a < t) ↔
      augmentedStack a b θ j.castSucc x < t := by
  refine j.cases ?_ fun i₀ ↦ ?_
  · simp [augmentedStack_zero]
  · simp only [Fin.succ_inj, forall_eq, ← Fin.succ_castSucc, augmentedStack_inner]
    exact ⟨fun h ↦ h.left, fun h ↦ ⟨h, (mem_Ioo.mp (hbnd i₀ x)).left.trans h⟩⟩

private theorem sectorUpper_iff {X : Type*} {a b : ℝ} {m : ℕ} {θ : Fin m → X → ℝ}
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) (j : Fin (m + 1)) (x : X) (t : ℝ) :
    ((∀ i : Fin m, i.castSucc = j → t < θ i x) ∧ t < b) ↔
      t < augmentedStack a b θ j.succ x := by
  refine j.lastCases ?_ fun i₀ ↦ ?_
  · simp [Fin.succ_last, augmentedStack_last, Fin.castSucc_ne_last]
  · simp only [Fin.castSucc_inj, forall_eq, augmentedStack_inner]
    exact ⟨fun h ↦ h.left, fun h ↦ ⟨h, h.trans (mem_Ioo.mp (hbnd i₀ x)).right⟩⟩

private theorem sectorSet_inter_Ioo_eq {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) (j : Fin (m + 1)) :
    cylinder S '' sectorSet θ j ∩ {v | v 0 ∈ Ioo a b} =
      cylinder S '' sectorSet (augmentedStack a b θ) j.castSucc.succ := by
  have hmono : ∀ x, Monotone fun r ↦ augmentedStack a b θ r x :=
    fun x ↦ (strictMono_augmentedStack hab hθ hbnd x).monotone
  ext v
  simp only [mem_inter_iff, mem_image_cylinder, mem_ofPred_eq, mem_Ioo,
    sectorSet_castSucc_succ hmono, mem_sectorSet_iff_of_monotone fun x ↦ (hθ x).monotone]
  refine ⟨fun ⟨⟨hx, hl, hu⟩, ha, hb⟩ ↦ ⟨hx, (sectorLower_iff hbnd j ⟨_, hx⟩ _).mp ⟨hl, ha⟩,
    (sectorUpper_iff hbnd j ⟨_, hx⟩ _).mp ⟨hu, hb⟩⟩, fun ⟨hx, hl, hu⟩ ↦ ?_⟩
  obtain ⟨hl', ha⟩ := (sectorLower_iff hbnd j ⟨_, hx⟩ _).mpr hl
  obtain ⟨hu', hb⟩ := (sectorUpper_iff hbnd j ⟨_, hx⟩ _).mpr hu
  exact ⟨⟨hx, hl', hu'⟩, ha, hb⟩

private theorem mem_stackCells_augmentedStack_of_mem_boundedStackCells {n m : ℕ} {a b : ℝ}
    {S : Set (Fin n → ℝ)} {θ : Fin m → S → ℝ} (hab : a < b)
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hbnd : ∀ i x, θ i x ∈ Ioo a b)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ boundedStackCells a b S θ) :
    E ∈ stackCells S (augmentedStack a b θ) := by
  rcases mem_boundedStackCells.mp hE with ⟨T, hT, rfl⟩
  rcases mem_stackCells.mp hT with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [sectionSet_inter_Ioo_eq hbnd i]
    exact image_cylinder_sectionSet_mem_stackCells i.castSucc.succ
  · rw [sectorSet_inter_Ioo_eq hab hθ hbnd j]
    exact image_cylinder_sectorSet_mem_stackCells j.castSucc.succ

/-- Every clipped cell of a strictly increasing stack whose values lie in `Ioo a b` projects onto
the base `S` under `Fin.tail`. -/
theorem image_tail_of_mem_boundedStackCells {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) {E : Set (Fin (n + 1) → ℝ)}
    (hE : E ∈ boundedStackCells a b S θ) : Fin.tail '' E = S :=
  image_tail_of_mem_stackCells (strictMono_augmentedStack hab hθ hbnd)
    (mem_stackCells_augmentedStack_of_mem_boundedStackCells hab hθ hbnd hE)

/-- Every clipped cell of a continuous strictly increasing stack whose values lie in `Ioo a b`
inherits preconnected approach regions at any ambient point `v₀ ∈ ℝⁿ⁺¹` whenever the base `S` has
preconnected approach regions at `Fin.tail v₀` and all sections `θ i` admit finite limits along `S`
at `Fin.tail v₀`. -/
theorem isPreconnectedApproachAt_of_mem_boundedStackCells {n m : ℕ} {a b : ℝ}
    {S : Set (Fin n → ℝ)} {θ : Fin m → S → ℝ} (hc : ∀ i, Continuous (θ i))
    (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hbnd : ∀ i x, θ i x ∈ Ioo a b)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ boundedStackCells a b S θ)
    {v₀ : Fin (n + 1) → ℝ} (hconn : IsPreconnectedApproachAt S (Fin.tail v₀))
    (hlim : ∀ i, ∃ L, Tendsto (θ i) (comap Subtype.val (𝓝 (Fin.tail v₀))) (𝓝 L)) :
    IsPreconnectedApproachAt E v₀ := by
  refine isPreconnectedApproachAt_of_mem_stackCells (continuous_augmentedStack hc)
    (strictMono_augmentedStack hab hθ hbnd)
    (mem_stackCells_augmentedStack_of_mem_boundedStackCells hab hθ hbnd hE) hconn fun r ↦ ?_
  refine r.cases ⟨a, tendsto_const_nhds⟩ fun s ↦ s.lastCases ?_ fun i ↦ ?_
  · rw [Fin.succ_last, funext (augmentedStack_last a b θ)]
    exact ⟨b, tendsto_const_nhds⟩
  · rw [funext (augmentedStack_inner a b θ i)]
    exact hlim i

end TauCeti
