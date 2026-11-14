/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.Order.Antichain
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.UpperLower.Closure
import Mathlib.Data.Finsupp.PWO
import TauCeti.Data.Finsupp.Fin
import TauCeti.Data.Finsupp.MapDomain

/-!
# Exponent diagrams, monotone coordinate transfers, and Bierstone–Milman's diagram cutoff

Let `D : Set (σ →₀ ℕ)` be a set of multi-indices on a finite linearly ordered variable set `σ`.
In Hironaka's and Bierstone–Milman's division theory, an upward-closed diagram `D` decomposes into
finitely many minimal vertices `D.diagramVertices : Finset (σ →₀ ℕ)` (by Dickson's lemma) and
pairwise disjoint translated cones `D.diagramCell α = α + D.diagramBox α` ordered by the
homogeneous lexicographic order `DegLex`.

A diagram `D` is *monotone* (`Set.IsMonotoneDiagram D`) if moving the entire exponent at any
coordinate `i` to a strictly larger coordinate `j` (`Finsupp.transferExp α i j`) keeps every
member of `D` inside `D`. Bierstone and Milman (1997, Definition 8.3 and Theorem 8.1, pp. 274–275)
show that monotone diagrams satisfy three finite-degree stability properties with respect to a
canonical combinatorial threshold `D.diagramCutoff`:

* For every vertex `α ∈ D.diagramVertices` whose first coordinate is positive and every quotient
  exponent `β ∈ D.diagramBox α`, all remaining coordinates of `β` are strictly bounded by that
  first coordinate (`Set.apply_succ_lt_of_mem_diagramBox`); hence if `β 0 = 0`, then
  `α.degree + β.degree < D.diagramCutoff` (`Set.degree_add_lt_diagramCutoff_of_mem_diagramBox`).
* When `D` is upward closed, above `D.diagramCutoff` the complement `Dᶜ` is closed under
  incrementing coordinate `0` (`Set.single_zero_add_notMem_of_notMem`).
* Above `D.diagramCutoff`, each quotient region `D.diagramBox α` is closed under incrementing
  coordinate `0` (`Set.single_zero_add_mem_diagramBox`).

## Main definitions

* `Finsupp.transferExp`: move the entire exponent of `α : σ →₀ ℕ` at `i` to `j`.
* `Set.IsMonotoneDiagram`: closure of `D : Set (σ →₀ ℕ)` under `Finsupp.transferExp · i j` for
  `i < j`.
* `Set.diagramVertices`: for `[Finite σ]`, the `Finset` of componentwise minimal elements of `D`.
* `Set.diagramBox`, `Set.diagramCell`: the `DegLex`-ordered quotient region `□_α` and translated
  division cell `Δ_α = α + □_α` of a diagram `D`.
* `Set.diagramSliceZero`: the coordinate-zero slice `{α' : Fin n →₀ ℕ | Finsupp.cons 0 α' ∈ D}` of
  a diagram on `Fin (n + 1)`.
* `Set.diagramCutoff`: Bierstone–Milman's recursive degree threshold `k(D)` of a diagram `D` on a
  finite linearly ordered index type `σ`.

## Main results

* `Finsupp.degree_transferExp`, `Finsupp.toDegLex_transferExp_lt`: `transferExp` preserves total
  degree and strictly decreases `DegLex` whenever `i < j` and `0 < α i`.
* `Set.disjoint_diagramCell`, `Set.biUnion_diagramCell_eq`,
  `Set.existsUnique_mem_diagramCell_of_mem`: for an upward-closed diagram `D`, the cells
  `D.diagramCell v` (`v ∈ D.diagramVertices`) partition `D`.
* `Set.mem_diagramVertices_diagramSliceZero_iff`, `Set.cons_zero_mem_diagramBox_iff`: vertices and
  division boxes of `D.diagramSliceZero` match the coordinate-zero vertices and boxes of `D`.
* `Set.apply_succ_lt_of_mem_diagramBox`, `Set.single_zero_add_notMem_of_notMem`,
  `Set.single_zero_add_mem_diagramBox`: the three monotonicity bounds above `D.diagramCutoff`.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Theorem 8.1 and Definition 8.3, pp. 274–275.
-/

public section

namespace Finsupp

section TransferExp

variable {σ τ : Type*}

/-- Move the entire exponent of `α : σ →₀ ℕ` at coordinate `i` to coordinate `j`. -/
noncomputable def transferExp (α : σ →₀ ℕ) (i j : σ) : σ →₀ ℕ :=
  α - single i (α i) + single j (α i)

theorem transferExp_def (α : σ →₀ ℕ) (i j : σ) :
    α.transferExp i j = α - single i (α i) + single j (α i) := (rfl)

@[simp]
theorem transferExp_self (α : σ →₀ ℕ) (i : σ) : α.transferExp i i = α := by
  classical
  ext k
  rw [transferExp_def]
  by_cases h : k = i
  · subst h
    simp
  · simp [single_eq_of_ne h]

@[simp]
theorem transferExp_zero (i j : σ) : (0 : σ →₀ ℕ).transferExp i j = 0 := by
  simp [transferExp_def]

theorem transferExp_apply_left (α : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) :
    α.transferExp i j i = 0 := by
  rw [transferExp_def, add_apply, tsub_apply, single_eq_same, tsub_self, zero_add,
    single_eq_of_ne hij]

theorem transferExp_apply_right (α : σ →₀ ℕ) {i j : σ} (hij : i ≠ j) :
    α.transferExp i j j = α j + α i := by
  rw [transferExp_def, add_apply, tsub_apply, single_eq_of_ne hij.symm, tsub_zero, single_eq_same]

theorem transferExp_apply_of_ne (α : σ →₀ ℕ) {i j k : σ} (hki : k ≠ i) (hkj : k ≠ j) :
    α.transferExp i j k = α k := by
  rw [transferExp_def, add_apply, tsub_apply, single_eq_of_ne hki, single_eq_of_ne hkj, tsub_zero,
    add_zero]

theorem transferExp_apply [DecidableEq σ] (α : σ →₀ ℕ) (i j k : σ) :
    α.transferExp i j k =
      if i = j then α k else if k = i then 0 else if k = j then α j + α i else α k := by
  split_ifs with hij hki hkj
  · subst hij
    exact congrArg (· k) (α.transferExp_self i)
  · subst hki
    exact α.transferExp_apply_left hij
  · subst hkj
    exact α.transferExp_apply_right hij
  · exact α.transferExp_apply_of_ne hki hkj

@[simp]
theorem degree_transferExp (α : σ →₀ ℕ) (i j : σ) : (α.transferExp i j).degree = α.degree := by
  have hle : single i (α i) ≤ α := single_le_iff.mpr le_rfl
  have hcancel : (α - single i (α i)).degree + α i = α.degree := by
    simpa [map_add, degree_single] using congrArg degree (tsub_add_cancel_of_le hle)
  rw [transferExp_def, map_add, degree_single, hcancel]

theorem transferExp_mono {α β : σ →₀ ℕ} (h : α ≤ β) (i j : σ) :
    α.transferExp i j ≤ β.transferExp i j := by
  classical
  intro k
  simp only [transferExp_apply]
  split_ifs
  · exact h k
  · exact le_rfl
  · exact add_le_add (h j) (h i)
  · exact h k

theorem equivMapDomain_transferExp (e : σ ≃ τ) (α : σ →₀ ℕ) (i j : σ) :
    equivMapDomain e (α.transferExp i j) = (equivMapDomain e α).transferExp (e i) (e j) := by
  classical
  ext k
  obtain ⟨k, rfl⟩ := e.surjective k
  simp [transferExp_apply, e.injective.eq_iff]

theorem cons_zero_transferExp {n : ℕ} (α' : Fin n →₀ ℕ) (i j : Fin n) :
    (cons 0 α').transferExp i.succ j.succ = cons 0 (α'.transferExp i j) := by
  classical
  ext k
  cases k using Fin.cases with
  | zero =>
    rw [cons_zero, transferExp_apply_of_ne _ (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm,
      cons_zero]
  | succ r =>
    simp [transferExp_apply, Fin.succ_inj]

/-- Moving a positive exponent from `i` to a strictly larger coordinate `j` strictly decreases
`DegLex`. -/
theorem toDegLex_transferExp_lt [LinearOrder σ] {α : σ →₀ ℕ} {i j : σ} (hij : i < j)
    (hα : 0 < α i) :
    toDegLex (α.transferExp i j) < toDegLex α := by
  rw [DegLex.lt_iff, ofDegLex_toDegLex, ofDegLex_toDegLex, degree_transferExp]
  refine Or.inr ⟨rfl, ?_⟩
  rw [Lex.lt_iff, ofLex_toLex, ofLex_toLex]
  refine ⟨i, fun k hk ↦ ?_, ?_⟩
  · exact α.transferExp_apply_of_ne hk.ne (hk.trans hij).ne
  · rw [α.transferExp_apply_left hij.ne]
    exact hα

theorem toDegLex_equivMapDomain_lt_iff [LinearOrder σ] [LinearOrder τ] (e : σ ≃o τ)
    {α β : σ →₀ ℕ} :
    toDegLex (equivMapDomain e.toEquiv α) < toDegLex (equivMapDomain e.toEquiv β) ↔
      toDegLex α < toDegLex β := by
  have hsm : StrictMono e.toEquiv := e.strictMono
  simp only [equivMapDomain_eq_mapDomain, DegLex.lt_iff, ofDegLex_toDegLex, degree_mapDomain,
    toLex_mapDomain_lt_toLex_mapDomain_iff hsm]

@[simp]
theorem degree_cons {n : ℕ} {M : Type*} [AddCommMonoid M] (c : M) (α' : Fin n →₀ M) :
    (cons c α').degree = c + α'.degree := by
  have hsplit : cons c α' = cons c 0 + cons 0 α' := by
    rw [cons_add_cons, add_zero, zero_add]
  rw [hsplit, map_add, cons_zero_eq_single_zero, degree_single, ← mapDomain_finSucc,
    degree_mapDomain]

@[simp]
theorem toDegLex_cons_zero_lt_iff {n : ℕ} {α' β' : Fin n →₀ ℕ} :
    toDegLex (cons 0 α') < toDegLex (cons 0 β') ↔ toDegLex α' < toDegLex β' := by
  simp [DegLex.lt_iff, toLex_cons_lt_toLex_cons_iff]

end TransferExp

end Finsupp

namespace Set

section MonotoneDiagram

variable {σ : Type*}

/-- A subset `D : Set (σ →₀ ℕ)` is a *monotone diagram* (Bierstone–Milman, Definition 8.3) if
moving the entire exponent at any coordinate `i` to a strictly larger coordinate `j` preserves
membership in `D`. -/
def IsMonotoneDiagram [LT σ] (D : Set (σ →₀ ℕ)) : Prop :=
  ∀ ⦃α : σ →₀ ℕ⦄, α ∈ D → ∀ ⦃i j : σ⦄, i < j → α.transferExp i j ∈ D

theorem isMonotoneDiagram_iff [LT σ] {D : Set (σ →₀ ℕ)} :
    D.IsMonotoneDiagram ↔ ∀ ⦃α : σ →₀ ℕ⦄, α ∈ D → ∀ ⦃i j : σ⦄, i < j → α.transferExp i j ∈ D :=
  Iff.rfl

@[simp]
theorem isMonotoneDiagram_empty [LT σ] : (∅ : Set (σ →₀ ℕ)).IsMonotoneDiagram :=
  fun _ h ↦ False.elim h

@[simp]
theorem isMonotoneDiagram_univ [LT σ] : (Set.univ : Set (σ →₀ ℕ)).IsMonotoneDiagram :=
  fun _ _ _ _ _ ↦ trivial

theorem IsMonotoneDiagram.inter [LT σ] {D₁ D₂ : Set (σ →₀ ℕ)} (h₁ : D₁.IsMonotoneDiagram)
    (h₂ : D₂.IsMonotoneDiagram) : (D₁ ∩ D₂).IsMonotoneDiagram :=
  fun _ h _ _ hij ↦ ⟨h₁ h.1 hij, h₂ h.2 hij⟩

theorem IsMonotoneDiagram.union [LT σ] {D₁ D₂ : Set (σ →₀ ℕ)} (h₁ : D₁.IsMonotoneDiagram)
    (h₂ : D₂.IsMonotoneDiagram) : (D₁ ∪ D₂).IsMonotoneDiagram :=
  fun _ h _ _ hij ↦ h.elim (fun h' ↦ Or.inl (h₁ h' hij)) (fun h' ↦ Or.inr (h₂ h' hij))

theorem isMonotoneDiagram_of_subsingleton [Preorder σ] [Subsingleton σ] (D : Set (σ →₀ ℕ)) :
    D.IsMonotoneDiagram :=
  fun _ _ i j hij ↦ absurd (Subsingleton.elim i j) hij.ne

theorem isMonotoneDiagram_degree_ge [LT σ] (d : ℕ) :
    {α : σ →₀ ℕ | d ≤ α.degree}.IsMonotoneDiagram := by
  intro α hα i j _
  simpa using hα

theorem IsMonotoneDiagram.upperClosure [LT σ] {S : Set (σ →₀ ℕ)} (hS : S.IsMonotoneDiagram) :
    (↑(_root_.upperClosure S) : Set (σ →₀ ℕ)).IsMonotoneDiagram := by
  intro α hα i j hij
  rw [coe_upperClosure, mem_iUnion₂] at hα ⊢
  obtain ⟨β, hβS, hle⟩ := hα
  exact ⟨β.transferExp i j, hS hβS hij, Finsupp.transferExp_mono hle i j⟩

theorem isMonotoneDiagram_preimage_equivMapDomain {τ : Type*} [Preorder σ] [Preorder τ]
    (e : σ ≃o τ) {D : Set (τ →₀ ℕ)} :
    (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).IsMonotoneDiagram ↔ D.IsMonotoneDiagram := by
  refine ⟨fun h α hα i j hij ↦ ?_, fun h α hα i j hij ↦ ?_⟩
  · obtain ⟨α₀, rfl⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective α
    obtain ⟨i₀, rfl⟩ := e.surjective i
    obtain ⟨j₀, rfl⟩ := e.surjective j
    simpa [Finsupp.equivMapDomain_transferExp] using h hα (e.lt_iff_lt.mp hij)
  · simpa [Finsupp.equivMapDomain_transferExp] using h hα (e.strictMono hij)

end MonotoneDiagram

section DiagramVertices

variable {σ : Type*}

/-- Every exponent in `D : Set (σ →₀ ℕ)` lies componentwise above a minimal element of `D`. -/
theorem exists_minimal_diagram_le {D : Set (σ →₀ ℕ)} {γ : σ →₀ ℕ} (hγ : γ ∈ D) :
    ∃ α ≤ γ, Minimal (· ∈ D) α :=
  exists_minimal_le_of_wellFoundedLT (· ∈ D) γ hγ

/-- For finitely many variables `σ`, the componentwise minimal elements of `D : Set (σ →₀ ℕ)` form
a finite set by Dickson's lemma. -/
theorem finite_minimal_diagram [Finite σ] (D : Set (σ →₀ ℕ)) :
    {α : σ →₀ ℕ | Minimal (· ∈ D) α}.Finite :=
  WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)

/-- For finitely many variables `σ`, the `Finset` of componentwise minimal vertices of an exponent
diagram `D : Set (σ →₀ ℕ)`. -/
noncomputable def diagramVertices [Finite σ] (D : Set (σ →₀ ℕ)) : Finset (σ →₀ ℕ) :=
  D.finite_minimal_diagram.toFinset

@[simp]
theorem mem_diagramVertices_iff [Finite σ] {D : Set (σ →₀ ℕ)} {α : σ →₀ ℕ} :
    α ∈ D.diagramVertices ↔ Minimal (· ∈ D) α :=
  Set.Finite.mem_toFinset _

theorem diagramVertices_subset [Finite σ] (D : Set (σ →₀ ℕ)) :
    (D.diagramVertices : Set (σ →₀ ℕ)) ⊆ D :=
  fun _ hα ↦ (mem_diagramVertices_iff.mp hα).prop

theorem isAntichain_diagramVertices [Finite σ] (D : Set (σ →₀ ℕ)) :
    IsAntichain (· ≤ ·) (D.diagramVertices : Set (σ →₀ ℕ)) :=
  fun _ hα _ hβ ↦ setOfPred_minimal_antichain _ (mem_diagramVertices_iff.mp hα)
    (mem_diagramVertices_iff.mp hβ)

theorem exists_mem_diagramVertices_le [Finite σ] {D : Set (σ →₀ ℕ)} {γ : σ →₀ ℕ} (hγ : γ ∈ D) :
    ∃ α ∈ D.diagramVertices, α ≤ γ := by
  obtain ⟨α, hle, hmin⟩ := exists_minimal_diagram_le hγ
  exact ⟨α, mem_diagramVertices_iff.mpr hmin, hle⟩

theorem mem_iff_exists_mem_diagramVertices_le [Finite σ] {D : Set (σ →₀ ℕ)} (hD : IsUpperSet D)
    {γ : σ →₀ ℕ} :
    γ ∈ D ↔ ∃ α ∈ D.diagramVertices, α ≤ γ :=
  ⟨exists_mem_diagramVertices_le, fun ⟨_, hα, hle⟩ ↦ hD hle (D.diagramVertices_subset hα)⟩

@[simp]
theorem diagramVertices_empty [Finite σ] : (∅ : Set (σ →₀ ℕ)).diagramVertices = ∅ := by
  ext α
  simp [Minimal]

@[simp]
theorem diagramVertices_eq_empty_iff [Finite σ] {D : Set (σ →₀ ℕ)} :
    D.diagramVertices = ∅ ↔ D = ∅ := by
  refine ⟨fun h ↦ eq_empty_iff_forall_notMem.mpr fun γ hγ ↦ ?_, fun h ↦ by simp [h]⟩
  obtain ⟨α, hα, _⟩ := exists_mem_diagramVertices_le hγ
  rw [h] at hα
  exact Finset.notMem_empty α hα

@[simp]
theorem diagramVertices_univ [Finite σ] : (Set.univ : Set (σ →₀ ℕ)).diagramVertices = {0} := by
  ext α
  simp only [mem_diagramVertices_iff, Minimal, mem_univ, true_and, forall_true_left,
    Finset.mem_singleton]
  exact ⟨fun h ↦ le_zero_iff.mp (h _root_.zero_le), fun h _ _ ↦ h ▸ _root_.zero_le⟩

@[simp]
theorem diagramVertices_Ici [Finite σ] (α : σ →₀ ℕ) :
    (Set.Ici α).diagramVertices = {α} := by
  ext β
  simp only [mem_diagramVertices_iff, Minimal, mem_Ici, Finset.mem_singleton]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ le_antisymm (h₂ le_rfl h₁) h₁,
    fun h ↦ h ▸ ⟨le_rfl, fun _ hle _ ↦ hle⟩⟩

theorem diagramVertices_upperClosure_finset [Finite σ] {s : Finset (σ →₀ ℕ)}
    (hs : IsAntichain (· ≤ ·) (s : Set (σ →₀ ℕ))) :
    (↑(upperClosure (s : Set (σ →₀ ℕ))) : Set (σ →₀ ℕ)).diagramVertices = s := by
  ext α
  simp only [mem_diagramVertices_iff, SetLike.mem_coe, hs.minimal_mem_upperClosure_iff_mem]

theorem mem_diagramVertices_preimage_equivMapDomain_iff {τ : Type*} [Finite σ] [Finite τ]
    (e : σ ≃ τ) {D : Set (τ →₀ ℕ)} {α : σ →₀ ℕ} :
    α ∈ (Finsupp.equivMapDomain e ⁻¹' D).diagramVertices ↔
      Finsupp.equivMapDomain e α ∈ D.diagramVertices := by
  have hle (x y : σ →₀ ℕ) : Finsupp.equivMapDomain e x ≤ Finsupp.equivMapDomain e y ↔ x ≤ y :=
    ⟨fun h i ↦ by simpa using h (e i), fun h j ↦ by
      obtain ⟨i, rfl⟩ := e.surjective j
      simpa using h i⟩
  simp only [mem_diagramVertices_iff, Minimal, mem_preimage, ← hle]
  refine and_congr Iff.rfl ⟨fun h y hy hyle ↦ ?_, fun h x hx hxle ↦ h hx hxle⟩
  obtain ⟨x, rfl⟩ := (Finsupp.domCongr e (M := ℕ)).surjective y
  simp only [Finsupp.domCongr_apply] at hy hyle ⊢
  exact h hy hyle

end DiagramVertices

section DivisionCells

variable {σ : Type*} [Finite σ] [LinearOrder σ]

/-- The quotient exponent box `□_α` associated to `α` and `D : Set (σ →₀ ℕ)`: those `β` such that
`α + β` avoids every cone above a `DegLex`-smaller vertex of `D`. -/
def diagramBox (D : Set (σ →₀ ℕ)) (α : σ →₀ ℕ) : Set (σ →₀ ℕ) :=
  {β | ∀ α' ∈ D.diagramVertices, toDegLex α' < toDegLex α → ¬ α' ≤ α + β}

/-- The translated division cell `Δ_α = α + □_α` associated to `α` and `D : Set (σ →₀ ℕ)`. -/
def diagramCell (D : Set (σ →₀ ℕ)) (α : σ →₀ ℕ) : Set (σ →₀ ℕ) :=
  {γ | α ≤ γ ∧ ∀ α' ∈ D.diagramVertices, toDegLex α' < toDegLex α → ¬ α' ≤ γ}

theorem mem_diagramBox_iff {D : Set (σ →₀ ℕ)} {α β : σ →₀ ℕ} :
    β ∈ D.diagramBox α ↔ ∀ α' ∈ D.diagramVertices, toDegLex α' < toDegLex α → ¬ α' ≤ α + β :=
  Iff.rfl

theorem mem_diagramCell_iff {D : Set (σ →₀ ℕ)} {α γ : σ →₀ ℕ} :
    γ ∈ D.diagramCell α ↔
      α ≤ γ ∧ ∀ α' ∈ D.diagramVertices, toDegLex α' < toDegLex α → ¬ α' ≤ γ :=
  Iff.rfl

@[simp]
theorem add_mem_diagramCell_iff {D : Set (σ →₀ ℕ)} {α β : σ →₀ ℕ} :
    α + β ∈ D.diagramCell α ↔ β ∈ D.diagramBox α :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨le_self_add, h⟩⟩

theorem tsub_mem_diagramBox_of_mem_diagramCell {D : Set (σ →₀ ℕ)} {α γ : σ →₀ ℕ}
    (h : γ ∈ D.diagramCell α) : γ - α ∈ D.diagramBox α := by
  rw [← add_mem_diagramCell_iff, add_tsub_cancel_of_le h.1]
  exact h

@[simp]
theorem zero_mem_diagramBox {D : Set (σ →₀ ℕ)} {α : σ →₀ ℕ} (hα : α ∈ D.diagramVertices) :
    0 ∈ D.diagramBox α := by
  intro α' hα' hlt hle
  rw [add_zero] at hle
  have heq : α' = α := by
    by_contra hne
    exact D.isAntichain_diagramVertices hα' hα hne hle
  exact hlt.ne (congrArg toDegLex heq)

@[simp]
theorem diagramBox_univ : (Set.univ : Set (σ →₀ ℕ)).diagramBox 0 = Set.univ := by
  ext β
  simp [diagramBox]

/-- Distinct vertices of `D` have disjoint division cells. -/
theorem disjoint_diagramCell {D : Set (σ →₀ ℕ)} {α₁ α₂ : σ →₀ ℕ}
    (h₁ : α₁ ∈ D.diagramVertices) (h₂ : α₂ ∈ D.diagramVertices) (hne : α₁ ≠ α₂) :
    Disjoint (D.diagramCell α₁) (D.diagramCell α₂) := by
  rw [disjoint_left]
  intro γ hc₁ hc₂
  rcases lt_trichotomy (toDegLex α₁) (toDegLex α₂) with hlt | heq | hlt
  · exact hc₂.2 α₁ h₁ hlt hc₁.1
  · exact hne (toDegLex_injective heq)
  · exact hc₁.2 α₂ h₂ hlt hc₂.1

/-- For an upward-closed diagram `D`, its vertex division cells cover `D`. -/
theorem biUnion_diagramCell_eq {D : Set (σ →₀ ℕ)} (hD : IsUpperSet D) :
    ⋃ α ∈ D.diagramVertices, D.diagramCell α = D := by
  classical
  ext γ
  simp only [mem_iUnion, exists_prop]
  refine ⟨fun ⟨α, hα, hc⟩ ↦ hD hc.1 (D.diagramVertices_subset hα), fun hγ ↦ ?_⟩
  let s : Finset (DegLex (σ →₀ ℕ)) :=
    (D.diagramVertices.filter (· ≤ γ)).image toDegLex
  have hs : s.Nonempty := by
    obtain ⟨α, hα, hle⟩ := exists_mem_diagramVertices_le hγ
    exact ⟨toDegLex α, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hα, hle⟩)⟩
  obtain ⟨α, hαf, hmin_eq⟩ := Finset.mem_image.mp (s.min'_mem hs)
  obtain ⟨hα, hle⟩ := Finset.mem_filter.mp hαf
  refine ⟨α, hα, hle, fun α' hα' hlt hle' ↦ ?_⟩
  have hmem' : toDegLex α' ∈ s :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hα', hle'⟩)
  exact hlt.not_ge (hmin_eq ▸ s.min'_le _ hmem')

/-- Every element of an upward-closed diagram `D` belongs to the division cell of a unique vertex
of `D`. -/
theorem existsUnique_mem_diagramCell_of_mem {D : Set (σ →₀ ℕ)} (hD : IsUpperSet D) {γ : σ →₀ ℕ}
    (hγ : γ ∈ D) :
    ∃! v : D.diagramVertices, γ ∈ D.diagramCell v.1 := by
  have hmem : γ ∈ ⋃ α ∈ D.diagramVertices, D.diagramCell α := by
    rwa [biUnion_diagramCell_eq hD]
  rw [mem_iUnion₂] at hmem
  obtain ⟨α, hα, hc⟩ := hmem
  refine ⟨⟨α, hα⟩, hc, fun v hv ↦ Subtype.ext ?_⟩
  by_contra hne
  exact (disjoint_diagramCell v.2 hα hne).le_bot ⟨hv, hc⟩

theorem mem_diagramBox_preimage_equivMapDomain_iff {τ : Type*} [Finite τ] [LinearOrder τ]
    (e : σ ≃o τ) {D : Set (τ →₀ ℕ)} {α β : σ →₀ ℕ} :
    β ∈ (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramBox α ↔
      Finsupp.equivMapDomain e.toEquiv β ∈ D.diagramBox (Finsupp.equivMapDomain e.toEquiv α) := by
  have hle (x y : σ →₀ ℕ) :
      Finsupp.equivMapDomain e.toEquiv x ≤ Finsupp.equivMapDomain e.toEquiv y ↔ x ≤ y :=
    ⟨fun h i ↦ by simpa using h (e i), fun h j ↦ by
      obtain ⟨i, rfl⟩ := e.surjective j
      simpa using h i⟩
  have hadd (x y : σ →₀ ℕ) :
      Finsupp.equivMapDomain e.toEquiv x + Finsupp.equivMapDomain e.toEquiv y =
        Finsupp.equivMapDomain e.toEquiv (x + y) :=
    ((Finsupp.domCongr e.toEquiv (M := ℕ)).map_add x y).symm
  simp only [mem_diagramBox_iff, mem_diagramVertices_preimage_equivMapDomain_iff]
  refine ⟨fun h α' hα' hlt ↦ ?_, fun h α' hα' hlt ↦ ?_⟩
  · obtain ⟨α₀, rfl⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective α'
    simp only [Finsupp.domCongr_apply] at hα' hlt ⊢
    rw [Finsupp.toDegLex_equivMapDomain_lt_iff e] at hlt
    rw [hadd, hle]
    exact h α₀ hα' hlt
  · have hlt' := (Finsupp.toDegLex_equivMapDomain_lt_iff e).mpr hlt
    rw [← hle, ← hadd]
    exact h _ hα' hlt'

end DivisionCells

section SliceZero

variable {n : ℕ}

/-- The coordinate-zero slice `{α' : Fin n →₀ ℕ | Finsupp.cons 0 α' ∈ D}` of an exponent diagram
`D` on `Fin (n + 1)`. -/
def diagramSliceZero (D : Set (Fin (n + 1) →₀ ℕ)) : Set (Fin n →₀ ℕ) :=
  {α' | Finsupp.cons 0 α' ∈ D}

@[simp]
theorem mem_diagramSliceZero_iff {D : Set (Fin (n + 1) →₀ ℕ)} {α' : Fin n →₀ ℕ} :
    α' ∈ D.diagramSliceZero ↔ Finsupp.cons 0 α' ∈ D :=
  Iff.rfl

@[simp]
theorem diagramSliceZero_empty : (∅ : Set (Fin (n + 1) →₀ ℕ)).diagramSliceZero = ∅ := by
  ext α'
  simp

@[simp]
theorem diagramSliceZero_univ :
    (Set.univ : Set (Fin (n + 1) →₀ ℕ)).diagramSliceZero = Set.univ := by
  ext α'
  simp

theorem _root_.IsUpperSet.diagramSliceZero {D : Set (Fin (n + 1) →₀ ℕ)} (hD : IsUpperSet D) :
    IsUpperSet D.diagramSliceZero :=
  fun _ _ hle hα ↦ hD (Finsupp.cons_le_cons_iff.mpr ⟨le_rfl, hle⟩) hα

theorem IsMonotoneDiagram.diagramSliceZero {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD : D.IsMonotoneDiagram) : D.diagramSliceZero.IsMonotoneDiagram := by
  intro α' hα' i j hij
  rw [mem_diagramSliceZero_iff, ← Finsupp.cons_zero_transferExp]
  exact hD hα' (Fin.succ_lt_succ_iff.mpr hij)

theorem mem_diagramVertices_diagramSliceZero_iff {D : Set (Fin (n + 1) →₀ ℕ)}
    {α' : Fin n →₀ ℕ} :
    α' ∈ D.diagramSliceZero.diagramVertices ↔ Finsupp.cons 0 α' ∈ D.diagramVertices := by
  simp only [mem_diagramVertices_iff, Minimal, mem_diagramSliceZero_iff]
  refine and_congr Iff.rfl ⟨fun h γ hγ hle ↦ ?_, fun h β' hβ' hle ↦ ?_⟩
  · have hγ0 : γ 0 = 0 := Nat.eq_zero_of_le_zero (by simpa using hle 0)
    have hγeq : Finsupp.cons 0 γ.tail = γ := by
      rw [← hγ0, Finsupp.cons_tail]
    have htail_le : γ.tail ≤ α' := fun i ↦ by simpa [Finsupp.tail_apply] using hle i.succ
    have hle' : α' ≤ γ.tail := h (hγeq.symm ▸ hγ) htail_le
    rw [← hγeq]
    exact Finsupp.cons_le_cons_iff.mpr ⟨le_rfl, hle'⟩
  · exact (Finsupp.cons_le_cons_iff.mp (h hβ' (Finsupp.cons_le_cons_iff.mpr ⟨le_rfl, hle⟩))).2

@[simp]
theorem cons_zero_mem_diagramBox_iff {D : Set (Fin (n + 1) →₀ ℕ)} {α' β' : Fin n →₀ ℕ} :
    Finsupp.cons 0 β' ∈ D.diagramBox (Finsupp.cons 0 α') ↔
      β' ∈ D.diagramSliceZero.diagramBox α' := by
  simp only [mem_diagramBox_iff, mem_diagramVertices_diagramSliceZero_iff, Finsupp.cons_add_cons,
    zero_add]
  refine ⟨fun h γ' hγ' hlt ↦ ?_, fun h γ hγ hlt hle ↦ ?_⟩
  · rw [← Finsupp.toDegLex_cons_zero_lt_iff] at hlt
    intro hle
    exact h (Finsupp.cons 0 γ') hγ' hlt (Finsupp.cons_le_cons_iff.mpr ⟨le_rfl, hle⟩)
  · have hγ0 : γ 0 = 0 := Nat.eq_zero_of_le_zero (by simpa using hle 0)
    have hγeq : Finsupp.cons 0 γ.tail = γ := by rw [← hγ0, Finsupp.cons_tail]
    rw [← hγeq] at hγ hlt hle
    rw [Finsupp.toDegLex_cons_zero_lt_iff] at hlt
    rw [Finsupp.cons_le_cons_iff] at hle
    exact h γ.tail hγ hlt hle.2

end SliceZero

section DiagramCutoff

open scoped Classical in
/-- Recursive degree cutoff on `Fin n` used to define `Set.diagramCutoff`. -/
private noncomputable def diagramCutoffFin : ∀ {n : ℕ}, Set (Fin n →₀ ℕ) → ℕ
  | 0, _ => 0
  | n + 1, D =>
    max (diagramCutoffFin D.diagramSliceZero)
      ((D.diagramVertices.filter (fun α ↦ 1 ≤ α 0)).sup (fun α ↦ α.degree + n * (α 0 - 1) + 1))

private noncomputable def diagramCutoffAux {σ : Type*} (ft : Fintype σ) [LinearOrder σ]
    (D : Set (σ →₀ ℕ)) : ℕ :=
  diagramCutoffFin
    (Finsupp.equivMapDomain (@Fintype.orderIsoFinOfCardEq σ _ ft _ rfl).toEquiv ⁻¹' D)

/-- Bierstone–Milman's finite degree cutoff `k(D)` of a diagram `D : Set (σ →₀ ℕ)` on a finite
linearly ordered variable set `σ`. -/
noncomputable def diagramCutoff {σ : Type*} [Finite σ] [LinearOrder σ] (D : Set (σ →₀ ℕ)) : ℕ :=
  diagramCutoffAux (Fintype.ofFinite σ) D

private theorem diagramCutoff_eq_of_orderIsoFin {σ : Type*} [Finite σ] [LinearOrder σ] {d : ℕ}
    (e : Fin d ≃o σ) (D : Set (σ →₀ ℕ)) :
    D.diagramCutoff = diagramCutoffFin (Finsupp.equivMapDomain e.toEquiv ⁻¹' D) := by
  rw [diagramCutoff]
  set ft : Fintype σ := Fintype.ofFinite σ
  rw [diagramCutoffAux]
  have hd : @Fintype.card σ ft = d := by
    simpa using (@Fintype.card_congr (Fin d) σ _ ft e.toEquiv).symm
  subst hd
  have heq : @Fintype.orderIsoFinOfCardEq σ _ ft _ rfl = e := by
    ext i
    let f := (@Fintype.orderIsoFinOfCardEq σ _ ft _ rfl).trans e.symm
    have hf : f i = i := Fin.ext (Fin.coe_orderIso_apply f i)
    exact (OrderIso.symm_apply_eq e).mp hf
  rw [heq]

theorem diagramCutoff_preimage_equivMapDomain {σ τ : Type*} [Finite σ] [LinearOrder σ]
    [Finite τ] [LinearOrder τ] (e : σ ≃o τ) (D : Set (τ →₀ ℕ)) :
    (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramCutoff = D.diagramCutoff := by
  cases nonempty_fintype σ
  let eσ : Fin (Fintype.card σ) ≃o σ := Fintype.orderIsoFinOfCardEq σ rfl
  rw [diagramCutoff_eq_of_orderIsoFin eσ, diagramCutoff_eq_of_orderIsoFin (eσ.trans e)]
  congr 1
  ext α
  simp [← Finsupp.equivMapDomain_trans]

private theorem diagramCutoff_fin_eq {n : ℕ} (D : Set (Fin n →₀ ℕ)) :
    D.diagramCutoff = diagramCutoffFin D := by
  rw [diagramCutoff_eq_of_orderIsoFin (OrderIso.refl (Fin n)) D]
  congr 1
  ext α
  simp

theorem diagramCutoff_of_isEmpty {σ : Type*} [IsEmpty σ] [LinearOrder σ] (D : Set (σ →₀ ℕ)) :
    D.diagramCutoff = 0 := by
  let e : Fin 0 ≃o σ :=
    { toEquiv := Equiv.equivOfIsEmpty (Fin 0) σ
      map_rel_iff' := fun {i} ↦ Fin.elim0 i }
  rw [diagramCutoff_eq_of_orderIsoFin e D, diagramCutoffFin]

open scoped Classical in
theorem diagramCutoff_fin_succ {n : ℕ} (D : Set (Fin (n + 1) →₀ ℕ)) :
    D.diagramCutoff =
      max D.diagramSliceZero.diagramCutoff
        ((D.diagramVertices.filter (fun α ↦ 1 ≤ α 0)).sup
          (fun α ↦ α.degree + n * (α 0 - 1) + 1)) := by
  rw [diagramCutoff_fin_eq, diagramCutoff_fin_eq, diagramCutoffFin]

@[simp]
theorem diagramCutoff_empty {σ : Type*} [Finite σ] [LinearOrder σ] :
    (∅ : Set (σ →₀ ℕ)).diagramCutoff = 0 := by
  cases nonempty_fintype σ
  let e : Fin (Fintype.card σ) ≃o σ := Fintype.orderIsoFinOfCardEq σ rfl
  rw [← diagramCutoff_preimage_equivMapDomain e ∅, preimage_empty]
  generalize Fintype.card σ = d
  induction d with
  | zero => exact diagramCutoff_of_isEmpty ∅
  | succ n ih => simp [diagramCutoff_fin_succ, ih]

@[simp]
theorem diagramCutoff_univ {σ : Type*} [Finite σ] [LinearOrder σ] :
    (Set.univ : Set (σ →₀ ℕ)).diagramCutoff = 0 := by
  cases nonempty_fintype σ
  let e : Fin (Fintype.card σ) ≃o σ := Fintype.orderIsoFinOfCardEq σ rfl
  rw [← diagramCutoff_preimage_equivMapDomain e Set.univ, preimage_univ]
  generalize Fintype.card σ = d
  induction d with
  | zero => exact diagramCutoff_of_isEmpty Set.univ
  | succ n ih =>
    classical
    have hflt : ((Set.univ : Set (Fin (n + 1) →₀ ℕ)).diagramVertices.filter
        (fun α ↦ 1 ≤ α 0)) = ∅ := by
      ext α
      simp only [Finset.mem_filter, diagramVertices_univ, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      simp
    rw [diagramCutoff_fin_succ, diagramSliceZero_univ, ih, hflt]
    simp

theorem diagramSliceZero_diagramCutoff_le {n : ℕ} (D : Set (Fin (n + 1) →₀ ℕ)) :
    D.diagramSliceZero.diagramCutoff ≤ D.diagramCutoff := by
  rw [diagramCutoff_fin_succ]
  exact le_max_left _ _

theorem add_mul_add_one_le_diagramCutoff {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    {α : Fin (n + 1) →₀ ℕ} (hα : α ∈ D.diagramVertices) (hα0 : 1 ≤ α 0) :
    α.degree + n * (α 0 - 1) + 1 ≤ D.diagramCutoff := by
  classical
  rw [diagramCutoff_fin_succ]
  refine le_trans ?_ (le_max_right _ _)
  exact Finset.le_sup (f := fun α : Fin (n + 1) →₀ ℕ ↦ α.degree + n * (α 0 - 1) + 1)
    (Finset.mem_filter.mpr ⟨hα, hα0⟩)

/-- For a monotone diagram `D` on `Fin (n + 1)`, if `α ∈ D.diagramVertices` has `1 ≤ α 0` and
`β ∈ D.diagramBox α`, then every remaining coordinate of `β` satisfies `β q.succ < α 0`. -/
theorem apply_succ_lt_of_mem_diagramBox {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram) {α β : Fin (n + 1) →₀ ℕ}
    (hα : α ∈ D.diagramVertices) (hα0 : 1 ≤ α 0) (hβ : β ∈ D.diagramBox α) (q : Fin n) :
    β q.succ < α 0 := by
  let δ : Fin (n + 1) →₀ ℕ := α.transferExp 0 q.succ
  have hδD : δ ∈ D := hD_mono (D.diagramVertices_subset hα) (Fin.succ_pos q)
  obtain ⟨α', hα', hα'δ⟩ := exists_mem_diagramVertices_le hδD
  have hlt : toDegLex α' < toDegLex α := by
    refine lt_of_le_of_lt ?_ (Finsupp.toDegLex_transferExp_lt (Fin.succ_pos q) hα0)
    rcases (Finsupp.degree_mono hα'δ).lt_or_eq with hdeg | hdeg
    · exact le_of_lt (Finsupp.DegLex.lt_iff.mpr (Or.inl hdeg))
    · have heq : α' = δ :=
        hα'δ.eq_or_lt.resolve_right fun hstrict ↦ (Finsupp.degree_strictMono hstrict).ne hdeg
      exact heq ▸ le_rfl
  have hnot : ¬ δ ≤ α + β := fun hle ↦ hβ α' hα' hlt (hα'δ.trans hle)
  by_contra! hge
  refine hnot fun i ↦ ?_
  cases i using Fin.cases with
  | zero =>
    rw [Finsupp.transferExp_apply_left α (Fin.succ_ne_zero q).symm]
    exact Nat.zero_le _
  | succ r =>
    by_cases hrq : r = q
    · subst hrq
      rw [Finsupp.transferExp_apply_right α (Fin.succ_ne_zero r).symm, Finsupp.add_apply]
      omega
    · rw [Finsupp.transferExp_apply_of_ne α (Fin.succ_ne_zero r) (Fin.succ_injective _ |>.ne hrq),
        Finsupp.add_apply]
      exact Nat.le_add_right _ _

/-- Under the hypotheses of `Set.apply_succ_lt_of_mem_diagramBox`, if `β 0 = 0`, then
`α.degree + β.degree < D.diagramCutoff`. -/
theorem degree_add_lt_diagramCutoff_of_mem_diagramBox {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram) {α β : Fin (n + 1) →₀ ℕ}
    (hα : α ∈ D.diagramVertices) (hα0 : 1 ≤ α 0) (hβ : β ∈ D.diagramBox α) (hβ0 : β 0 = 0) :
    α.degree + β.degree < D.diagramCutoff := by
  have htail : β.tail.degree ≤ n * (α 0 - 1) := by
    rw [Finsupp.degree_eq_sum]
    calc
      ∑ q : Fin n, β.tail q ≤ ∑ _q : Fin n, (α 0 - 1) := by
        refine Finset.sum_le_sum fun q _ ↦ ?_
        have hlt := apply_succ_lt_of_mem_diagramBox hD_mono hα hα0 hβ q
        rw [Finsupp.tail_apply]
        omega
      _ = n * (α 0 - 1) := by simp
  have hdegβ : β.degree = β.tail.degree := by
    conv_lhs => rw [← Finsupp.cons_tail β, hβ0, Finsupp.degree_cons, zero_add]
  have hcut := add_mul_add_one_le_diagramCutoff hα hα0
  omega

/-- Common degree bound when incrementing coordinate `0` crosses above an exponent `α` while all
transferred exponents `α.transferExp 0 q.succ` fail to bound `γ`. -/
private theorem degree_add_one_le_of_le_single_zero_add {n : ℕ} {α γ : Fin (n + 1) →₀ ℕ}
    (hnot : ¬ α ≤ γ) (hle : α ≤ Finsupp.single 0 1 + γ)
    (htrans : ∀ q : Fin n, ¬ α.transferExp 0 q.succ ≤ γ) :
    1 ≤ α 0 ∧ γ.degree + 1 ≤ α.degree + n * (α 0 - 1) := by
  have h0lt : γ 0 < α 0 := by
    by_contra! h0le
    refine hnot fun i ↦ ?_
    cases i using Fin.cases with
    | zero => exact h0le
    | succ q => simpa using hle q.succ
  have hle0 : α 0 ≤ 1 + γ 0 := by simpa using hle 0
  have hα0 : 1 ≤ α 0 := by omega
  have hsucc (q : Fin n) : γ.tail q ≤ α.tail q + (α 0 - 1) := by
    rw [Finsupp.tail_apply, Finsupp.tail_apply]
    by_contra! hgt
    have hqle : α q.succ + α 0 ≤ γ q.succ := by omega
    refine htrans q fun i ↦ ?_
    cases i using Fin.cases with
    | zero =>
      rw [Finsupp.transferExp_apply_left α (Fin.succ_ne_zero q).symm]
      exact Nat.zero_le _
    | succ r =>
      by_cases hrq : r = q
      · subst hrq
        rwa [Finsupp.transferExp_apply_right α (Fin.succ_ne_zero r).symm]
      · rw [Finsupp.transferExp_apply_of_ne α (Fin.succ_ne_zero r) (Fin.succ_injective _ |>.ne hrq)]
        simpa using hle r.succ
  have hsum : γ.tail.degree ≤ α.tail.degree + n * (α 0 - 1) := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    calc
      ∑ q : Fin n, γ.tail q ≤ ∑ q : Fin n, (α.tail q + (α 0 - 1)) :=
        Finset.sum_le_sum fun q _ ↦ hsucc q
      _ = (∑ q : Fin n, α.tail q) + n * (α 0 - 1) := by
        simp [Finset.sum_add_distrib]
  have hdegγ : γ.degree = γ 0 + γ.tail.degree := by
    conv_lhs => rw [← Finsupp.cons_tail γ, Finsupp.degree_cons]
  have hdegα : α.degree = α 0 + α.tail.degree := by
    conv_lhs => rw [← Finsupp.cons_tail α, Finsupp.degree_cons]
  exact ⟨hα0, by omega⟩

/-- Above `D.diagramCutoff`, the complement of an upward-closed monotone diagram `D` on
`Fin (n + 1)` is stable under adding `Finsupp.single 0 1`. -/
theorem single_zero_add_notMem_of_notMem {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram) {γ : Fin (n + 1) →₀ ℕ}
    (hγ : γ ∉ D) (hdeg : D.diagramCutoff ≤ γ.degree) :
    Finsupp.single 0 1 + γ ∉ D := by
  intro hmem
  obtain ⟨α, hα, hle⟩ := exists_mem_diagramVertices_le hmem
  have hnot : ¬ α ≤ γ := fun hαγ ↦ hγ (hD_up hαγ (D.diagramVertices_subset hα))
  have htrans (q : Fin n) : ¬ α.transferExp 0 q.succ ≤ γ := fun hle' ↦
    hγ (hD_up hle' (hD_mono (D.diagramVertices_subset hα) (Fin.succ_pos q)))
  obtain ⟨hα0, hbound⟩ := degree_add_one_le_of_le_single_zero_add hnot hle htrans
  have hcut := add_mul_add_one_le_diagramCutoff hα hα0
  omega

/-- Above `D.diagramCutoff`, every quotient box `D.diagramBox α` of a monotone diagram `D` on
`Fin (n + 1)` is stable under adding `Finsupp.single 0 1`. -/
theorem single_zero_add_mem_diagramBox {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram) {α β : Fin (n + 1) →₀ ℕ} (hβ : β ∈ D.diagramBox α)
    (hdeg : D.diagramCutoff ≤ α.degree + β.degree) :
    Finsupp.single 0 1 + β ∈ D.diagramBox α := by
  intro α' hα' hlt hle
  have hle' : α' ≤ Finsupp.single 0 1 + (α + β) := by
    rwa [add_left_comm]
  have hnot : ¬ α' ≤ α + β := hβ α' hα' hlt
  have htrans (q : Fin n) : ¬ α'.transferExp 0 q.succ ≤ α + β := by
    intro hle_q
    have hα'0 : 0 < α' 0 := by
      by_contra! h0
      refine hnot fun i ↦ ?_
      cases i using Fin.cases with
      | zero => omega
      | succ r => simpa using hle' r.succ
    have hmem_q : α'.transferExp 0 q.succ ∈ D :=
      hD_mono (D.diagramVertices_subset hα') (Fin.succ_pos q)
    obtain ⟨α'', hα'', hα''le⟩ := exists_mem_diagramVertices_le hmem_q
    have hlt'' : toDegLex α'' < toDegLex α' := by
      refine lt_of_le_of_lt ?_ (Finsupp.toDegLex_transferExp_lt (Fin.succ_pos q) hα'0)
      rcases (Finsupp.degree_mono hα''le).lt_or_eq with hd | hd
      · exact le_of_lt (Finsupp.DegLex.lt_iff.mpr (Or.inl hd))
      · have heq :=
          hα''le.eq_or_lt.resolve_right fun hstrict ↦ (Finsupp.degree_strictMono hstrict).ne hd
        exact heq ▸ le_rfl
    exact hβ α'' hα'' (hlt''.trans hlt) (hα''le.trans hle_q)
  obtain ⟨hα'0, hbound⟩ := degree_add_one_le_of_le_single_zero_add hnot hle' htrans
  rw [map_add] at hbound
  have hcut := add_mul_add_one_le_diagramCutoff hα' hα'0
  omega

end DiagramCutoff

end Set
