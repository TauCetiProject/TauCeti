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
import TauCeti.Data.Finsupp.MonomialOrder.DegLex
import TauCeti.Data.Finsupp.Weight

/-!
# Exponent diagrams, monotone coordinate transfers, and Bierstone–Milman's diagram cutoff

An upward-closed diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered variable set `σ`
decomposes into finitely many minimal vertices `D.diagramVertices : Finset (σ →₀ ℕ)` (by Dickson's
lemma) and pairwise disjoint `DegLex`-ordered cells `D.diagramCell α = α + D.diagramBox α`. These
boxes and cells index the quotient and remainder monomial supports in `DegLex` Hironaka division
and control the propagation of homogeneous supported division across degrees (see
`TauCeti.RingTheory.MvPolynomial.Diagram.Division` and
`TauCeti.RingTheory.MvPolynomial.Diagram.CutoffDet`).

A diagram `D` is *monotone* (`Set.IsMonotoneDiagram D`) if moving the entire exponent at any
coordinate `i` to `j > i` (`Finsupp.transferExp α i j`) maps `D` into `D`. For a monotone diagram
`D` on `Fin (n + 1)` with coordinate-zero slice `D.diagramSliceZero`, Bierstone and Milman (1997,
Definition 8.3 and Theorem 8.1, pp. 274–275) establish three finite-degree stability bounds with
respect to an explicit threshold `D.diagramCutoff`:
* For `D.IsMonotoneDiagram`, `α ∈ D.diagramVertices` with `1 ≤ α 0`, and `β ∈ D.diagramBox α`,
  every remaining coordinate satisfies `β q.succ < α 0` (`Set.apply_succ_lt_of_mem_diagramBox`), so
  `β 0 = 0` forces `α.degree + β.degree < D.diagramCutoff`
  (`Set.degree_add_lt_diagramCutoff_of_mem_diagramBox`).
* Above `D.diagramCutoff`, the complement `Dᶜ` of an upward-closed monotone diagram on `Fin (n + 1)`
  is stable under adding `Finsupp.single 0 1` (`Set.single_zero_add_notMem_of_notMem`).
* Above `D.diagramCutoff`, every box `D.diagramBox α` of a monotone diagram on `Fin (n + 1)` is
  stable under adding `Finsupp.single 0 1` (`Set.single_zero_add_mem_diagramBox`).

## Main definitions

* `Finsupp.transferExp`, `Set.IsMonotoneDiagram`: coordinate exponent transfers and monotone
  diagrams.
* `Set.diagramVertices`, `Set.diagramBox`, `Set.diagramCell`: minimal vertices, `DegLex` quotient
  boxes `□_α`, and translated division cells `Δ_α = α + □_α`.
* `Set.diagramSliceZero`, `Set.diagramCutoff`: coordinate-zero slice on `Fin (n + 1)` and explicit
  recursive degree cutoff `k(D)`.

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
  rw [transferExp_def]
  exact tsub_add_cancel_of_le (single_le_iff.mpr le_rfl)

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
  · exact hij ▸ congrArg (· k) (α.transferExp_self i)
  · subst hki; exact α.transferExp_apply_left hij
  · subst hkj; exact α.transferExp_apply_right hij
  · exact α.transferExp_apply_of_ne hki hkj

@[simp]
theorem transferExp_add (α β : σ →₀ ℕ) (i j : σ) :
    (α + β).transferExp i j = α.transferExp i j + β.transferExp i j := by
  classical
  ext k
  simp only [add_apply, transferExp_apply]
  split_ifs <;> omega

@[simp]
theorem transferExp_single_same (i j : σ) (a : ℕ) :
    (single i a).transferExp i j = single j a := by
  simp [transferExp_def]

theorem transferExp_of_apply_eq_zero {α : σ →₀ ℕ} {i : σ} (h : α i = 0) (j : σ) :
    α.transferExp i j = α := by
  simp [transferExp_def, h]

@[simp]
theorem degree_transferExp (α : σ →₀ ℕ) (i j : σ) : (α.transferExp i j).degree = α.degree := by
  have hcancel : (α - single i (α i)).degree + α i = α.degree := by
    simpa [map_add, degree_single] using
      congrArg degree (tsub_add_cancel_of_le (single_le_iff.mpr (le_rfl : α i ≤ α i)))
  rw [transferExp_def, map_add, degree_single, hcancel]

theorem transferExp_mono {α β : σ →₀ ℕ} (h : α ≤ β) (i j : σ) :
    α.transferExp i j ≤ β.transferExp i j := by
  classical
  intro k; simp only [transferExp_apply]; split_ifs
  exacts [h k, le_rfl, add_le_add (h j) (h i), h k]

/-- Pushing forward along an injective index map commutes with `Finsupp.transferExp`. -/
theorem mapDomain_transferExp {f : σ → τ} (hf : Function.Injective f) (α : σ →₀ ℕ) (i j : σ) :
    (α.transferExp i j).mapDomain f = (α.mapDomain f).transferExp (f i) (f j) := by
  classical
  ext k
  by_cases hk : k ∈ Set.range f
  · obtain ⟨r, rfl⟩ := hk
    simp [hf, transferExp_apply, hf.eq_iff]
  · have hki : k ≠ f i := fun h ↦ hk ⟨i, h.symm⟩
    have hkj : k ≠ f j := fun h ↦ hk ⟨j, h.symm⟩
    rw [mapDomain_of_notMem_range _ _ hk, transferExp_apply_of_ne _ hki hkj,
      mapDomain_of_notMem_range _ _ hk]

theorem equivMapDomain_transferExp (e : σ ≃ τ) (α : σ →₀ ℕ) (i j : σ) :
    equivMapDomain e (α.transferExp i j) = (equivMapDomain e α).transferExp (e i) (e j) := by
  simp only [equivMapDomain_eq_mapDomain, mapDomain_transferExp e.injective]

theorem transferExp_cons_zero_succ {n : ℕ} (α' : Fin n →₀ ℕ) (i j : Fin n) :
    (cons 0 α').transferExp i.succ j.succ = cons 0 (α'.transferExp i j) := by
  rw [← mapDomain_finSucc, ← mapDomain_finSucc, mapDomain_transferExp (Fin.succ_injective n)]

/-- Moving a positive exponent from `i` to a strictly larger coordinate `j` strictly decreases
`DegLex`. -/
theorem toDegLex_transferExp_lt [LinearOrder σ] {α : σ →₀ ℕ} {i j : σ} (hij : i < j)
    (hα : 0 < α i) :
    toDegLex (α.transferExp i j) < toDegLex α := by
  rw [DegLex.lt_iff, ofDegLex_toDegLex, ofDegLex_toDegLex, degree_transferExp]
  refine Or.inr ⟨rfl, Lex.lt_iff.mpr ⟨i, fun k hk ↦ ?_, ?_⟩⟩
  · exact α.transferExp_apply_of_ne hk.ne (hk.trans hij).ne
  · rwa [ofLex_toLex, ofLex_toLex, α.transferExp_apply_left hij.ne]

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

theorem IsMonotoneDiagram.transferExp_mem [LT σ] {D : Set (σ →₀ ℕ)} (hD : D.IsMonotoneDiagram)
    {α : σ →₀ ℕ} (hα : α ∈ D) {i j : σ} (hij : i < j) :
    α.transferExp i j ∈ D :=
  hD hα hij

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

@[simp]
theorem isMonotoneDiagram_of_subsingleton [Preorder σ] [Subsingleton σ] (D : Set (σ →₀ ℕ)) :
    D.IsMonotoneDiagram :=
  fun _ _ i j hij ↦ absurd (Subsingleton.elim i j) hij.ne

theorem isMonotoneDiagram_degree_ge [LT σ] (d : ℕ) :
    {α : σ →₀ ℕ | d ≤ α.degree}.IsMonotoneDiagram :=
  fun _ hα _ _ _ ↦ by simpa using hα

theorem IsMonotoneDiagram.upperClosure [LT σ] {S : Set (σ →₀ ℕ)} (hS : S.IsMonotoneDiagram) :
    (↑(_root_.upperClosure S) : Set (σ →₀ ℕ)).IsMonotoneDiagram := by
  intro α hα i j hij
  rw [coe_upperClosure, mem_iUnion₂] at hα ⊢
  obtain ⟨β, hβS, hle⟩ := hα
  exact ⟨β.transferExp i j, hS hβS hij, Finsupp.transferExp_mono hle i j⟩

/-- Pulling back a monotone diagram along `Finsupp.mapDomain f` for a strictly monotone injective
index map `f` yields a monotone diagram. -/
theorem IsMonotoneDiagram.preimage_mapDomain {τ : Type*} [Preorder σ] [Preorder τ]
    {f : σ → τ} (hf : StrictMono f) (hinj : Function.Injective f) {D : Set (τ →₀ ℕ)}
    (hD : D.IsMonotoneDiagram) : (Finsupp.mapDomain f ⁻¹' D).IsMonotoneDiagram := by
  intro α hα i j hij
  rw [mem_preimage, Finsupp.mapDomain_transferExp hinj]
  exact hD hα (hf hij)

theorem isMonotoneDiagram_preimage_equivMapDomain {τ : Type*} [Preorder σ] [Preorder τ]
    (e : σ ≃o τ) {D : Set (τ →₀ ℕ)} :
    (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).IsMonotoneDiagram ↔ D.IsMonotoneDiagram := by
  have hpre : Finsupp.equivMapDomain e.toEquiv ⁻¹' D = Finsupp.mapDomain e.toEquiv ⁻¹' D := by
    ext; simp [Finsupp.equivMapDomain_eq_mapDomain]
  refine ⟨fun h α hα i j hij ↦ ?_,
    fun h ↦ hpre ▸ h.preimage_mapDomain (f := e.toEquiv) e.strictMono e.injective⟩
  obtain ⟨α₀, rfl⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective α
  obtain ⟨i₀, rfl⟩ := e.surjective i
  obtain ⟨j₀, rfl⟩ := e.surjective j
  simpa [Finsupp.equivMapDomain_transferExp] using h hα (e.lt_iff_lt.mp hij)

end MonotoneDiagram

section DiagramVertices

variable {σ : Type*}

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
    ∃ α ∈ D.diagramVertices, α ≤ γ :=
  let ⟨α, hle, hmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D) γ hγ
  ⟨α, mem_diagramVertices_iff.mpr hmin, hle⟩

theorem mem_iff_exists_mem_diagramVertices_le [Finite σ] {D : Set (σ →₀ ℕ)} (hD : IsUpperSet D)
    {γ : σ →₀ ℕ} :
    γ ∈ D ↔ ∃ α ∈ D.diagramVertices, α ≤ γ :=
  ⟨exists_mem_diagramVertices_le, fun ⟨_, hα, hle⟩ ↦ hD hle (D.diagramVertices_subset hα)⟩

/-- An upward-closed diagram `D : Set (σ →₀ ℕ)` in finitely many variables is the finite union of
the cones `Set.Ici α` over its minimal vertices `α ∈ D.diagramVertices`. -/
theorem _root_.IsUpperSet.biUnion_Ici_diagramVertices [Finite σ] {D : Set (σ →₀ ℕ)}
    (hD : IsUpperSet D) :
    ⋃ α ∈ D.diagramVertices, Set.Ici α = D := by
  ext γ
  simp only [mem_iUnion, mem_Ici, exists_prop, mem_iff_exists_mem_diagramVertices_le hD]

@[simp]
theorem diagramVertices_empty [Finite σ] : (∅ : Set (σ →₀ ℕ)).diagramVertices = ∅ := by
  ext; simp [Minimal]

@[simp]
theorem diagramVertices_eq_empty_iff [Finite σ] {D : Set (σ →₀ ℕ)} :
    D.diagramVertices = ∅ ↔ D = ∅ := by
  refine ⟨fun h ↦ eq_empty_iff_forall_notMem.mpr fun γ hγ ↦ ?_, fun h ↦ by simp [h]⟩
  obtain ⟨α, hα, _⟩ := exists_mem_diagramVertices_le hγ
  exact Finset.notMem_empty α (h ▸ hα)

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
  exact ⟨fun ⟨h₁, h₂⟩ ↦ le_antisymm (h₂ le_rfl h₁) h₁, fun h ↦ h ▸ ⟨le_rfl, fun _ hle _ ↦ hle⟩⟩

theorem diagramVertices_upperClosure_finset [Finite σ] {s : Finset (σ →₀ ℕ)}
    (hs : IsAntichain (· ≤ ·) (s : Set (σ →₀ ℕ))) :
    (↑(upperClosure (s : Set (σ →₀ ℕ))) : Set (σ →₀ ℕ)).diagramVertices = s := by
  ext; simp only [mem_diagramVertices_iff, SetLike.mem_coe, hs.minimal_mem_upperClosure_iff_mem]

/-- Minimal vertices of the pullback `Finsupp.mapDomain f ⁻¹' D` along an injective index map `f`
are precisely those `α` whose pushforward `α.mapDomain f` is a minimal vertex of `D`. -/
theorem mem_diagramVertices_preimage_mapDomain_iff {τ : Type*} [Finite σ] [Finite τ]
    {f : σ → τ} (hf : Function.Injective f) {D : Set (τ →₀ ℕ)} {α : σ →₀ ℕ} :
    α ∈ (Finsupp.mapDomain f ⁻¹' D).diagramVertices ↔ α.mapDomain f ∈ D.diagramVertices := by
  simp only [mem_diagramVertices_iff, Minimal, mem_preimage,
    ← Finsupp.mapDomain_le_mapDomain_iff_le hf]
  refine and_congr Iff.rfl ⟨fun h γ hγ hle ↦ ?_, fun h _ hβ hle ↦ h hβ hle⟩
  have hmem : γ ∈ Set.range (Finsupp.mapDomain f) :=
    (Finsupp.mem_range_mapDomain_iff' f γ).mpr fun b hb ↦
      Nat.eq_zero_of_le_zero ((hle b).trans_eq (Finsupp.mapDomain_of_notMem_range α b hb))
  obtain ⟨β, rfl⟩ := hmem
  exact h hγ hle

theorem mem_diagramVertices_preimage_equivMapDomain_iff {τ : Type*} [Finite σ] [Finite τ]
    (e : σ ≃ τ) {D : Set (τ →₀ ℕ)} {α : σ →₀ ℕ} :
    α ∈ (Finsupp.equivMapDomain e ⁻¹' D).diagramVertices ↔
      Finsupp.equivMapDomain e α ∈ D.diagramVertices := by
  have hpre : Finsupp.equivMapDomain e ⁻¹' D = Finsupp.mapDomain e ⁻¹' D := by
    ext; simp [Finsupp.equivMapDomain_eq_mapDomain]
  rw [hpre, Finsupp.equivMapDomain_eq_mapDomain]
  exact mem_diagramVertices_preimage_mapDomain_iff e.injective

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

theorem isLowerSet_diagramBox (D : Set (σ →₀ ℕ)) (α : σ →₀ ℕ) :
    IsLowerSet (D.diagramBox α) :=
  fun _ _ hle hβ α' hα' hlt hα'le ↦ hβ α' hα' hlt (hα'le.trans (add_le_add_right hle α))

theorem le_of_mem_diagramCell {D : Set (σ →₀ ℕ)} {α γ : σ →₀ ℕ} (h : γ ∈ D.diagramCell α) :
    α ≤ γ :=
  h.1

@[simp]
theorem add_mem_diagramCell_iff {D : Set (σ →₀ ℕ)} {α β : σ →₀ ℕ} :
    α + β ∈ D.diagramCell α ↔ β ∈ D.diagramBox α :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨le_self_add, h⟩⟩

theorem tsub_mem_diagramBox_of_mem_diagramCell {D : Set (σ →₀ ℕ)} {α γ : σ →₀ ℕ}
    (h : γ ∈ D.diagramCell α) : γ - α ∈ D.diagramBox α := by
  rwa [← add_mem_diagramCell_iff, add_tsub_cancel_of_le h.1]

theorem image_add_diagramBox_eq_diagramCell (D : Set (σ →₀ ℕ)) (α : σ →₀ ℕ) :
    (α + ·) '' D.diagramBox α = D.diagramCell α := by
  ext γ
  refine ⟨?_, fun hγ ↦ ⟨γ - α, tsub_mem_diagramBox_of_mem_diagramCell hγ,
    add_tsub_cancel_of_le hγ.1⟩⟩
  rintro ⟨β, hβ, rfl⟩
  exact add_mem_diagramCell_iff.mpr hβ

@[simp]
theorem zero_mem_diagramBox {D : Set (σ →₀ ℕ)} {α : σ →₀ ℕ} (hα : α ∈ D.diagramVertices) :
    0 ∈ D.diagramBox α := fun α' hα' hlt hle ↦
  D.isAntichain_diagramVertices hα' hα (fun h ↦ hlt.ne (congrArg toDegLex h)) (by simpa using hle)

@[simp]
theorem self_mem_diagramCell {D : Set (σ →₀ ℕ)} {α : σ →₀ ℕ} (hα : α ∈ D.diagramVertices) :
    α ∈ D.diagramCell α := by
  simpa using add_mem_diagramCell_iff.mpr (zero_mem_diagramBox hα)

/-- Since `0` is the `DegLex`-least exponent, its quotient box `D.diagramBox 0` is all of `Set.univ`
for any diagram `D`. -/
@[simp]
theorem diagramBox_zero (D : Set (σ →₀ ℕ)) : D.diagramBox 0 = Set.univ := by
  ext β
  simp only [mem_diagramBox_iff, mem_univ, iff_true]
  intro α' _ hlt
  rw [Finsupp.DegLex.lt_iff, ofDegLex_toDegLex, ofDegLex_toDegLex, map_zero] at hlt
  rcases hlt with hdeg | ⟨hdeg, hlex⟩
  · exact absurd hdeg (Nat.not_lt_zero _)
  · rw [Finsupp.degree_eq_zero_iff] at hdeg
    subst hdeg
    exact absurd hlex (lt_irrefl _)

@[simp]
theorem diagramBox_Ici (α : σ →₀ ℕ) : (Set.Ici α).diagramBox α = Set.univ := by
  ext β
  simp [mem_diagramBox_iff]

/-- For an upward-closed diagram `D` and vertex `α ∈ D.diagramVertices`, the division cell
`D.diagramCell α` is contained in `D`. -/
theorem diagramCell_subset {D : Set (σ →₀ ℕ)} (hD : IsUpperSet D) {α : σ →₀ ℕ}
    (hα : α ∈ D.diagramVertices) : D.diagramCell α ⊆ D :=
  fun _ hγ ↦ hD hγ.1 (D.diagramVertices_subset hα)

/-- An exponent outside an upward-closed diagram `D` lies in no vertex division cell. -/
theorem notMem_diagramCell_of_notMem {D : Set (σ →₀ ℕ)} (hD : IsUpperSet D) {α : σ →₀ ℕ}
    (hα : α ∈ D.diagramVertices) {γ : σ →₀ ℕ} (hγ : γ ∉ D) : γ ∉ D.diagramCell α :=
  fun h ↦ hγ (diagramCell_subset hD hα h)

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

/-- If `γ` belongs to the division cells of two vertices `α₁, α₂ ∈ D.diagramVertices`, then
`α₁ = α₂`. -/
theorem eq_of_mem_diagramCell {D : Set (σ →₀ ℕ)} {α₁ α₂ γ : σ →₀ ℕ}
    (h₁ : α₁ ∈ D.diagramVertices) (h₂ : α₂ ∈ D.diagramVertices)
    (hc₁ : γ ∈ D.diagramCell α₁) (hc₂ : γ ∈ D.diagramCell α₂) : α₁ = α₂ := by
  by_contra hne
  exact (disjoint_diagramCell h₁ h₂ hne).le_bot ⟨hc₁, hc₂⟩

/-- For an upward-closed diagram `D`, its vertex division cells cover `D`. -/
theorem biUnion_diagramCell_eq {D : Set (σ →₀ ℕ)} (hD : IsUpperSet D) :
    ⋃ α ∈ D.diagramVertices, D.diagramCell α = D := by
  classical
  ext γ
  simp only [mem_iUnion, exists_prop]
  refine ⟨fun ⟨_, hα, hc⟩ ↦ diagramCell_subset hD hα hc, fun hγ ↦ ?_⟩
  let s : Finset (DegLex (σ →₀ ℕ)) := (D.diagramVertices.filter (· ≤ γ)).image toDegLex
  have hs : s.Nonempty := by
    obtain ⟨α, hα, hle⟩ := exists_mem_diagramVertices_le hγ
    exact ⟨toDegLex α, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hα, hle⟩)⟩
  obtain ⟨α, hαf, hmin_eq⟩ := Finset.mem_image.mp (s.min'_mem hs)
  obtain ⟨hα, hle⟩ := Finset.mem_filter.mp hαf
  exact ⟨α, hα, hle, fun α' hα' hlt hle' ↦ hlt.not_ge
    (hmin_eq ▸ s.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hα', hle'⟩)))⟩

/-- Every element of an upward-closed diagram `D` belongs to the division cell of a unique vertex
of `D`. -/
theorem existsUnique_mem_diagramCell_of_mem {D : Set (σ →₀ ℕ)} (hD : IsUpperSet D) {γ : σ →₀ ℕ}
    (hγ : γ ∈ D) :
    ∃! v : D.diagramVertices, γ ∈ D.diagramCell v.1 := by
  have hmem : γ ∈ ⋃ α ∈ D.diagramVertices, D.diagramCell α := by rwa [biUnion_diagramCell_eq hD]
  obtain ⟨α, hα, hc⟩ := mem_iUnion₂.mp hmem
  exact ⟨⟨α, hα⟩, hc, fun v hv ↦ Subtype.ext (eq_of_mem_diagramCell v.2 hα hv hc)⟩

/-- Quotient boxes pull back compatibly along `Finsupp.mapDomain f` for any strictly monotone index
map `f`. -/
theorem mem_diagramBox_preimage_mapDomain_iff {τ : Type*} [Finite τ] [LinearOrder τ]
    {f : σ → τ} (hf : StrictMono f) {D : Set (τ →₀ ℕ)} {α β : σ →₀ ℕ} :
    β ∈ (Finsupp.mapDomain f ⁻¹' D).diagramBox α ↔
      β.mapDomain f ∈ D.diagramBox (α.mapDomain f) := by
  simp only [mem_diagramBox_iff, ← Finsupp.mapDomain_add]
  refine ⟨fun h γ hγ hlt hle ↦ ?_, fun h α' hα' hlt hle ↦ ?_⟩
  · have hmem : γ ∈ Set.range (Finsupp.mapDomain f) :=
      (Finsupp.mem_range_mapDomain_iff' f γ).mpr fun b hb ↦
        Nat.eq_zero_of_le_zero ((hle b).trans_eq (Finsupp.mapDomain_of_notMem_range (α + β) b hb))
    obtain ⟨α', rfl⟩ := hmem
    exact h α' ((mem_diagramVertices_preimage_mapDomain_iff hf.injective).mpr hγ)
      ((Finsupp.toDegLex_mapDomain_lt_iff hf).mp hlt)
      ((Finsupp.mapDomain_le_mapDomain_iff_le hf.injective _ _).mp hle)
  · exact h (α'.mapDomain f)
      ((mem_diagramVertices_preimage_mapDomain_iff hf.injective).mp hα')
      ((Finsupp.toDegLex_mapDomain_lt_iff hf).mpr hlt)
      ((Finsupp.mapDomain_le_mapDomain_iff_le hf.injective _ _).mpr hle)

theorem mem_diagramBox_preimage_equivMapDomain_iff {τ : Type*} [Finite τ] [LinearOrder τ]
    (e : σ ≃o τ) {D : Set (τ →₀ ℕ)} {α β : σ →₀ ℕ} :
    β ∈ (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramBox α ↔
      Finsupp.equivMapDomain e.toEquiv β ∈ D.diagramBox (Finsupp.equivMapDomain e.toEquiv α) := by
  have hpre : Finsupp.equivMapDomain e.toEquiv ⁻¹' D = Finsupp.mapDomain e.toEquiv ⁻¹' D := by
    ext; simp [Finsupp.equivMapDomain_eq_mapDomain]
  rw [hpre, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain]
  exact mem_diagramBox_preimage_mapDomain_iff (f := e.toEquiv) e.strictMono

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

private theorem diagramSliceZero_eq_preimage_mapDomain (D : Set (Fin (n + 1) →₀ ℕ)) :
    D.diagramSliceZero = Finsupp.mapDomain Fin.succ ⁻¹' D := by
  ext; simp [diagramSliceZero, Finsupp.mapDomain_finSucc]

@[simp]
theorem diagramSliceZero_empty : (∅ : Set (Fin (n + 1) →₀ ℕ)).diagramSliceZero = ∅ := by
  ext; simp

@[simp]
theorem diagramSliceZero_univ :
    (Set.univ : Set (Fin (n + 1) →₀ ℕ)).diagramSliceZero = Set.univ := by
  ext; simp

theorem _root_.IsUpperSet.diagramSliceZero {D : Set (Fin (n + 1) →₀ ℕ)} (hD : IsUpperSet D) :
    IsUpperSet D.diagramSliceZero :=
  fun _ _ hle hα ↦ hD (Finsupp.cons_le_cons_iff.mpr ⟨le_rfl, hle⟩) hα

theorem IsMonotoneDiagram.diagramSliceZero {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD : D.IsMonotoneDiagram) : D.diagramSliceZero.IsMonotoneDiagram := by
  rw [diagramSliceZero_eq_preimage_mapDomain]
  exact hD.preimage_mapDomain Fin.strictMono_succ (Fin.succ_injective n)

theorem mem_diagramVertices_diagramSliceZero_iff {D : Set (Fin (n + 1) →₀ ℕ)}
    {α' : Fin n →₀ ℕ} :
    α' ∈ D.diagramSliceZero.diagramVertices ↔ Finsupp.cons 0 α' ∈ D.diagramVertices := by
  rw [diagramSliceZero_eq_preimage_mapDomain, ← Finsupp.mapDomain_finSucc]
  exact mem_diagramVertices_preimage_mapDomain_iff (Fin.succ_injective n)

@[simp]
theorem cons_zero_mem_diagramBox_iff {D : Set (Fin (n + 1) →₀ ℕ)} {α' β' : Fin n →₀ ℕ} :
    Finsupp.cons 0 β' ∈ D.diagramBox (Finsupp.cons 0 α') ↔
      β' ∈ D.diagramSliceZero.diagramBox α' := by
  rw [diagramSliceZero_eq_preimage_mapDomain, ← Finsupp.mapDomain_finSucc,
    ← Finsupp.mapDomain_finSucc]
  exact (mem_diagramBox_preimage_mapDomain_iff Fin.strictMono_succ).symm

end SliceZero

section DiagramCutoff

open scoped Classical in
private noncomputable def diagramCutoffFin : ∀ {n : ℕ}, Set (Fin n →₀ ℕ) → ℕ
  | 0, _ => 0
  | n + 1, D =>
    max (diagramCutoffFin D.diagramSliceZero)
      ((D.diagramVertices.filter (fun α ↦ 1 ≤ α 0)).sup (fun α ↦ α.degree + n * (α 0 - 1) + 1))

private noncomputable def diagramCutoffAux {σ : Type*} (ft : Fintype σ) [LinearOrder σ]
    (D : Set (σ →₀ ℕ)) : ℕ :=
  diagramCutoffFin
    (Finsupp.equivMapDomain (@Fintype.orderIsoFinOfCardEq σ _ ft _ rfl).toEquiv ⁻¹' D)

/-- Explicit finite degree cutoff `k(D)` of a diagram `D : Set (σ →₀ ℕ)` on a finite linearly
ordered variable set `σ`, supplying a concrete threshold for Bierstone–Milman's finite-degree
criterion (Bierstone–Milman 1997, Theorem 8.1, p. 274).

Transporting `D` along the unique order isomorphism
`Fintype.orderIsoFinOfCardEq : Fin (card σ) ≃o σ`, it is defined recursively on `Fin n` by `0` when
`n = 0`, and on `Fin (n + 1)` as the maximum of `D.diagramSliceZero.diagramCutoff` and the supremum
of `α.degree + n * (α 0 - 1) + 1` over all vertices `α ∈ D.diagramVertices` with `1 ≤ α 0` (see
`Set.diagramCutoff_preimage_equivMapDomain`, `Set.diagramCutoff_of_isEmpty`, and
`Set.diagramCutoff_fin_succ`). -/
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
    exact (OrderIso.symm_apply_eq e).mp (Fin.ext (Fin.coe_orderIso_apply f i))
  rw [heq]

/-- `Set.diagramCutoff` is invariant under pulling a diagram back along an order isomorphism of
variable sets. -/
theorem diagramCutoff_preimage_equivMapDomain {σ τ : Type*} [Finite σ] [LinearOrder σ]
    [Finite τ] [LinearOrder τ] (e : σ ≃o τ) (D : Set (τ →₀ ℕ)) :
    (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramCutoff = D.diagramCutoff := by
  cases nonempty_fintype σ
  let eσ : Fin (Fintype.card σ) ≃o σ := Fintype.orderIsoFinOfCardEq σ rfl
  rw [diagramCutoff_eq_of_orderIsoFin eσ, diagramCutoff_eq_of_orderIsoFin (eσ.trans e)]
  congr 1; ext; simp [← Finsupp.equivMapDomain_trans]

private theorem diagramCutoff_fin_eq {n : ℕ} (D : Set (Fin n →₀ ℕ)) :
    D.diagramCutoff = diagramCutoffFin D := by
  rw [diagramCutoff_eq_of_orderIsoFin (OrderIso.refl (Fin n)) D]
  congr 1; ext; simp

/-- Any diagram on an empty variable set has `Set.diagramCutoff` equal to `0`. -/
@[simp]
theorem diagramCutoff_of_isEmpty {σ : Type*} [IsEmpty σ] [LinearOrder σ] (D : Set (σ →₀ ℕ)) :
    D.diagramCutoff = 0 := by
  let e : Fin 0 ≃o σ :=
    { toEquiv := Equiv.equivOfIsEmpty (Fin 0) σ, map_rel_iff' := fun {i} ↦ Fin.elim0 i }
  rw [diagramCutoff_eq_of_orderIsoFin e D, diagramCutoffFin]

open scoped Classical in
/-- Recursive unfolding of `Set.diagramCutoff` on `Fin (n + 1)`: the maximum of the cutoff of the
coordinate-zero slice `D.diagramSliceZero` and the supremum of `α.degree + n * (α 0 - 1) + 1` over
all vertices `α ∈ D.diagramVertices` with `1 ≤ α 0`. -/
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
  rw [← diagramCutoff_preimage_equivMapDomain (Fintype.orderIsoFinOfCardEq σ rfl) ∅, preimage_empty]
  induction Fintype.card σ with
  | zero => exact diagramCutoff_of_isEmpty ∅
  | succ _ ih => simp [diagramCutoff_fin_succ, ih]

@[simp]
theorem diagramCutoff_univ {σ : Type*} [Finite σ] [LinearOrder σ] :
    (Set.univ : Set (σ →₀ ℕ)).diagramCutoff = 0 := by
  cases nonempty_fintype σ
  rw [← diagramCutoff_preimage_equivMapDomain (Fintype.orderIsoFinOfCardEq σ rfl) Set.univ,
    preimage_univ]
  induction Fintype.card σ with
  | zero => exact diagramCutoff_of_isEmpty Set.univ
  | succ _ ih => simp [diagramCutoff_fin_succ, ih]

theorem diagramCutoff_diagramSliceZero_le {n : ℕ} (D : Set (Fin (n + 1) →₀ ℕ)) :
    D.diagramSliceZero.diagramCutoff ≤ D.diagramCutoff := by
  rw [diagramCutoff_fin_succ]; exact le_max_left _ _

theorem add_mul_add_one_le_diagramCutoff {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    {α : Fin (n + 1) →₀ ℕ} (hα : α ∈ D.diagramVertices) (hα0 : 1 ≤ α 0) :
    α.degree + n * (α 0 - 1) + 1 ≤ D.diagramCutoff := by
  classical
  rw [diagramCutoff_fin_succ]
  exact (Finset.le_sup (f := fun α : Fin (n + 1) →₀ ℕ ↦ α.degree + n * (α 0 - 1) + 1)
    (Finset.mem_filter.mpr ⟨hα, hα0⟩)).trans (le_max_right _ _)

private theorem toDegLex_lt_of_le_transferExp {σ : Type*} [LinearOrder σ] {α' α : σ →₀ ℕ}
    {i j : σ} (hij : i < j) (hα : 0 < α i) (hle : α' ≤ α.transferExp i j) :
    toDegLex α' < toDegLex α := by
  refine lt_of_le_of_lt ?_ (Finsupp.toDegLex_transferExp_lt hij hα)
  rcases (Finsupp.degree_mono hle).lt_or_eq with hd | hd
  · exact (Finsupp.DegLex.lt_iff.mpr (Or.inl hd)).le
  · exact (hle.eq_or_lt.resolve_right fun hs ↦ (Finsupp.degree_strictMono hs).ne hd) ▸ le_rfl

/-- For a monotone diagram `D` on `Fin (n + 1)`, if `α ∈ D.diagramVertices` has `1 ≤ α 0` and
`β ∈ D.diagramBox α`, then every remaining coordinate of `β` satisfies `β q.succ < α 0`. -/
theorem apply_succ_lt_of_mem_diagramBox {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram) {α β : Fin (n + 1) →₀ ℕ}
    (hα : α ∈ D.diagramVertices) (hα0 : 1 ≤ α 0) (hβ : β ∈ D.diagramBox α) (q : Fin n) :
    β q.succ < α 0 := by
  obtain ⟨α', hα', hα'δ⟩ := exists_mem_diagramVertices_le
    (hD_mono (D.diagramVertices_subset hα) (Fin.succ_pos q))
  have hlt := toDegLex_lt_of_le_transferExp (Fin.succ_pos q) hα0 hα'δ
  by_contra! hge
  refine hβ α' hα' hlt (hα'δ.trans fun i ↦ ?_)
  cases i using Fin.cases with
  | zero => simp [Finsupp.transferExp_apply_left α (Fin.succ_ne_zero q).symm]
  | succ r =>
    by_cases hrq : r = q
    · subst hrq
      rw [Finsupp.transferExp_apply_right α (Fin.succ_ne_zero r).symm, Finsupp.add_apply]; omega
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
      ∑ q : Fin n, β.tail q ≤ ∑ _q : Fin n, (α 0 - 1) := Finset.sum_le_sum fun q _ ↦ by
        have hlt := apply_succ_lt_of_mem_diagramBox hD_mono hα hα0 hβ q
        rw [Finsupp.tail_apply]; omega
      _ = n * (α 0 - 1) := by simp
  have hdegβ : β.degree = β.tail.degree := by
    conv_lhs => rw [← Finsupp.cons_tail β, hβ0, Finsupp.degree_cons, zero_add]
  have hcut := add_mul_add_one_le_diagramCutoff hα hα0
  omega

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
    refine htrans q fun i ↦ ?_
    cases i using Fin.cases with
    | zero => simp [Finsupp.transferExp_apply_left α (Fin.succ_ne_zero q).symm]
    | succ r =>
      by_cases hrq : r = q
      · subst hrq; rw [Finsupp.transferExp_apply_right α (Fin.succ_ne_zero r).symm]; omega
      · rw [Finsupp.transferExp_apply_of_ne α (Fin.succ_ne_zero r) (Fin.succ_injective _ |>.ne hrq)]
        simpa using hle r.succ
  have hsum : γ.tail.degree ≤ α.tail.degree + n * (α 0 - 1) := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    calc
      ∑ q : Fin n, γ.tail q ≤ ∑ q : Fin n, (α.tail q + (α 0 - 1)) :=
        Finset.sum_le_sum fun q _ ↦ hsucc q
      _ = (∑ q : Fin n, α.tail q) + n * (α 0 - 1) := by simp [Finset.sum_add_distrib]
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
  have hle' : α' ≤ Finsupp.single 0 1 + (α + β) := by rwa [add_left_comm]
  have hnot : ¬ α' ≤ α + β := hβ α' hα' hlt
  have htrans (q : Fin n) : ¬ α'.transferExp 0 q.succ ≤ α + β := by
    intro hle_q
    have hα'0 : 0 < α' 0 := by
      by_contra! h0
      refine hnot fun i ↦ ?_
      cases i using Fin.cases with
      | zero => omega
      | succ r => simpa using hle' r.succ
    obtain ⟨α'', hα'', hα''le⟩ := exists_mem_diagramVertices_le
      (hD_mono (D.diagramVertices_subset hα') (Fin.succ_pos q))
    exact hβ α'' hα'' ((toDegLex_lt_of_le_transferExp (Fin.succ_pos q) hα'0 hα''le).trans hlt)
      (hα''le.trans hle_q)
  obtain ⟨hα'0, hbound⟩ := degree_add_one_le_of_le_single_zero_add hnot hle' htrans
  rw [map_add] at hbound
  have hcut := add_mul_add_one_le_diagramCutoff hα' hα'0
  omega

end DiagramCutoff

end Set
