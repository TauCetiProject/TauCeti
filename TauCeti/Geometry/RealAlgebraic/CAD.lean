/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Basic

/-!
# Cylindrical algebraic decompositions

A *cylindrical algebraic decomposition* (CAD) of `ℝ ^ n` is a finite partition of `ℝ ^ n` into
semialgebraic cells, built one dimension at a time. The only CAD of `ℝ ^ 0` is the partition into
the single point. A CAD of `ℝ ^ (n + 1)` is obtained from a CAD of `ℝ ^ n` by choosing, over each
of its cells `C`, finitely many continuous functions `θ₀ < θ₁ < … < θₖ₋₁ : C → ℝ` whose sections
and sectors are semialgebraic, and taking all the sections and sectors of all these stacks. The
distinguished new coordinate is coordinate `0`, as for `TauCeti.cylinder`.

`TauCeti.IsCAD n 𝒞` is this recursive definition, for a set `𝒞` of subsets of `Fin n → ℝ`. The
cells are not assumed to be connected, nor the decomposition to be a partition: these are
theorems. Every cell of a CAD is a nonempty, connected, semialgebraic set, there are finitely many
cells, and they partition `ℝ ^ n`. The projections of the cells of a CAD of `ℝ ^ (n + 1)` form a
CAD of `ℝ ^ n`, and the decomposition is cylindrical: two cells have equal or disjoint
projections, so each cell lies over the whole of the lower cell it meets.

Stacks of polynomial functions are semialgebraic. In particular finitely many points of `ℝ`,
together with the open intervals they cut out, form a CAD of `ℝ ^ 1`.

## Main declarations

* `TauCeti.IsSemialgebraicStack`: a continuous, strictly ordered stack with semialgebraic cells.
* `TauCeti.IsCAD`: cylindrical algebraic decompositions, defined recursively.
* `TauCeti.IsCAD.isPartition`, `TauCeti.IsCAD.finite`, `TauCeti.IsCAD.isSemialgebraic`,
  `TauCeti.IsCAD.isConnected`: a CAD is a finite partition into connected semialgebraic cells.
* `TauCeti.IsCAD.image_tail`, `TauCeti.IsCAD.image_tail_eq_or_disjoint`: projecting a CAD gives
  a CAD, and projections of cells are equal or disjoint.
* `TauCeti.isSemialgebraicStack_eval`, `TauCeti.isCAD_stackCells_const`: polynomial stacks, and
  the CAD of `ℝ ^ 1` cut out by finitely many points.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 (cylindrical algebraic decomposition).
-/

public section

open Function Set Topology MvPolynomial

namespace TauCeti

variable {n k : ℕ}

/-! ### Semialgebraic stacks -/

section Real

variable {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}

/-- A *semialgebraic stack* over `C ⊆ ℝ ^ n`: finitely many continuous functions
`θ₀ < θ₁ < … < θₖ₋₁` on `C` whose sections and sectors, placed in `ℝ ^ (n + 1)` by
`TauCeti.cylinder`, are semialgebraic. These are the stacks from which a cylindrical algebraic
decomposition is built. -/
structure IsSemialgebraicStack (C : Set (Fin n → ℝ)) (θ : Fin k → C → ℝ) : Prop where
  /-- Each function of the stack is continuous. -/
  continuous : ∀ i, Continuous (θ i)
  /-- The functions of the stack are strictly ordered at each point. -/
  strictMono : ∀ x, StrictMono fun i ↦ θ i x
  /-- Each section of the stack is semialgebraic. -/
  isSemialgebraic_sectionSet : ∀ i, IsSemialgebraic (cylinder C '' sectionSet θ i)
  /-- Each sector of the stack is semialgebraic. -/
  isSemialgebraic_sectorSet : ∀ j, IsSemialgebraic (cylinder C '' sectorSet θ j)

/-- Every cell of a semialgebraic stack is semialgebraic. -/
theorem IsSemialgebraicStack.isSemialgebraic (hθ : IsSemialgebraicStack C θ)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells C θ) : IsSemialgebraic E := by
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  exacts [hθ.isSemialgebraic_sectionSet i, hθ.isSemialgebraic_sectorSet j]

/-- A stack of polynomial functions on a semialgebraic set, strictly ordered at each point, is a
semialgebraic stack. -/
theorem isSemialgebraicStack_eval (hC : IsSemialgebraic C) (p : Fin k → MvPolynomial (Fin n) ℝ)
    (hp : ∀ x ∈ C, StrictMono fun i ↦ eval x (p i)) :
    IsSemialgebraicStack C fun i x ↦ eval x.1 (p i) := by
  -- In ambient coordinates, the value of the `i`-th function is a polynomial in the last `n`
  -- coordinates.
  have hq (i : Fin k) (y : Fin (n + 1) → ℝ) :
      eval y (rename Fin.succ (p i)) = eval (Fin.tail y) (p i) := by
    simp only [eval_rename, Fin.tail_def, comp_def]
  refine ⟨fun i ↦ (continuous_eval (p i)).comp continuous_subtype_val,
    fun x ↦ hp x.1 x.2, fun i ↦ ?_, fun j ↦ ?_⟩
  · convert hC.preimage_tail.inter (isSemialgebraic_eval_eq (rename Fin.succ (p i)) (X 0))
      using 1
    ext y
    rw [mem_image_cylinder]
    simp [hq, eq_comm]
  · have hs (i : Fin k) : IsSemialgebraic {y : Fin (n + 1) → ℝ |
        (i.castSucc < j → eval (Fin.tail y) (p i) < y 0) ∧
          (j ≤ i.castSucc → y 0 < eval (Fin.tail y) (p i))} := by
      rcases lt_or_ge i.castSucc j with h | h
      · simpa [h, h.not_ge, hq] using isSemialgebraic_eval_lt (rename Fin.succ (p i)) (X 0)
      · simpa [h, h.not_gt, hq] using isSemialgebraic_eval_lt (X 0) (rename Fin.succ (p i))
    convert hC.preimage_tail.inter (IsSemialgebraic.iInter hs) using 1
    ext y
    rw [mem_image_cylinder]
    simp [forall_and, and_left_comm]

end Real

/-! ### Cylindrical algebraic decompositions -/

/-- `IsCAD n 𝒞` says that the set `𝒞` of subsets of `ℝ ^ n` is a *cylindrical algebraic
decomposition* of `ℝ ^ n`. The decomposition of `ℝ ^ 0` is the single cell `univ`. A decomposition
of `ℝ ^ (n + 1)` consists of all the cells of the stacks over the cells of a decomposition `𝒟` of
`ℝ ^ n`, where over each cell `C ∈ 𝒟` the stack `θ C` is a semialgebraic stack. The new coordinate
is coordinate `0`. -/
inductive IsCAD : (n : ℕ) → Set (Set (Fin n → ℝ)) → Prop
  /-- The decomposition of `ℝ ^ 0` into a single point. -/
  | zero : IsCAD 0 {univ}
  /-- Lift a decomposition `𝒟` of `ℝ ^ n` by a semialgebraic stack over each of its cells. -/
  | succ {n : ℕ} {𝒟 : Set (Set (Fin n → ℝ))} (k : Set (Fin n → ℝ) → ℕ)
      (θ : ∀ C : Set (Fin n → ℝ), Fin (k C) → C → ℝ) :
      IsCAD n 𝒟 → (∀ C ∈ 𝒟, IsSemialgebraicStack C (θ C)) →
        IsCAD (n + 1) (⋃ C ∈ 𝒟, stackCells C (θ C))

namespace IsCAD

variable {𝒞 : Set (Set (Fin n → ℝ))}

/-- A cylindrical algebraic decomposition has finitely many cells. -/
theorem finite (h : IsCAD n 𝒞) : 𝒞.Finite := by
  induction h with
  | zero => exact finite_singleton _
  | succ k θ _ _ ih => exact ih.biUnion fun C _ ↦ finite_stackCells C (θ C)

/-- Every cell of a cylindrical algebraic decomposition is semialgebraic. -/
theorem isSemialgebraic (h : IsCAD n 𝒞) {E : Set (Fin n → ℝ)} (hE : E ∈ 𝒞) :
    IsSemialgebraic E := by
  induction h with
  | zero =>
    rw [mem_singleton_iff.1 hE]
    exact isSemialgebraic_univ
  | succ k θ _ hθ _ =>
    obtain ⟨C, hC, hE⟩ := mem_iUnion₂.1 hE
    exact (hθ C hC).isSemialgebraic hE

/-- Every cell of a cylindrical algebraic decomposition is connected, and in particular
nonempty. -/
theorem isConnected (h : IsCAD n 𝒞) {E : Set (Fin n → ℝ)} (hE : E ∈ 𝒞) : IsConnected E := by
  induction h with
  | zero =>
    rw [mem_singleton_iff.1 hE, univ_unique]
    exact isConnected_singleton
  | succ k θ _ hθ ih =>
    obtain ⟨C, hC, hE⟩ := mem_iUnion₂.1 hE
    exact isConnected_of_mem_stackCells (ih hC) (hθ C hC).continuous (hθ C hC).strictMono hE

/-- The cells of a cylindrical algebraic decomposition of `ℝ ^ n` partition `ℝ ^ n`. -/
theorem isPartition (h : IsCAD n 𝒞) : Setoid.IsPartition 𝒞 := by
  induction h with
  | zero => exact ⟨fun h ↦ empty_ne_univ (mem_singleton_iff.1 h), fun a ↦ ⟨univ, by simp, by simp⟩⟩
  | @succ n 𝒟 k θ h𝒟 hθ ih =>
    refine PairwiseDisjoint.isPartition_of_exists_of_ne_empty ?_ (fun y ↦ ?_) fun h₀ ↦ ?_
    · -- Cells over distinct base cells have disjoint projections.
      simp only [PairwiseDisjoint, Set.Pairwise, mem_iUnion₂, onFun, id]
      rintro E ⟨C, hC, hE⟩ E' ⟨C', hC', hE'⟩ hne
      rcases eq_or_ne C C' with rfl | hCC'
      · exact pairwiseDisjoint_stackCells (fun x ↦ ((hθ C hC).strictMono x).injective) hE hE'
          hne
      · refine Disjoint.of_image (f := Fin.tail) ?_
        rw [image_tail_of_mem_stackCells (hθ C hC).strictMono hE,
          image_tail_of_mem_stackCells (hθ C' hC').strictMono hE']
        exact ih.pairwiseDisjoint hC hC' hCC'
    · -- A point lies in a cell of the stack over the base cell containing its projection.
      obtain ⟨C, ⟨hC, hyC⟩, -⟩ := ih.2 (Fin.tail y)
      have hy : y ∈ ⋃₀ stackCells C (θ C) := by
        rw [sUnion_stackCells fun x ↦ ((hθ C hC).strictMono x).monotone]
        exact hyC
      obtain ⟨E, hE, hyE⟩ := hy
      exact ⟨E, mem_iUnion₂.2 ⟨C, hC, hE⟩, hyE⟩
    · exact not_nonempty_empty ((IsCAD.succ k θ h𝒟 hθ).isConnected h₀).nonempty

/-- The projections of the cells of a cylindrical algebraic decomposition of `ℝ ^ (n + 1)`,
forgetting the distinguished coordinate `0`, form a cylindrical algebraic decomposition of
`ℝ ^ n`. -/
theorem image_tail {𝒞 : Set (Set (Fin (n + 1) → ℝ))} (h : IsCAD (n + 1) 𝒞) :
    IsCAD n (image Fin.tail '' 𝒞) := by
  cases h with
  | succ k θ h𝒟 hθ => rwa [image_image_tail_iUnion_stackCells fun C hC ↦ (hθ C hC).strictMono]

/-- A cylindrical algebraic decomposition is cylindrical: the projections of two of its cells are
equal or disjoint. -/
theorem image_tail_eq_or_disjoint {𝒞 : Set (Set (Fin (n + 1) → ℝ))} (h : IsCAD (n + 1) 𝒞)
    {E E' : Set (Fin (n + 1) → ℝ)} (hE : E ∈ 𝒞) (hE' : E' ∈ 𝒞) :
    Fin.tail '' E = Fin.tail '' E' ∨ Disjoint (Fin.tail '' E) (Fin.tail '' E') :=
  h.image_tail.isPartition.pairwiseDisjoint.eq_or_disjoint (mem_image_of_mem _ hE)
    (mem_image_of_mem _ hE')

end IsCAD

/-- The trivial cylindrical algebraic decomposition of `ℝ ^ n` into a single cell. -/
theorem isCAD_singleton_univ (n : ℕ) : IsCAD n {univ} := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    convert IsCAD.succ (fun _ ↦ 0)
      (fun C i (x : C) ↦ eval x.1 (Fin.elim0 i : MvPolynomial (Fin n) ℝ)) ih fun C hC ↦ ?_
    · ext E
      simp [range_cylinder, eq_comm]
    · rw [mem_singleton_iff.1 hC]
      exact isSemialgebraicStack_eval isSemialgebraic_univ _ fun _ _ ↦ Subsingleton.strictMono _

/-- Strictly increasing points `c₀ < c₁ < … < cₖ₋₁` of `ℝ`, together with the open intervals they
cut out, form a cylindrical algebraic decomposition of `ℝ ^ 1`. -/
theorem isCAD_stackCells_const {c : Fin k → ℝ} (hc : StrictMono c) :
    IsCAD 1 (stackCells (univ : Set (Fin 0 → ℝ)) fun i _ ↦ c i) := by
  have hθ : IsSemialgebraicStack (univ : Set (Fin 0 → ℝ)) fun i _ ↦ c i := by
    simpa using isSemialgebraicStack_eval isSemialgebraic_univ (fun i ↦ MvPolynomial.C (c i))
      fun _ _ ↦ by simpa using hc
  convert IsCAD.succ (fun _ ↦ k) (fun _ ↦ fun i _ ↦ c i) .zero fun C hC ↦ by
    rwa [mem_singleton_iff.1 hC]
  simp

end TauCeti
