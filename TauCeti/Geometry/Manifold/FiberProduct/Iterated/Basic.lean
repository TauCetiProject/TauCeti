/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Iterated fibre products of a map

For any map `π : Y → M`, the `k`-fold iterated fibre product `Y^[k]` is the subtype
`TauCeti.IteratedFiberProduct π k = {y : Fin k → Y // ∀ i j, π (y i) = π (y j)}`, equipped with its
subspace topology in `Fin k → Y`.

This file collects the manifold-free set-theoretic and topological API:
* the factor projections `TauCeti.IteratedFiberProduct.eval`, the diagonal inclusion
  `TauCeti.IteratedFiberProduct.const`, and for positive `k = m + 1`, the common base projection
  `TauCeti.IteratedFiberProduct.baseProj`;
* contravariant reindexing `TauCeti.IteratedFiberProduct.reindex` along `α : Fin k₁ → Fin k₂`,
  yielding the Čech nerve face maps `TauCeti.IteratedFiberProduct.face`, diagonal degeneracies
  `TauCeti.IteratedFiberProduct.degeneracy`, prepending `TauCeti.IteratedFiberProduct.cons`, and all
  five simplicial identities (`face_comp_face`, `face_castSucc_comp_degeneracy_succ_of_le`,
  `face_castSucc_comp_degeneracy`, `face_succ_comp_degeneracy`,
  `face_succ_comp_degeneracy_castSucc_of_gt`, and `degeneracy_castSucc_comp_degeneracy`);
* continuity of `eval`, `const`, `baseProj`, `reindex`, `face`, and `degeneracy`, together with the
  embedding properties of `const (m + 1)`, surjective-reindex maps, and `degeneracy`
  (`TauCeti.IteratedFiberProduct.isEmbedding_const`,
  `TauCeti.IteratedFiberProduct.isClosedEmbedding_const`,
  `TauCeti.IteratedFiberProduct.isEmbedding_reindex_of_surjective`,
  `TauCeti.IteratedFiberProduct.isClosedEmbedding_reindex_of_surjective`,
  `TauCeti.IteratedFiberProduct.isEmbedding_degeneracy`,
  `TauCeti.IteratedFiberProduct.isClosedEmbedding_degeneracy`);
* when `M` is Hausdorff and `π` is continuous, the subtype inclusion into `Fin k → Y` is a closed
  topological embedding (`TauCeti.isClosedEmbedding_coe_iteratedFiberProduct`).
-/

public section

open Function Set Topology

namespace TauCeti

section Set

variable {Y M : Type*} {π : Y → M}

/-- The `k`-fold fibre product `Y^[k]` of a map `π : Y → M` over `M`: the subtype of tuples
`y : Fin k → Y` whose coordinates share a common image under `π`. It is an abbreviation so that it
inherits the subspace topology and `Subtype.val` coercion from `Fin k → Y` directly. -/
abbrev IteratedFiberProduct (π : Y → M) (k : ℕ) : Type _ :=
  {y : Fin k → Y // ∀ i j, π (y i) = π (y j)}

/-- The underlying set of `IteratedFiberProduct π k` in `Fin k → Y` is the set of tuples whose
entries have equal images under `π`. -/
theorem range_coe_iteratedFiberProduct (π : Y → M) (k : ℕ) :
    range (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) =
      {y : Fin k → Y | ∀ i j, π (y i) = π (y j)} :=
  Subtype.range_coe_subtype

/-- A tuple in `Fin k → Y` belongs to the image of `IteratedFiberProduct π k` if and only if all
its coordinates have the same image under `π`. -/
theorem mem_range_coe_iteratedFiberProduct_iff {k : ℕ} {y : Fin k → Y} :
    y ∈ range (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) ↔
      ∀ i j, π (y i) = π (y j) := by
  rw [range_coe_iteratedFiberProduct]
  rfl

namespace IteratedFiberProduct

/-- The zero-fold fibre product consists of the unique empty tuple. -/
instance instUniqueZero : Unique (IteratedFiberProduct π 0) where
  default := ⟨Fin.elim0, fun i ↦ i.elim0⟩
  uniq _ := Subtype.ext (funext fun i ↦ i.elim0)

/-- The `i`-th factor projection `Y^[k] → Y`. -/
@[expose] def eval {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) : Y :=
  y.val i

/-- Evaluation at `i` reads the `i`-th coordinate of the underlying tuple. -/
@[simp]
theorem eval_apply {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) :
    eval i y = y.val i := (rfl)

/-- Two points of `IteratedFiberProduct π k` are equal when all their factor projections agree. -/
theorem ext {k : ℕ} {y₁ y₂ : IteratedFiberProduct π k} (h : ∀ i, eval i y₁ = eval i y₂) :
    y₁ = y₂ :=
  Subtype.ext (funext h)

/-- Any two factor projections of `y : IteratedFiberProduct π k` have equal images under `π`. -/
theorem map_eval_eq {k : ℕ} (y : IteratedFiberProduct π k) (i j : Fin k) :
    π (eval i y) = π (eval j y) :=
  y.property i j

/-- The diagonal inclusion `Y → Y^[k]` sending `z` to the constant tuple `(z, …, z)`. -/
@[expose] def const (k : ℕ) (z : Y) : IteratedFiberProduct π k :=
  ⟨fun _ ↦ z, fun _ _ ↦ rfl⟩

/-- The underlying tuple of `const k z` is the constant function `Function.const (Fin k) z`. -/
@[simp]
theorem coe_const (k : ℕ) (z : Y) :
    (const (π := π) k z : Fin k → Y) = Function.const (Fin k) z := (rfl)

/-- Evaluating the diagonal tuple `const k z` at any index returns `z`. -/
theorem eval_const {k : ℕ} (i : Fin k) (z : Y) :
    eval i (const (π := π) k z) = z := (rfl)

/-- Every factor projection `eval i : Y^[k] → Y` is surjective, split by the diagonal `const k`. -/
theorem surjective_eval {k : ℕ} (i : Fin k) :
    Surjective (eval i : IteratedFiberProduct π k → Y) :=
  fun z ↦ ⟨const k z, rfl⟩

/-- For positive `k = m + 1`, the diagonal inclusion `const (m + 1) : Y → Y^[m + 1]` is
injective, split by `eval 0`. -/
theorem injective_const (m : ℕ) :
    Injective (const (π := π) (m + 1)) :=
  Function.LeftInverse.injective (fun z ↦ eval_const (π := π) (0 : Fin (m + 1)) z)

/-- The common projection `Y^[m + 1] → M` to the base, defined via the `0`-th factor and equal to
`π ∘ eval i` for every `i : Fin (m + 1)`. -/
@[expose] def baseProj {m : ℕ} (y : IteratedFiberProduct π (m + 1)) : M :=
  π (y.val 0)

/-- The base projection agrees with `π (y.1 i)` at every coordinate `i : Fin (m + 1)`. -/
theorem baseProj_eq_apply {m : ℕ} (y : IteratedFiberProduct π (m + 1)) (i : Fin (m + 1)) :
    baseProj y = π (y.val i) :=
  y.property 0 i

/-- Composing `π` with any factor projection `eval i` yields `baseProj`. -/
theorem map_eval_eq_baseProj {m : ℕ} (y : IteratedFiberProduct π (m + 1)) (i : Fin (m + 1)) :
    π (eval i y) = baseProj y :=
  (y.property 0 i).symm

/-- On a diagonal tuple `const (m + 1) z`, the base projection is `π z`. -/
@[simp]
theorem baseProj_const (m : ℕ) (z : Y) :
    baseProj (const (π := π) (m + 1) z) = π z := (rfl)

/-- The base projection `Y^[m + 1] → M` is surjective if and only if `π` is surjective. -/
theorem surjective_baseProj_iff {m : ℕ} :
    Surjective (baseProj : IteratedFiberProduct π (m + 1) → M) ↔ Surjective π :=
  ⟨fun h b ↦ by obtain ⟨y, rfl⟩ := h b; exact ⟨y.val 0, rfl⟩,
    fun h b ↦ by obtain ⟨z, rfl⟩ := h b; exact ⟨const (m + 1) z, rfl⟩⟩

/-- Contravariant reindexing of `IteratedFiberProduct π` along `α : Fin k₁ → Fin k₂`, sending
`y` to `y ∘ α`. -/
@[expose] def reindex {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) (y : IteratedFiberProduct π k₂) :
    IteratedFiberProduct π k₁ :=
  ⟨y.val ∘ α, fun i j ↦ y.property (α i) (α j)⟩

/-- The underlying tuple of `reindex α y` is `y.1 ∘ α`. -/
@[simp]
theorem coe_reindex {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) (y : IteratedFiberProduct π k₂) :
    (reindex α y : Fin k₁ → Y) = y.val ∘ α := (rfl)

/-- Evaluating `reindex α y` at `i` evaluates `y` at `α i`. -/
theorem eval_reindex {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) (y : IteratedFiberProduct π k₂)
    (i : Fin k₁) :
    eval i (reindex α y) = eval (α i) y := by
  simp only [eval_apply, coe_reindex, comp_apply]

/-- Reindexing along the identity map is the identity on `IteratedFiberProduct π k`. -/
@[simp]
theorem reindex_id {k : ℕ} :
    (reindex (id : Fin k → Fin k) : IteratedFiberProduct π k → IteratedFiberProduct π k) = id :=
  (rfl)

/-- Pointwise form of `reindex_id`. -/
@[simp]
theorem reindex_id_apply {k : ℕ} (y : IteratedFiberProduct π k) :
    reindex id y = y := (rfl)

/-- Reindexing is contravariantly functorial: `reindex (β ∘ α) = reindex α ∘ reindex β`. -/
theorem reindex_comp {k₁ k₂ k₃ : ℕ} (α : Fin k₁ → Fin k₂) (β : Fin k₂ → Fin k₃) :
    (reindex (β ∘ α) : IteratedFiberProduct π k₃ → IteratedFiberProduct π k₁) =
      reindex α ∘ reindex β := (rfl)

/-- Pointwise form of `reindex_comp`. -/
@[simp]
theorem reindex_reindex {k₁ k₂ k₃ : ℕ} (α : Fin k₁ → Fin k₂) (β : Fin k₂ → Fin k₃)
    (y : IteratedFiberProduct π k₃) :
    reindex α (reindex β y) = reindex (β ∘ α) y := (rfl)

/-- Reindexing a constant diagonal tuple produces the constant diagonal tuple. -/
@[simp]
theorem reindex_const {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) (z : Y) :
    reindex α (const (π := π) k₂ z) = const k₁ z :=
  ext fun _ ↦ by simp only [eval_reindex, eval_const]

/-- Reindexing between positive arities preserves `baseProj`. -/
@[simp]
theorem baseProj_reindex {m₁ m₂ : ℕ} (α : Fin (m₁ + 1) → Fin (m₂ + 1))
    (y : IteratedFiberProduct π (m₂ + 1)) :
    baseProj (reindex α y) = baseProj y := by
  rw [baseProj_eq_apply _ 0, baseProj_eq_apply _ 0]
  exact (y.property 0 (α 0)).symm

/-- Reindexing along an injective map between nonempty index sets is surjective: unassigned
coordinates can be filled with coordinate `0` of the given tuple, which lies in the same fibre. -/
theorem surjective_reindex_of_injective {m₁ m₂ : ℕ} {α : Fin (m₁ + 1) → Fin (m₂ + 1)}
    (hα : Injective α) :
    Surjective (reindex (π := π) α) := by
  intro x
  let g : Fin (m₂ + 1) → Y := extend α x.val (fun _ ↦ x.val 0)
  have hg_base : ∀ j : Fin (m₂ + 1), π (g j) = baseProj x := by
    intro j
    by_cases hj : ∃ i, α i = j
    · obtain ⟨i, rfl⟩ := hj
      dsimp only [g]
      rw [hα.extend_apply, baseProj_eq_apply x i]
    · dsimp only [g]
      rw [extend_apply' _ _ _ hj, baseProj_eq_apply x 0]
  refine ⟨⟨g, fun j₁ j₂ ↦ (hg_base j₁).trans (hg_base j₂).symm⟩, ext fun i ↦ ?_⟩
  rw [eval_apply, eval_apply]
  exact hα.extend_apply x.val (fun _ ↦ x.val 0) i

/-- Reindexing along a surjective map is injective. -/
theorem injective_reindex_of_surjective {k₁ k₂ : ℕ} {α : Fin k₁ → Fin k₂}
    (hα : Surjective α) :
    Injective (reindex (π := π) α) := by
  intro y₁ y₂ h
  refine ext fun j ↦ ?_
  obtain ⟨i, rfl⟩ := hα j
  simpa only [eval_reindex] using congrArg (eval i) h

/-- Reindexing along a right inverse `surjInv hα` of a surjective map `α` is a left inverse to
`reindex α`. -/
theorem leftInverse_reindex_surjInv {k₁ k₂ : ℕ} {α : Fin k₁ → Fin k₂} (hα : Surjective α) :
    LeftInverse (reindex (π := π) (surjInv hα)) (reindex (π := π) α) :=
  fun y ↦ ext fun i ↦ by rw [eval_reindex, eval_reindex, surjInv_eq hα]

/-- The `i`-th face map `Y^[m + 2] → Y^[m + 1]`, omitting coordinate `i` via `Fin.succAbove i`. -/
@[expose] def face {m : ℕ} (i : Fin (m + 2)) :
    IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1) :=
  reindex i.succAbove

/-- `face i` is reindexing along `i.succAbove`. -/
theorem face_eq_reindex {m : ℕ} (i : Fin (m + 2)) :
    (face i : IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1)) =
      reindex i.succAbove := (rfl)

/-- The underlying tuple of `face i y` is `y.1 ∘ i.succAbove`. -/
@[simp]
theorem coe_face {m : ℕ} (i : Fin (m + 2)) (y : IteratedFiberProduct π (m + 2)) :
    (face i y : Fin (m + 1) → Y) = y.val ∘ i.succAbove := (rfl)

/-- Evaluating `face i y` at `j` evaluates `y` at `i.succAbove j`. -/
theorem eval_face {m : ℕ} (i : Fin (m + 2)) (j : Fin (m + 1))
    (y : IteratedFiberProduct π (m + 2)) :
    eval j (face i y) = eval (i.succAbove j) y :=
  eval_reindex i.succAbove y j

/-- On `Y^[2]`, `face 0` omits coordinate `0` and therefore reads coordinate `1` (`pr₂`). -/
theorem eval_zero_face_zero (y : IteratedFiberProduct π 2) :
    eval 0 (face 0 y) = eval 1 y :=
  eval_face 0 0 y

/-- On `Y^[2]`, `face 1` omits coordinate `1` and therefore reads coordinate `0` (`pr₁`). -/
theorem eval_zero_face_one (y : IteratedFiberProduct π 2) :
    eval 0 (face 1 y) = eval 0 y :=
  eval_face 1 0 y

/-- Every face map sends a constant diagonal tuple to the constant diagonal tuple. -/
@[simp]
theorem face_const {m : ℕ} (i : Fin (m + 2)) (z : Y) :
    face i (const (π := π) (m + 2) z) = const (m + 1) z :=
  reindex_const i.succAbove z

/-- Every face map commutes with `baseProj`. -/
@[simp]
theorem baseProj_face {m : ℕ} (i : Fin (m + 2)) (y : IteratedFiberProduct π (m + 2)) :
    baseProj (face i y) = baseProj y :=
  baseProj_reindex i.succAbove y

/-- Every face map `face i : Y^[m + 2] → Y^[m + 1]` is surjective. -/
theorem surjective_face {m : ℕ} (i : Fin (m + 2)) :
    Surjective (face i : IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1)) :=
  surjective_reindex_of_injective Fin.succAbove_right_injective

/-- The `i`-th diagonal degeneracy map `Y^[m + 1] → Y^[m + 2]`, repeating coordinate `i` via
`Fin.predAbove i`. -/
@[expose] def degeneracy {m : ℕ} (i : Fin (m + 1)) :
    IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2) :=
  reindex i.predAbove

/-- `degeneracy i` is reindexing along `i.predAbove`. -/
theorem degeneracy_eq_reindex {m : ℕ} (i : Fin (m + 1)) :
    (degeneracy i : IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) =
      reindex i.predAbove := (rfl)

/-- The underlying tuple of `degeneracy i y` is `y.1 ∘ i.predAbove`. -/
@[simp]
theorem coe_degeneracy {m : ℕ} (i : Fin (m + 1)) (y : IteratedFiberProduct π (m + 1)) :
    (degeneracy i y : Fin (m + 2) → Y) = y.val ∘ i.predAbove := (rfl)

/-- Evaluating `degeneracy i y` at `j` evaluates `y` at `i.predAbove j`. -/
theorem eval_degeneracy {m : ℕ} (i : Fin (m + 1)) (j : Fin (m + 2))
    (y : IteratedFiberProduct π (m + 1)) :
    eval j (degeneracy i y) = eval (i.predAbove j) y :=
  eval_reindex i.predAbove y j

/-- Every degeneracy map sends a constant diagonal tuple to the constant diagonal tuple. -/
@[simp]
theorem degeneracy_const {m : ℕ} (i : Fin (m + 1)) (z : Y) :
    degeneracy i (const (π := π) (m + 1) z) = const (m + 2) z :=
  reindex_const i.predAbove z

/-- Every degeneracy map commutes with `baseProj`. -/
@[simp]
theorem baseProj_degeneracy {m : ℕ} (i : Fin (m + 1)) (y : IteratedFiberProduct π (m + 1)) :
    baseProj (degeneracy i y) = baseProj y :=
  baseProj_reindex i.predAbove y

/-! ### Simplicial identities -/

/-- **First simplicial identity**: for `i ≤ j`, `face i ∘ face j.succ = face j ∘ face i.castSucc`.
-/
theorem face_comp_face {m : ℕ} {i j : Fin (m + 2)} (hij : i ≤ j) :
    (face i ∘ face j.succ : IteratedFiberProduct π (m + 3) → IteratedFiberProduct π (m + 1)) =
      face j ∘ face i.castSucc := by
  have h : (j.succ.succAbove ∘ i.succAbove : Fin (m + 1) → Fin (m + 3)) =
      i.castSucc.succAbove ∘ j.succAbove :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_δ hij))
  exact (reindex_comp _ _).symm.trans ((congrArg reindex h).trans (reindex_comp _ _))

/-- Pointwise form of the first simplicial identity. -/
theorem face_face_succ {m : ℕ} {i j : Fin (m + 2)} (hij : i ≤ j)
    (y : IteratedFiberProduct π (m + 3)) :
    face i (face j.succ y) = face j (face i.castSucc y) :=
  congrFun (face_comp_face hij) y

/-- Special case `i = j` of the first simplicial identity:
`face i ∘ face i.succ = face i ∘ face i.castSucc`. -/
theorem face_comp_face_self {m : ℕ} (i : Fin (m + 2)) :
    (face i ∘ face i.succ : IteratedFiberProduct π (m + 3) → IteratedFiberProduct π (m + 1)) =
      face i ∘ face i.castSucc :=
  face_comp_face le_rfl

/-- **Second simplicial identity**: for `i ≤ j.castSucc`,
`face i.castSucc ∘ degeneracy j.succ = degeneracy j ∘ face i`. -/
theorem face_castSucc_comp_degeneracy_succ_of_le {m : ℕ} {i : Fin (m + 2)} {j : Fin (m + 1)}
    (hij : i ≤ j.castSucc) :
    (face i.castSucc ∘ degeneracy j.succ :
        IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 2)) =
      degeneracy j ∘ face i := by
  have h : (j.succ.predAbove ∘ i.castSucc.succAbove : Fin (m + 2) → Fin (m + 2)) =
      i.succAbove ∘ j.predAbove :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_of_le hij))
  exact (reindex_comp _ _).symm.trans ((congrArg reindex h).trans (reindex_comp _ _))

/-- Pointwise form of the second simplicial identity. -/
theorem face_castSucc_degeneracy_succ_of_le {m : ℕ} {i : Fin (m + 2)} {j : Fin (m + 1)}
    (hij : i ≤ j.castSucc) (y : IteratedFiberProduct π (m + 2)) :
    face i.castSucc (degeneracy j.succ y) = degeneracy j (face i y) :=
  congrFun (face_castSucc_comp_degeneracy_succ_of_le hij) y

/-- **Third simplicial identity (first part)**: `face i.castSucc ∘ degeneracy i = id`. -/
theorem face_castSucc_comp_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    (face i.castSucc ∘ degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 1)) = id := by
  have h : (i.predAbove ∘ i.castSucc.succAbove : Fin (m + 1) → Fin (m + 1)) = id :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_self (i := i)))
  exact (reindex_comp _ _).symm.trans (congrArg reindex h)

/-- Pointwise form of `face_castSucc_comp_degeneracy`. -/
@[simp]
theorem face_castSucc_degeneracy {m : ℕ} (i : Fin (m + 1))
    (y : IteratedFiberProduct π (m + 1)) :
    face i.castSucc (degeneracy i y) = y :=
  congrFun (face_castSucc_comp_degeneracy i) y

/-- `face i.castSucc` is a left inverse to `degeneracy i`. -/
theorem leftInverse_face_castSucc_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    LeftInverse (face (π := π) i.castSucc) (degeneracy i) :=
  face_castSucc_degeneracy i

/-- **Third simplicial identity (second part)**: `face i.succ ∘ degeneracy i = id`. -/
theorem face_succ_comp_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    (face i.succ ∘ degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 1)) = id := by
  have h : (i.predAbove ∘ i.succ.succAbove : Fin (m + 1) → Fin (m + 1)) = id :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_succ (i := i)))
  exact (reindex_comp _ _).symm.trans (congrArg reindex h)

/-- Pointwise form of `face_succ_comp_degeneracy`. -/
@[simp]
theorem face_succ_degeneracy {m : ℕ} (i : Fin (m + 1))
    (y : IteratedFiberProduct π (m + 1)) :
    face i.succ (degeneracy i y) = y :=
  congrFun (face_succ_comp_degeneracy i) y

/-- `face i.succ` is a left inverse to `degeneracy i`. -/
theorem leftInverse_face_succ_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    LeftInverse (face (π := π) i.succ) (degeneracy i) :=
  face_succ_degeneracy i

/-- Every degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is injective. -/
theorem injective_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    Injective (degeneracy i : IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) :=
  (leftInverse_face_castSucc_degeneracy i).injective

/-- **Fourth simplicial identity**: for `j.castSucc < i`,
`face i.succ ∘ degeneracy j.castSucc = degeneracy j ∘ face i`. -/
theorem face_succ_comp_degeneracy_castSucc_of_gt {m : ℕ} {i : Fin (m + 2)} {j : Fin (m + 1)}
    (hij : j.castSucc < i) :
    (face i.succ ∘ degeneracy j.castSucc :
        IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 2)) =
      degeneracy j ∘ face i := by
  have h : (j.castSucc.predAbove ∘ i.succ.succAbove : Fin (m + 2) → Fin (m + 2)) =
      i.succAbove ∘ j.predAbove :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_of_gt hij))
  exact (reindex_comp _ _).symm.trans ((congrArg reindex h).trans (reindex_comp _ _))

/-- Pointwise form of the fourth simplicial identity. -/
theorem face_succ_degeneracy_castSucc_of_gt {m : ℕ} {i : Fin (m + 2)} {j : Fin (m + 1)}
    (hij : j.castSucc < i) (y : IteratedFiberProduct π (m + 2)) :
    face i.succ (degeneracy j.castSucc y) = degeneracy j (face i y) :=
  congrFun (face_succ_comp_degeneracy_castSucc_of_gt hij) y

/-- **Fifth simplicial identity**: for `i ≤ j`,
`degeneracy i.castSucc ∘ degeneracy j = degeneracy j.succ ∘ degeneracy i`. -/
theorem degeneracy_castSucc_comp_degeneracy {m : ℕ} {i j : Fin (m + 1)} (hij : i ≤ j) :
    (degeneracy i.castSucc ∘ degeneracy j :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 3)) =
      degeneracy j.succ ∘ degeneracy i := by
  have h : (j.predAbove ∘ i.castSucc.predAbove : Fin (m + 3) → Fin (m + 1)) =
      i.predAbove ∘ j.succ.predAbove :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.σ_comp_σ hij))
  exact (reindex_comp _ _).symm.trans ((congrArg reindex h).trans (reindex_comp _ _))

/-- Pointwise form of the fifth simplicial identity. -/
theorem degeneracy_castSucc_degeneracy {m : ℕ} {i j : Fin (m + 1)} (hij : i ≤ j)
    (y : IteratedFiberProduct π (m + 1)) :
    degeneracy i.castSucc (degeneracy j y) = degeneracy j.succ (degeneracy i y) :=
  congrFun (degeneracy_castSucc_comp_degeneracy hij) y

/-! ### Prepending a point -/

/-- Prepend a point `z` of the fibre over `baseProj y` to the tuple `y`, giving the tuple
`(z, y₀, …, y_m)` of `Y^[m + 2]`. -/
@[expose] def cons {m : ℕ} (z : Y) (y : IteratedFiberProduct π (m + 1)) (h : π z = baseProj y) :
    IteratedFiberProduct π (m + 2) :=
  ⟨Fin.cons z y.val, by
    have key : ∀ i : Fin (m + 2), π (Fin.cons (α := fun _ ↦ Y) z y.val i) = baseProj y :=
      Fin.cases h fun j ↦ by rw [Fin.cons_succ, ← eval_apply]; exact map_eval_eq_baseProj y j
    exact fun i j ↦ (key i).trans (key j).symm⟩

/-- The underlying tuple of `cons z y h` is `Fin.cons z y`. -/
@[simp]
theorem coe_cons {m : ℕ} (z : Y) (y : IteratedFiberProduct π (m + 1)) (h : π z = baseProj y) :
    (cons z y h : Fin (m + 2) → Y) = Fin.cons z y.val := (rfl)

/-- Coordinate `0` of `cons z y h` is the prepended point `z`. -/
theorem eval_zero_cons {m : ℕ} (z : Y) (y : IteratedFiberProduct π (m + 1))
    (h : π z = baseProj y) :
    eval 0 (cons z y h) = z := by
  simp [eval_apply]

/-- Coordinate `j + 1` of `cons z y h` is coordinate `j` of `y`. -/
theorem eval_succ_cons {m : ℕ} (j : Fin (m + 1)) (z : Y) (y : IteratedFiberProduct π (m + 1))
    (h : π z = baseProj y) :
    eval j.succ (cons z y h) = eval j y := by
  simp [eval_apply]

/-- Prepending a point does not change the base point. -/
@[simp]
theorem baseProj_cons {m : ℕ} (z : Y) (y : IteratedFiberProduct π (m + 1))
    (h : π z = baseProj y) :
    baseProj (cons z y h) = baseProj y := by
  rw [baseProj_eq_apply _ 0]
  exact h

/-- Omitting the prepended point recovers the original tuple. -/
@[simp]
theorem face_zero_cons {m : ℕ} (z : Y) (y : IteratedFiberProduct π (m + 1))
    (h : π z = baseProj y) :
    face 0 (cons z y h) = y :=
  ext fun j ↦ by simp [eval_apply]

/-- Omitting coordinate `i + 1` after prepending `z` is prepending `z` after omitting
coordinate `i`. -/
@[simp]
theorem face_succ_cons {m : ℕ} (i : Fin (m + 2)) (z : Y) (y : IteratedFiberProduct π (m + 2))
    (h : π z = baseProj y) :
    face i.succ (cons z y h) = cons z (face i y) (h.trans (baseProj_face i y).symm) := by
  refine ext fun j ↦ ?_
  cases j using Fin.cases with
  | zero => simp [eval_apply]
  | succ j => simp [eval_apply, Fin.succ_succAbove_succ]

/-- On `Y^[1]`, omitting the original coordinate after prepending `z` leaves the one-point tuple
`z`. -/
@[simp]
theorem face_one_cons (z : Y) (y : IteratedFiberProduct π 1) (h : π z = baseProj y) :
    face 1 (cons z y h) = const 1 z :=
  ext fun j ↦ by simp [eval_apply, Fin.fin_one_eq_zero j]

end IteratedFiberProduct

end Set

section Topology

variable {Y M : Type*} [TopologicalSpace Y] {π : Y → M}

namespace IteratedFiberProduct

/-- Every factor projection `eval i : Y^[k] → Y` is continuous. -/
theorem continuous_eval {k : ℕ} (i : Fin k) :
    Continuous (eval i : IteratedFiberProduct π k → Y) :=
  (continuous_apply i).comp continuous_subtypeVal

/-- The diagonal map `const k : Y → Y^[k]` is continuous. -/
theorem continuous_const (k : ℕ) :
    Continuous (const (π := π) k) :=
  (continuous_pi fun _ ↦ continuous_id).subtype_mk _

/-- For positive `k = m + 1`, the diagonal inclusion `const (m + 1) : Y → Y^[m + 1]` is a
topological embedding, split by `eval 0`. -/
theorem isEmbedding_const (m : ℕ) :
    IsEmbedding (const (π := π) (m + 1)) :=
  Function.LeftInverse.isEmbedding (fun z ↦ eval_const (π := π) (0 : Fin (m + 1)) z)
    (continuous_eval 0) (continuous_const (m + 1))

/-- When `Y` is Hausdorff, the diagonal inclusion `const (m + 1) : Y → Y^[m + 1]` is a closed
topological embedding. -/
theorem isClosedEmbedding_const [T2Space Y] (m : ℕ) :
    IsClosedEmbedding (const (π := π) (m + 1)) :=
  Function.LeftInverse.isClosedEmbedding (fun z ↦ eval_const (π := π) (0 : Fin (m + 1)) z)
    (continuous_eval 0) (continuous_const (m + 1))

/-- When `π` is continuous, the base projection `baseProj : Y^[m + 1] → M` is continuous. -/
theorem continuous_baseProj [TopologicalSpace M] (hπ : Continuous π) (m : ℕ) :
    Continuous (baseProj : IteratedFiberProduct π (m + 1) → M) :=
  hπ.comp (continuous_eval 0)

/-- Contravariant reindexing of `IteratedFiberProduct π` is continuous. -/
theorem continuous_reindex {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) :
    Continuous (reindex (π := π) α) :=
  Continuous.subtype_mk
    (continuous_pi fun i ↦ (continuous_eval (π := π) (α i)).congr fun a ↦ eval_apply (α i) a) _

/-- Any surjective index map `α : Fin k₁ → Fin k₂` induces a topological embedding
`reindex α : Y^[k₂] → Y^[k₁]`. -/
theorem isEmbedding_reindex_of_surjective {k₁ k₂ : ℕ} {α : Fin k₁ → Fin k₂}
    (hα : Surjective α) :
    IsEmbedding (reindex (π := π) α) :=
  (leftInverse_reindex_surjInv hα).isEmbedding
    (continuous_reindex (surjInv hα)) (continuous_reindex α)

/-- When `Y` is Hausdorff, any surjective index map `α : Fin k₁ → Fin k₂` induces a closed
topological embedding `reindex α : Y^[k₂] → Y^[k₁]`. -/
theorem isClosedEmbedding_reindex_of_surjective [T2Space Y] {k₁ k₂ : ℕ}
    {α : Fin k₁ → Fin k₂} (hα : Surjective α) :
    IsClosedEmbedding (reindex (π := π) α) :=
  (leftInverse_reindex_surjInv hα).isClosedEmbedding
    (continuous_reindex (surjInv hα)) (continuous_reindex α)

/-- Every face map `face i : Y^[m + 2] → Y^[m + 1]` is continuous. -/
theorem continuous_face {m : ℕ} (i : Fin (m + 2)) :
    Continuous (face (π := π) i) :=
  continuous_reindex i.succAbove

/-- Every degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is continuous. -/
theorem continuous_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    Continuous (degeneracy (π := π) i) :=
  continuous_reindex i.predAbove

/-- Every degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is a topological embedding, split
by `face i.castSucc`. -/
theorem isEmbedding_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    IsEmbedding (degeneracy (π := π) i) :=
  degeneracy_eq_reindex i ▸ isEmbedding_reindex_of_surjective (Fin.predAbove_surjective i)

/-- When `Y` is Hausdorff, every degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is a closed
topological embedding. -/
theorem isClosedEmbedding_degeneracy [T2Space Y] {m : ℕ} (i : Fin (m + 1)) :
    IsClosedEmbedding (degeneracy (π := π) i) :=
  degeneracy_eq_reindex i ▸ isClosedEmbedding_reindex_of_surjective (Fin.predAbove_surjective i)

end IteratedFiberProduct

/-- When the base `M` is Hausdorff and `π` is continuous, the equal-fibre locus in `Fin k → Y` is
closed as the preimage of the closed multidiagonal of `Fin k → M` under `Pi.map fun _ ↦ π`. -/
theorem isClosed_setOf_map_eq [TopologicalSpace M] [T2Space M] (hπ : Continuous π) (k : ℕ) :
    IsClosed {y : Fin k → Y | ∀ i j, π (y i) = π (y j)} := by
  have hdiag : IsClosed {z : Fin k → M | ∀ i j, z i = z j} := by
    have hEq : {z : Fin k → M | ∀ i j, z i = z j} = ⋂ i, ⋂ j, {z : Fin k → M | z i = z j} := by
      ext z; simp
    rw [hEq]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_eq (continuous_apply i) (continuous_apply j)
  exact hdiag.preimage (continuous_pi fun i ↦ hπ.comp (continuous_apply i))

/-- When `M` is Hausdorff and `π` is continuous, the image of `IteratedFiberProduct π k` in
`Fin k → Y` is closed. -/
theorem isClosed_range_coe_iteratedFiberProduct [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosed (range (Subtype.val : IteratedFiberProduct π k → (Fin k → Y))) := by
  rw [range_coe_iteratedFiberProduct]
  exact isClosed_setOf_map_eq hπ k

/-- When `M` is Hausdorff and `π` is continuous, the subtype inclusion of
`IteratedFiberProduct π k` into `Fin k → Y` is a closed topological embedding. -/
theorem isClosedEmbedding_coe_iteratedFiberProduct [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosedEmbedding (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) :=
  .subtypeVal (isClosed_setOf_map_eq hπ k)

end Topology

end TauCeti
