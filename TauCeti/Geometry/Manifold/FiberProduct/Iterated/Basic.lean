/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Iterated fibre products of a map

For any map `π : Y → M`, the `k`-fold iterated fibre product `Y^[k]` is the subtype
`TauCeti.IteratedFiberProduct π k = {y : Fin k → Y // ∀ i j, π (y i) = π (y j)}`, equipped with its
subspace topology in `Fin k → Y`.

This file collects the manifold-free set-theoretic and topological API:
* the factor projections `TauCeti.IteratedFiberProduct.eval`, the diagonal inclusion
  `TauCeti.IteratedFiberProduct.const`, and for positive `k = m + 1`, the common base projection
  `TauCeti.IteratedFiberProduct.baseProj`;
* continuity of `eval`, `const`, and `baseProj`, together with the embedding properties of
  `const (m + 1)` (`TauCeti.IteratedFiberProduct.isEmbedding_const`,
  `TauCeti.IteratedFiberProduct.isClosedEmbedding_const`);
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
