/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Order.DirectedInverseSystem

/-!
# Sequential directed systems of non-unital star algebras

Given a sequence of non-unital `⋆`-algebras `A : ℕ → Type*` over `R` connected by step
`⋆`-homomorphisms `α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)`, iterating composition produces composite
transition `⋆`-homomorphisms `seqTransHom α h : A m →⋆ₙₐ[R] A n` for `m ≤ n` satisfying the
directed-system laws (`seqTransHom_self`, `seqTransHom_comp`), propagating compatible cocones
(`comp_seqTransHom_of_comp_eq`), and preserving any family of subsets invariant under each single
step (`seqTransHom_mem`).

## Main definitions and results

* `TauCeti.seqTransHom`: composite connecting `⋆`-homomorphism `A m →⋆ₙₐ[R] A n` for `m ≤ n`.
* `TauCeti.directedSystem_seqTransHom`: `DirectedSystem` instance on `A` given by `seqTransHom α`.
* `TauCeti.seqTransStarAlgHom`: unital composite connecting `⋆`-homomorphism
  `A m →⋆ₐ[R] A n` for `m ≤ n`.
* `TauCeti.directedSystem_seqTransStarAlgHom`: `DirectedSystem` instance on `A` given by
  `seqTransStarAlgHom α`.
* `TauCeti.comp_seqTransHom_of_comp_eq`: propagation of step-compatible cocones along
  `seqTransHom`.
* `TauCeti.seqTransHom_mem`: propagation of step-invariant subsets `F n ⊆ A n` along `seqTransHom`.
-/

public section

namespace TauCeti

section NonUnital

variable {R : Type*} [Monoid R] {A : ℕ → Type*}
  [∀ n, NonUnitalNonAssocSemiring (A n)] [∀ n, DistribMulAction R (A n)] [∀ n, Star (A n)]

/-- The composite connecting `⋆`-homomorphism `A m →⋆ₙₐ[R] A n` for `m ≤ n` obtained by iterating
a sequential system `α : ∀ k, A k →⋆ₙₐ[R] A (k + 1)`. -/
def seqTransHom (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {m n : ℕ} (h : m ≤ n) : A m →⋆ₙₐ[R] A n :=
  Nat.leRecOn (motive := fun k ↦ A m →⋆ₙₐ[R] A k) h (fun {k} f ↦ (α k).comp f) (.id R (A m))

@[simp]
theorem seqTransHom_self (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {n : ℕ} (h : n ≤ n) :
    seqTransHom α h = .id R (A n) := by
  cases Subsingleton.elim h n.le_refl
  exact Nat.leRecOn_self (motive := fun k ↦ A n →⋆ₙₐ[R] A k)
    (next := fun {k} f ↦ (α k).comp f) (NonUnitalStarAlgHom.id R (A n))

theorem seqTransHom_succ (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {m n : ℕ} (h : m ≤ n)
    (h' : m ≤ n + 1) : seqTransHom α h' = (α n).comp (seqTransHom α h) := by
  cases Subsingleton.elim h' (Nat.le_add_right_of_le h)
  exact Nat.leRecOn_succ (motive := fun k ↦ A m →⋆ₙₐ[R] A k) h
    (next := fun {k} f ↦ (α k).comp f) (NonUnitalStarAlgHom.id R (A m))

@[simp]
theorem seqTransHom_le_succ (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) (n : ℕ) :
    seqTransHom α (Nat.le_succ n) = α n := by
  rw [seqTransHom_succ α le_rfl (Nat.le_succ n), seqTransHom_self, NonUnitalStarAlgHom.comp_id]

@[simp]
theorem seqTransHom_comp (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {i j k : ℕ} (hij : i ≤ j)
    (hjk : j ≤ k) :
    (seqTransHom α hjk).comp (seqTransHom α hij) = seqTransHom α (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [seqTransHom_self, NonUnitalStarAlgHom.id_comp]
  | succ k hjk ih =>
    rw [seqTransHom_succ α hjk, seqTransHom_succ α (hij.trans hjk),
      NonUnitalStarAlgHom.comp_assoc, ih]

@[simp]
theorem seqTransHom_comp_apply (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {i j k : ℕ} (hij : i ≤ j)
    (hjk : j ≤ k) (a : A i) :
    seqTransHom α hjk (seqTransHom α hij a) = seqTransHom α (hij.trans hjk) a :=
  DFunLike.congr_fun (seqTransHom_comp α hij hjk) a

@[simp]
theorem seqTransHom_comp_step (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {m n : ℕ} (h : m + 1 ≤ n) :
    (seqTransHom α h).comp (α m) = seqTransHom α (Nat.le_of_succ_le h) := by
  rw [← seqTransHom_comp α (Nat.le_succ m) h, seqTransHom_le_succ]

@[simp]
theorem seqTransHom_comp_step_apply (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {m n : ℕ} (h : m + 1 ≤ n)
    (a : A m) :
    seqTransHom α h (α m a) = seqTransHom α (Nat.le_of_succ_le h) a :=
  DFunLike.congr_fun (seqTransHom_comp_step α h) a

@[simp]
theorem step_comp_seqTransHom (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {m n : ℕ} (h : m ≤ n) :
    (α n).comp (seqTransHom α h) = seqTransHom α (Nat.le_succ_of_le h) :=
  (seqTransHom_succ α h (Nat.le_succ_of_le h)).symm

@[simp]
theorem step_comp_seqTransHom_apply (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {m n : ℕ} (h : m ≤ n)
    (a : A m) :
    α n (seqTransHom α h a) = seqTransHom α (Nat.le_succ_of_le h) a :=
  DFunLike.congr_fun (step_comp_seqTransHom α h) a

@[simp]
theorem step_comp_step (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) (n : ℕ) :
    (α (n + 1)).comp (α n) = seqTransHom α (Nat.le_add_right n 2) := by
  rw [← seqTransHom_le_succ α n, step_comp_seqTransHom]

@[simp]
theorem step_comp_step_apply (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) (n : ℕ) (a : A n) :
    α (n + 1) (α n a) = seqTransHom α (Nat.le_add_right n 2) a :=
  DFunLike.congr_fun (step_comp_step α n) a

/-- Iterating step `⋆`-homomorphisms `α n : A n →⋆ₙₐ[R] A (n + 1)` forms a `DirectedSystem`. -/
instance directedSystem_seqTransHom (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) :
    DirectedSystem (F := A) (fun _ _ h ↦ ⇑(seqTransHom α h)) where
  map_self _ a := by simp
  map_map _ _ _ hij hjk a := seqTransHom_comp_apply α hij hjk a

/-- If a family of `⋆`-homomorphisms `ξ n : A n →⋆ₙₐ[R] B` is compatible with each step map
`α n`, then it is compatible with all composite transition maps `seqTransHom α h`. -/
theorem comp_seqTransHom_of_comp_eq {B : Type*} [NonUnitalNonAssocSemiring B]
    [DistribMulAction R B] [Star B] {α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)}
    {ξ : ∀ n, A n →⋆ₙₐ[R] B} (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) {m n : ℕ} (h : m ≤ n) :
    (ξ n).comp (seqTransHom α h) = ξ m := by
  induction n, h using Nat.le_induction with
  | base => rw [seqTransHom_self, NonUnitalStarAlgHom.comp_id]
  | succ k hmk ih =>
    rw [seqTransHom_succ α hmk, ← NonUnitalStarAlgHom.comp_assoc, hξ k, ih]

/-- Elementwise form of `comp_seqTransHom_of_comp_eq`: a step-compatible family of
`⋆`-homomorphisms is invariant along composite transition maps `seqTransHom α h`. -/
theorem comp_seqTransHom_apply_of_comp_eq {B : Type*} [NonUnitalNonAssocSemiring B]
    [DistribMulAction R B] [Star B] {α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)}
    {ξ : ∀ n, A n →⋆ₙₐ[R] B} (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) {m n : ℕ} (h : m ≤ n)
    (a : A m) : ξ n (seqTransHom α h a) = ξ m a :=
  DFunLike.congr_fun (comp_seqTransHom_of_comp_eq hξ h) a

/-- If a family of subsets `F n ⊆ A n` is preserved by each step map `α n`, then it is preserved
by all composite transition maps `seqTransHom α h`. -/
theorem seqTransHom_mem {α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)} {F : ∀ n, Set (A n)}
    (hF : ∀ n, ∀ a ∈ F n, α n a ∈ F (n + 1)) {m n : ℕ} (h : m ≤ n) {a : A m} (ha : a ∈ F m) :
    seqTransHom α h a ∈ F n := by
  induction n, h using Nat.le_induction with
  | base => simpa using ha
  | succ k hmk ih =>
    rw [seqTransHom_succ α hmk]
    exact hF k _ ih

end NonUnital

section Unital

variable {R : Type*} [CommSemiring R] {A : ℕ → Type*}
  [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)] [∀ n, Star (A n)]

/-- The composite connecting unital `⋆`-homomorphism `A m →⋆ₐ[R] A n` for `m ≤ n` obtained by
iterating a sequential system `α : ∀ k, A k →⋆ₐ[R] A (k + 1)`. -/
def seqTransStarAlgHom (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {m n : ℕ} (h : m ≤ n) :
    A m →⋆ₐ[R] A n :=
  Nat.leRecOn (motive := fun k ↦ A m →⋆ₐ[R] A k) h (fun {k} f ↦ (α k).comp f) (.id R (A m))

@[simp]
theorem seqTransStarAlgHom_self (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {n : ℕ} (h : n ≤ n) :
    seqTransStarAlgHom α h = .id R (A n) := by
  cases Subsingleton.elim h n.le_refl
  exact Nat.leRecOn_self (motive := fun k ↦ A n →⋆ₐ[R] A k)
    (next := fun {k} f ↦ (α k).comp f) (StarAlgHom.id R (A n))

theorem seqTransStarAlgHom_succ (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {m n : ℕ} (h : m ≤ n)
    (h' : m ≤ n + 1) : seqTransStarAlgHom α h' = (α n).comp (seqTransStarAlgHom α h) := by
  cases Subsingleton.elim h' (Nat.le_add_right_of_le h)
  exact Nat.leRecOn_succ (motive := fun k ↦ A m →⋆ₐ[R] A k) h
    (next := fun {k} f ↦ (α k).comp f) (StarAlgHom.id R (A m))

@[simp]
theorem toNonUnitalStarAlgHom_seqTransStarAlgHom (α : ∀ n, A n →⋆ₐ[R] A (n + 1))
    {m n : ℕ} (h : m ≤ n) :
    (seqTransStarAlgHom α h).toNonUnitalStarAlgHom =
      seqTransHom (fun k ↦ (α k).toNonUnitalStarAlgHom) h := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [seqTransStarAlgHom_self, seqTransHom_self]
    rfl
  | succ k hmk ih =>
    rw [seqTransStarAlgHom_succ α hmk, seqTransHom_succ _ hmk]
    ext a
    simp [← ih]

@[simp]
theorem seqTransStarAlgHom_le_succ (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) (n : ℕ) :
    seqTransStarAlgHom α (Nat.le_succ n) = α n := by
  rw [seqTransStarAlgHom_succ α le_rfl (Nat.le_succ n), seqTransStarAlgHom_self,
    StarAlgHom.comp_id]

@[simp]
theorem seqTransStarAlgHom_comp (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {i j k : ℕ} (hij : i ≤ j)
    (hjk : j ≤ k) :
    (seqTransStarAlgHom α hjk).comp (seqTransStarAlgHom α hij) =
      seqTransStarAlgHom α (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [seqTransStarAlgHom_self, StarAlgHom.id_comp]
  | succ k hjk ih =>
    rw [seqTransStarAlgHom_succ α hjk, seqTransStarAlgHom_succ α (hij.trans hjk),
      StarAlgHom.comp_assoc, ih]

@[simp]
theorem seqTransStarAlgHom_comp_apply (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {i j k : ℕ} (hij : i ≤ j)
    (hjk : j ≤ k) (a : A i) :
    seqTransStarAlgHom α hjk (seqTransStarAlgHom α hij a) =
      seqTransStarAlgHom α (hij.trans hjk) a :=
  DFunLike.congr_fun (seqTransStarAlgHom_comp α hij hjk) a

@[simp]
theorem seqTransStarAlgHom_comp_step (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {m n : ℕ} (h : m + 1 ≤ n) :
    (seqTransStarAlgHom α h).comp (α m) = seqTransStarAlgHom α (Nat.le_of_succ_le h) := by
  rw [← seqTransStarAlgHom_comp α (Nat.le_succ m) h, seqTransStarAlgHom_le_succ]

@[simp]
theorem seqTransStarAlgHom_comp_step_apply (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {m n : ℕ}
    (h : m + 1 ≤ n) (a : A m) :
    seqTransStarAlgHom α h (α m a) = seqTransStarAlgHom α (Nat.le_of_succ_le h) a :=
  DFunLike.congr_fun (seqTransStarAlgHom_comp_step α h) a

@[simp]
theorem step_comp_seqTransStarAlgHom (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {m n : ℕ} (h : m ≤ n) :
    (α n).comp (seqTransStarAlgHom α h) = seqTransStarAlgHom α (Nat.le_succ_of_le h) :=
  (seqTransStarAlgHom_succ α h (Nat.le_succ_of_le h)).symm

@[simp]
theorem step_comp_seqTransStarAlgHom_apply (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) {m n : ℕ} (h : m ≤ n)
    (a : A m) :
    α n (seqTransStarAlgHom α h a) = seqTransStarAlgHom α (Nat.le_succ_of_le h) a :=
  DFunLike.congr_fun (step_comp_seqTransStarAlgHom α h) a

@[simp]
theorem step_comp_step_starAlgHom (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) (n : ℕ) :
    (α (n + 1)).comp (α n) = seqTransStarAlgHom α (Nat.le_add_right n 2) := by
  rw [← seqTransStarAlgHom_le_succ α n, step_comp_seqTransStarAlgHom]

@[simp]
theorem step_comp_step_starAlgHom_apply (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) (n : ℕ) (a : A n) :
    α (n + 1) (α n a) = seqTransStarAlgHom α (Nat.le_add_right n 2) a :=
  DFunLike.congr_fun (step_comp_step_starAlgHom α n) a

/-- Iterating unital step `⋆`-homomorphisms `α n : A n →⋆ₐ[R] A (n + 1)` forms a
`DirectedSystem`. -/
instance directedSystem_seqTransStarAlgHom (α : ∀ n, A n →⋆ₐ[R] A (n + 1)) :
    DirectedSystem (F := A) (fun _ _ h ↦ ⇑(seqTransStarAlgHom α h)) where
  map_self _ a := by simp
  map_map _ _ _ hij hjk a := seqTransStarAlgHom_comp_apply α hij hjk a

end Unital

end TauCeti
