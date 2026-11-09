/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Generic loci and finite affine arrangements

The generic locus of an affine family consists of the points avoiding every member.
Finite exceptional arrangements support union and transport by affine equivalences,
over an arbitrary ring, with points in an affine space whose direction module is
implicit. No topology or chosen origin is required.

Adapted from `Mei/Geometry/Affine/Generic.lean` at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`:
https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Geometry/Affine/Generic.lean
-/

public section

open Set
open scoped Affine

namespace AffineSubspace

variable {k : Type*} [Ring k] {V P : Type*}
  [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The points avoiding every member of an affine family. -/
def genericLocus {ι : Sort*} (A : ι → AffineSubspace k P) : Set P :=
  {x | ∀ i, x ∉ A i}

/-- Membership in the generic locus means avoiding each exception. -/
@[simp]
theorem mem_genericLocus {ι : Sort*} {A : ι → AffineSubspace k P} {x : P} :
    x ∈ genericLocus A ↔ ∀ i, x ∉ A i := Iff.rfl

/-- The generic locus is the intersection of the complements. -/
theorem genericLocus_eq_iInter {ι : Sort*} (A : ι → AffineSubspace k P) :
    genericLocus A = ⋂ i, (A i : Set P)ᶜ := by
  ext x
  simp

end AffineSubspace

namespace TauCeti

/-- A finite collection of proper affine subspaces to be avoided. Repeated
exceptions are identified. Empty affine subspaces are permitted. -/
structure ExceptionalArrangement (k : Type*) [Ring k] {V : Type*}
    [AddCommGroup V] [Module k V] (P : Type*) [AffineSpace V P] where
  /-- The finite set of affine subspaces to avoid. -/
  exceptions : Finset (AffineSubspace k P)
  /-- No exception contains the whole ambient space. -/
  proper : ∀ S ∈ exceptions, S ≠ ⊤

namespace ExceptionalArrangement

variable {k : Type*} [Ring k] {V W P Q : Type*}
  [AddCommGroup V] [Module k V] [AffineSpace V P]
  [AddCommGroup W] [Module k W] [AffineSpace W Q]

/-- A point is generic if it avoids every affine exception. -/
def IsGeneric (E : ExceptionalArrangement k P) (x : P) : Prop :=
  ∀ S ∈ E.exceptions, x ∉ S

/-- A point is generic exactly when it avoids every exception. -/
theorem isGeneric_iff {E : ExceptionalArrangement k P} {x : P} :
    E.IsGeneric x ↔ ∀ S ∈ E.exceptions, x ∉ S := (Iff.rfl)

/-- Union of the exceptions in two arrangements. -/
noncomputable def union (E F : ExceptionalArrangement k P) : ExceptionalArrangement k P := by
  classical
  exact ⟨E.exceptions ∪ F.exceptions, fun S h =>
    (Finset.mem_union.mp h).elim (E.proper S) (F.proper S)⟩

open Classical in
/-- The exceptions of a union are the union of the exceptions. -/
@[simp]
theorem exceptions_union (E F : ExceptionalArrangement k P) :
    (E.union F).exceptions = E.exceptions ∪ F.exceptions := (rfl)

/-- Genericity for a union is genericity for each arrangement. -/
@[simp]
theorem isGeneric_union {E F : ExceptionalArrangement k P} {x : P} :
    (E.union F).IsGeneric x ↔ E.IsGeneric x ∧ F.IsGeneric x := by
  classical
  simp [IsGeneric, union, or_imp, forall_and]

/-- Transport an arrangement by an affine equivalence. -/
noncomputable def map (E : ExceptionalArrangement k P) (e : P ≃ᵃ[k] Q) :
    ExceptionalArrangement k Q := by
  classical
  refine ⟨E.exceptions.image (AffineSubspace.map e.toAffineMap), ?_⟩
  intro T hT htop
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
  apply E.proper S hS
  apply top_unique
  intro x _
  apply (AffineSubspace.mem_map_iff_mem_of_injective (f := e.toAffineMap) e.injective).mp
  rw [htop]
  trivial

open Classical in
/-- Transport maps the finite set of exceptions by the affine equivalence. -/
@[simp]
theorem exceptions_map (E : ExceptionalArrangement k P) (e : P ≃ᵃ[k] Q) :
    (E.map e).exceptions = E.exceptions.image (AffineSubspace.map e.toAffineMap) := (rfl)

/-- Transport preserves genericity of the corresponding points. -/
@[simp]
theorem isGeneric_map_iff {E : ExceptionalArrangement k P} (e : P ≃ᵃ[k] Q) {x : P} :
    (E.map e).IsGeneric (e x) ↔ E.IsGeneric x := by
  classical
  simp [IsGeneric, map]

/-- Pullback under an affine equivalence, expressed by transport under its inverse. -/
noncomputable def comap (E : ExceptionalArrangement k Q) (e : P ≃ᵃ[k] Q) :
    ExceptionalArrangement k P :=
  E.map e.symm

open Classical in
/-- Pullback maps the exceptions by the inverse affine equivalence. -/
@[simp]
theorem exceptions_comap (E : ExceptionalArrangement k Q) (e : P ≃ᵃ[k] Q) :
    (E.comap e).exceptions = E.exceptions.image (AffineSubspace.map e.symm.toAffineMap) :=
  (rfl)

/-- A point is generic in a pullback exactly when its image is generic. -/
@[simp]
theorem isGeneric_comap_iff {E : ExceptionalArrangement k Q} {e : P ≃ᵃ[k] Q} {x : P} :
    (E.comap e).IsGeneric x ↔ E.IsGeneric (e x) := by
  simpa [comap] using (isGeneric_map_iff (E := E) e.symm (x := e x))

end ExceptionalArrangement

end TauCeti
