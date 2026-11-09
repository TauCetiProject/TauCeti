/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Normed.Affine.Generic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exceptional arrangements

An *exceptional arrangement* in a real vector space is a finite set of proper affine subspaces,
the exceptions, which a generic point avoids. Empty exceptions are allowed. Arrangements are
closed under unions and under transport along affine equivalences, which preserves genericity.

In a finite-dimensional real normed space, the generic points of an arrangement form an open dense
set, and the common generic points of countably many arrangements form a dense `Gδ` set. The common
generic locus of infinitely many arrangements need not be open, and a common generic point need not
have a generic neighbourhood: `ExceptionalArrangement.point` for the points `1 / (j + 1)` of the
real line gives a family of single-point arrangements whose common generic locus is not open.

A line starting at a generic point meets an arrangement at only finitely many parameters.

## Attribution

Adapted from `Mei/Geometry/Affine/Generic.lean`, `Mei/Geometry/Affine/Generic/Line.lean` and
`Mei/Geometry/Affine/Generic/Examples.lean` in Mei at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/Affine/Generic.lean
-/

public section

namespace TauCeti

/-- A finite collection of proper affine subspaces to be avoided. Repeated
exceptions are identified. Empty affine subspaces are permitted. -/
@[ext]
structure ExceptionalArrangement (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The finite set of affine subspaces to avoid. -/
  exceptions : Finset (AffineSubspace ℝ V)
  /-- No exception contains the whole ambient space. -/
  proper : ∀ S ∈ exceptions, S ≠ ⊤

namespace ExceptionalArrangement

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A point is generic if it avoids every affine exception. -/
def IsGeneric (E : ExceptionalArrangement V) (x : V) : Prop :=
  ∀ S ∈ E.exceptions, x ∉ S

theorem isGeneric_iff {E : ExceptionalArrangement V} {x : V} :
    E.IsGeneric x ↔ ∀ S ∈ E.exceptions, x ∉ S := (Iff.rfl)

/-- Union of the exceptions in two arrangements. -/
noncomputable def union (E F : ExceptionalArrangement V) : ExceptionalArrangement V := by
  classical
  exact ⟨E.exceptions ∪ F.exceptions, fun S h =>
    (Finset.mem_union.mp h).elim (E.proper S) (F.proper S)⟩

open Classical in
/-- The exceptions of a union are the union of the exceptions. -/
@[simp]
theorem exceptions_union (E F : ExceptionalArrangement V) :
    (E.union F).exceptions = E.exceptions ∪ F.exceptions := (rfl)

/-- Genericity for a union is genericity for each arrangement. -/
@[simp]
theorem isGeneric_union {E F : ExceptionalArrangement V} {x : V} :
    (E.union F).IsGeneric x ↔ E.IsGeneric x ∧ F.IsGeneric x := by
  classical
  simp [IsGeneric, union, or_imp, forall_and]

/-- Transport an arrangement by an affine equivalence. -/
noncomputable def map (E : ExceptionalArrangement V) (e : V ≃ᵃ[ℝ] W) :
    ExceptionalArrangement W := by
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
theorem exceptions_map (E : ExceptionalArrangement V) (e : V ≃ᵃ[ℝ] W) :
    (E.map e).exceptions = E.exceptions.image (AffineSubspace.map e.toAffineMap) := (rfl)

/-- A point is generic for a transported arrangement exactly when its preimage is generic. -/
@[simp]
theorem isGeneric_map_iff {E : ExceptionalArrangement V} {e : V ≃ᵃ[ℝ] W} {y : W} :
    (E.map e).IsGeneric y ↔ E.IsGeneric (e.symm y) := by
  obtain ⟨x, rfl⟩ := e.surjective y
  classical
  simp [IsGeneric, map]

/-- Pullback under an affine equivalence, expressed by transport under its inverse. -/
noncomputable def comap (E : ExceptionalArrangement W) (e : V ≃ᵃ[ℝ] W) :
    ExceptionalArrangement V :=
  E.map e.symm

open Classical in
/-- Pullback maps the exceptions by the inverse affine equivalence. -/
@[simp]
theorem exceptions_comap (E : ExceptionalArrangement W) (e : V ≃ᵃ[ℝ] W) :
    (E.comap e).exceptions = E.exceptions.image (AffineSubspace.map e.symm.toAffineMap) :=
  (rfl)

/-- A point is generic in a pullback exactly when its image is generic. -/
@[simp]
theorem isGeneric_comap_iff {E : ExceptionalArrangement W} {e : V ≃ᵃ[ℝ] W} {x : V} :
    (E.comap e).IsGeneric x ↔ E.IsGeneric (e x) := by
  -- `e.symm.symm x` is `e x` by unfolding `AffineEquiv.symm`; Mathlib has no `symm_symm` lemma
  exact isGeneric_map_iff

/-- The arrangement whose only exception is a point, in a nontrivial space. -/
noncomputable def point [Nontrivial V] (p : V) : ExceptionalArrangement V :=
  ⟨{AffineSubspace.mk' p ⊥}, fun S hS htop => by
    obtain rfl := Finset.mem_singleton.mp hS
    simpa [AffineSubspace.direction_mk'] using congrArg AffineSubspace.direction htop⟩

/-- The only exception of `point p` is the subspace `{p}`. -/
@[simp]
theorem exceptions_point [Nontrivial V] (p : V) :
    (point p).exceptions = {AffineSubspace.mk' p ⊥} := (rfl)

/-- A point is generic for `point p` exactly when it differs from `p`. -/
@[simp]
theorem isGeneric_point_iff [Nontrivial V] {p x : V} : (point p).IsGeneric x ↔ x ≠ p := by
  simp [IsGeneric, point, AffineSubspace.mem_mk', vsub_eq_sub, sub_eq_zero]

/-- A line starting at a generic point meets an arrangement at finitely many parameter values.
No transversality or distinctness assumption on its second endpoint is required. -/
theorem finite_setOf_not_isGeneric_lineMap (E : ExceptionalArrangement V)
    {x : V} (hx : E.IsGeneric x) (y : V) :
    {t : ℝ | ¬ E.IsGeneric (AffineMap.lineMap x y t)}.Finite := by
  have hS (S : AffineSubspace ℝ V) (hS : S ∈ E.exceptions) :
      {t : ℝ | AffineMap.lineMap x y t ∈ S}.Subsingleton :=
    S.subsingleton_preimage_of_notMem (AffineMap.lineMap x y)
      (t₀ := 0) (by simpa only [AffineMap.lineMap_apply_zero] using hx S hS)
  have he : {t : ℝ | ¬ E.IsGeneric (AffineMap.lineMap x y t)} =
      ⋃ S ∈ E.exceptions, {t : ℝ | AffineMap.lineMap x y t ∈ S} := by
    ext t
    simp only [Set.mem_ofPred_eq, isGeneric_iff, not_forall, not_not, Set.mem_iUnion,
      exists_prop]
  rw [he]
  exact E.exceptions.finite_toSet.biUnion fun S hmem => (hS S hmem).finite

section Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- Generic points of an arrangement form an open set. -/
theorem isOpen_setOf_isGeneric (E : ExceptionalArrangement X) : IsOpen {x | E.IsGeneric x} := by
  simpa [IsGeneric] using AffineSubspace.isOpen_setOf_forall_notMem (fun S : E.exceptions => S.1)

/-- Generic points of an arrangement form a dense set. -/
theorem dense_setOf_isGeneric (E : ExceptionalArrangement X) : Dense {x | E.IsGeneric x} := by
  simpa [IsGeneric] using AffineSubspace.dense_setOf_forall_notMem
    (fun S : E.exceptions => S.1) (fun S => E.proper S.1 S.2)

/-- The common generic points of countably many arrangements form a dense set. -/
theorem dense_setOf_forall_isGeneric {ι : Type*} [Countable ι]
    (E : ι → ExceptionalArrangement X) : Dense {x | ∀ i, (E i).IsGeneric x} := by
  simpa [IsGeneric, Sigma.forall] using
    AffineSubspace.dense_setOf_forall_notMem (fun p : Σ i, (E i).exceptions => p.2.1)
      (fun p => (E p.1).proper p.2.1 p.2.2)

/-- The common generic points of countably many arrangements form a `Gδ` set. -/
theorem isGδ_setOf_forall_isGeneric {ι : Type*} [Countable ι]
    (E : ι → ExceptionalArrangement X) : IsGδ {x | ∀ i, (E i).IsGeneric x} := by
  simpa [IsGeneric, Sigma.forall] using
    AffineSubspace.isGδ_setOf_forall_notMem (fun p : Σ i, (E i).exceptions => p.2.1)

end Topology

/-- The common generic locus of the arrangements `point (1 / (j + 1))` of the real line is not
open: the exceptional points `1 / (j + 1)` accumulate at `0`, which is a common generic point.
This contrasts with the finite case `isOpen_setOf_isGeneric`. -/
theorem not_isOpen_setOf_forall_isGeneric_point :
    ¬ IsOpen {x : ℝ | ∀ j : ℕ, (point (1 / ((j : ℝ) + 1))).IsGeneric x} := by
  intro hopen
  have h0 : (0 : ℝ) ∈ {x : ℝ | ∀ j : ℕ, (point (1 / ((j : ℝ) + 1))).IsGeneric x} := by
    intro j
    rw [isGeneric_point_iff]
    positivity
  obtain ⟨j, hj⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (hopen.mem_nhds h0)).exists
  exact isGeneric_point_iff.mp (hj j) rfl

end ExceptionalArrangement

end TauCeti
