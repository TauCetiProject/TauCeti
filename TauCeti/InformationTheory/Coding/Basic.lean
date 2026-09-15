/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Map

/-!
# Linear codes

A linear code over `R` on coordinates `ι` is a submodule of the word space `ι → R`. This file
introduces the carrier `LinearCode` and the basic operation of relabelling the coordinates along
an equivalence, which every construction on codes is expected to commute with.

Nothing here requires the alphabet or the coordinate type to be finite: a semiring suffices.

## Main declarations

* `LinearCode`: the unbundled linear-code carrier `Submodule R (ι → R)`.
* `reindex`: transport of a code along a coordinate equivalence.
* `mem_reindex`: membership characterization, with the direction of the equivalence explicit.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Chapter 1.
-/

public section

namespace TauCeti

universe u v w

/-- A linear code over `R` on coordinates `ι`, represented by its submodule of words. -/
abbrev LinearCode (R : Type u) [Semiring R] (ι : Type v) := Submodule R (ι → R)

variable {R : Type u} [Semiring R] {ι : Type v}

/-- Reindex a linear code along a coordinate equivalence. The equivalence points from the new
coordinate type to the old one, so the transported word has value `x (e j)` at `j`. -/
noncomputable def reindex {κ : Type w} (C : LinearCode R ι) (e : κ ≃ ι) : LinearCode R κ :=
  C.map (LinearEquiv.funCongrLeft R R e).toLinearMap

/-- Reindexing is the image under coordinate transport. -/
theorem reindex_def {κ : Type w} (C : LinearCode R ι) (e : κ ≃ ι) :
    reindex C e = C.map (LinearEquiv.funCongrLeft R R e).toLinearMap := (rfl)

/-- Membership in a reindexed code, with the direction of the coordinate equivalence explicit. -/
@[simp]
theorem mem_reindex {κ : Type w} {C : LinearCode R ι} {e : κ ≃ ι} {y : κ → R} :
    y ∈ reindex C e ↔ ∃ x ∈ C, ∀ j, x (e j) = y j := by
  rw [reindex, Submodule.mem_map]
  constructor
  · rintro ⟨x, hxC, rfl⟩
    exact ⟨x, hxC, fun _ ↦ rfl⟩
  · rintro ⟨x, hxC, hxy⟩
    refine ⟨x, hxC, ?_⟩
    ext j
    exact hxy j

/-- Reindexing along the identity equivalence leaves a code unchanged. -/
@[simp]
theorem reindex_refl (C : LinearCode R ι) : reindex C (Equiv.refl ι) = C := by
  ext x
  simp only [mem_reindex, Equiv.refl_apply]
  exact ⟨fun ⟨y, hy, hxy⟩ ↦ (funext hxy).symm ▸ hy, fun hx ↦ ⟨x, hx, fun _ ↦ rfl⟩⟩

/-- Successive changes of coordinates compose in their contravariant order. -/
@[simp]
theorem reindex_trans {κ : Type w} {κ' : Type*} (C : LinearCode R ι)
    (e : κ ≃ ι) (f : κ' ≃ κ) :
    reindex (reindex C e) f = reindex C (f.trans e) := by
  ext x
  simp only [mem_reindex, Equiv.trans_apply]
  constructor
  · rintro ⟨y, ⟨z, hzC, hzy⟩, hyx⟩
    exact ⟨z, hzC, fun j ↦ (hzy (f j)).trans (hyx j)⟩
  · rintro ⟨z, hzC, hzx⟩
    exact ⟨fun j ↦ z (e j), ⟨z, hzC, fun _ ↦ rfl⟩, hzx⟩

/-- Reindexing is monotone in the code. -/
theorem reindex_mono {κ : Type w} {C D : LinearCode R ι} (h : C ≤ D) (e : κ ≃ ι) :
    reindex C e ≤ reindex D e :=
  Submodule.map_mono h

/-- Reindexing sends the zero code to the zero code. -/
@[simp]
theorem reindex_bot {κ : Type w} (e : κ ≃ ι) : reindex (⊥ : LinearCode R ι) e = ⊥ := by
  simp [reindex]

/-- Reindexing sends the whole word space to the whole word space. -/
@[simp]
theorem reindex_top {κ : Type w} (e : κ ≃ ι) : reindex (⊤ : LinearCode R ι) e = ⊤ := by
  simp [reindex]

/-- Reindexing commutes with sums of codes. -/
@[simp]
theorem reindex_sup {κ : Type w} (C D : LinearCode R ι) (e : κ ≃ ι) :
    reindex (C ⊔ D) e = reindex C e ⊔ reindex D e :=
  Submodule.map_sup _ _ _

/-- Reindexing commutes with intersections of codes. -/
@[simp]
theorem reindex_inf {κ : Type w} (C D : LinearCode R ι) (e : κ ≃ ι) :
    reindex (C ⊓ D) e = reindex C e ⊓ reindex D e :=
  Submodule.map_inf _ (LinearEquiv.funCongrLeft R R e).injective

end TauCeti
