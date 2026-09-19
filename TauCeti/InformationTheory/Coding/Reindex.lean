/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.InformationTheory.Coding.Basic
public import TauCeti.InformationTheory.Coding.Equivalence

/-!
# Relabelling the coordinates of a linear code

Relabelling the coordinate set of a linear code along an equivalence is the most basic operation
on codes, and every further construction is expected to commute with it. This file defines
`TauCeti.reindex` as the image of the code under coordinate transport, and records membership,
functoriality, the order and lattice laws, and invariance of the dimension.

Neither the field nor the coordinate types are assumed finite.

## Main declarations

* `TauCeti.reindex`: transport of a code along a coordinate equivalence.
* `TauCeti.mem_reindex`: membership characterization, with the direction of the equivalence
  explicit.
* `TauCeti.finrank_reindex`: relabelling coordinates preserves the dimension.
* `TauCeti.isPermutationEquivalent_reindex`: a reindexed code is permutation equivalent to the
  original one.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Chapter 1.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] {ι κ : Type*}

/-- Reindex a linear code along a coordinate equivalence. The equivalence points from the new
coordinate type to the old one, so the transported word has value `x (e j)` at `j`. -/
noncomputable def reindex (C : LinearCode F ι) (e : κ ≃ ι) : LinearCode F κ :=
  C.map (LinearEquiv.funCongrLeft F F e).toLinearMap

/-- Reindexing is the image under coordinate transport. -/
theorem reindex_def (C : LinearCode F ι) (e : κ ≃ ι) :
    reindex C e = C.map (LinearEquiv.funCongrLeft F F e).toLinearMap := (rfl)

/-- Membership in a reindexed code, with the direction of the coordinate equivalence explicit. -/
@[simp]
theorem mem_reindex {C : LinearCode F ι} {e : κ ≃ ι} {y : κ → F} :
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
theorem reindex_refl (C : LinearCode F ι) : reindex C (Equiv.refl ι) = C := by
  rw [reindex_def, LinearEquiv.funCongrLeft_id, LinearEquiv.refl_toLinearMap, Submodule.map_id]

/-- Successive changes of coordinates compose in their contravariant order. -/
@[simp]
theorem reindex_reindex {κ' : Type*} (C : LinearCode F ι) (e : κ ≃ ι) (f : κ' ≃ κ) :
    reindex (reindex C e) f = reindex C (f.trans e) := by
  rw [reindex_def, reindex_def, reindex_def, ← Submodule.map_comp, ← LinearEquiv.coe_trans,
    ← LinearEquiv.funCongrLeft_comp]

/-- Reindexing is monotone in the code. -/
theorem reindex_mono {C D : LinearCode F ι} (h : C ≤ D) (e : κ ≃ ι) :
    reindex C e ≤ reindex D e :=
  Submodule.map_mono h

/-- Reindexing sends the zero code to the zero code. -/
@[simp]
theorem reindex_bot (e : κ ≃ ι) : reindex (⊥ : LinearCode F ι) e = ⊥ := by
  simp [reindex]

/-- Reindexing sends the whole word space to the whole word space. -/
@[simp]
theorem reindex_top (e : κ ≃ ι) : reindex (⊤ : LinearCode F ι) e = ⊤ := by
  simp [reindex]

/-- Reindexing commutes with sums of codes. -/
@[simp]
theorem reindex_sup (C D : LinearCode F ι) (e : κ ≃ ι) :
    reindex (C ⊔ D) e = reindex C e ⊔ reindex D e :=
  Submodule.map_sup _ _ _

/-- Reindexing commutes with intersections of codes. -/
@[simp]
theorem reindex_inf (C D : LinearCode F ι) (e : κ ≃ ι) :
    reindex (C ⊓ D) e = reindex C e ⊓ reindex D e :=
  Submodule.map_inf _ (LinearEquiv.funCongrLeft F F e).injective

/-- Reindexing along a coordinate equivalence is exactly a permutation equivalence of codes. -/
theorem isPermutationEquivalent_reindex (C : LinearCode F ι) (e : κ ≃ ι) :
    IsPermutationEquivalent (reindex C e) C :=
  isPermutationEquivalent_iff.mpr
    ⟨e, by rw [← reindex_def, reindex_reindex, Equiv.symm_trans_self, reindex_refl]⟩

/-- A coordinate equivalence preserves the dimension of a code. -/
@[simp]
theorem finrank_reindex (C : LinearCode F ι) (e : κ ≃ ι) :
    Module.finrank F (reindex C e) = Module.finrank F C := by
  rw [reindex_def, LinearEquiv.finrank_map_eq]

end TauCeti
