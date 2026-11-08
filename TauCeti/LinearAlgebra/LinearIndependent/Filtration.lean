/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Independent generating subfamilies adapted to a filtration

A family of vectors admits an independent generating subfamily that simultaneously generates
every member of a finite increasing filtration of the indices. In particular, the subfamily
can be chosen to contain as many low-weight vectors as their span permits.
-/

public section

namespace TauCeti

open Submodule Set

variable {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- An independent generating subfamily can be chosen so that its intersection with every
member of a finite increasing family of index sets generates the corresponding vector span. -/
theorem exists_linearIndepOn_inter_span_eq (v : ι → V) {n : ℕ} (s : Fin n → Set ι)
    (hs : Monotone s) (t : Set ι) (hst : ∀ i, s i ⊆ t) :
    ∃ b ⊆ t, LinearIndepOn K v b ∧ span K (v '' b) = span K (v '' t) ∧
      ∀ i, span K (v '' (b ∩ s i)) = span K (v '' s i) := by
  induction n generalizing t with
  | zero =>
    obtain ⟨b, hbt, -, hbsp, hbi⟩ :=
      exists_linearIndepOn_extension (v := v) (linearIndepOn_empty K v) (empty_subset t)
    refine ⟨b, hbt, hbi, le_antisymm (span_mono (image_mono hbt))
      (span_le.mpr hbsp), fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨a, has, hai, hasp, ha⟩ := ih (fun i ↦ s i.castSucc)
      (hs.comp (fun _ _ h ↦ h)) (s (Fin.last n))
      (fun i ↦ hs (Fin.le_last i.castSucc))
    obtain ⟨b, hbt, hab, hbsp, hbi⟩ :=
      exists_linearIndepOn_extension hai (has.trans (hst _))
    refine ⟨b, hbt, hbi, le_antisymm (span_mono (image_mono hbt))
      (span_le.mpr hbsp), ?_⟩
    intro i
    refine le_antisymm (span_mono (image_mono inter_subset_right)) ?_
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [← hasp]
      exact span_mono (image_mono (subset_inter hab has))
    · rw [← ha j]
      exact span_mono (image_mono (inter_subset_inter_left _ hab))

end TauCeti
