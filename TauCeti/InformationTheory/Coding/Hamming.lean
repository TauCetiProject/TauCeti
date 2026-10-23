/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Basic
public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear codes in Hamming space

A linear code uses the function space `ι → F`, while Mathlib's `Hamming` type synonym equips
the same words with their Hamming metric. Transporting a code through the canonical linear
equivalence gives a submodule of Hamming space with exactly the original codewords. This
bridge lets metric statements such as `Set.infsep` apply directly to the transported code,
while preserving the linear structure and dimension.

The Hamming-space convention and minimum-distance comparison follow Cristina Dueñas Navarro's
[Mathlib coding-theory PR #38014](https://github.com/leanprover-community/mathlib4/pull/38014).
-/

public section

namespace TauCeti

variable {F ι : Type*} [Field F]

/-- A linear code transported to Mathlib's Hamming-space type synonym. -/
noncomputable def toHammingCode (C : LinearCode F ι) :
    Submodule F (Hamming (fun _ : ι ↦ F)) :=
  C.map (LinearEquiv.refl F (ι → F) : (ι → F) ≃ₗ[F] Hamming (fun _ : ι ↦ F)).toLinearMap

/-- The Hamming-space transport is the image under the identity linear equivalence. -/
theorem toHammingCode_def (C : LinearCode F ι) :
    toHammingCode C =
      C.map (LinearEquiv.refl F (ι → F) :
        (ι → F) ≃ₗ[F] Hamming (fun _ : ι ↦ F)).toLinearMap := by
  unfold toHammingCode
  rfl

/-- A Hamming-space word belongs to the transported code exactly when its underlying
function belongs to the original code. -/
@[simp]
theorem mem_toHammingCode_iff (C : LinearCode F ι)
    (x : Hamming (fun _ : ι ↦ F)) :
    x ∈ toHammingCode C ↔ Hamming.ofHamming x ∈ C := by
  -- `Hamming` is a type synonym, so the inverse of `refl` is `ofHamming` by definition.
  exact (Submodule.mem_map_equiv C (e :=
    (LinearEquiv.refl F (ι → F) : (ι → F) ≃ₗ[F] Hamming (fun _ : ι ↦ F)))
    (x := x)).trans (by rfl)

/-- The underlying set of the transported code is the image of the original codewords. -/
theorem coe_toHammingCode (C : LinearCode F ι) :
    (toHammingCode C : Set (Hamming (fun _ : ι ↦ F))) =
      Hamming.toHamming '' (C : Set (ι → F)) := by
  -- The underlying map of `refl` is `toHamming` by definition.
  exact (Submodule.map_coe
    (LinearEquiv.refl F (ι → F) : (ι → F) ≃ₗ[F] Hamming (fun _ : ι ↦ F)).toLinearMap
    C).trans (by rfl)

/-- A code and its Hamming-space transport have the same dimension. -/
@[simp]
theorem finrank_toHammingCode (C : LinearCode F ι) :
    Module.finrank F (toHammingCode C) = Module.finrank F C := by
  exact (LinearEquiv.refl F (ι → F) :
    (ι → F) ≃ₗ[F] Hamming (fun _ : ι ↦ F)).finrank_map_eq C

/-- The minimum distance of a code is the metric infimum separation of its Hamming-space
transport, including the zero and singleton codes. -/
theorem hammingMinDist_eq_infsep_toHammingCode [Fintype ι] [DecidableEq F]
    (C : LinearCode F ι) :
    (Set.hammingMinDist (C : Set (ι → F)) : ℝ) =
      (toHammingCode C : Set (Hamming (fun _ : ι ↦ F))).infsep := by
  rw [Set.hammingMinDist_eq_infsep, ← coe_toHammingCode]

end TauCeti
