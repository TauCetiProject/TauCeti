/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.OneForm.Basic

/-!
# The index of a zero of a Morse one-form

The Morse index of a zero of a Morse closed one-form is the index of any local primitive.
Primitive independence makes this a well-defined natural number, without a chosen global
potential. The index is defined only at zeros; no value is assigned at a nonzero point.
For an exact form it agrees with the manifold Morse index of the potential.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 1.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {α : RoughForm I M ℝ 1} {f : M → ℝ} {U : Set M} {x : M}

namespace IsMorseOneForm

/-- The Morse index of a zero of a Morse one-form, computed using any local primitive. -/
def morseIndex (hα : IsMorseOneForm α) (x : M) (hx : α x = 0) : ℕ :=
  manifoldMorseIndex I (hα.exists_nondegenerate_primitive x hx).choose x

/-- Any local primitive computes the index of a zero of a Morse one-form. -/
theorem morseIndex_eq (hα : IsMorseOneForm α) (hx : α x = 0)
    (hf : IsPrimitiveOn α f U) (hxU : x ∈ U) :
    hα.morseIndex x hx = manifoldMorseIndex I f x := by
  obtain ⟨V, hxV, hg, -⟩ := (hα.exists_nondegenerate_primitive x hx).choose_spec
  exact hg.manifoldMorseIndex_eq hf hxV hxU

/-- The index of a zero is at most the dimension of the manifold. -/
theorem morseIndex_le_finrank [FiniteDimensional ℝ E] (hα : IsMorseOneForm α)
    (hx : α x = 0) : hα.morseIndex x hx ≤ Module.finrank ℝ E :=
  manifoldMorseIndex_le_finrank

/-- The index of an exact Morse one-form is the index of its potential. -/
@[simp]
theorem morseIndex_mextDeriv_ofFunction
    (hα : IsMorseOneForm (mextDeriv (RoughForm.ofFunction I f)))
    (hf : MDifferentiable I 𝓘(ℝ) f) (hx : mextDeriv (RoughForm.ofFunction I f) x = 0) :
    hα.morseIndex x hx = manifoldMorseIndex I f x :=
  hα.morseIndex_eq hx ⟨isOpen_univ, hf.mdifferentiableOn, fun _ _ ↦ rfl⟩ (mem_univ x)

end IsMorseOneForm

end TauCeti
