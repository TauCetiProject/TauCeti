/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Finite generators before extension of scalars

If an extension of scalars is finitely generated, a finitely generated submodule of the
original module already spans that extension. This does not require faithful flatness:
the submodule need not be the whole original module.
-/

public section

open TensorProduct

namespace TauCeti

/-- If `S ⊗[R] M` is finite over `S`, some finitely generated submodule of `M` spans it
after extension of scalars. No flatness or finiteness of `M` is assumed. -/
theorem exists_fg_baseChange_eq_top (R S M : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] [Module.Finite S (S ⊗[R] M)] :
    ∃ P : Submodule R M, P.FG ∧ P.baseChange S = ⊤ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := S ⊗[R] M)
  obtain ⟨P, hP, hspan⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    (s : Set (S ⊗[R] M)) s.finite_toSet
  refine ⟨P, Module.Finite.iff_fg.mp hP, top_unique ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  obtain ⟨y, rfl⟩ := hspan hx
  exact ⟨y, congr_fun (LinearMap.baseChange_eq_lTensor (A := S) P.subtype) y⟩

end TauCeti
