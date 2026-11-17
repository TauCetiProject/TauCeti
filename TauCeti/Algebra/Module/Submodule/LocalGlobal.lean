/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# A local criterion for submodule membership

Membership can be tested by scalar multiples that avoid each maximal ideal.
The ideal of scalars sending the element into the submodule must then be the unit ideal.
-/

public section

/-- If every maximal ideal avoids some scalar sending `x` into `N`, then `x` belongs to `N`. -/
lemma Submodule.mem_of_forall_maximal_exists_smul_mem {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (N : Submodule R M) (x : M)
    (h : ∀ q : Ideal R, q.IsMaximal → ∃ e : R, e ∉ q ∧ e • x ∈ N) : x ∈ N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M x)
  suffices hI : I = ⊤ by
    have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul] using h1
  by_contra hI
  obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨e, heq, he⟩ := h q hq
  exact heq (hIq he)
