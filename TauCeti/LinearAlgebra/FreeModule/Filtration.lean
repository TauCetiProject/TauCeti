/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import TauCeti.LinearAlgebra.DirectSum.Filtration

/-!
# Free modules with an exhaustive filtration by free subquotients

Let `N 0 ≤ N 1 ≤ ⋯` be an increasing sequence of submodules of `M`, with `N 0` free and
supremum `⊤`. If every subquotient `N (j + 1) ⧸ N j` is free, then `M` is free. Splitting each
subquotient off `N (j + 1)` identifies `M` with the direct sum of `N 0` and the subquotients.

No finiteness is assumed: this is the form needed when a module that is not finitely generated
over the base, such as a polynomial ring, is filtered by degree.

## Main declarations

* `Module.Free.of_filtration`: a module with an exhaustive filtration by free subquotients is
  free.
-/

public section

open DirectSum

namespace Module.Free

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A module with an exhaustive increasing filtration `⊥ = N 0 ≤ N 1 ≤ ⋯`, all of whose
subquotients `N (j + 1) ⧸ N j` are free, is free. -/
private theorem of_filtration_of_bot (N : ℕ → Submodule R M) (hN : Monotone N) (h0 : N 0 = ⊥)
    (htop : ⨆ j, N j = ⊤)
    (hfree : ∀ j, Module.Free R (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1)))) :
    Module.Free R M := by
  classical
  let Q : ℕ → Type _ := fun j ↦ N (j + 1) ⧸ (N j).submoduleOf (N (j + 1))
  -- `Q` is a local abbreviation, so its additive groups are recorded for the direct sum.
  let _ (j : ℕ) : AddCommGroup (Q j) := Submodule.Quotient.addCommGroup _
  -- Split each subquotient off the next filtration step.
  have hsplit : ∀ j, ∃ s : Q j →ₗ[R] N (j + 1),
      ((N j).submoduleOf (N (j + 1))).mkQ ∘ₗ s = LinearMap.id := fun j ↦
    LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)
  choose s hs using hsplit
  have hs' (j : ℕ) (q : Q j) : Submodule.Quotient.mk (s j q) = q :=
    LinearMap.congr_fun (hs j) q
  let f (j : ℕ) : Q j →ₗ[R] M := (N (j + 1)).subtype ∘ₗ s j
  have hψinj : Function.Injective (DirectSum.toModule R ℕ M f) :=
    DirectSum.toModule_injective_of_filtration N hN f (fun j q ↦ (s j q).2) fun j q hq ↦ by
      rw [← hs' j q, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_comap.mpr hq
  have hψsurj : Function.Surjective (DirectSum.toModule R ℕ M f) :=
    DirectSum.toModule_surjective_of_filtration N h0 htop f fun J x hx ↦ by
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      have hmem : (⟨x, hx⟩ - s J (Submodule.Quotient.mk ⟨x, hx⟩) : N (J + 1)) ∈
          (N J).submoduleOf (N (J + 1)) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hs', sub_self]
      simpa [f] using Submodule.mem_comap.mp hmem
  exact Module.Free.of_equiv (LinearEquiv.ofBijective _ ⟨hψinj, hψsurj⟩)

/-- A module with an exhaustive increasing filtration `N 0 ≤ N 1 ≤ ⋯`, whose initial term
and successive subquotients `N (j + 1) ⧸ N j` are free, is free. -/
theorem of_filtration (N : ℕ → Submodule R M) (hN : Monotone N)
    (h0 : Module.Free R (N 0)) (htop : ⨆ j, N j = ⊤)
    (hfree : ∀ j, Module.Free R (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1)))) :
    Module.Free R M := by
  -- Prepend zero so that the initial free module is also a successive subquotient.
  let P : ℕ → Submodule R M
    | 0 => ⊥
    | j + 1 => N j
  refine of_filtration_of_bot P (monotone_nat_of_le_succ fun j ↦ ?_) rfl ?_ ?_
  · cases j with
    | zero => exact bot_le
    | succ j => exact hN j.le_succ
  · apply top_unique
    rw [← htop]
    exact iSup_le fun j ↦ le_iSup P (j + 1)
  · intro j
    cases j with
    | zero =>
      exact Module.Free.of_equiv (Submodule.quotEquivOfEqBot _
        ((Submodule.comap_bot _).trans (Submodule.ker_subtype _))).symm
    | succ j => exact hfree j

end Module.Free
