/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module

import TauCeti.Order.WellFounded.Infimum

/-!
# Artinian modules embed into finite powers of a separating module

In an Artinian module every indexed intersection of submodules is already the intersection of a
finite subfamily (`WellFoundedLT.exists_finset_iInf_eq`). Consequently, if the linear maps from an
Artinian module `M` to a module `E` separate the points of `M`, then finitely many of them already
do: `M` embeds into a finite power `Eⁿ` (`IsArtinian.exists_injective_linearMap_pi`).

For an injective cogenerator `E`, for instance the injective hull of the residue field of a local
ring, this embedding of an Artinian module into a finite sum of copies of `E` is the first step of
Matlis duality for Artinian modules.

## References

* The Stacks Project, Lemma 47.7.6, Tag 08Z7.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

variable {R : Type*} [Ring R] {M E : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup E] [Module R E]

/-- **An Artinian module embeds into a finite power of a module separating its points.** If every
nonzero element of an Artinian module `M` is detected by a linear map to `E`, then there is an
injective linear map `M → Eⁿ` for some `n`. -/
theorem IsArtinian.exists_injective_linearMap_pi [IsArtinian R M]
    (h : ∀ m : M, m ≠ 0 → ∃ f : M →ₗ[R] E, f m ≠ 0) :
    ∃ (n : ℕ) (g : M →ₗ[R] Fin n → E), Function.Injective g := by
  -- Finitely many maps `M → E` already cut out the common kernel of all of them, which is zero.
  obtain ⟨s, hs⟩ :=
    WellFoundedLT.exists_finset_iInf_eq fun f : M →ₗ[R] E ↦ LinearMap.ker f
  refine ⟨s.card, LinearMap.pi fun i ↦ (s.equivFin.symm i).val,
    (injective_iff_map_eq_zero _).2 fun m hm ↦ ?_⟩
  -- Each map in `s` is a coordinate of the product map, as `s.equivFin.symm` is surjective.
  have hmem : m ∈ ⨅ g ∈ s, LinearMap.ker g := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro g hg
    obtain ⟨i, hi⟩ := s.equivFin.symm.surjective ⟨g, hg⟩
    simpa [hi] using congr_fun hm i
  rw [hs] at hmem
  by_contra hm0
  obtain ⟨f, hf⟩ := h m hm0
  exact hf ((Submodule.mem_iInf _).1 hmem f)
