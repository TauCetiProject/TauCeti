/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.Algebra.Module.PseudoCoherent.Basic

/-!
# Pseudocoherent modules and chain complexes

A pseudocoherent module `M` over a ring `R` (`TauCeti.Huber.IsPseudoCoherentOver R M ⊤`) is
given by a coordinate resolution `⋯ → Rⁿ¹ → Rⁿ⁰ → M → 0`. This file repackages such a resolution
as a chain complex `P` of `R`-modules in nonnegative degrees, each term the coordinate module
`Fin k → R`, together with a quasi-isomorphism `P ⟶ M[0]` to `M` placed in degree zero. This is
the shape in which resolutions are transported along exact functors, for instance to the sheaves
associated with modules on an affine scheme.

## References

* The Stacks Project, Definition 15.66.1 (Tag 064Q).
-/

public section

open CategoryTheory

namespace TauCeti.Huber.IsPseudoCoherentOver

universe u

variable {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M]

/-- A pseudocoherent module `M` has a resolution by a chain complex of coordinate modules
`Fin k → R`: a chain complex `P` in nonnegative degrees whose terms are finite free, together with
a quasi-isomorphism from `P` to `M` placed in degree zero. -/
theorem exists_quasiIso_single₀ (h : IsPseudoCoherentOver R M ⊤) :
    ∃ (P : ChainComplex (ModuleCat.{u} R) ℕ)
      (π : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R M)),
      (∀ i, ∃ k : ℕ, Nonempty (P.X i ≅ ModuleCat.of R (Fin k → R))) ∧ QuasiIso π := by
  obtain ⟨n, d, ε, hε, h₀, hd⟩ := (isPseudoCoherentOver_iff R M ⊤).mp h
  have hd' (i : ℕ) : Function.Exact (d (i + 1)) (d i) := hd i le_top
  have h₀' : Function.Exact (d 0) ε := h₀ le_top
  let P : ChainComplex (ModuleCat.{u} R) ℕ :=
    ChainComplex.of (fun i ↦ ModuleCat.of R (Fin (n i) → R)) (fun i ↦ ModuleCat.ofHom (d i))
      fun i ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦ by
        simpa using (hd' i).apply_apply_eq_zero x
  have hP (i : ℕ) : P.d (i + 1) i = ModuleCat.ofHom (d i) := by simp [P]
  have hP₀ : P.d 1 0 = ModuleCat.ofHom (d 0) := hP 0
  let π : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R M) :=
    (P.toSingle₀Equiv _).symm ⟨ModuleCat.ofHom ε, ModuleCat.hom_ext (LinearMap.ext fun x ↦ by
      simpa [hP₀] using h₀'.apply_apply_eq_zero x)⟩
  have hπ₀ : π.f 0 = ModuleCat.ofHom ε := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
  refine ⟨P, π, fun i ↦ ⟨n i, ⟨Iso.refl _⟩⟩, ⟨fun i ↦ ?_⟩⟩
  cases i with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    refine ⟨?_, ?_⟩
    -- In degree zero the incoming differential is `d 0` and `π` is `ε`; the term `P.X 0` is the
    -- coordinate module `Fin (n 0) → R` by `ChainComplex.of_X`.
    · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      dsimp only [HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_map_τ₂]
      rw [hP₀, hπ₀]
      simp only [ModuleCat.hom_ofHom]
      exact (LinearMap.exact_iff.mp h₀').symm
    · rw [ModuleCat.epi_iff_surjective]
      dsimp only [HomologicalComplex.shortComplexFunctor'_map_τ₂]
      rw [hπ₀]
      exact hε
  | succ i =>
    rw [quasiIsoAt_iff_exactAt' π (i + 1) (ChainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    simpa [hP (i + 1), hP i] using (LinearMap.exact_iff.mp (hd' i)).symm

end TauCeti.Huber.IsPseudoCoherentOver
