/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.AlgHom
public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic

/-!
# Naturality of completed exponentials and logarithms

A filtered ring or algebra map preserving the first ideal induces a map of exponential
coordinates. The cutoff modulus may change orders. Preservation of the first
ideal is a separate hypothesis: continuity alone need not preserve that ideal.

We use the existing completion maps (`mapCompletion` and `mapCompletionₐ`) and naturality of
finite nilpotent exponentials and logarithms. All statements allow noncommutative rational
algebras and noninjective maps.

Adapted from `Mei/RingTheory/FilteredAlgebra/Exp/Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace TauCeti.AlgFiltration

variable {A B : Type*} [Ring A] [Ring B]
  (F : AlgFiltration A) (G : AlgFiltration B)
  (f : A →+* B) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap f)
  (h₁ : F.ideal 1 ≤ (G.ideal 1).comap f)

variable [Algebra ℚ A] [Algebra ℚ B]

/-- Completed exponentiation commutes with filtered ring maps preserving the first ideal. -/
@[simp]
theorem mapCompletion_completedExp (x : F.completionIdeal 1) :
    F.mapCompletion G f l hl hf (F.completedExp x) =
      G.completedExp ⟨F.mapCompletion G f l hl hf x,
        F.mapCompletion_mem_first G f l hl hf h₁ x.property⟩ := by
  apply G.completion_ext
  intro k
  rw [projection_mapCompletion, projection_completedExp, projection_completedExp,
    projection_mapCompletion]
  exact (F.isNilpotent_projection x.property (l k)).map_exp _

/-- Completed logarithms commute with the same maps on elements congruent to one. -/
@[simp]
theorem mapCompletion_completedLog
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.mapCompletion G f l hl hf (F.completedLog u) =
      G.completedLog ⟨F.mapCompletion G f l hl hf u, by
        simpa only [map_sub, map_one] using
          F.mapCompletion_mem_first G f l hl hf h₁ u.property⟩ := by
  apply G.completion_ext
  intro k
  rw [projection_mapCompletion, projection_completedLog, projection_completedLog,
    projection_mapCompletion]
  have hu : IsNilpotent (F.projection (l k) u - 1) := by
    simpa only [map_sub, map_one] using F.isNilpotent_projection u.property (l k)
  exact hu.map_log _

section AlgHom

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  (F : AlgFiltration A) (G : AlgFiltration B)
  (f : A →ₐ[R] B) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap f)
  (h₁ : F.ideal 1 ≤ (G.ideal 1).comap f)

variable [Algebra ℚ A] [Algebra ℚ B]

/-- Completed exponentiation commutes with filtered algebra maps preserving the first ideal. -/
@[simp]
theorem mapCompletionₐ_completedExp (x : F.completionIdeal 1) :
    F.mapCompletionₐ G f l hl hf (F.completedExp x) =
      G.completedExp ⟨F.mapCompletionₐ G f l hl hf x,
        F.mapCompletionₐ_mem_first G f l hl hf h₁ x.property⟩ := by
  simpa only [← F.coe_mapCompletionₐ G f l hl hf, AlgHom.coe_toRingHom] using
    F.mapCompletion_completedExp G (f : A →+* B) l hl hf h₁ x

/-- Completed logarithms commute with filtered algebra maps preserving the first ideal. -/
@[simp]
theorem mapCompletionₐ_completedLog
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.mapCompletionₐ G f l hl hf (F.completedLog u) =
      G.completedLog ⟨F.mapCompletionₐ G f l hl hf u, by
        simpa only [map_sub, map_one] using
          F.mapCompletionₐ_mem_first G f l hl hf h₁ u.property⟩ := by
  simpa only [← F.coe_mapCompletionₐ G f l hl hf, AlgHom.coe_toRingHom] using
    F.mapCompletion_completedLog G (f : A →+* B) l hl hf h₁ u

end AlgHom

end TauCeti.AlgFiltration
