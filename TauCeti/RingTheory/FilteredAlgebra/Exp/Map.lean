/-
Copyright (c) 2026 The Tau Ceti contributors and Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic
public import TauCeti.RingTheory.FilteredAlgebra.Map

/-!
# Naturality of completed exponentials and logarithms

A filtered ring map preserving the first ideal induces a map of exponential
coordinates. The cutoff modulus may change orders. Preservation of the first
ideal is a separate hypothesis: continuity alone need not preserve that ideal.

More generally, any map between completions computed at each order `k` by a ring homomorphism on the
quotient rings commutes with `completedExp` and `completedLog` (`map_completedExp_of_projection`,
`map_completedLog_of_projection`), applying directly to opaque maps like completed coproducts.

We use the existing completion map and naturality of finite nilpotent
exponentials and logarithms. All statements allow noncommutative rational
algebras and noninjective maps.

Adapted from `Mei/RingTheory/FilteredAlgebra/Exp/Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0), generalized with projection naturality.
-/

public section

namespace TauCeti.AlgFiltration

section Projection

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
  (F : AlgFiltration A) (G : AlgFiltration B)

/-- A map between completions computed at each order `k` by a ring homomorphism on quotients
commutes with `completedExp` on elements sent into `G.completionIdeal 1`. -/
theorem map_completedExp_of_projection (l : ℕ → ℕ) (g : F.completion → G.completion)
    (φ : ∀ k, A ⧸ F.ideal (l k + 1) →+* B ⧸ G.ideal (k + 1))
    (hproj : ∀ k z, G.projection k (g z) = φ k (F.projection (l k) z))
    (x : F.completionIdeal 1) (hx : g x ∈ G.completionIdeal 1) :
    g (F.completedExp x) = G.completedExp ⟨g x, hx⟩ :=
  G.completion_ext fun k => by
    rw [hproj k, projection_completedExp, projection_completedExp, hproj k]
    exact (F.isNilpotent_projection x.property (l k)).map_exp (φ k)

/-- A map between completions computed at each order `k` by a ring homomorphism on quotients
commutes with `completedLog` on elements sent congruent to `1` modulo `G.completionIdeal 1`. -/
theorem map_completedLog_of_projection (l : ℕ → ℕ) (g : F.completion → G.completion)
    (φ : ∀ k, A ⧸ F.ideal (l k + 1) →+* B ⧸ G.ideal (k + 1))
    (hproj : ∀ k z, G.projection k (g z) = φ k (F.projection (l k) z))
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1})
    (hu : g u - 1 ∈ G.completionIdeal 1) :
    g (F.completedLog u) = G.completedLog ⟨g u, hu⟩ :=
  G.completion_ext fun k => by
    rw [hproj k, projection_completedLog, projection_completedLog, hproj k]
    have hnil : IsNilpotent (F.projection (l k) u - 1) := by
      simpa only [map_sub, map_one] using F.isNilpotent_projection u.property (l k)
    exact hnil.map_log (φ k)

end Projection

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
        F.mapCompletion_mem_first G f l hl hf h₁ x.property⟩ :=
  F.map_completedExp_of_projection G l (F.mapCompletion G f l hl hf)
    (fun k => Ideal.quotientMap (G.ideal (k + 1)) f (hf k))
    (F.projection_mapCompletion G f l hl hf) x _

/-- Completed logarithms commute with the same maps on elements congruent to one. -/
@[simp]
theorem mapCompletion_completedLog
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.mapCompletion G f l hl hf (F.completedLog u) =
      G.completedLog ⟨F.mapCompletion G f l hl hf u, by
        simpa only [map_sub, map_one] using
          F.mapCompletion_mem_first G f l hl hf h₁ u.property⟩ :=
  F.map_completedLog_of_projection G l (F.mapCompletion G f l hl hf)
    (fun k => Ideal.quotientMap (G.ideal (k + 1)) f (hf k))
    (F.projection_mapCompletion G f l hl hf) u _

end TauCeti.AlgFiltration
