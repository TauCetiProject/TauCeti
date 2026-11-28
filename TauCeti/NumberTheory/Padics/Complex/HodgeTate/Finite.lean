/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.HodgeTate.Jump

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finiteness and boundedness of Hodge–Tate jumps

For a finitely generated R-module T equipped with a representation ρ of Γ, and a
homomorphism j : Γ →* Gal(PadicAlgCl p / ℚ_p) whose image is a neighbourhood of 1, the space
of γ-semilinear maps T →ₛₗ[γ] ℂ_p is finite-dimensional over ℂ_p. Combined with the
Hodge–Tate comparison theorem PadicComplex.mem_span_image_of_mem_hodgeTateMaps, this implies:

1. Each weight space PadicComplex.hodgeTateMaps j ρ γ u is finite-dimensional over
   PadicAlgCl p.
2. Consequently PadicComplex.hodgeTateJump j ρ γ u = 0 holds if and only if no nonzero
   Hodge–Tate map of weight u exists.
3. The set of weights u : ℤ with nonzero jump hodgeTateJump j ρ γ u ≠ 0 is bounded.

## Main results

* PadicComplex.finite_hodgeTateMaps: hodgeTateMaps j ρ γ u is finite-dimensional over
  PadicAlgCl p.
* PadicComplex.hodgeTateJump_eq_zero_iff: hodgeTateJump j ρ γ u = 0 iff every Hodge–Tate map
  of weight u vanishes.
* PadicComplex.exists_hodgeTateJump_bound: all nonzero Hodge–Tate jumps lie in a bounded
  interval [-a, a].

## Provenance

Adapted from New.Period.finite_hodgeTateMaps
(src/Lib/PadicHodge/Crystalline/HodgeTateForms.lean) and New.Period.jump_eq_zero_iff,
New.Period.exists_jump_bound (src/Lib/PadicHodge/Crystalline/HodgeTateJumps.lean) of
grh-lean (https://github.com/lsernau/grh-lean, commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Topology Filter Module

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime] {Γ R T : Type*} [Monoid Γ] [CommSemiring R]
  [AddCommMonoid T] [Module R T]

/-- If the image of j is a neighbourhood of 1 and T is finitely generated over R, then the
PadicAlgCl p-vector space hodgeTateMaps j ρ γ u is finite-dimensional. -/
theorem finite_hodgeTateMaps [Module.Finite R T]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    (ρ : Representation R Γ T) (γ : R →+* ℂ_[p]) (u : ℤ) :
    Module.Finite (PadicAlgCl p) (hodgeTateMaps j ρ γ u) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := T)
  have hfinC : Module.Finite ℂ_[p] (T →ₛₗ[γ] ℂ_[p]) :=
    Module.Finite.of_injective (LinearMap.pi fun x : s ↦ LinearMap.id.flip x.val) fun f g hfg ↦ by
      ext x
      have hx : x ∈ Submodule.span R (s : Set T) := hs.symm ▸ Submodule.mem_top
      refine Submodule.span_induction (fun y hy ↦ congrFun hfg ⟨y, hy⟩) (by simp)
        (fun y z _ _ hy hz ↦ by simp [hy, hz]) (fun r y _ hy ↦ by simp [hy]) hx
  obtain ⟨κ, a, -, hspan, hli⟩ :=
    exists_linearIndependent' ℂ_[p] (Subtype.val : hodgeTateMaps j ρ γ u → T →ₛₗ[γ] ℂ_[p])
  have : Finite κ := hli.finite
  have hle : hodgeTateMaps j ρ γ u ≤
      Submodule.span (PadicAlgCl p) (Set.range fun i : κ ↦ (a i).val) := fun φ hφ ↦ by
    have hmem : φ ∈ Submodule.span (PadicAlgCl p)
        ((fun i : κ ↦ (a i).val) '' {i : κ | (fun _ : κ ↦ u) i = u}) :=
      mem_span_image_of_mem_hodgeTateMaps hj (fun i ↦ (a i).property) hφ
        (hspan.ge (Submodule.subset_span ⟨⟨φ, hφ⟩, rfl⟩))
    simpa using hmem
  exact Module.Finite.of_fg ((Submodule.fg_span (Set.finite_range _)).of_le hle)

/-- If the image of j is a neighbourhood of 1 and T is finitely generated over R, then
hodgeTateJump j ρ γ u = 0 holds if and only if there is no nonzero Hodge–Tate map of weight
u. -/
theorem hodgeTateJump_eq_zero_iff [Module.Finite R T]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    {ρ : Representation R Γ T} {γ : R →+* ℂ_[p]} {u : ℤ} :
    hodgeTateJump j ρ γ u = 0 ↔ ∀ f ∈ hodgeTateMaps j ρ γ u, f = 0 := by
  have := finite_hodgeTateMaps hj ρ γ u
  rw [hodgeTateJump_def, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]

/-- If the image of j is a neighbourhood of 1 and T is finitely generated over R, then all
weights u : ℤ with nonzero Hodge–Tate jump lie in a bounded interval [-a, a]. -/
theorem exists_hodgeTateJump_bound [Module.Finite R T]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    (ρ : Representation R Γ T) (γ : R →+* ℂ_[p]) :
    ∃ a : ℕ, ∀ u : ℤ, hodgeTateJump j ρ γ u ≠ 0 → -(a : ℤ) ≤ u ∧ u ≤ a := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := T)
  have hfinC : Module.Finite ℂ_[p] (T →ₛₗ[γ] ℂ_[p]) :=
    Module.Finite.of_injective (LinearMap.pi fun x : s ↦ LinearMap.id.flip x.val) fun f g hfg ↦ by
      ext x
      have hx : x ∈ Submodule.span R (s : Set T) := hs.symm ▸ Submodule.mem_top
      refine Submodule.span_induction (fun y hy ↦ congrFun hfg ⟨y, hy⟩) (by simp)
        (fun y z _ _ hy hz ↦ by simp [hy, hz]) (fun r y _ hy ↦ by simp [hy]) hx
  let S : Set (T →ₛₗ[γ] ℂ_[p]) := {F | ∃ w : ℤ, F ∈ hodgeTateMaps j ρ γ w}
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ_[p] (Subtype.val : S → T →ₛₗ[γ] ℂ_[p])
  have : Finite κ := hli.finite
  let := Fintype.ofFinite κ
  choose w hw using fun i : κ ↦ (a i).property
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : κ, (w i).natAbs ≤ N :=
    ⟨Finset.univ.sup fun i ↦ (w i).natAbs,
      fun i ↦ Finset.le_sup (f := fun i ↦ (w i).natAbs) (Finset.mem_univ i)⟩
  refine ⟨N, fun u hu ↦ ?_⟩
  by_contra hnot
  refine hu ((hodgeTateJump_eq_zero_iff hj).mpr fun F hF ↦ ?_)
  have hmem : F ∈ Submodule.span (PadicAlgCl p) ((Subtype.val ∘ a) '' {i : κ | w i = u}) :=
    mem_span_image_of_mem_hodgeTateMaps hj hw hF
      (hspan.ge (Submodule.subset_span ⟨⟨F, u, hF⟩, rfl⟩))
  have hne (i : κ) : w i ≠ u := by
    intro hwi
    have habs : (w i).natAbs ≤ N := hN i
    rw [hwi] at habs
    exact hnot ⟨by omega, by omega⟩
  simpa [hne] using hmem

end PadicComplex
