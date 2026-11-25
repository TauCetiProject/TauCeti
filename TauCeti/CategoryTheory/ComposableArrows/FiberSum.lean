/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.Quiver.Covering
public import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Sums over strings with a fixed tail

The fiber of the first face map on composable strings is the set of arrows into the initial
vertex of the tail. Reindexing a sum by these arrows allows weighted insertion operators to
be treated as fiberwise sums.
-/

public noncomputable section

open CategoryTheory Set

namespace CategoryTheory.ComposableArrows

variable {C : Type*} [Category C] {n : ℕ}

/-- Summing over strings with a fixed tail is summing over arrows into the first vertex
of that tail. -/
theorem finsum_mem_preimage_δ₀_singleton {M : Type*} [AddCommMonoid M]
    (f : ComposableArrows C (n + 1) → M) (σ : ComposableArrows C n) :
    ∑ᶠ τ ∈ (fun τ : ComposableArrows C (n + 1) ↦ τ.δ₀) ⁻¹' {σ}, f τ =
      ∑ᶠ b : Quiver.Costar σ.left, f (σ.precomp b.2) := by
  have hrange : (fun τ : ComposableArrows C (n + 1) ↦ τ.δ₀) ⁻¹' {σ} =
      range (fun b : Quiver.Costar σ.left ↦ σ.precomp b.2) := by
    ext τ
    constructor
    · intro h
      obtain ⟨F, x, a, rfl⟩ := precomp_surjective τ
      simp only [mem_preimage, mem_singleton_iff, precomp_δ₀] at h
      subst F
      exact ⟨⟨x, a⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact precomp_δ₀ _ _
  rw [hrange, finsum_mem_range]
  rintro ⟨x, a⟩ ⟨y, b⟩ h
  have he := congrArg (fun τ : ComposableArrows C (n + 1) ↦
    τ.totalArrow 0 1 (Fin.zero_le _)) h
  have ha := totalArrow_precomp_zero_one (⟨x, σ.left, a⟩ : Quiver.Total C) σ rfl
  have hb := totalArrow_precomp_zero_one (⟨y, σ.left, b⟩ : Quiver.Total C) σ rfl
  simp only [eqToHom_refl, Category.comp_id] at ha hb
  rw [ha, hb] at he
  obtain ⟨rfl, _, hab⟩ := Quiver.Total.mk.inj he
  exact Sigma.ext rfl hab

end CategoryTheory.ComposableArrows
