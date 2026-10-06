/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Invariant maps on cosets of a representation

For a representation `ρ` of a submonoid `Δ` of a group and a subgroup `Γ` contained in `Δ`,
let `q` be a semilinear map satisfying `q ∘ ρ(γ) = q` for `γ ∈ Γ`. Then `q ∘ ρ(x)` depends
only on the right coset `Γ x`. In particular, sums of these maps can be compared using coset
decompositions, as in `HeckeCoset.heckeSum_eq_sum_of_rightCosets`.

The target of `q` may be a module over a different semiring: the coset argument uses only
composition and the invariance of `q`.
-/

public section

open scoped Pointwise

namespace Representation

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ : Subgroup G}
  {R S V W : Type*} [Semiring R] [Semiring S] [AddCommMonoid V] [Module R V]
  [AddCommMonoid W] [Module S W] {σ : R →+* S} (ρ : Representation R Δ V)

/-- For a `Γ`-invariant semilinear map `q`, the map `q ∘ ρ(x)` depends only on the right
coset `Γ x`. -/
theorem comp_eq_of_rightCoset_eq (hΓ : Γ.toSubmonoid ≤ Δ) {q : V →ₛₗ[σ] W}
    (hq : ∀ γ (hγ : γ ∈ Γ), q ∘ₛₗ ρ ⟨γ, hΓ hγ⟩ = q) {x y : G}
    (hx : x ∈ Δ) (hy : y ∈ Δ)
    (h : MulOpposite.op x • (Γ : Set G) = MulOpposite.op y • (Γ : Set G)) :
    q ∘ₛₗ ρ ⟨x, hx⟩ = q ∘ₛₗ ρ ⟨y, hy⟩ := by
  have hγ : y * x⁻¹ ∈ Γ := (rightCoset_eq_iff Γ).mp h
  calc q ∘ₛₗ ρ ⟨x, hx⟩ = (q ∘ₛₗ ρ ⟨y * x⁻¹, hΓ hγ⟩) ∘ₛₗ ρ ⟨x, hx⟩ := by rw [hq _ hγ]
    _ = q ∘ₛₗ ρ (⟨y * x⁻¹, hΓ hγ⟩ * ⟨x, hx⟩) := by
      rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _ = q ∘ₛₗ ρ ⟨y, hy⟩ := by
      congr 2
      exact Subtype.ext (inv_mul_cancel_right y x)

end Representation

end
