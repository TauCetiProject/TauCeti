/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith

/-!
# Projection contraction for a secondary sesquilinear pairing

Let `V` be a finite-dimensional inner product space over `𝕜` (`[RCLike 𝕜]`). If `A : Module.End 𝕜 V`
is normal (`A.adjoint ∘ₗ A = A ∘ₗ A.adjoint`), then `(LinearMap.range A)ᗮ ≤ LinearMap.ker A`
(`TauCeti.orthogonal_range_le_ker_of_commute_adjoint`).

Given a symmetric operator `e`, an operator `A` with `(LinearMap.range A)ᗮ ≤ LinearMap.ker A`, and
a subspace `Z ≤ LinearMap.range e ⊓ LinearMap.ker A`, any vector `y` orthogonal to
`LinearMap.range e ⊓ LinearMap.ker A ⊓ Zᗮ` decomposes as `y = z + x` with `z ∈ Z` and
`x ∈ LinearMap.ker e ⊔ LinearMap.range A` (`TauCeti.mem_sup_ker_sup_range_of_orthogonal_inf`).
For any positive-semidefinite sesquilinear pairing `B` for which `e` is symmetric and `A` sends `V`
into the `B`-orthogonal complement of `LinearMap.ker A`, this decomposition is simultaneously
orthogonal for `inner` and for `B`, so `Z.starProjection` does not increase `v ↦ RCLike.re (B v v)`
at `y` (`TauCeti.re_apply_starProjection_le`).

## Main results

* `TauCeti.orthogonal_range_le_ker_of_commute_adjoint`: for a normal operator `A`,
  `(LinearMap.range A)ᗮ ≤ LinearMap.ker A`.
* `TauCeti.mem_sup_ker_sup_range_of_orthogonal_inf`: vectors orthogonal to
  `range e ⊓ ker A ⊓ Zᗮ` lie in `Z ⊔ (ker e ⊔ range A)`.
* `TauCeti.re_apply_starProjection_le`: `Z.starProjection` contracts `RCLike.re (B v v)` on
  `(range e ⊓ ker A ⊓ Zᗮ)ᗮ`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/New/OneLift/TestedForms.lean`
(`New.DescentPair.orthogonal_range_heckePolyOnForms_le_ker`,
`New.DescentPair.mem_sup_ker_sup_range_of_isOrthogonalToFalseLifts`,
`New.DescentPair.normSqAt_starProjection_le`).
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [Module.Finite 𝕜 V]

/-- For a normal endomorphism `A` of a finite-dimensional inner product space, every vector
orthogonal to `LinearMap.range A` lies in `LinearMap.ker A`. -/
theorem orthogonal_range_le_ker_of_commute_adjoint {A : Module.End 𝕜 V}
    (hcomm : A.adjoint ∘ₗ A = A ∘ₗ A.adjoint) :
    (LinearMap.range A)ᗮ ≤ LinearMap.ker A := by
  intro u hu
  have horth : ⟪u, A (A.adjoint u)⟫_𝕜 = 0 :=
    Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self A (A.adjoint u)) hu
  have hself : ⟪A u, A u⟫_𝕜 = 0 := by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, horth]
  exact inner_self_eq_zero.mp hself

/-- If `e` is symmetric and `(LinearMap.range A)ᗮ ≤ LinearMap.ker A`, then any vector `y`
orthogonal to `LinearMap.range e ⊓ LinearMap.ker A ⊓ Zᗮ` lies in
`Z ⊔ (LinearMap.ker e ⊔ LinearMap.range A)`. -/
theorem mem_sup_ker_sup_range_of_orthogonal_inf {e A : Module.End 𝕜 V} (he : e.IsSymmetric)
    (hA : (LinearMap.range A)ᗮ ≤ LinearMap.ker A) {Z : Submodule 𝕜 V} {y : V}
    (hy : y ∈ (LinearMap.range e ⊓ LinearMap.ker A ⊓ Zᗮ)ᗮ) :
    y ∈ Z ⊔ (LinearMap.ker e ⊔ LinearMap.range A) := by
  have hle : (Z ⊔ (LinearMap.ker e ⊔ LinearMap.range A))ᗮ ≤
      LinearMap.range e ⊓ LinearMap.ker A ⊓ Zᗮ := by
    intro u hu
    obtain ⟨huZ, hue', huA⟩ : u ∈ Zᗮ ∧ u ∈ (LinearMap.ker e)ᗮ ∧ u ∈ (LinearMap.range A)ᗮ := by
      simpa only [← Submodule.inf_orthogonal, Submodule.mem_inf] using hu
    have hue : u ∈ LinearMap.range e := by
      simpa [← he.orthogonal_range, Submodule.orthogonal_orthogonal] using hue'
    exact ⟨⟨hue, hA huA⟩, huZ⟩
  rw [← Submodule.orthogonal_orthogonal (Z ⊔ (LinearMap.ker e ⊔ LinearMap.range A))]
  exact Submodule.orthogonal_le hle hy

/-- Let `e` be symmetric, `A` satisfy `(LinearMap.range A)ᗮ ≤ LinearMap.ker A` and
`⟪A v, z⟫ = 0` for `z ∈ ker A`, `Z ≤ range e ⊓ ker A`, and `y ∈ (range e ⊓ ker A ⊓ Zᗮ)ᗮ`.
Then for any positive-semidefinite sesquilinear pairing `B` for which `e` is symmetric and
`B (A v) z = 0` for `z ∈ ker A`, the orthogonal projection `Z.starProjection` does not increase
`v ↦ RCLike.re (B v v)` at `y`. -/
theorem re_apply_starProjection_le {e A : Module.End 𝕜 V} (he : e.IsSymmetric)
    (hA : (LinearMap.range A)ᗮ ≤ LinearMap.ker A)
    (hA_inner : ∀ v z : V, A z = 0 → ⟪A v, z⟫_𝕜 = 0)
    {Z : Submodule 𝕜 V} (hZ : Z ≤ LinearMap.range e ⊓ LinearMap.ker A) {y : V}
    (hy : y ∈ (LinearMap.range e ⊓ LinearMap.ker A ⊓ Zᗮ)ᗮ)
    (B : V →ₛₗ[starRingEnd 𝕜] V →ₗ[𝕜] 𝕜)
    (hB_nonneg : ∀ v : V, 0 ≤ RCLike.re (B v v))
    (hB_symm : ∀ x z : V, B x z = 0 → B z x = 0)
    (hB_e : ∀ x z : V, B (e x) z = B x (e z))
    (hB_A : ∀ v z : V, A z = 0 → B (A v) z = 0) :
    RCLike.re (B (Z.starProjection y) (Z.starProjection y)) ≤ RCLike.re (B y y) := by
  obtain ⟨z, hz, x, hx, rfl⟩ :=
    Submodule.mem_sup.mp (mem_sup_ker_sup_range_of_orthogonal_inf he hA hy)
  have horth_inner (z' : V) (hz' : z' ∈ Z) : ⟪x, z'⟫_𝕜 = 0 := by
    obtain ⟨k, hk, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨⟨u, rfl⟩, hAz⟩ := hZ hz'
    rw [inner_add_left, ← he k u, LinearMap.mem_ker.mp hk, inner_zero_left, zero_add]
    exact hA_inner v (e u) (LinearMap.mem_ker.mp hAz)
  have horth_B : B x z = 0 := by
    obtain ⟨k, hk, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨⟨u, rfl⟩, hAz⟩ := hZ hz
    rw [map_add, LinearMap.add_apply, ← hB_e k u, LinearMap.mem_ker.mp hk, map_zero,
      LinearMap.zero_apply, zero_add]
    exact hB_A v (e u) (LinearMap.mem_ker.mp hAz)
  have hproj : Z.starProjection (z + x) = z :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hz fun z' hz' ↦ by
      rw [add_sub_cancel_left]
      exact horth_inner z' hz'
  rw [hproj]
  have hpyth : RCLike.re (B (z + x) (z + x)) = RCLike.re (B z z) + RCLike.re (B x x) := by
    simp [map_add, horth_B, hB_symm _ _ horth_B]
  linarith [hB_nonneg x]

end TauCeti
