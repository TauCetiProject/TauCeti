/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import TauCeti.Geometry.Convex.Cone.MinkowskiWeyl

/-!
# Faces of the intersection of a cone with a preimage

Let `σ ⊆ V` and `τ ⊆ W` be finitely generated cones in finite-dimensional spaces over a linearly
ordered field and `f : V → W` a linear map. Every face of `σ ⊓ τ.comap f` is `σ' ⊓ τ'.comap f`
for a face `σ'` of `σ` and a face `τ'` of `τ`
(`PointedCone.IsFaceOf.exists_inf_comap_eq`). Conversely every such intersection is a face, by
`PointedCone.IsFaceOf.inf` and `PointedCone.IsFaceOf.comap`.

This is what makes the cones `σ ⊓ τ.comap f`, for `σ` and `τ` running over two fans, closed under
passing to faces, so that they form a common refinement. The proof exposes the face by a
nonnegative functional and splits that functional along `σ` and `τ` by Farkas' lemma
(`PointedCone.dual_flip_inf_comap`).

## References

* G. M. Ziegler, *Lectures on Polytopes*, Proposition 1.1 and §2.1.
-/

public section

namespace PointedCone.IsFaceOf

variable {K V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup W] [Module K W]
  [Module.Finite K W] {σ F : PointedCone K V} {τ : PointedCone K W} {f : V →ₗ[K] W}

/-- Every face of the intersection of a finitely generated cone `σ` with the preimage of a
finitely generated cone `τ` is the intersection of a face of `σ` with the preimage of a face of
`τ`. -/
theorem exists_inf_comap_eq (hF : F.IsFaceOf (σ ⊓ τ.comap f)) (hσ : σ.FG) (hτ : τ.FG) :
    ∃ σ' : PointedCone K V, ∃ τ' : PointedCone K W, σ'.IsFaceOf σ ∧ τ'.IsFaceOf τ ∧
      σ' ⊓ τ'.comap f = F := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hF.exists_nonneg_linear_inf_ker (hσ.cone_inf (hτ.cone_comap f))
  have hℓmem : ℓ ∈ dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V).flip
      (σ ⊓ τ.comap f) := mem_dual.2 fun x hx ↦ by simpa using hℓ x hx
  rw [dual_flip_inf_comap hσ hτ f] at hℓmem
  obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hℓmem
  have ha' : ∀ x ∈ σ, 0 ≤ a x := fun x hx ↦ by simpa using ha hx
  have hb' : ∀ y ∈ τ, 0 ≤ b y := fun y hy ↦ by simpa using hb hy
  refine ⟨_, _, isFaceOf_inf_ker ha', isFaceOf_inf_ker hb', ?_⟩
  ext x
  simp only [Submodule.mem_inf, mem_comap, mem_ofSubmodule_iff, LinearMap.mem_ker,
    LinearMap.add_apply, LinearMap.restrictScalars_apply, LinearMap.dualMap_apply]
  constructor
  · rintro ⟨⟨hxσ, hax⟩, hxτ, hbx⟩
    exact ⟨⟨hxσ, hxτ⟩, by rw [hax, hbx, add_zero]⟩
  · rintro ⟨⟨hxσ, hxτ⟩, hx⟩
    have hax := ha' x hxσ
    have hbx := hb' _ hxτ
    exact ⟨⟨hxσ, by linarith⟩, hxτ, by linarith⟩

end PointedCone.IsFaceOf
