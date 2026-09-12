/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Intertwining maps along a homomorphism of groups

Mathlib's `Representation.IsIntertwiningMap` compares two representations of one and the same
group. For a homomorphism `f : G →* H`, a linear map intertwining `ρ : Representation R G V` with
`σ.comp f`, for `σ : Representation R H W`, is the same datum as a morphism of `G`-representations
`M ⟶ Res(f)(N)`, and, when `f` is an isomorphism, also as a morphism `Res(f⁻¹)(M) ⟶ N` of
`H`-representations. This file supplies those two adapters, the identity, composition and
inversion lemmas for intertwining maps along a homomorphism of groups, and the compatibility of
such a map with the norm `∑ g, ρ g` of a finite group.

These are the general representation-theoretic inputs of a change-of-group map in group homology
and cohomology: `groupHomology.chainsMap` consumes the first adapter and
`groupCohomology.cochainsMap` the second.

## Main definitions

* `TauCeti.Representation.IsIntertwiningMap.toRes`: an intertwining map along `f : G →* H` read as
  a morphism `M ⟶ Res(f)(N)` of `G`-representations.
* `TauCeti.Representation.IsIntertwiningMap.ofRes`: an intertwining map along an isomorphism
  `e : G ≃* H` read as a morphism `Res(e⁻¹)(M) ⟶ N` of `H`-representations.

## Main results

* `TauCeti.Representation.IsIntertwiningMap.trans` and
  `TauCeti.Representation.IsIntertwiningMap.symm`: intertwining maps along an isomorphism of groups
  compose, and invert when their linear part is an equivalence.
* `TauCeti.Representation.IsIntertwiningMap.comp_norm`: an intertwining map along an isomorphism of
  finite groups intertwines the two norms.
* `TauCeti.Representation.isIntertwiningMap_id` and
  `TauCeti.Representation.isIntertwiningMap_res`: the identity map is intertwining along the
  identity isomorphism of the group, and along `f` between a restricted representation and the
  representation it restricts.
-/

public noncomputable section

universe u

namespace TauCeti.Representation

variable {R G H K V W U : Type u} [CommRing R] [Group G] [Group H] [Group K]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U]

namespace IsIntertwiningMap

variable {ρ : Representation R G V} {σ : Representation R H W} {τ : Representation R K U}
  {e : G ≃* H} {φ : V →ₗ[R] W}

/-- **Intertwining maps along isomorphisms of groups compose.** -/
theorem trans (hφ : ρ.IsIntertwiningMap (σ.comp (e : G →* H)) φ)
    {e₂ : H ≃* K} {ψ : W →ₗ[R] U}
    (hψ : σ.IsIntertwiningMap (τ.comp (e₂ : H →* K)) ψ) :
    ρ.IsIntertwiningMap (τ.comp (e.trans e₂ : G →* K)) (ψ ∘ₗ φ) :=
  ⟨fun g v ↦ by
    have hφ' : φ (ρ g v) = σ (e g) (φ v) := by
      simpa using hφ.isIntertwining g v
    have hψ' : ψ (σ (e g) (φ v)) = τ (e₂ (e g)) (ψ (φ v)) := by
      simpa using hψ.isIntertwining (e g) (φ v)
    change ψ (φ (ρ g v)) = τ (e₂ (e g)) (ψ (φ v))
    rw [hφ', hψ']⟩

/-- **The inverse of an intertwining map along an isomorphism of groups is intertwining**, when
its linear part is an equivalence. -/
theorem symm {e' : V ≃ₗ[R] W}
    (he : ρ.IsIntertwiningMap (σ.comp (e : G →* H)) (e' : V →ₗ[R] W)) :
    σ.IsIntertwiningMap (ρ.comp (e.symm : H →* G)) (e'.symm : W →ₗ[R] V) :=
  ⟨fun h v ↦ by
    have he' : ∀ g, (e' : V →ₗ[R] W) ∘ₗ ρ g = σ (e g) ∘ₗ (e' : V →ₗ[R] W) :=
      fun g ↦ by ext x; exact he.isIntertwining g x
    simpa using congr($(e'.isIntertwining_symm_isIntertwining
      (σ := σ.comp (e : G →* H)) he' (e.symm h)) v)⟩

/-- **An intertwining map along an isomorphism of finite groups intertwines the two norms.** The
group isomorphism permutes the summands of `∑ g, ρ g`. -/
theorem comp_norm [Fintype G] [Fintype H]
    (hφ : ρ.IsIntertwiningMap (σ.comp (e : G →* H)) φ) :
    φ ∘ₗ ρ.norm = σ.norm ∘ₗ φ := by
  ext x
  simpa [_root_.Representation.norm] using
    Fintype.sum_equiv e.toEquiv (fun g ↦ φ (ρ g x)) (fun h ↦ σ h (φ x))
      fun g ↦ hφ.isIntertwining g x

end IsIntertwiningMap

section RepMorphisms

/-- The identity map of a representation is intertwining along the identity isomorphism of its
group. -/
theorem isIntertwiningMap_id (M : Rep R G) :
    M.ρ.IsIntertwiningMap (M.ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G))
      (LinearMap.id : M.V →ₗ[R] M.V) := ⟨fun g v ↦ by simp⟩

/-- Restricting the coefficients along `f` and comparing back by the identity is an intertwining
map along `f`. -/
theorem isIntertwiningMap_res (f : G →* H) (N : Rep R H) :
    (Rep.res f N).ρ.IsIntertwiningMap (N.ρ.comp f)
      ((LinearEquiv.refl R N.V : N.V →ₗ[R] N.V) : (Rep.res f N).V →ₗ[R] N.V) :=
  ⟨fun g v ↦ by simp⟩

variable {M : Rep R G} {N : Rep R H} {φ : M.V →ₗ[R] N.V}

namespace IsIntertwiningMap

/-- An intertwining map along `f : G →* H` read as a morphism `M ⟶ Res(f)(N)` of
`G`-representations. This is the datum that `groupHomology.chainsMap` consumes. -/
-- Exposed, like Mathlib's `Rep.resMap`, because the comparison of a change-of-group map along
-- the identity isomorphism with the coefficient functoriality of a fixed group is definitional.
@[expose] def toRes {f : G →* H} (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp f) φ) : M ⟶ Rep.res f N :=
  Rep.ofHom ⟨φ, fun g ↦ by ext v; exact hφ.isIntertwining g v⟩

/-- An intertwining map along an isomorphism `e : G ≃* H` read as a morphism `Res(e⁻¹)(M) ⟶ N` of
`H`-representations. This is the datum that `groupCohomology.cochainsMap` consumes. -/
@[expose] def ofRes {e : G ≃* H} (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    Rep.res (e.symm : H →* G) M ⟶ N :=
  Rep.ofHom ⟨φ, fun h ↦ by ext v; simpa using hφ.isIntertwining (e.symm h) v⟩

@[simp] theorem toRes_hom_toLinearMap {f : G →* H}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp f) φ) :
    (toRes hφ).hom.toLinearMap = φ := by simp [toRes]

@[simp] theorem ofRes_hom_toLinearMap {e : G ≃* H}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    (ofRes hφ).hom.toLinearMap = φ := by simp [ofRes]

end IsIntertwiningMap

end RepMorphisms

end TauCeti.Representation
