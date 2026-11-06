/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Basic

/-!
# Semilinear functoriality of the Weil restriction and induced Galois actions

Let `B` be a finite projective `A`-algebra and `C`, `D` finitely presented `B`-algebras. Besides
`B`-algebra homomorphisms, the Weil restriction is functorial in pairs `(σ, φ)` consisting of an
`A`-algebra automorphism `σ` of `B` and a ring homomorphism `φ : C →+* D` that is semilinear
over `σ`, in the sense that `φ (b • c) = σ b • φ c`. The induced `A`-algebra homomorphism
`WeilRestriction.semilinearMap σ φ hφ : WeilRestriction A B C →ₐ[A] WeilRestriction A B D` acts
on points by twisting: it sends a point `y : D →ₐ[B] B ⊗[A] T` to its semilinear twist
`AlgHom.semilinearTwist`, that is, to `(σ⁻¹ ⊗ id) ∘ y ∘ φ`
(`WeilRestriction.homEquiv_comp_semilinearMap_apply`). For `σ = id` this is the usual
functoriality `WeilRestriction.map`.

Consequently, an action of a group (or monoid) `Γ` on `B` by `A`-algebra automorphisms
together with a compatible semilinear action on `C` by ring automorphisms induces an action of
`Γ` on the Weil restriction by `A`-algebra automorphisms, `WeilRestriction.inducedAction`, even
though `Γ` does not act on `C` by `B`-algebra automorphisms. This is the action used for the Weil
restriction of a model `𝒳'` over a Galois extension `O'/O` of discrete valuation rings whose
Galois group acts semilinearly on `𝒳'`: a point is fixed by `γ` exactly when the point of `C` it
classifies is `γ`-equivariant (`WeilRestriction.comp_inducedAction_eq_iff`), which is the starting
point of the fixed-point schemes of Edixhoven's tame descent.

## Main definitions

* `TauCeti.Algebra.WeilRestriction.semilinearMap σ φ hφ`: the homomorphism of Weil restrictions
  induced by a ring homomorphism `φ` semilinear over `σ`.
* `TauCeti.Algebra.WeilRestriction.semilinearEquiv σ φ hφ`: the isomorphism of Weil restrictions
  induced by a ring isomorphism semilinear over `σ`.
* `TauCeti.Algebra.WeilRestriction.inducedAction ρB ρC h`: the action of a monoid `Γ` on
  `WeilRestriction A B C` induced by actions `ρB` on `B` and `ρC` on `C` that are compatible
  with the algebra map `B → C`.

## Main results

* `TauCeti.Algebra.WeilRestriction.homEquiv_comp_semilinearMap_apply`: the effect of
  `semilinearMap` on points.
* `TauCeti.Algebra.WeilRestriction.semilinearMap_refl`: for `σ = id`, `semilinearMap` is `map`.
* `TauCeti.Algebra.WeilRestriction.semilinearMap_comp`: `semilinearMap` respects composition.
* `TauCeti.Algebra.WeilRestriction.homEquiv_comp_inducedAction_apply`: precomposition with the
  action of `γ` sends a point `y` to `(γ⁻¹ ⊗ id) ∘ y ∘ γ`.
* `TauCeti.Algebra.WeilRestriction.comp_inducedAction_eq_iff`: a point is fixed by `γ` if and
  only if the point it classifies is `γ`-equivariant.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §2.4, p. 292.
* M. Kisin, G. Pappas, *Integral models of Shimura varieties with parahoric level structure*,
  Publ. Math. IHÉS 128 (2018), proof of Prop. 1.3.3 and Prop. 1.3.9, pp. 142–143.
-/

public noncomputable section

open Algebra TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable {A B C D E : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
  [Algebra A B] [Algebra B C] [Algebra B D] [Algebra B E]
  {T : Type*} [CommRing T] [Algebra A T]

section Semilinear

variable [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C] [FinitePresentation B D] [FinitePresentation B E]

/-- The **semilinear functoriality of the Weil restriction**: a ring homomorphism `φ : C →+* D`
that is semilinear over an `A`-algebra automorphism `σ` of `B`, in the sense that
`φ (b • c) = σ b • φ c`, induces an `A`-algebra homomorphism of Weil restrictions. On points it
sends `y : D →ₐ[B] B ⊗[A] T` to `(σ⁻¹ ⊗ id) ∘ y ∘ φ`, see
`WeilRestriction.homEquiv_comp_semilinearMap_apply`. -/
def semilinearMap (σ : B ≃ₐ[A] B) (φ : C →+* D)
    (hφ : ∀ b, φ (algebraMap B C b) = algebraMap B D (σ b)) :
    WeilRestriction A B C →ₐ[A] WeilRestriction A B D :=
  (homEquiv A B C _).symm ((universalPoint A B D).semilinearTwist σ φ hφ)

/-- `WeilRestriction.semilinearMap σ φ hφ` classifies the twist `(σ⁻¹ ⊗ id) ∘ u ∘ φ` of the
universal point `u` of `D`. -/
theorem homEquiv_semilinearMap_apply (σ : B ≃ₐ[A] B) (φ : C →+* D)
    (hφ : ∀ b, φ (algebraMap B C b) = algebraMap B D (σ b)) (c : C) :
    homEquiv A B C _ (semilinearMap σ φ hφ) c =
      Algebra.TensorProduct.rTensor _ (σ.symm : B →ₐ[A] B) (universalPoint A B D (φ c)) := by
  rw [semilinearMap, Equiv.apply_symm_apply, AlgHom.semilinearTwist_apply]

/-- The **effect of `WeilRestriction.semilinearMap` on points**: precomposing a point `g` of the
Weil restriction of `D` with `semilinearMap σ φ hφ` twists the point `y` of `D` it classifies to
`(σ⁻¹ ⊗ id) ∘ y ∘ φ`. -/
theorem homEquiv_comp_semilinearMap_apply (σ : B ≃ₐ[A] B) (φ : C →+* D)
    (hφ : ∀ b, φ (algebraMap B C b) = algebraMap B D (σ b))
    (g : WeilRestriction A B D →ₐ[A] T) (c : C) :
    homEquiv A B C T (g.comp (semilinearMap σ φ hφ)) c =
      Algebra.TensorProduct.rTensor T (σ.symm : B →ₐ[A] B) (homEquiv A B D T g (φ c)) := by
  rw [homEquiv_comp, AlgHom.comp_apply, homEquiv_semilinearMap_apply, homEquiv_apply,
    AlgHom.comp_apply]
  -- `B ⊗[A] g` and `σ⁻¹ ⊗ T` act on different tensor factors, so both composites are `σ⁻¹ ⊗ g`.
  exact (DFunLike.congr_fun (Algebra.TensorProduct.map_comp (AlgHom.id A B) (σ.symm : B →ₐ[A] B)
    g (AlgHom.id A _)) _).symm.trans (DFunLike.congr_fun
      (Algebra.TensorProduct.map_comp (σ.symm : B →ₐ[A] B) (AlgHom.id A B) (AlgHom.id A T) g) _)

/-- For `σ = id`, the semilinear functoriality of the Weil restriction is the usual functoriality
`WeilRestriction.map` in `B`-algebra homomorphisms. -/
theorem semilinearMap_refl (φ : C →ₐ[B] D) :
    semilinearMap (AlgEquiv.refl : B ≃ₐ[A] B) (φ : C →+* D) (fun b ↦ φ.commutes b) =
      map A B φ := by
  apply (homEquiv A B C _).injective
  ext c
  rw [homEquiv_semilinearMap_apply AlgEquiv.refl (φ : C →+* D) (fun b ↦ φ.commutes b) c,
    homEquiv_map]
  simp

/-- The trivial twist induces the identity of the Weil restriction. -/
@[simp]
theorem semilinearMap_one :
    semilinearMap (1 : B ≃ₐ[A] B) (RingHom.id C) (fun _ ↦ rfl) =
      AlgHom.id A (WeilRestriction A B C) :=
  (semilinearMap_refl (AlgHom.id B C)).trans map_id

-- `semilinearMap` depends on its semilinearity proof only through the twist data.
private theorem semilinearMap_congr {σ σ' : B ≃ₐ[A] B} {φ φ' : C →+* D}
    (hσ : σ = σ') (hφφ' : φ = φ') (hφ : ∀ b, φ (algebraMap B C b) = algebraMap B D (σ b)) :
    semilinearMap σ φ hφ = semilinearMap σ' φ' (hσ ▸ hφφ' ▸ hφ) := by
  subst hσ hφφ'
  rfl

/-- The semilinear functoriality of the Weil restriction respects composition: if `φ` is
semilinear over `σ₁` and `ψ` over `σ₂`, then `ψ ∘ φ` is semilinear over `σ₂ ∘ σ₁` and induces
the composite homomorphism. -/
theorem semilinearMap_comp (σ₁ σ₂ : B ≃ₐ[A] B) (φ : C →+* D) (ψ : D →+* E)
    (hφ : ∀ b, φ (algebraMap B C b) = algebraMap B D (σ₁ b))
    (hψ : ∀ b, ψ (algebraMap B D b) = algebraMap B E (σ₂ b)) :
    semilinearMap (σ₁.trans σ₂) (ψ.comp φ) (fun b ↦ by simp [hφ, hψ]) =
      (semilinearMap σ₂ ψ hψ).comp (semilinearMap σ₁ φ hφ) := by
  apply (homEquiv A B C _).injective
  ext c
  rw [homEquiv_comp_semilinearMap_apply, homEquiv_semilinearMap_apply,
    homEquiv_semilinearMap_apply, RingHom.comp_apply]
  -- `(σ₂ ∘ σ₁)⁻¹ ⊗ T` factors as `(σ₁⁻¹ ⊗ T) ∘ (σ₂⁻¹ ⊗ T)`.
  exact DFunLike.congr_fun (Algebra.TensorProduct.map_comp (σ₁.symm : B →ₐ[A] B)
    (σ₂.symm : B →ₐ[A] B) (AlgHom.id A _) (AlgHom.id A _)) _

/-- The **semilinear functoriality of the Weil restriction on isomorphisms**: a ring isomorphism
`φ : C ≃+* D` that is semilinear over an `A`-algebra automorphism `σ` of `B` induces an
`A`-algebra isomorphism of Weil restrictions, with underlying homomorphism
`WeilRestriction.semilinearMap σ φ hφ`. -/
def semilinearEquiv (σ : B ≃ₐ[A] B) (φ : C ≃+* D)
    (hφ : ∀ b, φ (algebraMap B C b) = algebraMap B D (σ b)) :
    WeilRestriction A B C ≃ₐ[A] WeilRestriction A B D :=
  have hφ' (b : B) : φ.symm (algebraMap B D b) = algebraMap B C (σ.symm b) := by
    rw [RingEquiv.symm_apply_eq, hφ, AlgEquiv.apply_symm_apply]
  AlgEquiv.ofAlgHom (semilinearMap σ φ hφ) (semilinearMap σ.symm φ.symm hφ')
    (by
      rw [← semilinearMap_comp σ.symm σ (φ.symm : D →+* C) (φ : C →+* D) hφ' hφ,
        ← semilinearMap_one]
      exact semilinearMap_congr (AlgEquiv.ext fun b ↦ σ.apply_symm_apply b)
        (RingHom.ext fun d ↦ φ.apply_symm_apply d) _)
    (by
      rw [← semilinearMap_comp σ σ.symm (φ : C →+* D) (φ.symm : D →+* C) hφ hφ',
        ← semilinearMap_one]
      exact semilinearMap_congr (AlgEquiv.ext fun b ↦ σ.symm_apply_apply b)
        (RingHom.ext fun c ↦ φ.symm_apply_apply c) _)

/-- The forward map of `WeilRestriction.semilinearEquiv` is `WeilRestriction.semilinearMap`. -/
@[simp]
theorem semilinearEquiv_apply (σ : B ≃ₐ[A] B) (φ : C ≃+* D)
    (hφ : ∀ b, φ (algebraMap B C b) = algebraMap B D (σ b)) (x : WeilRestriction A B C) :
    semilinearEquiv σ φ hφ x = semilinearMap σ (φ : C →+* D) hφ x :=
  (rfl)

/-- The inverse of `WeilRestriction.semilinearEquiv σ φ hφ` is induced by `φ⁻¹`, which is
semilinear over `σ⁻¹`. -/
@[simp]
theorem semilinearEquiv_symm (σ : B ≃ₐ[A] B) (φ : C ≃+* D)
    (hφ : ∀ b, φ (algebraMap B C b) = algebraMap B D (σ b)) :
    (semilinearEquiv σ φ hφ).symm = semilinearEquiv σ.symm φ.symm
      (fun b ↦ by rw [RingEquiv.symm_apply_eq, hφ, AlgEquiv.apply_symm_apply]) :=
  AlgEquiv.ext fun _ ↦ rfl

end Semilinear

section Action

variable [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- The **action induced on the Weil restriction** by an action `ρB` of a monoid `Γ` on `B` by
`A`-algebra automorphisms and an action `ρC` of `Γ` on `C` by ring automorphisms that is
semilinear over `ρB`, in the sense that `γ (b • c) = γ b • γ c`. The automorphism attached to `γ`
is `WeilRestriction.semilinearEquiv (ρB γ) (ρC γ)`; on points, precomposition with it sends
`y : C →ₐ[B] B ⊗[A] T` to `(γ⁻¹ ⊗ id) ∘ y ∘ γ`, see
`WeilRestriction.homEquiv_comp_inducedAction_apply`. -/
def inducedAction : Γ →* (WeilRestriction A B C ≃ₐ[A] WeilRestriction A B C) where
  toFun γ := semilinearEquiv (ρB γ) (ρC γ) (h γ)
  map_one' := AlgEquiv.ext fun x ↦ by
    rw [semilinearEquiv_apply, AlgEquiv.one_apply,
      semilinearMap_congr (φ' := RingHom.id C) (map_one ρB) (RingHom.ext fun c ↦ by simp) (h 1),
      semilinearMap_one, AlgHom.id_apply]
  map_mul' γ δ := AlgEquiv.ext fun x ↦ by
    rw [AlgEquiv.mul_apply, semilinearEquiv_apply, semilinearEquiv_apply, semilinearEquiv_apply,
      ← AlgHom.comp_apply, ← semilinearMap_comp (ρB δ) (ρB γ) (ρC δ : C →+* C) (ρC γ : C →+* C)
        (h δ) (h γ),
      semilinearMap_congr (σ' := (ρB δ).trans (ρB γ)) (φ' := (ρC γ : C →+* C).comp (ρC δ))
        (AlgEquiv.ext fun b ↦ by simp) (RingHom.ext fun c ↦ by simp) (h (γ * δ))]

/-- The automorphism of the Weil restriction attached to `γ` by the induced action is
`WeilRestriction.semilinearMap (ρB γ) (ρC γ)`. -/
@[simp]
theorem inducedAction_apply (γ : Γ) (x : WeilRestriction A B C) :
    inducedAction ρB ρC h γ x = semilinearMap (ρB γ) (ρC γ : C →+* C) (h γ) x :=
  (rfl)

/-- The **induced action on points**: precomposing a point `g` of the Weil restriction with the
action of `γ` twists the point `y` of `C` it classifies to `(γ⁻¹ ⊗ id) ∘ y ∘ γ`. -/
theorem homEquiv_comp_inducedAction_apply (γ : Γ) (g : WeilRestriction A B C →ₐ[A] T) (c : C) :
    homEquiv A B C T (g.comp (inducedAction ρB ρC h γ : _ →ₐ[A] _)) c =
      Algebra.TensorProduct.rTensor T ((ρB γ).symm : B →ₐ[A] B) (homEquiv A B C T g (ρC γ c)) :=
  homEquiv_comp_semilinearMap_apply (ρB γ) (ρC γ : C →+* C) (h γ) g c

/-- **Fixed points of the induced action**: a point `g` of the Weil restriction is fixed by `γ`
if and only if the point of `C` it classifies is `γ`-equivariant, that is, intertwines the action
of `γ` on `C` with the action `γ ⊗ id` on `B ⊗[A] T`. -/
theorem comp_inducedAction_eq_iff (γ : Γ) (g : WeilRestriction A B C →ₐ[A] T) :
    g.comp (inducedAction ρB ρC h γ : _ →ₐ[A] _) = g ↔
      ∀ c, homEquiv A B C T g (ρC γ c) =
        Algebra.TensorProduct.rTensor T ((ρB γ : B →ₐ[A] B)) (homEquiv A B C T g c) := by
  rw [← (homEquiv A B C T).injective.eq_iff, AlgHom.ext_iff]
  refine forall_congr' fun c ↦ ?_
  rw [homEquiv_comp_inducedAction_apply]
  -- `σ⁻¹ ⊗ T` is the inverse of the automorphism `σ ⊗ T` of `B ⊗[A] T`.
  exact (Algebra.TensorProduct.congr (ρB γ) (AlgEquiv.refl : T ≃ₐ[A] T)).symm_apply_eq

/-- If `Γ` acts trivially on `B` and on `C`, the induced action on the Weil restriction is
trivial. -/
theorem inducedAction_eq_one (hB : ρB = 1) (hC : ρC = 1) : inducedAction ρB ρC h = 1 := by
  subst hB hC
  ext γ x
  rw [inducedAction_apply,
    semilinearMap_congr (φ := ((1 : Γ →* RingAut C) γ : C →+* C)) (φ' := RingHom.id C)
      (MonoidHom.one_apply γ) (RingHom.ext fun _ ↦ rfl) (h γ), semilinearMap_one,
    AlgHom.id_apply, MonoidHom.one_apply, AlgEquiv.one_apply]

end Action

end TauCeti.Algebra.WeilRestriction
