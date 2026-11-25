/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.RingTheory.Deformation.Lift

/-!
# Restriction of lifts and of strict classes

Let `ρbar : G →* GL n k` be a residual representation and `ι : H →ₜ* G` a continuous monoid
homomorphism, such as the map from a decomposition group to a global Galois group (which need not
be injective). Precomposition with `ι` sends a lift `ρ` of `ρbar` to a lift `ρ ∘ ι` of
`ρbar ∘ ι`. It commutes with pushforward along morphisms of `C_Λ` and with conjugation by the
strict kernel `Γ̂ₙ(A)`, so it descends to strict classes. This gives natural transformations
from the framed lifting functor and from the deformation functor of `ρbar` to those of `ρbar ∘ ι`.

Restriction of strict classes is well defined, but restriction of lifts is not invariant under
strict conjugation. To select an invariant lift one uses a *frame*: a framed pair `(ρ, α)` with
`α ∈ Γ̂ₙ(A)` has the framed restricted lift `α⁻¹ (ρ ∘ ι) α`. This lift is unchanged by the
simultaneous replacement `(ρ, α) ↦ (βρβ⁻¹, βα)` for `β ∈ Γ̂ₙ(A)`
(`TauCeti.Deformation.Lift.framedRestrict_smul_mul`), and its strict class is the restriction of
the strict class of `ρ`. Framed restricted lifts are the local lifts of globally framed
deformations: frames at the places of a set `T` produce well-defined local lifts at those places.

## Main definitions

* `TauCeti.Deformation.Lift.restrict ι ρ`: the restriction `ρ ∘ ι` of a lift `ρ` along `ι`.
* `TauCeti.Deformation.Lift.framedRestrict ι ρ α`: the framed restricted lift `α⁻¹ (ρ ∘ ι) α`.
* `TauCeti.Deformation.StrictClass.restrict ι`: the restriction of strict classes along `ι`.
* `TauCeti.Deformation.liftFunctorRestrict Λ ρbar ι` and
  `TauCeti.Deformation.strictClassFunctorRestrict Λ ρbar ι`: restriction as natural
  transformations of the lifting and deformation functors.

## Main results

* `TauCeti.Deformation.Lift.restrict_smul`: restriction commutes with strict conjugation.
* `TauCeti.Deformation.Lift.framedRestrict_smul_mul`: the framed restricted lift of a framed pair
  is invariant under simultaneous strict conjugation of the lift and the frame.
* `TauCeti.Deformation.StrictClass.mk_framedRestrict`: the strict class of a framed restricted
  lift is the restriction of the strict class.

## References

* T. Gee, *Modularity lifting theorems*, Essent. Number Theory 1 (2022), §§3.20–3.21.
* B. Mazur, *Deforming Galois representations*, in *Galois groups over `ℚ`*, MSRI Publ. 16
  (1989), 385–437, §1.
-/

public section

open CategoryTheory Matrix

universe u v w w' w'' x

namespace TauCeti.Deformation

open ArtinLocalAlg

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]
  {n : Type x} [Fintype n] [DecidableEq n]
  {G : Type w} [Monoid G] [TopologicalSpace G] {H : Type w'} [Monoid H] [TopologicalSpace H]
  {H' : Type w''} [Monoid H'] [TopologicalSpace H']
  {ρbar : G →* GL n k} {A B : ArtinLocalAlg Λ k}

namespace Lift

/-- The restriction `h ↦ ρ (ι h)` of a lift `ρ` of `ρbar` along a continuous homomorphism
`ι : H →ₜ* G`, a lift of `ρbar ∘ ι`. -/
def restrict (ι : H →ₜ* G) (ρ : Lift ρbar A) : Lift (ρbar.comp (ι : H →* G)) A where
  toMonoidHom := ρ.toMonoidHom.comp (ι : H →* G)
  isLocallyConstant' := ρ.isLocallyConstant.comp_continuous (map_continuous ι)
  map_augmentation_comp' := MonoidHom.ext fun h ↦ by simp

@[simp]
theorem restrict_apply (ι : H →ₜ* G) (ρ : Lift ρbar A) (h : H) : ρ.restrict ι h = ρ (ι h) :=
  (rfl)

/-- Restriction along the identity is the identity. -/
theorem restrict_id (ρ : Lift ρbar A) : ρ.restrict (ContinuousMonoidHom.id G) = ρ :=
  ext fun _ ↦ rfl

/-- Restricting along `ι` and then along `ι'` is restricting along `ι ∘ ι'`. -/
theorem restrict_restrict (ι : H →ₜ* G) (ι' : H' →ₜ* H) (ρ : Lift ρbar A) :
    (ρ.restrict ι).restrict ι' = ρ.restrict (ι.comp ι') :=
  ext fun _ ↦ rfl

/-- Restriction commutes with pushforward along a morphism of `C_Λ`. -/
theorem restrict_map (ι : H →ₜ* G) (f : A ⟶ B) (ρ : Lift ρbar A) :
    (ρ.map f).restrict ι = (ρ.restrict ι).map f :=
  ext fun _ ↦ by simp

/-- Restriction commutes with conjugation by the strict kernel. -/
@[simp]
theorem restrict_smul (ι : H →ₜ* G) (a : A.strictKernel n) (ρ : Lift ρbar A) :
    (a • ρ).restrict ι = a • ρ.restrict ι :=
  ext fun _ ↦ rfl

/-- The *framed restricted lift* `h ↦ α⁻¹ ρ (ι h) α` of a lift `ρ` with a frame `α` in the strict
kernel `Γ̂ₙ(A)`: the restriction of `ρ` along `ι`, conjugated by `α⁻¹`. -/
def framedRestrict (ι : H →ₜ* G) (ρ : Lift ρbar A) (α : A.strictKernel n) :
    Lift (ρbar.comp (ι : H →* G)) A :=
  α⁻¹ • ρ.restrict ι

@[simp]
theorem framedRestrict_apply (ι : H →ₜ* G) (ρ : Lift ρbar A) (α : A.strictKernel n) (h : H) :
    ρ.framedRestrict ι α h = (α : GL n A.obj.left)⁻¹ * ρ (ι h) * α := by
  simp [framedRestrict]

/-- With the trivial frame, the framed restricted lift is the restriction. -/
@[simp]
theorem framedRestrict_one (ι : H →ₜ* G) (ρ : Lift ρbar A) :
    ρ.framedRestrict ι 1 = ρ.restrict ι := by
  simp [framedRestrict]

/-- The framed restricted lift of a framed pair `(ρ, α)` is invariant under the simultaneous strict
conjugation `(ρ, α) ↦ (βρβ⁻¹, βα)`. -/
@[simp]
theorem framedRestrict_smul_mul (ι : H →ₜ* G) (β α : A.strictKernel n) (ρ : Lift ρbar A) :
    (β • ρ).framedRestrict ι (β * α) = ρ.framedRestrict ι α := by
  simp [framedRestrict, mul_smul]

/-- Changing the frame of a framed pair by `β` conjugates its framed restricted lift by `β⁻¹`. -/
theorem framedRestrict_mul (ι : H →ₜ* G) (α β : A.strictKernel n) (ρ : Lift ρbar A) :
    ρ.framedRestrict ι (α * β) = β⁻¹ • ρ.framedRestrict ι α := by
  simp [framedRestrict, mul_smul]

/-- Framed restriction commutes with pushforward along a morphism `f` of `C_Λ`, which carries the
frame `α` to its image. -/
theorem framedRestrict_map (ι : H →ₜ* G) (f : A ⟶ B) (ρ : Lift ρbar A) (α : A.strictKernel n) :
    (ρ.map f).framedRestrict ι ⟨_, map_mem_strictKernel f α.property⟩ =
      (ρ.framedRestrict ι α).map f :=
  ext fun h ↦ by simp

end Lift

namespace StrictClass

/-- The restriction of strict classes of lifts of `ρbar` along a continuous homomorphism
`ι : H →ₜ* G`, the class of `ρ` going to the class of `ρ ∘ ι`. -/
def restrict (ι : H →ₜ* G) : StrictClass ρbar A → StrictClass (ρbar.comp (ι : H →* G)) A :=
  lift (fun ρ ↦ mk (ρ.restrict ι)) fun a ρ ↦ by
    rw [Lift.restrict_smul, mk_eq_mk_iff]
    exact ⟨a⁻¹, inv_smul_smul a _⟩

@[simp]
theorem restrict_mk (ι : H →ₜ* G) (ρ : Lift ρbar A) : (mk ρ).restrict ι = mk (ρ.restrict ι) :=
  lift_mk _ _ ρ

/-- Restriction of strict classes along the identity is the identity. -/
theorem restrict_id (c : StrictClass ρbar A) : c.restrict (ContinuousMonoidHom.id G) = c := by
  obtain ⟨ρ, rfl⟩ := mk_surjective c
  rw [restrict_mk]
  exact congrArg mk (Lift.restrict_id ρ)

/-- Restricting strict classes along `ι` and then along `ι'` is restricting along `ι ∘ ι'`. -/
theorem restrict_restrict (ι : H →ₜ* G) (ι' : H' →ₜ* H) (c : StrictClass ρbar A) :
    (c.restrict ι).restrict ι' = c.restrict (ι.comp ι') := by
  obtain ⟨ρ, rfl⟩ := mk_surjective c
  rw [restrict_mk, restrict_mk, restrict_mk]
  exact congrArg mk (Lift.restrict_restrict ι ι' ρ)

/-- The strict class of a framed restricted lift is the restriction of the strict class of the
underlying lift: the frame only selects a representative. -/
@[simp]
theorem mk_framedRestrict (ι : H →ₜ* G) (ρ : Lift ρbar A) (α : A.strictKernel n) :
    mk (ρ.framedRestrict ι α) = (mk ρ).restrict ι := by
  rw [restrict_mk, mk_eq_mk_iff]
  exact ⟨α, smul_inv_smul α _⟩

/-- Restriction of strict classes commutes with pushforward along a morphism of `C_Λ`. -/
theorem restrict_map (ι : H →ₜ* G) (f : A ⟶ B) (c : StrictClass ρbar A) :
    (c.map f).restrict ι = (c.restrict ι).map f := by
  obtain ⟨ρ, rfl⟩ := mk_surjective c
  simp [Lift.restrict_map]

end StrictClass

section Functor

variable {H : Type w} [Monoid H] [TopologicalSpace H] (ρbar)

variable (Λ) in
/-- Restriction along a continuous homomorphism `ι : H →ₜ* G` as a natural transformation from
the framed lifting functor of `ρbar` to that of `ρbar ∘ ι`. -/
def liftFunctorRestrict (ι : H →ₜ* G) :
    liftFunctor Λ ρbar ⟶ liftFunctor Λ (ρbar.comp (ι : H →* G)) where
  app A := TypeCat.ofHom (Lift.restrict ι)
  naturality A B f := by
    ext ρ : 3
    exact Lift.restrict_map ι f ρ

variable (Λ) in
@[simp]
theorem liftFunctorRestrict_app_apply (ι : H →ₜ* G) (A : ArtinLocalAlg Λ k) (ρ : Lift ρbar A) :
    (liftFunctorRestrict Λ ρbar ι).app A ρ = ρ.restrict ι :=
  (rfl)

variable (Λ) in
/-- Restriction along a continuous homomorphism `ι : H →ₜ* G` as a natural transformation from
the deformation functor of `ρbar` to that of `ρbar ∘ ι`. -/
def strictClassFunctorRestrict (ι : H →ₜ* G) :
    strictClassFunctor Λ ρbar ⟶ strictClassFunctor Λ (ρbar.comp (ι : H →* G)) where
  app A := TypeCat.ofHom (StrictClass.restrict ι)
  naturality A B f := by
    ext c : 3
    exact StrictClass.restrict_map ι f c

variable (Λ) in
@[simp]
theorem strictClassFunctorRestrict_app_apply (ι : H →ₜ* G) (A : ArtinLocalAlg Λ k)
    (c : StrictClass ρbar A) : (strictClassFunctorRestrict Λ ρbar ι).app A c = c.restrict ι :=
  (rfl)

end Functor

end TauCeti.Deformation
