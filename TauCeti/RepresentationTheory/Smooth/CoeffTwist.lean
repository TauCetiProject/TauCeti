/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CoeffTwist
public import TauCeti.RepresentationTheory.Smooth.Admissible
public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# The twist of a smooth representation by a ring automorphism

Let `σ` be a ring automorphism of a commutative ring `A` (for instance `σ ∈ Aut(ℂ)`), and
`ρ^σ = Representation.coeffTwist σ ρ` the `σ`-twist of a representation `ρ`
(`TauCeti.RepresentationTheory.CoeffTwist`): the same operators, on `V` with `a` acting as
`σ⁻¹(a)`. The twist keeps the stabilizer of every vector and the invariants of every subgroup, so
it preserves smoothness and admissibility, and twisting by `σ` and then by `τ` is twisting by
`σ.trans τ = τ ∘ σ`. On smooth representations it is an autoequivalence of `SmoothRep A G`, with
inverse the twist by `σ⁻¹`.

## Main definitions

* `TauCeti.SmoothRep.coeffTwist σ`: the `σ`-twist functor `SmoothRep A G ⥤ SmoothRep A G`.
* `TauCeti.SmoothRep.coeffTwistEquiv σ`: the `σ`-twist as an autoequivalence of `SmoothRep A G`,
  with inverse `coeffTwist σ.symm`.

## Main results

* `Representation.isSmooth_coeffTwist_iff`: `ρ^σ` is smooth exactly when `ρ` is.
* `Representation.isAdmissible_coeffTwist_iff`: `ρ^σ` is admissible exactly when `ρ` is.
* `TauCeti.SmoothRep.coeffTwistReflIso`, `TauCeti.SmoothRep.coeffTwistTransIso`: twisting by the
  identity is the identity functor, and twisting by `σ` then by `τ` is twisting by `σ.trans τ`;
  `TauCeti.SmoothRep.coeffTwistCongr` identifies the twists by equal automorphisms.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, 1987
  manuscript, §2.0, Generalization, p. 9.
-/

public section

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

open CategoryTheory

universe w u v

namespace Representation

open TauCeti

variable {A G V : Type*} [Group G] [TopologicalSpace G]

section Smooth

variable [CommSemiring A] [AddCommMonoid V] [Module A V] {σ : A ≃+* A} {ρ : Representation A G V}

/-- **Twisting preserves smoothness**, in both directions. -/
theorem isSmooth_coeffTwist_iff : IsSmooth (ρ.coeffTwist σ) ↔ IsSmooth ρ :=
  ⟨fun h ↦ ⟨fun v ↦ by simpa using h.isOpen_stabilizer (CoeffTwist.of σ V v)⟩,
    fun h ↦ ⟨fun x ↦ by
      induction x using CoeffTwist.induction
      rw [stabilizer_coeffTwist]
      exact h.isOpen_stabilizer _⟩⟩

instance [IsSmooth ρ] : IsSmooth (ρ.coeffTwist σ) :=
  isSmooth_coeffTwist_iff.2 ‹_›

end Smooth

section Admissible

variable [CommRing A] [AddCommGroup V] [Module A V] {σ : A ≃+* A} {ρ : Representation A G V}

/-- **Twisting preserves admissibility**, in both directions: the invariants of a compact open
subgroup are carried to each other by a `σ`-semilinear bijection. -/
theorem isAdmissible_coeffTwist_iff : IsAdmissible (ρ.coeffTwist σ) ↔ IsAdmissible ρ := by
  simp only [isAdmissible_iff, isSmooth_coeffTwist_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun U _ ↦ ?_
  rw [coeffTwist_comp]
  let e := invariantsCoeffTwistEquiv σ (ρ.comp (U : Subgroup G).subtype)
  exact ⟨fun _ ↦ Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
    fun _ ↦ Module.Finite.of_surjective e.toLinearMap e.surjective⟩

instance [IsAdmissible ρ] : IsAdmissible (ρ.coeffTwist σ) :=
  isAdmissible_coeffTwist_iff.2 ‹_›

end Admissible

end Representation

namespace TauCeti.SmoothRep

open Representation

variable {A : Type u} [CommRing A] {G : Type v} [Group G] [TopologicalSpace G] (σ : A ≃+* A)

/-- **The `σ`-twist functor** `SmoothRep A G ⥤ SmoothRep A G`, `V ↦ V^σ`, acting on morphisms by
the same underlying maps. -/
abbrev coeffTwist : SmoothRep.{w} A G ⥤ SmoothRep.{w} A G where
  obj V := SmoothRep.of (V.obj.ρ.coeffTwist σ)
  map f := ObjectProperty.homMk (Rep.ofHom (f.hom.hom.coeffTwist σ))

/-- **Twisting by the identity is the identity functor**, with components the identity on
vectors. -/
def coeffTwistReflIso : coeffTwist.{w} (RingEquiv.refl A) ≅ 𝟭 (SmoothRep.{w} A G) :=
  NatIso.ofComponents
    (fun V ↦ mkIso
      { toFun := (CoeffTwist.of (RingEquiv.refl A) V.obj.V).symm
        invFun := CoeffTwist.of (RingEquiv.refl A) V.obj.V
        map_add' := map_add _
        map_smul' a (x : CoeffTwist (RingEquiv.refl A) V.obj.V) := by
          induction x using CoeffTwist.induction
          simp [RingEquiv.symm_refl]
        left_inv := (CoeffTwist.of _ _).apply_symm_apply
        right_inv := (CoeffTwist.of _ _).symm_apply_apply }
      fun _ ↦ rfl)
    fun _ ↦ rfl

/-- `coeffTwistReflIso` sends `CoeffTwist.of _ V v` to `v`. Not `@[simp]`, like the component
lemmas below: `simp` fails to rewrite with it, even on its own statement, because its index keeps
the unfolded `Functor.mk` of the abbreviation `coeffTwist`; so use it with `rw`. -/
theorem coeffTwistReflIso_hom_app_of (V : SmoothRep.{w} A G) (v : V.obj.V) :
    (coeffTwistReflIso.hom.app V).hom.hom (CoeffTwist.of (RingEquiv.refl A) V.obj.V v) = v :=
  (rfl)

/-- The inverse of `coeffTwistReflIso` sends `v` to `CoeffTwist.of _ V v`. -/
theorem coeffTwistReflIso_inv_app_apply (V : SmoothRep.{w} A G) (v : V.obj.V) :
    (coeffTwistReflIso.inv.app V).hom.hom v = CoeffTwist.of (RingEquiv.refl A) V.obj.V v :=
  (rfl)

/-- **Twists by equal automorphisms are isomorphic**: `coeffTwist σ ≅ coeffTwist τ` when `σ = τ`,
with components the identity on vectors. -/
def coeffTwistCongr {σ τ : A ≃+* A} (h : σ = τ) :
    coeffTwist.{w} (G := G) σ ≅ coeffTwist τ :=
  NatIso.ofComponents
    (fun V ↦ mkIso
      { toFun x := CoeffTwist.of τ V.obj.V ((CoeffTwist.of σ V.obj.V).symm x)
        invFun x := CoeffTwist.of σ V.obj.V ((CoeffTwist.of τ V.obj.V).symm x)
        map_add' := by simp
        map_smul' a (x : CoeffTwist σ V.obj.V) := by
          subst h
          induction x using CoeffTwist.induction
          simp
        left_inv _ := by simp
        right_inv _ := by simp }
      fun _ ↦ by subst h; rfl)
    fun _ ↦ by subst h; rfl

/-- `coeffTwistCongr h` sends `CoeffTwist.of σ V v` to `CoeffTwist.of τ V v`. -/
theorem coeffTwistCongr_hom_app_of {σ τ : A ≃+* A} (h : σ = τ) (V : SmoothRep.{w} A G)
    (v : V.obj.V) :
    ((coeffTwistCongr h).hom.app V).hom.hom (CoeffTwist.of σ V.obj.V v) =
      CoeffTwist.of τ V.obj.V v :=
  (rfl)

/-- The inverse of `coeffTwistCongr h` sends `CoeffTwist.of τ V v` to `CoeffTwist.of σ V v`. -/
theorem coeffTwistCongr_inv_app_of {σ τ : A ≃+* A} (h : σ = τ) (V : SmoothRep.{w} A G)
    (v : V.obj.V) :
    ((coeffTwistCongr h).inv.app V).hom.hom (CoeffTwist.of τ V.obj.V v) =
      CoeffTwist.of σ V.obj.V v :=
  (rfl)

/-- **Twisting by `σ` and then by `τ` is twisting by `σ.trans τ = τ ∘ σ`**, with components the
identity on vectors. -/
def coeffTwistTransIso (τ : A ≃+* A) :
    coeffTwist.{w} σ ⋙ coeffTwist τ ≅ coeffTwist.{w, u, v} (G := G) (σ.trans τ) :=
  NatIso.ofComponents
    (fun V ↦ mkIso
      { toFun x := CoeffTwist.of (σ.trans τ) V.obj.V ((CoeffTwist.of σ V.obj.V).symm
          ((CoeffTwist.of τ (CoeffTwist σ V.obj.V)).symm x))
        invFun x := CoeffTwist.of τ (CoeffTwist σ V.obj.V) (CoeffTwist.of σ V.obj.V
          ((CoeffTwist.of (σ.trans τ) V.obj.V).symm x))
        map_add' := by simp
        map_smul' a (x : CoeffTwist τ (CoeffTwist σ V.obj.V)) := by
          induction x using CoeffTwist.induction with | h y => ?_
          induction y using CoeffTwist.induction
          simp [RingEquiv.symm_trans_apply]
        left_inv _ := by simp
        right_inv _ := by simp }
      fun _ ↦ rfl)
    fun _ ↦ rfl

/-- `coeffTwistTransIso σ τ` sends the vector `v` of `(V^σ)^τ` to the vector `v` of
`V^(σ.trans τ)`. -/
theorem coeffTwistTransIso_hom_app_of (τ : A ≃+* A) (V : SmoothRep.{w} A G) (v : V.obj.V) :
    ((coeffTwistTransIso σ τ).hom.app V).hom.hom
        (CoeffTwist.of τ (CoeffTwist σ V.obj.V) (CoeffTwist.of σ V.obj.V v)) =
      CoeffTwist.of (σ.trans τ) V.obj.V v :=
  (rfl)

/-- The inverse of `coeffTwistTransIso σ τ` sends the vector `v` of `V^(σ.trans τ)` to the
vector `v` of `(V^σ)^τ`. -/
theorem coeffTwistTransIso_inv_app_of (τ : A ≃+* A) (V : SmoothRep.{w} A G) (v : V.obj.V) :
    ((coeffTwistTransIso σ τ).inv.app V).hom.hom (CoeffTwist.of (σ.trans τ) V.obj.V v) =
      CoeffTwist.of τ (CoeffTwist σ V.obj.V) (CoeffTwist.of σ V.obj.V v) :=
  (rfl)

/-- **The `σ`-twist is an autoequivalence** of `SmoothRep A G`, with inverse the twist by `σ⁻¹`.
Its unit and counit are the composites of `coeffTwistTransIso`, `coeffTwistCongr` and
`coeffTwistReflIso`, the identity on vectors. -/
-- Exposed, so that its functor and inverse are seen to be `coeffTwist σ` and `coeffTwist σ.symm`.
@[expose]
def coeffTwistEquiv : SmoothRep.{w} A G ≌ SmoothRep.{w} A G where
  functor := coeffTwist σ
  inverse := coeffTwist σ.symm
  unitIso := (coeffTwistTransIso σ σ.symm ≪≫ coeffTwistCongr σ.self_trans_symm ≪≫
    coeffTwistReflIso).symm
  counitIso := coeffTwistTransIso σ.symm σ ≪≫ coeffTwistCongr σ.symm_trans_self ≪≫
    coeffTwistReflIso
  -- Every component is the identity on vectors by construction.
  functor_unitIso_comp _ := by
    ext
    rfl

/-- The unit of `coeffTwistEquiv σ` sends `v` to the vector `v` of `(V^σ)^(σ⁻¹)`. -/
theorem coeffTwistEquiv_unitIso_hom_app_apply (V : SmoothRep.{w} A G) (v : V.obj.V) :
    ((coeffTwistEquiv σ).unitIso.hom.app V).hom.hom v =
      CoeffTwist.of σ.symm (CoeffTwist σ V.obj.V) (CoeffTwist.of σ V.obj.V v) :=
  (rfl)

/-- The inverse of the unit of `coeffTwistEquiv σ` sends the vector `v` of `(V^σ)^(σ⁻¹)` to
`v`. -/
theorem coeffTwistEquiv_unitIso_inv_app_of (V : SmoothRep.{w} A G) (v : V.obj.V) :
    ((coeffTwistEquiv σ).unitIso.inv.app V).hom.hom
        (CoeffTwist.of σ.symm (CoeffTwist σ V.obj.V) (CoeffTwist.of σ V.obj.V v)) = v :=
  (rfl)

/-- The counit of `coeffTwistEquiv σ` sends the vector `v` of `(V^(σ⁻¹))^σ` to `v`. -/
theorem coeffTwistEquiv_counitIso_hom_app_of (V : SmoothRep.{w} A G) (v : V.obj.V) :
    ((coeffTwistEquiv σ).counitIso.hom.app V).hom.hom
        (CoeffTwist.of σ (CoeffTwist σ.symm V.obj.V) (CoeffTwist.of σ.symm V.obj.V v)) = v :=
  (rfl)

/-- The inverse of the counit of `coeffTwistEquiv σ` sends `v` to the vector `v` of
`(V^(σ⁻¹))^σ`. -/
theorem coeffTwistEquiv_counitIso_inv_app_apply (V : SmoothRep.{w} A G) (v : V.obj.V) :
    ((coeffTwistEquiv σ).counitIso.inv.app V).hom.hom v =
      CoeffTwist.of σ (CoeffTwist σ.symm V.obj.V) (CoeffTwist.of σ.symm V.obj.V v) :=
  (rfl)

instance isEquivalence_coeffTwist : (coeffTwist.{w} (G := G) σ).IsEquivalence :=
  (coeffTwistEquiv.{w} (G := G) σ).isEquivalence_functor

end TauCeti.SmoothRep
