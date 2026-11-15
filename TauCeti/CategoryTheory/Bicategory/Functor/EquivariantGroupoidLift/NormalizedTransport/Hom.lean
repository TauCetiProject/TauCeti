/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Normalized

/-!
# Morphisms of normalized equivariant transport

Normalized transport lives on fixed prescribed categories with fixed actions. A morphism
therefore consists of natural isomorphisms between the transport functors, preserving their
units, compositors and commuting isomorphisms with the actions. These morphisms form a
category. There is no independently chosen functor on a prescribed fiber.

The conventions follow the strong transformations and modifications of Johnson–Yau,
*2-Dimensional Categories*, Chapter 4. In particular the mixed equation expresses
equivariance of the comparison of transport functors.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.NormalizedTransport

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-- A comparison of normalized transports on the prescribed fibers, coherent with units,
composition and the prescribed actions. -/
structure Hom (N N' : NormalizedTransport Γ actions) where
  /-- The natural isomorphism comparing transport along a parameter arrow. -/
  transportIso {p q : Γ} (g : p ⟶ q) : N.transport g ≅ N'.transport g
  /-- The transport comparison preserves the unit comparison. -/
  transportIso_unit (p : Γ) (X : fiber actions p) :
    (transportIso (𝟙 p)).hom.app X ≫ (N'.transportId p).hom.app X =
      (N.transportId p).hom.app X
  /-- The transport comparison preserves the compositors. -/
  transportIso_comp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : g ≫ h = gh)
    (X : fiber actions p) :
    (N.transportComp g h gh hgh).hom.app X ≫ (transportIso gh).hom.app X =
      (transportIso h).hom.app ((N.transport g).obj X) ≫
        (N'.transport h).map ((transportIso g).hom.app X) ≫
          (N'.transportComp g h gh hgh).hom.app X
  /-- The transport comparison is equivariant for every prescribed action functor. -/
  transportIso_comm {p q : Γ} (g : p ⟶ q) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (N.transportCommIso g a).hom.app X ≫ (act actions q a).map ((transportIso g).hom.app X) =
      (transportIso g).hom.app ((act actions p a).obj X) ≫
        (N'.transportCommIso g a).hom.app X

attribute [reassoc] Hom.transportIso_comp Hom.transportIso_comm

namespace Hom

variable {N N' N'' N''' : NormalizedTransport Γ actions}

/-- A morphism of normalized transports is determined by its transport comparisons. -/
@[ext]
lemma ext {φ ψ : Hom N N'}
    (h : ∀ (p q : Γ) (g : p ⟶ q), φ.transportIso g = ψ.transportIso g) : φ = ψ := by
  cases φ
  cases ψ
  congr 1
  funext p q g
  exact h p q g

/-- The identity comparison of normalized transports. -/
def id (N : NormalizedTransport Γ actions) : Hom N N where
  transportIso _ := Iso.refl _
  transportIso_unit _ _ := by simp
  transportIso_comp _ _ _ _ _ := by simp
  transportIso_comm _ _ _ := by simp

/-- Compose comparisons of normalized transports on each transport functor. -/
def comp (φ : Hom N N') (ψ : Hom N' N'') : Hom N N'' where
  transportIso g := φ.transportIso g ≪≫ ψ.transportIso g
  transportIso_unit p X := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [ψ.transportIso_unit, φ.transportIso_unit]
  transportIso_comp g h gh hgh X := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [← Category.assoc, φ.transportIso_comp, Category.assoc, Category.assoc, ψ.transportIso_comp]
    rw [(ψ.transportIso h).hom.naturality_assoc]
  transportIso_comm g a X := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [← Category.assoc, φ.transportIso_comm, Category.assoc, ψ.transportIso_comm]

private def inverseHom (φ : Hom N N') : Hom N' N where
  transportIso g := (φ.transportIso g).symm
  transportIso_unit p X :=
    (Iso.inv_comp_eq ((φ.transportIso (𝟙 p)).app X)).2 (φ.transportIso_unit p X).symm
  transportIso_comp g h gh hgh X := by
    apply (cancel_mono ((φ.transportIso gh).hom.app X)).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [φ.transportIso_comp]
    erw [← (φ.transportIso h).hom.naturality_assoc]
    simp only [Functor.comp_obj]
    simp
  transportIso_comm g a X := by
    rw [← cancel_epi ((φ.transportIso g).hom.app ((act actions _ a).obj X))]
    simp only [Iso.symm_hom, Iso.hom_inv_id_app_assoc]
    rw [← φ.transportIso_comm_assoc]
    simp only [← Functor.map_comp, Iso.hom_inv_id_app]
    simp


end Hom

/-- The category of normalized transports on the prescribed fibers and actions. -/
instance instCategory : Category (NormalizedTransport Γ actions) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp φ := Hom.ext fun _ _ _ ↦ by simp [Hom.id, Hom.comp]
  comp_id φ := Hom.ext fun _ _ _ ↦ by simp [Hom.id, Hom.comp]
  assoc φ ψ χ := Hom.ext fun _ _ _ ↦ by simp [Hom.comp, Iso.trans_assoc]

@[simp]
lemma id_transportIso (N : NormalizedTransport Γ actions) {p q : Γ} (g : p ⟶ q) :
    (Hom.transportIso (𝟙 N) g) = Iso.refl (N.transport g) := (rfl)

@[simp]
lemma comp_transportIso {N N' N'' : NormalizedTransport Γ actions}
    (φ : N ⟶ N') (ψ : N' ⟶ N'') {p q : Γ} (g : p ⟶ q) :
    Hom.transportIso (φ ≫ ψ) g = φ.transportIso g ≪≫ ψ.transportIso g := (rfl)

/-- All comparisons of normalized transports are invertible, making this category a groupoid. -/
instance instIsGroupoid : IsGroupoid (NormalizedTransport Γ actions) where
  all_isIso φ :=
    ⟨⟨Hom.inverseHom φ,
      Hom.ext (fun _ _ _ ↦ by simp [Hom.inverseHom]),
      Hom.ext (fun _ _ _ ↦ by simp [Hom.inverseHom])⟩⟩

/-- The inverse comparison has the inverse natural isomorphism on every transport functor. -/
@[simp]
lemma inv_transportIso {N N' : NormalizedTransport Γ actions}
    (φ : N ⟶ N') {p q : Γ} (g : p ⟶ q) :
    Hom.transportIso (CategoryTheory.inv φ) g = (φ.transportIso g).symm := by
  have h : φ ≫ Hom.inverseHom φ = 𝟙 N :=
    Hom.ext (fun _ _ _ ↦ by simp [Hom.inverseHom])
  rw [IsIso.inv_eq_of_hom_inv_id h]
  rfl

end TauCeti.EquivariantGroupoidLift.NormalizedTransport
