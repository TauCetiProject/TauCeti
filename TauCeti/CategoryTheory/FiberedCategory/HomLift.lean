/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Lifts with fixed endpoints

When a morphism `f` of the base already has the source `p.obj a` and target `p.obj b`, a morphism
`φ : a ⟶ b` lifts `f` through `p` exactly when `p.map φ = f`. For arbitrary endpoints, `φ` lifts
`f` exactly when `p.map φ` and `f` are the same arrow of the base, and a morphism into the target
of a lift `φ` of `f` lifts a composite `g ≫ f` exactly when its image is `g ≫ p.map φ`.
-/

public section

namespace CategoryTheory.Functor

variable {𝒮 : Type*} {𝒳 : Type*} [Category* 𝒳] [Category* 𝒮] {p : 𝒳 ⥤ 𝒮}

/-- A morphism `φ : a ⟶ b` lifts a morphism `f : p.obj a ⟶ p.obj b` exactly when `p.map φ = f`. -/
lemma isHomLift_iff_map_eq {a b : 𝒳} {f : p.obj a ⟶ p.obj b} {φ : a ⟶ b} :
    p.IsHomLift f φ ↔ p.map φ = f :=
  ⟨fun _ ↦ (IsHomLift.eq_of_isHomLift p f φ).symm, fun h ↦ h ▸ IsHomLift.map φ⟩

/-- A morphism `φ : a ⟶ b` lifts a morphism `f : R ⟶ S` exactly when `p.map φ` and `f` are equal
as arrows of the base. -/
lemma isHomLift_iff_arrow_mk_eq {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} :
    p.IsHomLift f φ ↔ Arrow.mk (p.map φ) = Arrow.mk f := by
  rw [Arrow.mk_eq_mk_iff]
  exact ⟨fun _ ↦ ⟨IsHomLift.domain_eq p f φ, IsHomLift.codomain_eq p f φ, IsHomLift.fac' p f φ⟩,
    fun ⟨ha, hb, h⟩ ↦ IsHomLift.of_fac' (p := p) f φ ha hb h⟩

/-- If `φ : b ⟶ c` lies over `f : p.obj b ⟶ S`, then a morphism `ψ : a ⟶ c` lies over `g ≫ f`
exactly when `p.map ψ = g ≫ p.map φ`. -/
lemma isHomLift_comp_iff_map_eq {a b c : 𝒳} {S : 𝒮} {f : p.obj b ⟶ S} {φ : b ⟶ c}
    (hφ : p.IsHomLift f φ) {g : p.obj a ⟶ p.obj b} {ψ : a ⟶ c} :
    p.IsHomLift (g ≫ f) ψ ↔ p.map ψ = g ≫ p.map φ := by
  obtain rfl := IsHomLift.codomain_eq p f φ
  obtain rfl := IsHomLift.eq_of_isHomLift p f φ
  exact isHomLift_iff_map_eq

end CategoryTheory.Functor
