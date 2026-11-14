/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat

/-!
# Monoid actions on commutative Hopf algebras from categorical endomorphisms

Let `H : CommHopfAlgCat R` be a bundled commutative Hopf `R`-algebra and
`ρ : Θ →* CategoryTheory.End H` a monoid homomorphism into its categorical endomorphisms. Because
multiplication in `CategoryTheory.End H` agrees with function composition (`(f * g) h = f (g h)`
rather than categorical diagram order `f ≫ g`), setting `θ • h = (ρ θ).asHom.hom h` defines a
left `MulSemiringAction Θ H` that commutes with the `R`-algebra scalar multiplication.

Declarations live in root `CommHopfAlgCat` because their first explicit argument has Mathlib type
`CommHopfAlgCat R`.

## Main definitions

* `CommHopfAlgCat.mulSemiringActionOfEnd`: the left `MulSemiringAction Θ H` attached to
  `ρ : Θ →* CategoryTheory.End H`.

## Main results

* `CommHopfAlgCat.smul_mulSemiringActionOfEnd`: `θ • h = (ρ θ).asHom.hom h`.
* `CommHopfAlgCat.smulCommClass_mulSemiringActionOfEnd`: the induced `Θ`-action commutes with the
  base `R`-action on `H`.
-/

public section

namespace CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R] (H : CommHopfAlgCat.{v} R)

/-- A monoid homomorphism `ρ : Θ →* CategoryTheory.End H` induces a left action of `Θ` on `H` by
ring endomorphisms (`θ • h = (ρ θ).asHom.hom h`), because multiplication in `CategoryTheory.End H`
agrees with function composition rather than categorical diagram order. -/
@[instance_reducible]
def mulSemiringActionOfEnd {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.End H) :
    MulSemiringAction Θ H where
  smul θ h := (ρ θ).asHom.hom h
  one_smul h := congrArg (fun e : CategoryTheory.End H ↦ e.asHom.hom h) (map_one ρ)
  mul_smul θ₁ θ₂ h := congrArg (fun e : CategoryTheory.End H ↦ e.asHom.hom h) (map_mul ρ θ₁ θ₂)
  smul_zero θ := map_zero (ρ θ).asHom.hom
  smul_add θ := map_add (ρ θ).asHom.hom
  smul_one θ := map_one (ρ θ).asHom.hom
  smul_mul θ := map_mul (ρ θ).asHom.hom

/-- Under `H.mulSemiringActionOfEnd ρ`, `θ • h` is `(ρ θ).asHom.hom h`. -/
@[simp]
theorem smul_mulSemiringActionOfEnd {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.End H)
    (θ : Θ) (h : H) :
    letI := H.mulSemiringActionOfEnd ρ
    θ • h = (ρ θ).asHom.hom h :=
  (rfl)

/-- The `Θ`-action `H.mulSemiringActionOfEnd ρ` commutes with the base `R`-action on `H`. -/
theorem smulCommClass_mulSemiringActionOfEnd {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.End H) :
    letI := H.mulSemiringActionOfEnd ρ
    SMulCommClass Θ R H := by
  let _ := H.mulSemiringActionOfEnd ρ
  exact ⟨fun θ r h ↦ (ρ θ).asHom.hom.toAlgHom.map_smul_of_tower r h⟩

end CommHopfAlgCat
