/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import TauCeti.AlgebraicGeometry.LineBundle.GroupPairing

/-!
# The Mumford correspondence on line-bundle classes

On a monoid scheme `G` over `S`, the normalized Mumford construction is a homomorphism from
`Pic(G)` to `Pic(G ×ₛ G)`. It kills classes pulled back from `S`, commutes with pullback along
homomorphisms, and is invariant under interchange of the factors when `G` is commutative.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.GroupScheme

open TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

variable {S : Scheme.{u}}

/-- The normalized Mumford correspondence, as a homomorphism of Picard groups. Its four
factors are the pullback along multiplication, the inverses of the two projection pullbacks,
and the pullback along the constant map at the identity. -/
noncomputable def mumfordClass (G : Over S) [MonObj G] :
    LineBundleClass G.left →* LineBundleClass (Limits.pullback G.hom G.hom) where
  toFun L := pairing L (fst G G) (snd G G)
  map_one' := pairing_one _ _
  map_mul' L M := pairing_mul L M _ _

/-- The normalized Mumford class is the pairing of the two projections of `G ×ₛ G`. -/
theorem mumfordClass_eq_pairing (G : Over S) [MonObj G] (L : LineBundleClass G.left) :
    mumfordClass G L = pairing L (fst G G) (snd G G) :=
  (rfl)

/-- The four factors of the normalized Mumford correspondence on a line-bundle class. -/
theorem mumfordClass_apply (G : Over S) [MonObj G] (L : LineBundleClass G.left) :
    mumfordClass G L = pullback μ[G].left L /
      (pullback (fst G G).left L * pullback (snd G G).left L) *
        pullback (toUnit (G ⊗ G) ≫ η[G]).left L := by
  have hmul : fst G G * snd G G = μ[G] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  simp only [mumfordClass_eq_pairing, pairing_def, hmul, Hom.one_def, div_eq_mul_inv,
    mul_inv, mul_assoc]

/-- The Mumford class restricts to the trivial class along `x ↦ (x, 1)`. -/
@[simp]
theorem pullback_lift_id_unit_mumfordClass (G : Over S) [MonObj G] (L : LineBundleClass G.left) :
    pullback (Limits.pullback.lift (𝟙 G.left) (G.hom ≫ η[G].left) (by simp))
      (mumfordClass G L) = 1 := by
  suffices pullback (lift (𝟙 G) (toUnit G ≫ η[G])).left (mumfordClass G L) = 1 by
    simpa only [Over.lift_left, Over.comp_left, Over.toUnit_left, Over.id_left] using this
  rw [mumfordClass_eq_pairing, pullback_pairing, lift_fst, lift_snd, ← Hom.one_def]
  exact pairing_one_right L _

/-- The Mumford class restricts to the trivial class along `x ↦ (1, x)`. -/
@[simp]
theorem pullback_lift_unit_id_mumfordClass (G : Over S) [MonObj G] (L : LineBundleClass G.left) :
    pullback (Limits.pullback.lift (G.hom ≫ η[G].left) (𝟙 G.left) (by simp))
      (mumfordClass G L) = 1 := by
  suffices pullback (lift (toUnit G ≫ η[G]) (𝟙 G)).left (mumfordClass G L) = 1 by
    simpa only [Over.lift_left, Over.comp_left, Over.toUnit_left, Over.id_left] using this
  rw [mumfordClass_eq_pairing, pullback_pairing, lift_fst, lift_snd, ← Hom.one_def]
  exact pairing_one_left L _

/-- On a commutative monoid scheme, swapping the two factors preserves the Mumford class. -/
@[simp]
theorem pullback_pullbackSymmetry_hom_mumfordClass (G : Over S) [MonObj G] [IsCommMonObj G]
    (L : LineBundleClass G.left) :
    pullback (Limits.pullbackSymmetry G.hom G.hom).hom (mumfordClass G L) =
      mumfordClass G L := by
  rw [← Over.braiding_hom_left (R := G) (S := G)]
  simp only [mumfordClass_apply, div_eq_mul_inv, pullback_mul, pullback_inv, pullback_comp,
    ← Over.comp_left, IsCommMonObj.mul_comm, braiding_hom_fst, braiding_hom_snd, comp_toUnit_assoc,
    mul_comm (pullback (fst G G).left L) (pullback (snd G G).left L)]

/-- The Mumford correspondence commutes with pullback along a homomorphism of monoid schemes. -/
@[simp]
theorem pullback_mumfordClass {G H : Over S} [MonObj G] [MonObj H] (f : G ⟶ H)
    [IsMonHom f] (L : LineBundleClass H.left) :
    pullback (X := Limits.pullback G.hom G.hom) (Y := Limits.pullback H.hom H.hom)
      (f ⊗ₘ f).left (mumfordClass H L) = mumfordClass G (pullback f.left L) := by
  simp only [mumfordClass_apply, div_eq_mul_inv, pullback_mul, pullback_inv, pullback_comp,
    ← Over.comp_left, IsMonHom.mul_hom, tensorHom_fst, tensorHom_snd, comp_toUnit_assoc,
    Category.assoc, IsMonHom.one_hom]

/-- A line-bundle class pulled back from the base has trivial Mumford correspondence. -/
@[simp]
theorem mumfordClass_pullback_hom (G : Over S) [MonObj G] (L : LineBundleClass S) :
    mumfordClass G (pullback G.hom L) = 1 := by
  simp only [mumfordClass_apply, pullback_comp, Over.w, div_mul_eq_mul_div, div_self']

end TauCeti.GroupScheme
