/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Comap maps of structure sheaves and restriction

For a ring homomorphism `f : R →+* S`, Mathlib's `AlgebraicGeometry.StructureSheaf.comap f U V`
is the ring map from the sections of the structure sheaf of `Spec R` on `U` to those of `Spec S`
on `V`, for opens with `V ⊆ (Spec f)⁻¹ U`. This file records that these maps commute with the
restriction maps of both structure sheaves, which makes the family of comap maps a morphism of
sheaves from the structure sheaf of `Spec R` to the pushforward of that of `Spec S`, and that
`comap f U V` depends on `f` only up to equality.

## Main results

* `AlgebraicGeometry.StructureSheaf.map_comp_comap`: restricting after a comap map is a comap map.
* `AlgebraicGeometry.StructureSheaf.comap_comp_map`: a comap map after restricting is a comap map.
* `AlgebraicGeometry.StructureSheaf.comap_congr`: equal ring homomorphisms have equal comap maps.
-/

public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.StructureSheaf

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Restricting from `V` to `W ⊆ V` after the comap map `Γ(Spec R, U) → Γ(Spec S, V)` gives the
comap map `Γ(Spec R, U) → Γ(Spec S, W)`. -/
theorem map_comp_comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    {V W : Opens (PrimeSpectrum.Top S)} (h : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (i : W ⟶ V) :
    ((Spec.structureSheaf S).obj.map i.op).hom.comp (comap f U V h) =
      comap f U W fun _ hp ↦ h (leOfHom i hp) := by
  rw [← comap_id_eq_map]
  exact (comap_comp f (RingHom.id S) U V W _ _).symm

/-- Restricting from `U` to `U' ⊆ U` before the comap map `Γ(Spec R, U') → Γ(Spec S, W)` gives
the comap map `Γ(Spec R, U) → Γ(Spec S, W)`. -/
theorem comap_comp_map (f : R →+* S) {U U' : Opens (PrimeSpectrum.Top R)}
    (W : Opens (PrimeSpectrum.Top S)) (h : W.1 ⊆ PrimeSpectrum.comap f ⁻¹' U'.1) (i : U' ⟶ U) :
    (comap f U' W h).comp ((Spec.structureSheaf R).obj.map i.op).hom =
      comap f U W (h.trans fun _ hp ↦ leOfHom i hp) := by
  rw [← comap_id_eq_map]
  exact (comap_comp (RingHom.id R) f U U' W _ _).symm

/-- Equal ring homomorphisms have equal comap maps; this transports a comap map along an equation
between ring homomorphisms. -/
theorem comap_congr {f g : R →+* S} (hfg : f = g) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hf : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (hg : V.1 ⊆ PrimeSpectrum.comap g ⁻¹' U.1) : comap f U V hf = comap g U V hg := by
  subst hfg
  rfl

end AlgebraicGeometry.StructureSheaf
