/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
import TauCeti.RingTheory.Ideal.Maps

/-!
# A fraction ring of a localization is a fraction ring of the base

Let `S` be the localization of a ring `R` at a submonoid `M` of non-zero-divisors. A total ring
of fractions `T` of `S` is then a total ring of fractions of `R`
(`TauCeti.IsFractionRing.of_isLocalization_of_isFractionRing`). Mathlib proves the converse
direction, from a fraction ring of `R` to one of `S`, as
`IsFractionRing.isFractionRing_of_isLocalization`.
This lets a statement about the fraction field of a localization of a domain be reduced to the
fraction field of the domain itself. The non-zero-divisor hypothesis holds whenever a domain is
localized to a nontrivial ring (`TauCeti.IsLocalization.le_nonZeroDivisors_of_nontrivial`, in
`TauCeti.RingTheory.Localization.Defs`).

Similarly, if `S` is a localization of `B` at a submonoid `M`, then any fraction ring `F` of
`B ⧸ P` (for a prime `P` of `B`) receiving a compatible `S ⧸ P S`-algebra structure is a fraction
ring of `S ⧸ P S` (`TauCeti.IsFractionRing.quotient_map_of_isLocalization`), and
`TauCeti.IsFractionRing.with_quotient_map_isFractionRing` installs that induced `S ⧸ P S`-algebra
structure and scalar towers from a compatible `S`-algebra structure on `F`.
-/

public section

namespace TauCeti.IsFractionRing

variable {R : Type*} [CommRing R] (M : Submonoid R) (S T : Type*) [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- If `S` is the localization of `R` at a submonoid `M` of non-zero-divisors, then a total ring of
fractions of `S` is a total ring of fractions of `R`. -/
theorem of_isLocalization_of_isFractionRing [IsLocalization M S] [IsFractionRing S T]
    (hM : M ≤ nonZeroDivisors R) : IsFractionRing R T := by
  -- `T` is the localization of `R` at the preimage of the non-zero-divisors of `S`, which are
  -- exactly the non-zero-divisors of `R`, since `R ⟶ S` is injective and localization maps
  -- non-zero-divisors to non-zero-divisors
  have := IsLocalization.localization_localization_isLocalization_of_has_all_units M
    (nonZeroDivisors S) T fun _ hx ↦ hx.mem_nonZeroDivisors
  rwa [le_antisymm (comap_nonZeroDivisors_le_of_injective (IsLocalization.injective S hM))
    (IsLocalization.nonZeroDivisors_le_comap M S)] at this

/-- If `P` is a prime of `B`, `S` is a localization of `B` at `M`, and `F` is a fraction ring of
`B ⧸ P` with compatible `S`- and `(S ⧸ P S)`-algebra structures, then `F` is a fraction ring of
`S ⧸ P S`. -/
theorem quotient_map_of_isLocalization {B S F : Type*} [CommRing B] {P : Ideal B} [P.IsPrime]
    (M : Submonoid B) [CommRing S] [Algebra B S] [IsLocalization M S] [CommRing F] [Algebra B F]
    [Algebra (B ⧸ P) F] [IsScalarTower B (B ⧸ P) F] [IsFractionRing (B ⧸ P) F] [Algebra S F]
    [IsScalarTower B S F] [Algebra (S ⧸ P.map (algebraMap B S)) F]
    [IsScalarTower S (S ⧸ P.map (algebraMap B S)) F] :
    IsFractionRing (S ⧸ P.map (algebraMap B S)) F := by
  have : IsScalarTower (B ⧸ P) (S ⧸ P.map (algebraMap B S)) F := .of_algebraMap_eq fun x ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hb : algebraMap (B ⧸ P) (S ⧸ P.map (algebraMap B S)) (algebraMap B (B ⧸ P) b) =
        algebraMap S (S ⧸ P.map (algebraMap B S)) (algebraMap B S b) := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_quotient_map_quotient,
        ← Ideal.Quotient.algebraMap_eq]
    simp [hb, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply B (B ⧸ P) F,
      ← IsScalarTower.algebraMap_apply S (S ⧸ P.map (algebraMap B S)) F,
      ← IsScalarTower.algebraMap_apply B S F]
  exact _root_.IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid (B ⧸ P) M) (S ⧸ P.map (algebraMap B S)) F

/-- If `P` is a prime of `B`, `S` is a localization of `B` at `M`, and `F` is a fraction ring of
`B ⧸ P` receiving a compatible `S`-algebra structure over `R`, then `F` carries the induced
`S ⧸ P S`-algebra structure, compatible scalar towers over `S` and `R`, and is a fraction ring of
`S ⧸ P S`. -/
theorem with_quotient_map_isFractionRing {R B S F : Type*} [CommRing R] [CommRing B]
    {P : Ideal B} [P.IsPrime] (M : Submonoid B) [CommRing S] [Algebra R S]
    [Algebra B S] [IsLocalization M S] [CommRing F] [Algebra R F] [Algebra B F]
    [Algebra (B ⧸ P) F] [IsScalarTower B (B ⧸ P) F] [IsFractionRing (B ⧸ P) F] [Algebra S F]
    [IsScalarTower B S F] [IsScalarTower R S F]
    {C : Prop}
    (h : [Algebra (S ⧸ P.map (algebraMap B S)) F] →
      [IsScalarTower S (S ⧸ P.map (algebraMap B S)) F] →
      [IsScalarTower R (S ⧸ P.map (algebraMap B S)) F] →
      [IsFractionRing (S ⧸ P.map (algebraMap B S)) F] → C) : C := by
  let g : (S ⧸ P.map (algebraMap B S)) →ₐ[R] F :=
    Ideal.Quotient.liftₐ (P.map (algebraMap B S)) (IsScalarTower.toAlgHom R S F)
      Ideal.map_le_ker_of_isScalarTower_quotient
  let : Algebra (S ⧸ P.map (algebraMap B S)) F := g.toRingHom.toAlgebra
  have : IsScalarTower S (S ⧸ P.map (algebraMap B S)) F := .of_algebraMap_eq fun s ↦ by
    have hs := AlgHom.congr_fun
      (Ideal.Quotient.liftₐ_comp (P.map (algebraMap B S)) (IsScalarTower.toAlgHom R S F)
        Ideal.map_le_ker_of_isScalarTower_quotient) s
    simpa [g, RingHom.algebraMap_toAlgebra, Ideal.Quotient.algebraMap_eq] using hs.symm
  have : IsScalarTower R (S ⧸ P.map (algebraMap B S)) F :=
    .of_algebraMap_eq fun c ↦ by simp [g, RingHom.algebraMap_toAlgebra]
  have : IsFractionRing (S ⧸ P.map (algebraMap B S)) F :=
    quotient_map_of_isLocalization M
  exact h

end TauCeti.IsFractionRing
