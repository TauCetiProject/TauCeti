/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Localization of Kähler differentials

Let `A` be an `R`-algebra and `F` a commutative `A`-algebra. For a localization `B` of `A`
receiving a compatible map to `F`, the image of `Ω[B⁄R]` in `Ω[F⁄R]` is the localization of
the image of `Ω[A⁄R]`. Consequently, a differential in `Ω[F⁄R]` comes from `Ω[A⁄R]` if and
only if it comes from the differentials of `A` localized at every maximal ideal. No
domain, fraction-field, perfectness, finite type, or Noetherian hypothesis is needed.

The main application is to a domain `A` with fraction field `F`: there the criterion says that
regularity of a rational differential can be checked in the local rings of `A`. When
`Ω[A⁄R]` is torsion-free, for instance when `A` is formally smooth over `R`, the map
`Ω[A⁄R] → Ω[F⁄R]` is injective, so regular differentials can be treated as rational
differentials. This injectivity is not restated here: it follows from Mathlib's
`IsLocalizedModule.injective_iff_isRegular`, applied to the instance
`KaehlerDifferential.isLocalizedModule_map`, together with
`Module.Flat.isSMulRegular_of_nonZeroDivisors` in the formally smooth case.

## Main results

* `TauCeti.KaehlerDifferential.range_map_eq_localized₀_range`: localization of differentials
  localizes their image in the target differential module.
* `TauCeti.KaehlerDifferential.mem_range_map_iff_forall_isMaximal`: membership in the global
  image can be checked using any family of maximal localizations.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 8.
* The Stacks Project, Tag 00RM (localization of differentials) and Tag 031J
  (projectivity of differentials of a formally smooth algebra).
-/

public section

noncomputable section

namespace TauCeti

open KaehlerDifferential
open scoped nonZeroDivisors

namespace KaehlerDifferential

variable (R A B F : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing F]
  [Algebra R A] [Algebra R B] [Algebra R F] [Algebra A B] [Algebra A F]
  [Algebra B F] [IsScalarTower R A B] [IsScalarTower R A F]
  [IsScalarTower R B F] [IsScalarTower A B F]

/-- The image of the differentials of `S⁻¹A` in `Ω[F⁄R]` is the localization at `S` of the
image of the differentials of `A`. Here `F` is any commutative algebra receiving `B`, and
the equality is in `A`-submodules of `Ω[F⁄R]`. -/
theorem range_map_eq_localized₀_range (S : Submonoid A) [IsLocalization S B] :
    haveI := isLocalizedModule_id S Ω[F⁄R] B
    ((map R R B F).restrictScalars A).range =
      (map R R A F).range.localized₀ S (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) := by
  have : IsLocalizedModule S (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) :=
    isLocalizedModule_id S Ω[F⁄R] B
  have hmap : IsLocalizedModule.map S (map R R A B)
      (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) (map R R A F) =
        (map R R B F).restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext S (map R R A B)
      (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R])
    rw [IsLocalizedModule.map_comp]
    apply LinearMap.ext_on (span_range_derivation R A)
    rintro _ ⟨a, rfl⟩
    simp [map_D, ← IsScalarTower.algebraMap_apply A B F]
  rw [← hmap]
  exact LinearMap.range_localizedMap_eq_localized₀_range _ _ _ _

section Maximal

variable (Aₚ : ∀ (P : Ideal A) [P.IsMaximal], Type*)
  [∀ (P : Ideal A) [P.IsMaximal], CommRing (Aₚ P)]
  [∀ (P : Ideal A) [P.IsMaximal], Algebra A (Aₚ P)]
  [∀ (P : Ideal A) [P.IsMaximal], IsLocalization.AtPrime (Aₚ P) P]
  [∀ (P : Ideal A) [P.IsMaximal], Algebra R (Aₚ P)]
  [∀ (P : Ideal A) [P.IsMaximal], Algebra (Aₚ P) F]
  [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R A (Aₚ P)]
  [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R (Aₚ P) F]
  [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower A (Aₚ P) F]

/-- A differential in `Ω[F⁄R]` comes from `Ω[A⁄R]` exactly when it comes from the
differentials of every maximal localization, using any family of localization models
mapping compatibly to `F`. -/
theorem mem_range_map_iff_forall_isMaximal (ω : Ω[F⁄R]) :
    ω ∈ (map R R A F).range ↔
      ∀ (P : Ideal A) [P.IsMaximal],
        ω ∈ ((map R R (Aₚ P) F).restrictScalars A).range := by
  have hlocal (P : Ideal A) [P.IsMaximal] :
      IsLocalizedModule P.primeCompl (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) :=
    isLocalizedModule_id P.primeCompl Ω[F⁄R] (Aₚ P)
  refine ⟨fun h P _ ↦ ?_, fun h ↦ ?_⟩
  · rw [range_map_eq_localized₀_range R A (Aₚ P) F P.primeCompl]
    exact ⟨ω, h, 1, by simp⟩
  · -- Pass the localization family explicitly: instance synthesis does not recover this
    -- higher-order family from `hlocal`. Name the module and map families to fix their roles.
    refine @Submodule.mem_of_localization_maximal (R := A) (M := Ω[F⁄R])
      (Mₚ := fun _ _ ↦ Ω[F⁄R]) (f := fun _ _ ↦ LinearMap.id) _ _ _ _ _ hlocal ω _
      fun P _ ↦ ?_
    rw [← range_map_eq_localized₀_range R A (Aₚ P) F P.primeCompl]
    exact h P

end Maximal

end KaehlerDifferential

end TauCeti
