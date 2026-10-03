/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.AsSubring

/-!
# Regular and rational Kähler differentials

Let `A` be a domain over a commutative ring `R`, with fraction field `F`. A rational
differential in `Ω[F⁄R]` comes from `Ω[A⁄R]` if and only if it comes from the differentials
of `A` localized at every maximal ideal. More generally, the image of the differentials of
any localization of `A` is the localization of the image of `Ω[A⁄R]`.

For a formally smooth algebra `A`, the map `Ω[A⁄R] → Ω[F⁄R]` is injective. Thus regular
differentials can be treated as rational differentials, and their regularity can be checked
in the local rings. This is the affine-local input to identifying the differential sheaf
of a smooth curve with a divisor sheaf in its rational differential space.

No perfectness, finite type, or Noetherian hypothesis is needed for the local criterion.

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

variable (R A B F : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing F]
  [Algebra R A] [Algebra R B] [Algebra R F] [Algebra A B] [Algebra A F]
  [Algebra B F] [IsScalarTower R A B] [IsScalarTower R A F]
  [IsScalarTower R B F] [IsScalarTower A B F]

/-- The rational image of the differentials of `S⁻¹A` is the localization at `S` of the
rational image of the differentials of `A`. The equality is in `A`-submodules of `Ω[F⁄R]`. -/
theorem range_kaehler_map_localization (S : Submonoid A) [IsLocalization S B] :
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

variable {B}
variable [IsDomain A] [IsFractionRing A F]

/-- A rational differential comes from `Ω[A⁄R]` exactly when it comes from the differentials
of every maximal localization. Each localization is realized as Mathlib's canonical
subalgebra of the fraction field. -/
theorem mem_range_kaehler_map_fractionRing_iff (ω : Ω[F⁄R]) :
    ω ∈ (map R R A F).range ↔
      ∀ (P : Ideal A) [P.IsMaximal],
        let B := Localization.subalgebra F P.primeCompl P.primeCompl_le_nonZeroDivisors
        ω ∈ ((map R R B F).restrictScalars A).range := by
  have hlocal : ∀ (P : Ideal A) [P.IsMaximal],
      IsLocalizedModule P.primeCompl (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) :=
    fun P _ ↦ isLocalizedModule_id P.primeCompl Ω[F⁄R]
      (Localization.subalgebra F P.primeCompl P.primeCompl_le_nonZeroDivisors)
  constructor
  · intro h P hP
    dsimp only
    rw [range_kaehler_map_localization R A _ F P.primeCompl]
    exact ⟨ω, h, 1, by simp⟩
  · intro h
    apply @Submodule.mem_of_localization_maximal A Ω[F⁄R] _ _ _
      (fun _ _ ↦ Ω[F⁄R]) _ _ (fun _ _ ↦ LinearMap.id) hlocal ω (map R R A F).range
    intro P hP
    rw [← range_kaehler_map_localization R A
      (Localization.subalgebra F P.primeCompl P.primeCompl_le_nonZeroDivisors) F P.primeCompl]
    exact h P

/-- If the module of differentials is torsion-free (as for a formally smooth algebra), a rational
differential has a unique regular preimage exactly when it is regular at every maximal
localization. -/
theorem existsUnique_kaehler_preimage_iff [Module.IsTorsionFree A Ω[A⁄R]] (ω : Ω[F⁄R]) :
    (∃! η : Ω[A⁄R], map R R A F η = ω) ↔
      ∀ (P : Ideal A) [P.IsMaximal],
        let B := Localization.subalgebra F P.primeCompl P.primeCompl_le_nonZeroDivisors
        ω ∈ ((map R R B F).restrictScalars A).range := by
  have hinj : Function.Injective (map R R A F) :=
    (IsLocalizedModule.injective_iff_isRegular A⁰ (map R R A F)).mpr
      fun s x y h ↦ (IsSMulRegular.of_ne_zero (r := (s : A)) (M := Ω[A⁄R])
        (nonZeroDivisors.ne_zero s.property)) h
  rw [← mem_range_kaehler_map_fractionRing_iff R A F, LinearMap.mem_range]
  exact ⟨fun ⟨η, hη, _⟩ ↦ ⟨η, hη⟩,
    fun ⟨η, hη⟩ ↦ ⟨η, hη, fun ζ hζ ↦ hinj (hζ.trans hη.symm)⟩⟩

end Maximal

end TauCeti
