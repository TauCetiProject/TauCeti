/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Tame.Presentation
-- Constructing the free-group change of relator needs the arithmetic presentation's bodies.
import all TauCeti.NumberTheory.LocalField.Tame.Presentation

/-!
# The geometric Frobenius convention for the tame presentation

Arithmetic Frobenius satisfies `σ τ σ⁻¹ = τ ^ q`. Marking its inverse as geometric Frobenius
instead gives the presentation `⟨γ, τ | γ⁻¹ τ γ = τ ^ q⟩`. This file identifies these two
profinite presentations, including the images of their marked generators in both directions.

The geometric presentation has the same unramified coordinate as the arithmetic presentation:
its marked Frobenius has coordinate `zHat.gen⁻¹`. Composing the identification with
`tameQuotientEquiv` identifies the tame quotient with the geometric presentation, carrying
the inverse of the chosen arithmetic Frobenius lift to the geometric marked generator.

The change of presentation uses `presentedProfiniteGroup.congr`, induced by the involution
of the free profinite group that inverts the Frobenius generator and fixes the inertia generator.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.5.2)–(7.5.3).
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The geometric Iwasawa relator `γ⁻¹ τ γ τ⁻ᵠ`, where `γ = of 0`, `τ = of 1`, and
`q` is the cardinality of the residue field. -/
def iwasawaRelatorGeometric : freeProfiniteGroup (ULift.{u} (Fin 2)) :=
  (freeProfiniteGroup.of (ULift.up 0))⁻¹ * freeProfiniteGroup.of (ULift.up 1) *
    freeProfiniteGroup.of (ULift.up 0) *
      (freeProfiniteGroup.of (ULift.up 1) ^ Nat.card 𝓀[K])⁻¹

/-- The word defining the geometric Iwasawa relator. -/
theorem iwasawaRelatorGeometric_def :
    iwasawaRelatorGeometric K =
      (freeProfiniteGroup.of (ULift.up 0))⁻¹ * freeProfiniteGroup.of (ULift.up 1) *
        freeProfiniteGroup.of (ULift.up 0) *
          (freeProfiniteGroup.of (ULift.up 1) ^ Nat.card 𝓀[K])⁻¹ := (rfl)

/-- The tame presentation with a geometric Frobenius generator:
`⟨γ, τ | γ⁻¹ τ γ = τ ^ q⟩`. -/
abbrev IwasawaGroupGeometric : Type u :=
  presentedProfiniteGroup (ULift.{u} (Fin 2)) {iwasawaRelatorGeometric K}

/-- The marked geometric Frobenius generator of the geometric Iwasawa presentation. -/
abbrev iwasawaSigmaGeometric : IwasawaGroupGeometric K :=
  presentedProfiniteGroup.of {iwasawaRelatorGeometric K} (ULift.up 0)

/-- The marked tame inertia generator of the geometric Iwasawa presentation. -/
abbrev iwasawaTauGeometric : IwasawaGroupGeometric K :=
  presentedProfiniteGroup.of {iwasawaRelatorGeometric K} (ULift.up 1)

/-- The geometric Frobenius generator is the image of the zeroth free generator. -/
theorem iwasawaSigmaGeometric_def :
    iwasawaSigmaGeometric K =
      presentedProfiniteGroup.of {iwasawaRelatorGeometric K} (ULift.up 0) := (rfl)

/-- The tame inertia generator is the image of the first free generator. -/
theorem iwasawaTauGeometric_def :
    iwasawaTauGeometric K =
      presentedProfiniteGroup.of {iwasawaRelatorGeometric K} (ULift.up 1) := (rfl)

private def iwasawaGeneratorInversion :
    freeProfiniteGroup (ULift.{u} (Fin 2)) →ₜ* freeProfiniteGroup (ULift.{u} (Fin 2)) :=
  freeProfiniteGroup.lift fun i ↦
    ![(freeProfiniteGroup.of (ULift.up 0))⁻¹, freeProfiniteGroup.of (ULift.up 1)] i.down

private theorem iwasawaGeneratorInversion_involutive :
    Function.Involutive iwasawaGeneratorInversion.{u} := by
  have h : iwasawaGeneratorInversion.comp iwasawaGeneratorInversion =
      ContinuousMonoidHom.id (freeProfiniteGroup (ULift.{u} (Fin 2))) :=
    freeProfiniteGroup.hom_ext fun ⟨i⟩ ↦ by
      fin_cases i <;> simp [iwasawaGeneratorInversion]
  exact fun x ↦ DFunLike.congr_fun h x

private def iwasawaFreeGeometricEquiv :
    freeProfiniteGroup (ULift.{u} (Fin 2)) ≃ₜ* freeProfiniteGroup (ULift.{u} (Fin 2)) where
  toFun := iwasawaGeneratorInversion
  invFun := iwasawaGeneratorInversion
  left_inv := iwasawaGeneratorInversion_involutive
  right_inv := iwasawaGeneratorInversion_involutive
  map_mul' := map_mul _
  continuous_toFun := map_continuous _
  continuous_invFun := map_continuous _

private theorem iwasawaFreeGeometricEquiv_symm :
    iwasawaFreeGeometricEquiv.{u}.symm = iwasawaFreeGeometricEquiv :=
  ContinuousMulEquiv.ext fun _ ↦ rfl

/-- Changing from arithmetic to geometric Frobenius identifies the two tame presentations,
sending the arithmetic Frobenius generator to the inverse of the geometric generator and
preserving the tame inertia generator. -/
def iwasawaGeometricEquiv : IwasawaGroup K ≃ₜ* IwasawaGroupGeometric K :=
  presentedProfiniteGroup.congr iwasawaFreeGeometricEquiv
    (fun r hr ↦ by
      rw [Set.mem_singleton_iff.1 hr]
      simpa [iwasawaFreeGeometricEquiv, iwasawaGeneratorInversion, iwasawaRelator,
        iwasawaRelatorGeometric] using
        presentedProfiniteGroup.mk_relator (rels := {iwasawaRelatorGeometric K}) _
          (Set.mem_singleton (iwasawaRelatorGeometric K)))
    (fun r hr ↦ by
      rw [Set.mem_singleton_iff.1 hr]
      rw [iwasawaFreeGeometricEquiv_symm]
      simpa [iwasawaFreeGeometricEquiv, iwasawaGeneratorInversion, iwasawaRelator,
        iwasawaRelatorGeometric] using
        presentedProfiniteGroup.mk_relator (rels := {iwasawaRelator K}) _
          (Set.mem_singleton (iwasawaRelator K)))

/-- Arithmetic Frobenius becomes the inverse of the geometric marked generator. -/
@[simp]
theorem iwasawaGeometricEquiv_iwasawaSigma :
    iwasawaGeometricEquiv K (iwasawaSigma K) = (iwasawaSigmaGeometric K)⁻¹ := by
  rw [iwasawaSigma, ← presentedProfiniteGroup.mk_of, iwasawaGeometricEquiv,
    presentedProfiniteGroup.congr_mk]
  simp [iwasawaFreeGeometricEquiv, iwasawaGeneratorInversion]

/-- Changing the Frobenius convention preserves the marked tame inertia generator. -/
@[simp]
theorem iwasawaGeometricEquiv_iwasawaTau :
    iwasawaGeometricEquiv K (iwasawaTau K) = iwasawaTauGeometric K := by
  rw [iwasawaTau, ← presentedProfiniteGroup.mk_of, iwasawaGeometricEquiv,
    presentedProfiniteGroup.congr_mk]
  simp [iwasawaFreeGeometricEquiv, iwasawaGeneratorInversion]

/-- Geometric Frobenius becomes the inverse of the arithmetic marked generator. -/
@[simp]
theorem iwasawaGeometricEquiv_symm_iwasawaSigmaGeometric :
    (iwasawaGeometricEquiv K).symm (iwasawaSigmaGeometric K) = (iwasawaSigma K)⁻¹ := by
  rw [iwasawaSigmaGeometric, ← presentedProfiniteGroup.mk_of, iwasawaGeometricEquiv,
    presentedProfiniteGroup.congr_symm_mk]
  rw [iwasawaFreeGeometricEquiv_symm]
  simp [iwasawaFreeGeometricEquiv, iwasawaGeneratorInversion]

/-- Changing back to arithmetic Frobenius preserves the marked tame inertia generator. -/
@[simp]
theorem iwasawaGeometricEquiv_symm_iwasawaTauGeometric :
    (iwasawaGeometricEquiv K).symm (iwasawaTauGeometric K) = iwasawaTau K := by
  rw [iwasawaTauGeometric, ← presentedProfiniteGroup.mk_of, iwasawaGeometricEquiv,
    presentedProfiniteGroup.congr_symm_mk]
  rw [iwasawaFreeGeometricEquiv_symm]
  simp [iwasawaFreeGeometricEquiv, iwasawaGeneratorInversion]

/-- The geometric Iwasawa relation: conjugation by inverse geometric Frobenius raises the
inertia generator to the residue-cardinality power. -/
theorem inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul :
    (iwasawaSigmaGeometric K)⁻¹ * iwasawaTauGeometric K * iwasawaSigmaGeometric K =
      iwasawaTauGeometric K ^ Nat.card 𝓀[K] := by
  simpa using congrArg (iwasawaGeometricEquiv K) (iwasawaSigma_mul_iwasawaTau_mul_inv K)

/-- The unramified coordinate on the geometric presentation, transported from the arithmetic
presentation. Its Frobenius generator has coordinate `zHat.gen⁻¹`. -/
def iwasawaCoordinateGeometric : IwasawaGroupGeometric K →ₜ* zHat.{u} :=
  (iwasawaCoordinate K).comp (iwasawaGeometricEquiv K).symm

/-- Changing Frobenius conventions preserves the unramified coordinate. -/
@[simp]
theorem iwasawaCoordinateGeometric_iwasawaGeometricEquiv (x : IwasawaGroup K) :
    iwasawaCoordinateGeometric K (iwasawaGeometricEquiv K x) = iwasawaCoordinate K x := by
  simp [iwasawaCoordinateGeometric]

/-- The geometric Frobenius generator has inverse arithmetic Frobenius coordinate. -/
@[simp]
theorem iwasawaCoordinateGeometric_iwasawaSigmaGeometric :
    iwasawaCoordinateGeometric K (iwasawaSigmaGeometric K) = zHat.gen⁻¹ := by
  simp [iwasawaCoordinateGeometric]

/-- The unramified coordinate kills the geometric presentation's inertia generator. -/
@[simp]
theorem iwasawaCoordinateGeometric_iwasawaTauGeometric :
    iwasawaCoordinateGeometric K (iwasawaTauGeometric K) = 1 := by
  simp [iwasawaCoordinateGeometric]

variable {K} {σ : Field.absoluteGaloisGroup K}
  (hσ : IsArithFrobeniusLift K σ) (τ : inertiaSubgroup K)
  (hτ : (Subgroup.zpowers (inertiaTameCharacter K τ)).topologicalClosure = ⊤)

/-- The tame quotient identified with the geometric Iwasawa presentation using the inverse
of the chosen arithmetic Frobenius lift and the chosen tame inertia generator. -/
def tameQuotientGeometricEquiv : tameQuotient K ≃ₜ* IwasawaGroupGeometric K :=
  (tameQuotientEquiv hσ τ hτ).trans (iwasawaGeometricEquiv K)

/-- The class of an arithmetic Frobenius lift is the inverse geometric marked generator. -/
@[simp]
theorem tameQuotientGeometricEquiv_toTameQuotient_frobenius :
    tameQuotientGeometricEquiv hσ τ hτ (toTameQuotient K σ) =
      (iwasawaSigmaGeometric K)⁻¹ := by
  simp [tameQuotientGeometricEquiv]

/-- The class of the geometric Frobenius lift is the geometric marked generator. -/
theorem tameQuotientGeometricEquiv_toTameQuotient_frobenius_inv :
    tameQuotientGeometricEquiv hσ τ hτ (toTameQuotient K σ⁻¹) = iwasawaSigmaGeometric K := by
  simp

/-- The class of the chosen tame inertia generator is the geometric inertia generator. -/
@[simp]
theorem tameQuotientGeometricEquiv_toTameQuotient_tameGenerator :
    tameQuotientGeometricEquiv hσ τ hτ (toTameQuotient K τ) = iwasawaTauGeometric K := by
  simp [tameQuotientGeometricEquiv]

/-- The inverse marking sends the geometric Frobenius generator to the inverse Frobenius lift. -/
@[simp]
theorem tameQuotientGeometricEquiv_symm_iwasawaSigmaGeometric :
    (tameQuotientGeometricEquiv hσ τ hτ).symm (iwasawaSigmaGeometric K) =
      toTameQuotient K σ⁻¹ := by
  simp [tameQuotientGeometricEquiv]

/-- The inverse marking sends the geometric inertia generator to the chosen tame inertia class. -/
@[simp]
theorem tameQuotientGeometricEquiv_symm_iwasawaTauGeometric :
    (tameQuotientGeometricEquiv hσ τ hτ).symm (iwasawaTauGeometric K) = toTameQuotient K τ := by
  simp [tameQuotientGeometricEquiv]

/-- The geometric presentation coordinate agrees with the canonical unramified coordinate
of the tame quotient. -/
@[simp]
theorem iwasawaCoordinateGeometric_tameQuotientGeometricEquiv (x : tameQuotient K) :
    iwasawaCoordinateGeometric K (tameQuotientGeometricEquiv hσ τ hτ x) =
      tameQuotientToZHat K x := by
  simp [tameQuotientGeometricEquiv]

end TauCeti
