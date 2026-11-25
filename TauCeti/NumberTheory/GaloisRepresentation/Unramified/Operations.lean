/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.Unramified.Basic
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Smul
import TauCeti.RepresentationTheory.Stabilizer

/-!
# Unramified tensor products, twists and Hom representations

For continuous representations of the absolute Galois group of a nonarchimedean local field:

* tensor products, twists by unramified (or tamely ramified) characters and Hom representations
  of unramified (or tamely ramified) representations are unramified (or tamely ramified);
* **twist formula**: on a free module of rank `n`, the Frobenius polynomial of the twist by `χ`
  is `P(ρ(χ), X) = χ(Φ)ⁿ P(ρ, χ(Φ)⁻¹ X)`, integrally `P(ρ(χ), χ(Φ) X) = χ(Φ)ⁿ P(ρ, X)`.

## Main results

* `TauCeti.ContinuousRep.IsUnramified.tprod`, `TauCeti.ContinuousRep.IsUnramified.twist`,
  `TauCeti.ContinuousRep.IsUnramified.linHom` and their tame analogues.
* `TauCeti.ContinuousRep.frobCharpoly_twist_comp`, `TauCeti.ContinuousRep.frobCharpoly_twist`:
  the twist formula.
-/

public section

open Polynomial

namespace TauCeti.ContinuousRep

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Twist

variable {A M : Type*} [CommSemiring A] [TopologicalSpace A] [ContinuousMul A] [AddCommMonoid M]
  [Module A M] [TopologicalSpace M] [ContinuousSMul A M]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M} {χ : Field.absoluteGaloisGroup K →ₜ* Aˣ}

/-- The twist of an unramified representation by an unramified character is unramified. -/
theorem IsUnramified.twist (h : ρ.IsUnramified) (hχ : (ofCharacter χ).IsUnramified) :
    (ρ.twist χ).IsUnramified := by
  rw [isUnramified_ofCharacter_iff] at hχ
  rw [isUnramified_iff] at h ⊢
  intro σ hσ
  ext x
  simp [hχ σ hσ, h σ hσ]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The twist of a tamely ramified representation by a tamely ramified character is tamely
ramified. -/
theorem IsTamelyRamified.twist (h : ρ.IsTamelyRamified) (hχ : (ofCharacter χ).IsTamelyRamified) :
    (ρ.twist χ).IsTamelyRamified := by
  rw [isTamelyRamified_ofCharacter_iff] at hχ
  rw [isTamelyRamified_iff] at h ⊢
  intro σ hσ
  ext x
  simp [hχ σ hσ, h σ hσ]

end Twist

section Tensor

variable {A M N : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [AddCommGroup M]
  [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M] [AddCommGroup N]
  [Module A N] [TopologicalSpace N] [IsModuleTopology A N] [Module.Finite A N]
  [TopologicalSpace (TensorProduct A M N)] [IsModuleTopology A (TensorProduct A M N)]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}
  {ρ' : ContinuousRep (Field.absoluteGaloisGroup K) A N}

/-- A tensor product of unramified representations is unramified. -/
theorem IsUnramified.tprod (h : ρ.IsUnramified) (h' : ρ'.IsUnramified) :
    (ρ.tprod ρ').IsUnramified := by
  rw [isUnramified_iff] at h h' ⊢
  intro σ hσ
  rw [← coe_toRepresentation, toRepresentation_tprod]
  exact MonoidHom.mem_ker.mp (Representation.ker_inf_ker_le_ker_tprod _ _
    ⟨MonoidHom.mem_ker.mpr (h σ hσ), MonoidHom.mem_ker.mpr (h' σ hσ)⟩)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A tensor product of tamely ramified representations is tamely ramified. -/
theorem IsTamelyRamified.tprod (h : ρ.IsTamelyRamified) (h' : ρ'.IsTamelyRamified) :
    (ρ.tprod ρ').IsTamelyRamified := by
  rw [isTamelyRamified_iff] at h h' ⊢
  intro σ hσ
  rw [← coe_toRepresentation, toRepresentation_tprod]
  exact MonoidHom.mem_ker.mp (Representation.ker_inf_ker_le_ker_tprod _ _
    ⟨MonoidHom.mem_ker.mpr (h σ hσ), MonoidHom.mem_ker.mpr (h' σ hσ)⟩)

end Tensor

section LinHom

variable {A M N : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [AddCommGroup M]
  [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]
  [Module.Projective A M] [AddCommGroup N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N]
  [TopologicalSpace (M →ₗ[A] N)] [IsModuleTopology A (M →ₗ[A] N)]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}
  {ρ' : ContinuousRep (Field.absoluteGaloisGroup K) A N}

/-- The Hom representation of two unramified representations is unramified. -/
theorem IsUnramified.linHom (h : ρ.IsUnramified) (h' : ρ'.IsUnramified) :
    (ρ.linHom ρ').IsUnramified := by
  rw [isUnramified_iff] at h h' ⊢
  intro σ hσ
  ext f x
  simp [linHom_apply_apply, h' σ hσ, h σ⁻¹ (inv_mem hσ)]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The Hom representation of two tamely ramified representations is tamely ramified. -/
theorem IsTamelyRamified.linHom (h : ρ.IsTamelyRamified) (h' : ρ'.IsTamelyRamified) :
    (ρ.linHom ρ').IsTamelyRamified := by
  rw [isTamelyRamified_iff] at h h' ⊢
  intro σ hσ
  ext f x
  simp [linHom_apply_apply, h' σ hσ, h σ⁻¹ (inv_mem hσ)]

end LinHom

section FrobCharpoly

variable {A M : Type*} [CommRing A] [TopologicalSpace A] [AddCommGroup M]
  [Module A M] [TopologicalSpace M] [ContinuousSMul A M] [Module.Free A M] [Module.Finite A M]
  (ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M) (χ : Field.absoluteGaloisGroup K →ₜ* Aˣ)

/-- **The twist formula**, integrally: substituting `χ(Φ) X` for `X` in the Frobenius polynomial
of `ρ(χ)` gives `χ(Φ)ⁿ P(ρ, X)`, for `n` the rank. -/
theorem frobCharpoly_twist_comp :
    (ρ.twist χ).frobCharpoly.comp (C (χ (arithFrobLift K) : A) * X) =
      C ((χ (arithFrobLift K) : A) ^ Module.finrank A M) * ρ.frobCharpoly := by
  rw [frobCharpoly_def, frobCharpoly_def, twist_apply_eq_smul,
    LinearMap.charpoly_smul_comp_C_mul_X]

/-- **The twist formula** `P(ρ(χ), X) = χ(Φ)ⁿ P(ρ, χ(Φ)⁻¹ X)`, for `n` the rank. -/
theorem frobCharpoly_twist :
    (ρ.twist χ).frobCharpoly = C ((χ (arithFrobLift K) : A) ^ Module.finrank A M) *
      ρ.frobCharpoly.comp (C (((χ (arithFrobLift K))⁻¹ : Aˣ) : A) * X) := by
  rw [frobCharpoly_def, frobCharpoly_def, twist_apply_eq_smul, LinearMap.charpoly_units_smul]

end FrobCharpoly

end TauCeti.ContinuousRep
