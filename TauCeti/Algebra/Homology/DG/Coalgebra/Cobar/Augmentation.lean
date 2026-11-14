/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TwistingCochain

/-!
# The canonical augmentation of the cobar construction

The cobar construction `ΩC = T(s⁻¹ C)` of a noncounital DG coalgebra `C` over `R` carries a
canonical DG algebra augmentation `IsNonCounitalDGCoalgebra.cobarAugmentation : ΩC ⟶ R` induced by
the zero twisting cochain `C →ₗ[R] R`, annihilating every desuspended generator `s⁻¹ c`.

Under `cobarTwistingCochainEquiv`, a DG algebra morphism `ΩC ⟶ A` into an augmented DG algebra
`(A, ε_A)` intertwines augmentations if and only if its twisting cochain `τ : C →ₗ[R] A` lands in
`ε_A.augmentationIdeal` (`IsNonCounitalDGCoalgebra.augmentedCobarTwistingCochainEquiv`).

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
-/

public section

open TensorProduct TensorAlgebra

namespace TauCeti

universe uR uC uD uA

variable {R : Type uR} {C : Type uC} {D : Type uD} {A : Type uA}
  [CommRing R] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  [Ring A] [Algebra R A]
  (G : InternalGrading R C ℤ) (Δ : C →ₗ[R] C ⊗[R] C) (dC : C →ₗ[R] C)
  (𝒜 : ℤ → Submodule R A) (dA : A →ₗ[R] A)

/-- The zero linear map is a twisting cochain from any noncounital DG coalgebra datum to any DG
algebra datum. -/
theorem isTwistingCochain_zero : IsTwistingCochain G Δ dC 𝒜 dA 0 where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ _ ↦ Submodule.zero_mem _
  equation _ := by simp

variable {G Δ dC 𝒜 dA}

namespace IsNonCounitalDGCoalgebra

variable (hC : IsNonCounitalDGCoalgebra G Δ dC)

/-- The canonical augmentation `ΩC ⟶ R` of the cobar construction, sending `ι c` to `0`. -/
noncomputable def cobarAugmentation : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0
    (isTwistingCochain_zero G Δ dC (trivialGrading R R) 0)

@[simp]
theorem cobarAugmentation_ι (c : C) : hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

@[simp]
theorem cobarTwistingCochainEquiv_cobarAugmentation :
    (hC.cobarTwistingCochainEquiv (isDGAlgebra_trivialGrading R) hC.cobarAugmentation).val = 0 :=
  LinearMap.ext fun _ ↦ by simp

@[simp]
theorem cobarAugmentation_comp_cobarMap
    {GD : InternalGrading R D ℤ} {ΔD : D →ₗ[R] D ⊗[R] D} {dD : D →ₗ[R] D}
    (hD : IsNonCounitalDGCoalgebra GD ΔD dD) (f : D →ₗ[R] C)
    (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD) (hf_d : dC ∘ₗ f = f ∘ₗ dD) :
    hC.cobarAugmentation.comp (hD.cobarMap hC f hf_hom hf_comul hf_d) = hD.cobarAugmentation :=
  hD.cobarHom_ext _ fun _ ↦ by simp

section Target

variable [GradedAlgebra 𝒜] {hA : IsDGAlgebra 𝒜 dA} (eA : DGAlgAugmentation hA)

/-- A DG algebra morphism `ΩC ⟶ A` preserves augmentations if and only if its associated twisting
cochain takes values in `eA.augmentationIdeal`. -/
theorem comp_eq_cobarAugmentation_iff (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    eA.comp φ = hC.cobarAugmentation ↔
      ∀ c, (hC.cobarTwistingCochainEquiv hA φ).val c ∈ eA.augmentationIdeal := by
  refine ⟨fun h c ↦ ?_, fun h ↦ hC.cobarHom_ext _ fun c ↦ ?_⟩
  · have hc := congrArg (fun ψ ↦ ψ (ι R c)) h
    simpa [DGAlgAugmentation.mem_augmentationIdeal] using hc
  · simpa [DGAlgAugmentation.mem_augmentationIdeal] using h c

/-- The **augmented cobar universal property**: augmentation-preserving DG algebra morphisms
`ΩC ⟶ A` correspond bijectively to twisting cochains `C →ₗ[R] A` landing in `ker ε_A`. -/
noncomputable def augmentedCobarTwistingCochainEquiv :
    {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA // eA.comp φ = hC.cobarAugmentation} ≃
      {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal} where
  toFun φ := ⟨(hC.cobarTwistingCochainEquiv hA φ.val).val,
    (hC.cobarTwistingCochainEquiv hA φ.val).property,
    (hC.comp_eq_cobarAugmentation_iff eA φ.val).mp φ.property⟩
  invFun τ := ⟨hC.cobarLift hA τ.val τ.property.1,
    (hC.comp_eq_cobarAugmentation_iff eA _).mpr fun c ↦ by simp [τ.property.2 c]⟩
  left_inv φ := Subtype.ext (hC.cobarHom_ext hA fun _ ↦ by simp)
  right_inv τ := Subtype.ext (LinearMap.ext fun _ ↦ by simp)

@[simp]
theorem augmentedCobarTwistingCochainEquiv_apply
    (φ : {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA // eA.comp φ = hC.cobarAugmentation})
    (c : C) : (hC.augmentedCobarTwistingCochainEquiv eA φ).val c = -φ.val (ι R c) := by
  simp [augmentedCobarTwistingCochainEquiv]

@[simp]
theorem augmentedCobarTwistingCochainEquiv_symm_apply_val
    (τ : {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal}) :
    ((hC.augmentedCobarTwistingCochainEquiv eA).symm τ).val =
      hC.cobarLift hA τ.val τ.property.1 := (rfl)

theorem augmentedCobarTwistingCochainEquiv_symm_apply_ι
    (τ : {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal})
    (c : C) : ((hC.augmentedCobarTwistingCochainEquiv eA).symm τ).val (ι R c) = -τ.val c :=
  hC.cobarLift_ι hA τ.val τ.property.1 c

end Target

end IsNonCounitalDGCoalgebra

end TauCeti
