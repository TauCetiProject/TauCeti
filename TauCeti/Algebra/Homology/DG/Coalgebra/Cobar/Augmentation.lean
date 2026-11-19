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

variable {R : Type uR} {C : Type uC} {D : Type uD}
  [CommRing R] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {dC : C →ₗ[R] C}

namespace IsNonCounitalDGCoalgebra

variable (hC : IsNonCounitalDGCoalgebra G Δ dC)

/-- The canonical augmentation `ΩC ⟶ R` of the cobar construction, sending `ι c` to `0`. -/
noncomputable def cobarAugmentation : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0
    (isTwistingCochain_zero G Δ dC (trivialGrading R R) 0)

@[simp] theorem cobarAugmentation_ι (c : C) : hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

@[simp] theorem cobarTwistingCochainEquiv_cobarAugmentation :
    (hC.cobarTwistingCochainEquiv (isDGAlgebra_trivialGrading R) hC.cobarAugmentation).val = 0 :=
  LinearMap.ext fun _ ↦ by simp

/-- The cobar morphism induced by a coalgebra map intertwines the canonical cobar augmentations. -/
@[simp] theorem cobarAugmentation_comp_cobarMap
    {GD : InternalGrading R D ℤ} {ΔD : D →ₗ[R] D ⊗[R] D} {dD : D →ₗ[R] D}
    (hD : IsNonCounitalDGCoalgebra GD ΔD dD) (f : D →ₗ[R] C)
    (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD) (hf_d : dC ∘ₗ f = f ∘ₗ dD) :
    hC.cobarAugmentation.comp (hD.cobarMap hC f hf_hom hf_comul hf_d) = hD.cobarAugmentation :=
  hD.cobarHom_ext _ fun _ ↦ by simp

section Target

variable {A : Type uA} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} (eA : DGAlgAugmentation hA)

/-- A DG algebra morphism `ΩC ⟶ A` preserves augmentations if and only if its associated twisting
cochain takes values in `eA.augmentationIdeal`. -/
theorem comp_eq_cobarAugmentation_iff (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    eA.comp φ = hC.cobarAugmentation ↔
      ∀ c, (hC.cobarTwistingCochainEquiv hA φ).val c ∈ eA.augmentationIdeal :=
  ⟨fun h c ↦ by simpa [DGAlgAugmentation.mem_augmentationIdeal] using congrArg (· (ι R c)) h,
    fun h ↦ hC.cobarHom_ext _ fun c ↦ by simpa [DGAlgAugmentation.mem_augmentationIdeal] using h c⟩

/-- The **augmented cobar universal property**: augmentation-preserving DG algebra morphisms
`ΩC ⟶ A` correspond bijectively to twisting cochains `C →ₗ[R] A` landing in `ker ε_A`. -/
noncomputable def augmentedCobarTwistingCochainEquiv :
    {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA // eA.comp φ = hC.cobarAugmentation} ≃
      {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal} :=
  ((hC.cobarTwistingCochainEquiv hA).subtypeEquiv (hC.comp_eq_cobarAugmentation_iff eA)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _)

@[simp] theorem augmentedCobarTwistingCochainEquiv_apply
    (φ : {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA // eA.comp φ = hC.cobarAugmentation})
    (c : C) : (hC.augmentedCobarTwistingCochainEquiv eA φ).val c = -φ.val (ι R c) :=
  hC.cobarTwistingCochainEquiv_apply hA φ.val c

@[simp] theorem augmentedCobarTwistingCochainEquiv_symm_apply_val
    (τ : {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal}) :
    ((hC.augmentedCobarTwistingCochainEquiv eA).symm τ).val =
      hC.cobarLift hA τ.val τ.property.1 :=
  hC.cobarHom_ext _ fun _ ↦ by simp [augmentedCobarTwistingCochainEquiv]

end Target
end IsNonCounitalDGCoalgebra
end TauCeti
