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

For a noncounital differential graded coalgebra `C` over `R`, the zero map `C → R` into the
trivially graded ground ring is a twisting cochain (`TauCeti.isTwistingCochain_zero`).  By the
cobar universal property, it extends uniquely to a differential graded algebra morphism
`ΩC → R` annihilating every desuspended generator `s⁻¹ c`: the canonical augmentation
`TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation` of the cobar construction.

A differential graded algebra morphism `φ : ΩC → A` into an augmented differential graded
algebra `(A, ε)` commutes with the augmentations if and only if it maps every desuspended
generator into the augmentation ideal `ker ε`, equivalently if and only if the corresponding
twisting cochain `C → A` takes values in `ker ε`.  Restricting `cobarTwistingCochainEquiv`
therefore identifies augmentation-preserving DG algebra morphisms out of `ΩC` with twisting
cochains valued in `ker ε`.

## Main definitions

* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation`: the canonical augmentation `ΩC → R`
  annihilating every desuspended generator.
* `TauCeti.IsNonCounitalDGCoalgebra.augmentedCobarTwistingCochainEquiv`: the bijection between
  augmentation-preserving DG algebra morphisms `ΩC → A` and twisting cochains `C → A` valued in
  the augmentation ideal.

## Main results

* `TauCeti.IsNonCounitalDGCoalgebra.comp_eq_cobarAugmentation_iff`: `ε ∘ φ = cobarAugmentation`
  holds if and only if `φ` maps every desuspended generator into `ker ε`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
-/

public section

open TensorProduct TensorAlgebra

namespace TauCeti

universe uR uC uA

namespace IsNonCounitalDGCoalgebra

variable {R : Type uR} {C : Type uC} [CommRing R] [AddCommGroup C] [Module R C]
  {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {dC : C →ₗ[R] C}
  (hC : IsNonCounitalDGCoalgebra G Δ dC)

/-- The canonical augmentation `ΩC → R` of the cobar construction of a noncounital DG coalgebra,
obtained as the cobar lift of the zero twisting cochain into the trivially graded ground ring. -/
noncomputable def cobarAugmentation : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0
    (isTwistingCochain_zero G Δ dC (trivialGrading R R) 0)

/-- The canonical cobar augmentation annihilates every desuspended generator. -/
@[simp]
theorem cobarAugmentation_ι (c : C) : hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

/-- Every desuspended generator lies in the augmentation ideal of the cobar construction. -/
theorem ι_mem_cobarAugmentationIdeal (c : C) :
    ι R c ∈ hC.cobarAugmentation.augmentationIdeal := by
  rw [DGAlgAugmentation.mem_augmentationIdeal, hC.cobarAugmentation_ι]

section Target

variable {A : Type uA} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} (eA : DGAlgAugmentation hA)

/-- A DG algebra morphism out of the cobar construction commutes with the augmentations if and
only if it sends every desuspended generator into the target augmentation ideal. -/
theorem comp_eq_cobarAugmentation_iff
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    eA.comp φ = hC.cobarAugmentation ↔ ∀ c, φ (ι R c) ∈ eA.augmentationIdeal := by
  constructor
  · intro h c
    have hc := congrArg (fun ψ : DGAlgHom _ _ ↦ ψ (ι R c)) h
    simpa [DGAlgAugmentation.mem_augmentationIdeal] using hc
  · intro h
    refine hC.cobarHom_ext (isDGAlgebra_trivialGrading R) fun c ↦ ?_
    rw [DGAlgHom.comp_apply, hC.cobarAugmentation_ι]
    exact (eA.mem_augmentationIdeal).mp (h c)

/-- The cobar lift of a twisting cochain `τ` preserves the augmentation if and only if `τ` takes
values in the target augmentation ideal. -/
@[simp]
theorem cobarLift_comp_eq_cobarAugmentation_iff (τ : C →ₗ[R] A)
    (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) :
    eA.comp (hC.cobarLift hA τ hτ) = hC.cobarAugmentation ↔
      ∀ c, τ c ∈ eA.augmentationIdeal := by
  rw [hC.comp_eq_cobarAugmentation_iff eA]
  refine forall_congr' fun c ↦ ?_
  simp [hC.cobarLift_ι]

/-- Under `cobarTwistingCochainEquiv`, augmentation-preserving DG algebra morphisms out of `ΩC`
correspond to twisting cochains valued in the target augmentation ideal. -/
theorem cobarTwistingCochainEquiv_mem_augmentationIdeal_iff
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    (∀ c, (hC.cobarTwistingCochainEquiv hA φ).val c ∈ eA.augmentationIdeal) ↔
      eA.comp φ = hC.cobarAugmentation := by
  rw [hC.comp_eq_cobarAugmentation_iff eA]
  refine forall_congr' fun c ↦ ?_
  simp [hC.cobarTwistingCochainEquiv_apply]

/-- **The augmented cobar universal property**: augmentation-preserving DG algebra morphisms
`ΩC → A` correspond bijectively to twisting cochains `C → A` taking values in `ker ε`. -/
noncomputable def augmentedCobarTwistingCochainEquiv :
    {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA // eA.comp φ = hC.cobarAugmentation} ≃
      {τ : C →ₗ[R] A //
        IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal} where
  toFun φ :=
    ⟨(hC.cobarTwistingCochainEquiv hA φ.val).val,
      (hC.cobarTwistingCochainEquiv hA φ.val).property,
      (hC.cobarTwistingCochainEquiv_mem_augmentationIdeal_iff eA φ.val).2 φ.property⟩
  invFun τ :=
    ⟨hC.cobarLift hA τ.val τ.property.1,
      (hC.cobarLift_comp_eq_cobarAugmentation_iff eA τ.val τ.property.1).2 τ.property.2⟩
  left_inv φ := Subtype.ext (hC.cobarHom_ext hA fun c ↦ by simp)
  right_inv τ := Subtype.ext (LinearMap.ext fun c ↦ by simp)

/-- Forward evaluation of `augmentedCobarTwistingCochainEquiv` is negative restriction to
desuspended generators. -/
@[simp]
theorem augmentedCobarTwistingCochainEquiv_apply
    (φ : {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA //
      eA.comp φ = hC.cobarAugmentation}) (c : C) :
    (hC.augmentedCobarTwistingCochainEquiv eA φ).val c = -φ.val (ι R c) :=
  hC.cobarTwistingCochainEquiv_apply hA φ.val c

/-- Inverse evaluation of `augmentedCobarTwistingCochainEquiv` on a desuspended generator negates
the twisting cochain. -/
@[simp]
theorem augmentedCobarTwistingCochainEquiv_symm_apply_ι
    (τ : {τ : C →ₗ[R] A //
      IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal}) (c : C) :
    ((hC.augmentedCobarTwistingCochainEquiv eA).symm τ).val (ι R c) = -τ.val c :=
  hC.cobarLift_ι hA τ.val τ.property.1 c

end Target

end IsNonCounitalDGCoalgebra

end TauCeti
