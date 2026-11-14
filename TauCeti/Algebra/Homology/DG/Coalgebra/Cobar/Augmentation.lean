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

The cobar construction `ΩC = T(s⁻¹ C)` of a noncounital differential graded coalgebra `C` is
canonically an augmented differential graded algebra over its ground ring `R`: the zero map
`C →ₗ[R] R` is a twisting cochain into the trivially graded base ring with zero differential, and
its cobar lift `IsNonCounitalDGCoalgebra.cobarAugmentation` sends every desuspended generator
`s⁻¹ c` to `0`.

Under the cobar universal property `IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv`, a DG
algebra morphism `ΩC ⟶ A` into an augmented DG algebra `(A, ε_A)` intertwines the augmentations
`ε_A ∘ φ = ε_{ΩC}` if and only if its corresponding twisting cochain `τ : C →ₗ[R] A` takes values
in `ε_A.augmentationIdeal`.  This is the augmented cobar universal property
(`IsNonCounitalDGCoalgebra.augmentedCobarTwistingCochainEquiv`).

## Main definitions

* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation`: the canonical DG algebra augmentation of
  `ΩC`, annihilating all desuspended generators.
* `TauCeti.IsNonCounitalDGCoalgebra.augmentedCobarTwistingCochainEquiv`: the bijection between
  augmentation-preserving DG algebra morphisms `ΩC ⟶ A` and twisting cochains `C →ₗ[R] A` landing
  in `ker ε_A`.

## Main results

* `TauCeti.isTwistingCochain_zero`: the zero linear map is a twisting cochain.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation_comp_cobarMap`: induced cobar maps preserve
  the canonical augmentation.
* `TauCeti.IsNonCounitalDGCoalgebra.comp_eq_cobarAugmentation_iff`: an algebra morphism `ΩC ⟶ A`
  preserves augmentations exactly when its twisting cochain lands in the augmentation ideal.

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

/-- The canonical augmentation `ΩC ⟶ R` of the cobar construction, sending every desuspended
generator `ι c` to `0`. -/
noncomputable def cobarAugmentation : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0
    (isTwistingCochain_zero G Δ dC (trivialGrading R R) 0)

/-- The canonical cobar augmentation annihilates every desuspended generator. -/
@[simp]
theorem cobarAugmentation_ι (c : C) : hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

/-- The twisting cochain corresponding to the canonical cobar augmentation is zero. -/
@[simp]
theorem cobarTwistingCochainEquiv_cobarAugmentation :
    (hC.cobarTwistingCochainEquiv (isDGAlgebra_trivialGrading R) hC.cobarAugmentation).val = 0 := by
  ext c
  simp

/-- Any induced cobar map between noncounital DG coalgebras intertwines their canonical
augmentations. -/
@[simp]
theorem cobarAugmentation_comp_cobarMap
    {GD : InternalGrading R D ℤ} {ΔD : D →ₗ[R] D ⊗[R] D} {dD : D →ₗ[R] D}
    (hD : IsNonCounitalDGCoalgebra GD ΔD dD) (f : D →ₗ[R] C)
    (hf_hom : LinearMap.IsHomogeneous f GD.piece G.piece 0)
    (hf_comul : Δ ∘ₗ f = TensorProduct.map f f ∘ₗ ΔD)
    (hf_d : dC ∘ₗ f = f ∘ₗ dD) :
    hC.cobarAugmentation.comp (hD.cobarMap hC f hf_hom hf_comul hf_d) = hD.cobarAugmentation :=
  hD.cobarHom_ext _ fun x ↦ by simp

section Target

variable [GradedAlgebra 𝒜] {hA : IsDGAlgebra 𝒜 dA} (eA : DGAlgAugmentation hA)

/-- A DG algebra morphism `ΩC ⟶ A` into an augmented DG algebra preserves augmentations if and only
if its associated twisting cochain takes values in the augmentation ideal of `A`. -/
theorem comp_eq_cobarAugmentation_iff (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    eA.comp φ = hC.cobarAugmentation ↔
      ∀ c, (hC.cobarTwistingCochainEquiv hA φ).val c ∈ eA.augmentationIdeal := by
  constructor
  · intro h c
    have hc := congrArg (fun ψ ↦ ψ (ι R c)) h
    simp only [DGAlgHom.comp_apply, cobarAugmentation_ι] at hc
    rw [DGAlgAugmentation.mem_augmentationIdeal, cobarTwistingCochainEquiv_apply, map_neg, hc,
      neg_zero]
  · intro h
    refine hC.cobarHom_ext _ fun c ↦ ?_
    have hc := (DGAlgAugmentation.mem_augmentationIdeal eA).mp (h c)
    rw [cobarTwistingCochainEquiv_apply, map_neg, neg_eq_zero] at hc
    simpa using hc

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
  left_inv φ := Subtype.ext (hC.cobarHom_ext hA fun c ↦ by simp)
  right_inv τ := Subtype.ext (LinearMap.ext fun c ↦ by simp)

@[simp]
theorem augmentedCobarTwistingCochainEquiv_apply
    (φ : {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA // eA.comp φ = hC.cobarAugmentation})
    (c : C) :
    (hC.augmentedCobarTwistingCochainEquiv eA φ).val c = -φ.val (ι R c) := by
  simp [augmentedCobarTwistingCochainEquiv]

@[simp]
theorem augmentedCobarTwistingCochainEquiv_symm_apply_val
    (τ : {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal}) :
    ((hC.augmentedCobarTwistingCochainEquiv eA).symm τ).val =
      hC.cobarLift hA τ.val τ.property.1 := (rfl)

theorem augmentedCobarTwistingCochainEquiv_symm_apply_ι
    (τ : {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal})
    (c : C) :
    ((hC.augmentedCobarTwistingCochainEquiv eA).symm τ).val (ι R c) = -τ.val c :=
  hC.cobarLift_ι hA τ.val τ.property.1 c

end Target

end IsNonCounitalDGCoalgebra

end TauCeti
