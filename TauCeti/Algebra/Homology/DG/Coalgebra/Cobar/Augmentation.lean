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

For a noncounital differential graded coalgebra `C`, the cobar differential on
`ΩC = T(s⁻¹ C)` sends every desuspended generator `s⁻¹ c` into the positive tensor powers
(`cobarDifferential_ι`). Consequently the algebra map `ΩC → R` that kills all generators
intertwines the cobar differential with the zero differential on `R`: it is the canonical
augmentation `IsNonCounitalDGCoalgebra.cobarAugmentation`, obtained as the cobar lift of the zero
twisting cochain.

Under `cobarTwistingCochainEquiv`, a DG algebra morphism `φ : ΩC → A` into an augmented DG algebra
`(A, e_A)` commutes with the augmentations precisely when the corresponding twisting cochain
`τ : C → A` takes values in `e_A.augmentationIdeal`. This refines the cobar universal property to
augmented DG algebra morphisms (`IsNonCounitalDGCoalgebra.cobarAugmentedHomEquiv`).

## Main definitions

* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation`: the canonical augmentation `ΩC → R`
  annihilating all desuspended generators.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentedHomEquiv`: equivalence between augmented DG
  algebra maps `ΩC → A` and twisting cochains `C → A` valued in `e_A.augmentationIdeal`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
-/

public section

open TensorProduct TensorAlgebra

namespace TauCeti.IsNonCounitalDGCoalgebra

universe uR uC uC' uA uB

variable {R : Type uR} {C : Type uC} [CommRing R] [AddCommGroup C] [Module R C]
  {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {dC : C →ₗ[R] C}
  (hC : IsNonCounitalDGCoalgebra G Δ dC)

/-- The canonical augmentation of the cobar construction `ΩC = T(s⁻¹ C)`, annihilating every
desuspended generator. -/
noncomputable def cobarAugmentation : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0 IsTwistingCochain.zero

/-- The canonical cobar augmentation kills every desuspended generator. -/
@[simp]
theorem cobarAugmentation_ι (c : C) : hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

/-- Every desuspended generator lies in the augmentation ideal of `cobarAugmentation`. -/
theorem ι_mem_cobarAugmentation_augmentationIdeal (c : C) :
    ι R c ∈ hC.cobarAugmentation.augmentationIdeal := by
  simp

/-- The twisting cochain associated to `cobarAugmentation` is zero. -/
@[simp]
theorem cobarTwistingCochainEquiv_cobarAugmentation :
    (hC.cobarTwistingCochainEquiv (isDGAlgebra_trivialGrading R) hC.cobarAugmentation).val = 0 := by
  ext c
  simp

section Functoriality

variable {C' : Type uC'} [AddCommGroup C'] [Module R C']
  {G' : InternalGrading R C' ℤ} {Δ' : C' →ₗ[R] C' ⊗[R] C'} {dC' : C' →ₗ[R] C'}
  (hC' : IsNonCounitalDGCoalgebra G' Δ' dC')

/-- Every induced cobar morphism preserves the canonical cobar augmentation. -/
@[simp]
theorem cobarAugmentation_comp_cobarMap (F : C →ₗ[R] C')
    (hF_hom : LinearMap.IsHomogeneous F G.piece G'.piece 0)
    (hF_comul : Δ' ∘ₗ F = TensorProduct.map F F ∘ₗ Δ)
    (hF_d : dC' ∘ₗ F = F ∘ₗ dC) :
    hC'.cobarAugmentation.comp (hC.cobarMap hC' F hF_hom hF_comul hF_d) =
      hC.cobarAugmentation := by
  apply hC.cobarHom_ext (isDGAlgebra_trivialGrading R)
  intro c
  simp

end Functoriality

section UniversalProperty

variable {A : Type uA} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} (eA : DGAlgAugmentation hA)

/-- A DG algebra map out of `ΩC` preserves the augmentation if and only if it maps every
desuspended generator into `eA.augmentationIdeal`. -/
theorem comp_eq_cobarAugmentation_iff (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    eA.comp φ = hC.cobarAugmentation ↔ ∀ c, φ (ι R c) ∈ eA.augmentationIdeal := by
  refine ⟨fun h c ↦ ?_, fun h ↦ ?_⟩
  · rw [DGAlgAugmentation.mem_augmentationIdeal, ← DGAlgHom.comp_apply, h, cobarAugmentation_ι]
  · apply hC.cobarHom_ext (isDGAlgebra_trivialGrading R)
    intro c
    rw [DGAlgHom.comp_apply, cobarAugmentation_ι]
    exact (DGAlgAugmentation.mem_augmentationIdeal eA).mp (h c)

/-- A DG algebra map out of `ΩC` preserves the augmentation if and only if its associated twisting
cochain lands in `eA.augmentationIdeal`. -/
theorem comp_eq_cobarAugmentation_iff_twistingCochain
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    eA.comp φ = hC.cobarAugmentation ↔
      ∀ c, (hC.cobarTwistingCochainEquiv hA φ).val c ∈ eA.augmentationIdeal := by
  simp [hC.comp_eq_cobarAugmentation_iff eA, DGAlgAugmentation.mem_augmentationIdeal,
    cobarTwistingCochainEquiv_apply]

/-- The cobar lift of a twisting cochain `τ` preserves the augmentation if and only if `τ` lands in
`eA.augmentationIdeal`. -/
@[simp]
theorem comp_cobarLift_eq_cobarAugmentation_iff (τ : C →ₗ[R] A)
    (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) :
    eA.comp (hC.cobarLift hA τ hτ) = hC.cobarAugmentation ↔
      ∀ c, τ c ∈ eA.augmentationIdeal := by
  simp [hC.comp_eq_cobarAugmentation_iff eA, DGAlgAugmentation.mem_augmentationIdeal,
    cobarLift_ι]

/-- The **augmented cobar universal property**: augmented DG algebra maps `(ΩC, ε_Ω) → (A, e_A)`
correspond bijectively to twisting cochains `C → A` valued in `eA.augmentationIdeal`. -/
noncomputable def cobarAugmentedHomEquiv :
    {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA //
        eA.comp φ = hC.cobarAugmentation} ≃
      {τ : C →ₗ[R] A //
        IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal} where
  toFun φ :=
    ⟨(hC.cobarTwistingCochainEquiv hA φ.1).val,
      (hC.cobarTwistingCochainEquiv hA φ.1).property,
      (hC.comp_eq_cobarAugmentation_iff_twistingCochain eA φ.1).mp φ.2⟩
  invFun τ :=
    ⟨hC.cobarLift hA τ.1 τ.2.1,
      (hC.comp_cobarLift_eq_cobarAugmentation_iff eA τ.1 τ.2.1).mpr τ.2.2⟩
  left_inv φ := Subtype.ext (hC.cobarHom_ext hA fun c ↦ by simp)
  right_inv τ := Subtype.ext (LinearMap.ext fun c ↦ by simp)

/-- The forward direction of `cobarAugmentedHomEquiv` is negative restriction to generators. -/
@[simp]
theorem cobarAugmentedHomEquiv_apply
    (φ : {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA //
      eA.comp φ = hC.cobarAugmentation}) (c : C) :
    (hC.cobarAugmentedHomEquiv eA φ).val c = -φ.1 (ι R c) :=
  hC.cobarTwistingCochainEquiv_apply hA φ.1 c

/-- The inverse of `cobarAugmentedHomEquiv` evaluates on a generator to the negative of the
twisting cochain. -/
@[simp]
theorem cobarAugmentedHomEquiv_symm_apply_ι
    (τ : {τ : C →ₗ[R] A //
      IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, τ c ∈ eA.augmentationIdeal}) (c : C) :
    ((hC.cobarAugmentedHomEquiv eA).symm τ).1 (ι R c) = -τ.1 c :=
  hC.cobarLift_ι hA τ.1 τ.2.1 c

end UniversalProperty

end TauCeti.IsNonCounitalDGCoalgebra
