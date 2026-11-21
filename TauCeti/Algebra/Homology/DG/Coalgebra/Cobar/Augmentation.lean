/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Module.GradedModule.Quotient
import TauCeti.LinearAlgebra.TensorAlgebra.Basic

/-!
# The canonical augmentation of the cobar construction

The cobar construction `ΩC = T(s⁻¹ C)` of a noncounital DG coalgebra `C` over `R` carries a
canonical DG algebra augmentation `IsNonCounitalDGCoalgebra.cobarAugmentation : ΩC ⟶ R` induced by
the zero twisting cochain `C →ₗ[R] R`, annihilating every desuspended generator `s⁻¹ c`.

Under `cobarTwistingCochainEquiv`, a DG algebra morphism `ΩC ⟶ A` into an augmented DG algebra
`(A, ε_A)` intertwines augmentations if and only if its twisting cochain `τ : C →ₗ[R] A` lands in
`ε_A.augmentationIdeal` (`IsNonCounitalDGCoalgebra.augmentedCobarTwistingCochainEquiv`).

The augmentation ideal `Ω⁺C` is spanned by the nonempty products of generators
(`IsNonCounitalDGCoalgebra.cobarAugmentation_augmentationIdeal_eq_span_tprod`), odd derivations
mapping generators into `Ω⁺C` preserve it (`cobarAugmentation_derivation_eq_zero`), and the grading
and differential of `ΩC` restrict to `Ω⁺C` (`IsNonCounitalDGCoalgebra.cobarReducedGrading`,
`IsNonCounitalDGCoalgebra.cobarReducedDifferential`).

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

theorem ι_mem_cobarAugmentation_augmentationIdeal (c : C) :
    ι R c ∈ hC.cobarAugmentation.augmentationIdeal :=
  hC.cobarAugmentation.mem_augmentationIdeal.2 (hC.cobarAugmentation_ι c)

/-- An odd derivation of `Ω C` mapping generators into `Ω⁺ C` maps all of `Ω C` into `Ω⁺ C`. -/
theorem cobarAugmentation_derivation_eq_zero {f : C →ₗ[R] TensorAlgebra R C}
    (hf : ∀ c, hC.cobarAugmentation (f c) = 0) (x : TensorAlgebra R C) :
    hC.cobarAugmentation (tensorAlgebraDerivation (G.shift (-1)) f x) = 0 := by
  induction x using TensorAlgebra.induction with
  | algebraMap _ => simp
  | ι c => simp [hf c]
  | add _ _ hx hy => simp [hx, hy]
  | mul _ _ hx hy => simp [tensorAlgebraDerivation_mul, hx, hy]

theorem cobarAugmentation_tprod {n : ℕ} (hn : 0 < n) (x : Fin n → C) :
    hC.cobarAugmentation (tprod R C n x) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'; simp

theorem tprod_mem_cobarAugmentation_augmentationIdeal {n : ℕ} (hn : 0 < n) (x : Fin n → C) :
    tprod R C n x ∈ hC.cobarAugmentation.augmentationIdeal :=
  hC.cobarAugmentation.mem_augmentationIdeal.2 (hC.cobarAugmentation_tprod hn x)

/-- The augmentation ideal of the cobar construction is spanned by nonempty generator products. -/
theorem cobarAugmentation_augmentationIdeal_eq_span_tprod :
    hC.cobarAugmentation.augmentationIdeal.toSubmodule =
      Submodule.span R {w | ∃ (n : ℕ) (x : Fin (n + 1) → C), w = tprod R C (n + 1) x} := by
  set S := Submodule.span R {w | ∃ (n : ℕ) (x : Fin (n + 1) → C), w = tprod R C (n + 1) x}
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.2 fun _ ⟨n, x, hx⟩ ↦
    hx ▸ hC.tprod_mem_cobarAugmentation_augmentationIdeal (Nat.succ_pos n) x)
  have hq : S.mkQ ∘ₗ hC.cobarAugmentation.augmentationIdeal.toSubmodule.subtype ∘ₗ
      hC.cobarAugmentation.reducedPart = 0 := linearMap_ext_tprod fun
    | 0, _ => by simp [tprod_apply]
    | k + 1, x => by
      have hx : tprod R C (k + 1) x ∈ S := Submodule.subset_span ⟨k, x, rfl⟩
      simpa [-tprod_apply, DGAlgAugmentation.coe_reducedPart,
        hC.cobarAugmentation_tprod (Nat.succ_pos k)] using hx
  simpa [hC.cobarAugmentation.mem_augmentationIdeal.1 hz] using
    (Submodule.Quotient.mk_eq_zero S).1 (LinearMap.congr_fun hq z)

theorem cobarAugmentation_augmentationIdeal_le_iff {S : Submodule R (TensorAlgebra R C)} :
    hC.cobarAugmentation.augmentationIdeal.toSubmodule ≤ S ↔
      ∀ (n : ℕ) (x : Fin (n + 1) → C), tprod R C (n + 1) x ∈ S := by
  rw [hC.cobarAugmentation_augmentationIdeal_eq_span_tprod, Submodule.span_le]
  exact ⟨fun h n x ↦ h ⟨n, x, rfl⟩, fun h _ ⟨n, x, hx⟩ ↦ hx ▸ h n x⟩

/-- The internal grading inherited by the augmentation ideal `Ω⁺ C` of the cobar construction. -/
noncomputable def cobarReducedGrading :
    InternalGrading R hC.cobarAugmentation.augmentationIdeal.toSubmodule ℤ :=
  (InternalGrading.ofDecomposition (tensorAlgebraPiece (G.shift (-1)))).submodule _
    ((InternalGrading.isHomogeneous_ofDecomposition_piece_iff _ _).2
      hC.cobarAugmentation.augmentationIdeal.is_homogeneous')

@[simp] theorem mem_cobarReducedGrading_piece {p : ℤ}
    {x : hC.cobarAugmentation.augmentationIdeal.toSubmodule} :
    x ∈ hC.cobarReducedGrading.piece p ↔
      (x : TensorAlgebra R C) ∈ tensorAlgebraPiece (G.shift (-1)) p := by simp [cobarReducedGrading]

/-- The cobar differential restricted to the augmentation ideal `Ω⁺ C`. -/
noncomputable def cobarReducedDifferential :
    Module.End R hC.cobarAugmentation.augmentationIdeal.toSubmodule :=
  (cobarDifferential G Δ dC).restrict fun x _ ↦ hC.cobarAugmentation.map_mem_augmentationIdeal x

@[simp] theorem coe_cobarReducedDifferential
    (x : hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    (hC.cobarReducedDifferential x : TensorAlgebra R C) = cobarDifferential G Δ dC x := (rfl)

theorem isHomogeneous_cobarReducedDifferential :
    LinearMap.IsHomogeneous hC.cobarReducedDifferential
      hC.cobarReducedGrading.piece hC.cobarReducedGrading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ hC.mem_cobarReducedGrading_piece.2
    (hC.isDGAlgebra_cobarDifferential.map_mem (hC.mem_cobarReducedGrading_piece.1 hx))

@[simp] theorem cobarReducedDifferential_comp_self :
    hC.cobarReducedDifferential ∘ₗ hC.cobarReducedDifferential = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext (hC.cobarDifferential_cobarDifferential x)

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
