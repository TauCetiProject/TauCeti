/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Module.GradedModule.Quotient
import TauCeti.LinearAlgebra.TensorAlgebra.Projection

/-!
# Canonical augmentation of the cobar construction

For a noncounital DG coalgebra `(C, Δ, d)`, we construct `cobarAugmentation : Ω C ⟶ R`, describe
its augmentation ideal `Ω⁺ C`, show odd derivations mapping generators into `Ω⁺ C` preserve `Ω⁺ C`,
characterize augmented morphisms out of `Ω C`, and restrict the grading and differential to `Ω⁺ C`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Springer (2012), Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemp. Math. 406 (2006), §4.
-/

public section

open scoped TensorProduct
open TensorAlgebra

namespace TauCeti.IsNonCounitalDGCoalgebra

universe uR uC uA

variable {R : Type uR} {C : Type uC} {A : Type uA} [CommRing R] [AddCommGroup C] [Module R C]
  {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {dC : C →ₗ[R] C}
  (hC : IsNonCounitalDGCoalgebra G Δ dC)

/-- The canonical augmentation `Ω C ⟶ R` of the cobar construction, sending generators to zero. -/
noncomputable def cobarAugmentation : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0
    ⟨LinearMap.isHomogeneous_zero _ _ _, fun _ ↦ by simp⟩

@[simp] theorem cobarAugmentation_ι (c : C) : hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

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
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, DGAlgAugmentation.coe_reducedPart,
        hC.cobarAugmentation_tprod (Nat.succ_pos k), map_zero, sub_zero]
      exact Submodule.subset_span ⟨k, x, rfl⟩
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

variable [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA}

/-- A DG algebra morphism out of `Ω C` preserves augmentations iff it maps generators to `ker e`. -/
theorem comp_eq_cobarAugmentation_iff (e : DGAlgAugmentation hA)
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    e.comp φ = hC.cobarAugmentation ↔ ∀ c, e (φ (ι R c)) = 0 :=
  ⟨fun h c ↦ by simpa using DFunLike.congr_fun h (ι R c),
    fun h ↦ hC.cobarHom_ext _ fun c ↦ by simp [h c]⟩

theorem comp_cobarLift_eq_cobarAugmentation_iff (e : DGAlgAugmentation hA) (τ : C →ₗ[R] A)
    (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) :
    e.comp (hC.cobarLift hA τ hτ) = hC.cobarAugmentation ↔ ∀ c, e (τ c) = 0 := by
  simp [hC.comp_eq_cobarAugmentation_iff e]

end TauCeti.IsNonCounitalDGCoalgebra
