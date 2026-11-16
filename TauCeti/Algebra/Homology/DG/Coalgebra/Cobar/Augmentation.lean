/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# Canonical augmentation of the cobar construction

For a noncounital DG coalgebra `(C, Δ, d)`, we construct `cobarAugmentation : Ω C ⟶ R`, describe
its augmentation ideal `Ω⁺ C`, characterize augmented morphisms out of `Ω C`, and restrict the
grading and differential to `Ω⁺ C`.

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

theorem cobarAugmentation_tprod {n : ℕ} (hn : 0 < n) (x : Fin n → C) :
    hC.cobarAugmentation (tprod R C n x) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [tprod_apply, List.ofFn_succ, List.prod_cons, map_mul, hC.cobarAugmentation_ι, zero_mul]

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
  suffices ∀ y : TensorAlgebra R C, (hC.cobarAugmentation.reducedPart y : TensorAlgebra R C) ∈ S by
    simpa only [DGAlgAugmentation.coe_reducedPart, hC.cobarAugmentation.mem_augmentationIdeal.1 hz,
      map_zero, sub_zero] using this z
  intro y; rw [← ofDirectSum_toDirectSum y]
  induction toDirectSum y using DirectSum.induction_on with
  | zero => simp
  | add _ _ hu hv => simpa only [map_add, Submodule.coe_add] using S.add_mem hu hv
  | of n t => induction t using PiTensorProduct.induction_on with
    | add _ _ hu hv => simpa only [map_add, Submodule.coe_add] using S.add_mem hu hv
    | smul_tprod r x =>
      rw [DirectSum.of_smul, map_smul, ofDirectSum_of_tprod, map_smul, Submodule.coe_smul]
      refine S.smul_mem r ?_; cases n with
      | zero => simp [tprod_apply]
      | succ k =>
        rw [DGAlgAugmentation.coe_reducedPart, hC.cobarAugmentation_tprod (Nat.succ_pos k),
          map_zero, sub_zero]
        exact Submodule.subset_span ⟨k, x, rfl⟩

theorem cobarAugmentation_augmentationIdeal_le_iff {S : Submodule R (TensorAlgebra R C)} :
    hC.cobarAugmentation.augmentationIdeal.toSubmodule ≤ S ↔
      ∀ (n : ℕ) (x : Fin (n + 1) → C), tprod R C (n + 1) x ∈ S := by
  rw [hC.cobarAugmentation_augmentationIdeal_eq_span_tprod, Submodule.span_le]
  exact ⟨fun h n x ↦ h ⟨n, x, rfl⟩, fun h _ ⟨n, x, hx⟩ ↦ hx ▸ h n x⟩

/-- The internal grading inherited by the augmentation ideal `Ω⁺ C` of the cobar construction. -/
noncomputable def cobarReducedGrading :
    InternalGrading R hC.cobarAugmentation.augmentationIdeal.toSubmodule ℤ :=
  (InternalGrading.ofDecomposition (tensorAlgebraPiece (G.shift (-1)))).submodule
    hC.cobarAugmentation.augmentationIdeal.toSubmodule
    ((InternalGrading.isHomogeneous_ofDecomposition_piece_iff _ _).2
      hC.cobarAugmentation.augmentationIdeal.is_homogeneous')

@[simp] theorem mem_cobarReducedGrading_piece {p : ℤ}
    {x : hC.cobarAugmentation.augmentationIdeal.toSubmodule} :
    x ∈ hC.cobarReducedGrading.piece p ↔
      (x : TensorAlgebra R C) ∈ tensorAlgebraPiece (G.shift (-1)) p := by
  rw [cobarReducedGrading, InternalGrading.mem_submodule_piece,
    InternalGrading.ofDecomposition_piece]

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
  ⟨fun h c ↦ by simpa [hC.cobarAugmentation_ι] using DFunLike.congr_fun h (ι R c),
    fun h ↦ hC.cobarHom_ext (isDGAlgebra_trivialGrading R) fun c ↦ by
      rw [DGAlgHom.comp_apply, hC.cobarAugmentation_ι, h c]⟩

theorem comp_cobarLift_eq_cobarAugmentation_iff (e : DGAlgAugmentation hA) (τ : C →ₗ[R] A)
    (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) :
    e.comp (hC.cobarLift hA τ hτ) = hC.cobarAugmentation ↔ ∀ c, e (τ c) = 0 := by
  rw [hC.comp_eq_cobarAugmentation_iff e]; simp only [hC.cobarLift_ι, map_neg, neg_eq_zero]

end TauCeti.IsNonCounitalDGCoalgebra
