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

The cobar construction `Ω C = T(s⁻¹ C)` of a noncounital differential graded coalgebra `(C, Δ, d)`
carries a canonical augmentation `Ω C ⟶ R` (`TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation`),
the cobar lift of the zero twisting cochain.  It sends every desuspended generator `s⁻¹ c` to zero
and restricts to the identity on the ground ring `R`.

Its augmentation ideal `Ω⁺ C` is therefore spanned by the nonempty tensor products of generators
(`TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation_augmentationIdeal_eq_span_tprod`), and a DG
algebra map `φ : Ω C ⟶ A` into an augmented DG algebra `(A, e)` preserves augmentations precisely
when `e (φ (s⁻¹ c)) = 0` for every `c : C`
(`TauCeti.IsNonCounitalDGCoalgebra.comp_eq_cobarAugmentation_iff`).  Under the cobar universal
property, augmented DG algebra maps `Ω C ⟶ A` correspond to twisting cochains taking values in the
augmentation ideal of `A`.

## Main definitions

* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation`: the canonical augmentation of the cobar
  construction `Ω C`.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarReducedGrading`: the internal grading inherited by the
  augmentation ideal `Ω⁺ C`.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarReducedDifferential`: the cobar differential restricted to
  the augmentation ideal `Ω⁺ C`.

## Main results

* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation_ι` and
  `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation_tprod`: the augmentation kills every
  generator and every nonempty tensor product of generators.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation_augmentationIdeal_eq_span_tprod`: the
  augmentation ideal of `Ω C` is spanned by the nonempty products of generators.
* `TauCeti.IsNonCounitalDGCoalgebra.comp_eq_cobarAugmentation_iff` and
  `TauCeti.IsNonCounitalDGCoalgebra.comp_cobarLift_eq_cobarAugmentation_iff`: characterization of
  augmentation-preserving DG algebra morphisms out of `Ω C`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for the augmented cobar construction.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
-/

public section

open scoped TensorProduct
open TensorAlgebra

namespace TauCeti.IsNonCounitalDGCoalgebra

universe uR uC uA

variable {R : Type uR} {C : Type uC} {A : Type uA}
  [CommRing R] [AddCommGroup C] [Module R C]
  {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {dC : C →ₗ[R] C}
  (hC : IsNonCounitalDGCoalgebra G Δ dC)

/-- The canonical augmentation `Ω C ⟶ R` of the cobar construction, sending every generator `s⁻¹ c`
to zero and fixing the ground ring `R`. -/
noncomputable def cobarAugmentation : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0
    ⟨LinearMap.isHomogeneous_zero _ _ _, fun _ ↦ by simp⟩

/-- The canonical augmentation of the cobar construction kills every generator. -/
@[simp]
theorem cobarAugmentation_ι (c : C) : hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

/-- Every generator lies in the augmentation ideal of the cobar construction. -/
theorem ι_mem_cobarAugmentation_augmentationIdeal (c : C) :
    ι R c ∈ hC.cobarAugmentation.augmentationIdeal :=
  hC.cobarAugmentation.mem_augmentationIdeal.2 (hC.cobarAugmentation_ι c)

/-- The canonical augmentation kills every nonempty product of generators. -/
theorem cobarAugmentation_tprod {n : ℕ} (hn : 0 < n) (x : Fin n → C) :
    hC.cobarAugmentation (TensorAlgebra.tprod R C n x) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [TensorAlgebra.tprod_apply, List.ofFn_succ, List.prod_cons, map_mul,
    hC.cobarAugmentation_ι, zero_mul]

/-- Every nonempty product of generators lies in the augmentation ideal of the cobar
construction. -/
theorem tprod_mem_cobarAugmentation_augmentationIdeal {n : ℕ} (hn : 0 < n) (x : Fin n → C) :
    TensorAlgebra.tprod R C n x ∈ hC.cobarAugmentation.augmentationIdeal :=
  hC.cobarAugmentation.mem_augmentationIdeal.2 (hC.cobarAugmentation_tprod hn x)

/-- The reduced part of every element of `Ω C` lies in the span of nonempty products of
generators. -/
private theorem reducedPart_mem_span_tprod (z : TensorAlgebra R C) :
    (hC.cobarAugmentation.reducedPart z : TensorAlgebra R C) ∈
      Submodule.span R {w | ∃ (n : ℕ) (x : Fin (n + 1) → C),
        w = TensorAlgebra.tprod R C (n + 1) x} := by
  set S : Submodule R (TensorAlgebra R C) :=
    Submodule.span R {w | ∃ (n : ℕ) (x : Fin (n + 1) → C), w = TensorAlgebra.tprod R C (n + 1) x}
  rw [← TensorAlgebra.ofDirectSum_toDirectSum z]
  generalize TensorAlgebra.toDirectSum z = y
  induction y using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv =>
    simpa only [map_add, Submodule.coe_add] using S.add_mem hu hv
  | of n t =>
    induction t using PiTensorProduct.induction_on with
    | add u v hu hv =>
      simpa only [map_add, Submodule.coe_add] using S.add_mem hu hv
    | smul_tprod r x =>
      rw [DirectSum.of_smul, map_smul, TensorAlgebra.ofDirectSum_of_tprod, map_smul,
        Submodule.coe_smul]
      refine S.smul_mem r ?_
      cases n with
      | zero =>
        rw [DGAlgAugmentation.coe_reducedPart, TensorAlgebra.tprod_apply, List.ofFn_zero,
          List.prod_nil, map_one, map_one, sub_self]
        exact S.zero_mem
      | succ k =>
        rw [DGAlgAugmentation.coe_reducedPart, hC.cobarAugmentation_tprod (Nat.succ_pos k),
          map_zero, sub_zero]
        exact Submodule.subset_span ⟨k, x, rfl⟩

/-- The augmentation ideal of the cobar construction is spanned by the nonempty products of
generators. -/
theorem cobarAugmentation_augmentationIdeal_eq_span_tprod :
    hC.cobarAugmentation.augmentationIdeal.toSubmodule =
      Submodule.span R {w | ∃ (n : ℕ) (x : Fin (n + 1) → C),
        w = TensorAlgebra.tprod R C (n + 1) x} := by
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.2 ?_)
  · have h := hC.reducedPart_mem_span_tprod z
    simpa only [DGAlgAugmentation.coe_reducedPart,
      hC.cobarAugmentation.mem_augmentationIdeal.1 hz, map_zero, sub_zero] using h
  · rintro _ ⟨n, x, rfl⟩
    exact hC.tprod_mem_cobarAugmentation_augmentationIdeal (Nat.succ_pos n) x

/-- A submodule of `Ω C` contains the augmentation ideal `Ω⁺ C` precisely when it contains every
nonempty product of generators. -/
theorem cobarAugmentation_augmentationIdeal_le_iff {S : Submodule R (TensorAlgebra R C)} :
    hC.cobarAugmentation.augmentationIdeal.toSubmodule ≤ S ↔
      ∀ (n : ℕ) (x : Fin (n + 1) → C), TensorAlgebra.tprod R C (n + 1) x ∈ S := by
  rw [hC.cobarAugmentation_augmentationIdeal_eq_span_tprod, Submodule.span_le]
  constructor
  · intro h n x
    exact h ⟨n, x, rfl⟩
  · rintro h _ ⟨n, x, rfl⟩
    exact h n x

section Target

variable [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA}

/-- A DG algebra morphism out of the cobar construction preserves augmentations precisely when it
sends every generator into the augmentation ideal of the target. -/
theorem comp_eq_cobarAugmentation_iff (e : DGAlgAugmentation hA)
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    e.comp φ = hC.cobarAugmentation ↔ ∀ c, e (φ (ι R c)) = 0 := by
  constructor
  · intro h c
    simpa only [DGAlgHom.comp_apply, hC.cobarAugmentation_ι] using DFunLike.congr_fun h (ι R c)
  · intro h
    refine hC.cobarHom_ext (isDGAlgebra_trivialGrading R) fun c ↦ ?_
    rw [DGAlgHom.comp_apply, hC.cobarAugmentation_ι, h c]

/-- The cobar lift of a twisting cochain preserves augmentations precisely when the twisting
cochain takes values in the augmentation ideal of the target. -/
theorem comp_cobarLift_eq_cobarAugmentation_iff (e : DGAlgAugmentation hA) (τ : C →ₗ[R] A)
    (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) :
    e.comp (hC.cobarLift hA τ hτ) = hC.cobarAugmentation ↔ ∀ c, e (τ c) = 0 := by
  rw [hC.comp_eq_cobarAugmentation_iff e]
  simp only [hC.cobarLift_ι, map_neg, neg_eq_zero]

end Target

/-- The internal grading inherited by the augmentation ideal `Ω⁺ C` of the cobar construction. -/
noncomputable def cobarReducedGrading :
    InternalGrading R hC.cobarAugmentation.augmentationIdeal.toSubmodule ℤ :=
  (InternalGrading.ofDecomposition (tensorAlgebraPiece (G.shift (-1)))).submodule
    hC.cobarAugmentation.augmentationIdeal.toSubmodule
    ((InternalGrading.isHomogeneous_ofDecomposition_piece_iff _ _).2
      hC.cobarAugmentation.augmentationIdeal.is_homogeneous')

/-- A vector of the cobar augmentation ideal has degree `p` exactly when its underlying element of
`Ω C` has cobar degree `p`. -/
@[simp]
theorem mem_cobarReducedGrading_piece {p : ℤ}
    {x : hC.cobarAugmentation.augmentationIdeal.toSubmodule} :
    x ∈ hC.cobarReducedGrading.piece p ↔
      (x : TensorAlgebra R C) ∈ tensorAlgebraPiece (G.shift (-1)) p := by
  rw [cobarReducedGrading, InternalGrading.mem_submodule_piece,
    InternalGrading.ofDecomposition_piece]

/-- The cobar differential restricted to the augmentation ideal `Ω⁺ C`. -/
noncomputable def cobarReducedDifferential :
    Module.End R hC.cobarAugmentation.augmentationIdeal.toSubmodule :=
  (cobarDifferential G Δ dC).restrict fun x _ ↦ hC.cobarAugmentation.map_mem_augmentationIdeal x

/-- The restricted cobar differential acts as `cobarDifferential` on underlying elements. -/
@[simp]
theorem coe_cobarReducedDifferential (x : hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    (hC.cobarReducedDifferential x : TensorAlgebra R C) = cobarDifferential G Δ dC x := (rfl)

/-- The restricted cobar differential raises cobar degree by one. -/
theorem isHomogeneous_cobarReducedDifferential :
    LinearMap.IsHomogeneous hC.cobarReducedDifferential
      hC.cobarReducedGrading.piece hC.cobarReducedGrading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
    hC.mem_cobarReducedGrading_piece.2
      (hC.isDGAlgebra_cobarDifferential.map_mem (hC.mem_cobarReducedGrading_piece.1 hx))

/-- The restricted cobar differential squares to zero. -/
@[simp]
theorem cobarReducedDifferential_comp_self :
    hC.cobarReducedDifferential ∘ₗ hC.cobarReducedDifferential = 0 := by
  ext x
  exact hC.cobarDifferential_cobarDifferential x

end TauCeti.IsNonCounitalDGCoalgebra
