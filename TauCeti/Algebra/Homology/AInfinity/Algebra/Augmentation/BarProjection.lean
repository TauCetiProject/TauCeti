/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation
import TauCeti.LinearAlgebra.TensorCoalgebra.Coassoc

/-!
# Bar projection of an augmented `A∞` algebra

Let `(A, ε)` be an augmented `A∞` algebra with augmentation ideal `I = ker ε`.  The letterwise
reduced-part projection `π = ReducedTensorWords.map ε.reducedPart` retracts the bar map of the
inclusion `I ⟶ A` (`TauCeti.AInfinityAlgebra.Augmentation.inclusion`).

This file computes `ε ∘ 𝒜.taylor` (`TauCeti.AInfinityAlgebra.Augmentation.comp_taylor`) and
expresses `π ∘ b_A` as `b_I ∘ π` plus the two boundary unit-contraction terms coming from the
strict unit acting in arity two
(`TauCeti.AInfinityAlgebra.Augmentation.map_reducedPart_comp_barDifferential`).

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.comp_taylor`: the augmentation of the Taylor map is the
  product of the two letter augmentations on length-two words and vanishes elsewhere.
* `TauCeti.AInfinityAlgebra.Augmentation.map_reducedPart_comp_barDifferential`: the letterwise
  reduced-part projection intertwines `b_A` with `b_I` up to the two unit-contraction terms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Section 3.2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {𝒜 : AInfinityAlgebra R A}

/-- Splitting each letter of a pure tensor word into its reduced and scalar parts writes the
difference between the word and its reduced-part projection as a sum of pure words of the same
length, each having at least one scalar-multiple-of-unit letter. -/
private theorem of_tprod_sub_map_eq_sum_erase (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (x : Fin n.val → A) :
    ReducedTensorWords.of R A n (PiTensorProduct.tprod R x) -
      ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
        (ReducedTensorWords.map (R := R) ε.reducedPart
          (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) =
      ∑ f ∈ (Finset.univ : Finset (Fin n.val → Bool)).erase (fun _ ↦ false),
        ReducedTensorWords.of R A n (PiTensorProduct.tprod R fun i ↦
          if f i then ε (x i) • ε.unit else (ε.reducedPart (x i) : A)) := by
  classical
  let piece : Fin n.val → Bool → A := fun i b ↦
    if b then ε (x i) • ε.unit else (ε.reducedPart (x i) : A)
  have hx (i : Fin n.val) : ∑ b ∈ (Finset.univ : Finset Bool), piece i b = x i := by
    rw [Fintype.sum_bool]
    simp only [piece, Bool.false_eq_true, ↓reduceIte]
    rw [add_comm, ε.coe_reducedPart_add_smul_unit]
  have hsum : PiTensorProduct.tprod R x =
      ∑ f : Fin n.val → Bool, PiTensorProduct.tprod R (fun i ↦ piece i (f i)) := by
    rw [← Fintype.piFinset_univ, ← (PiTensorProduct.tprod R).map_sum_finset]
    exact congrArg _ (funext fun i ↦ (hx i).symm)
  have hof : ReducedTensorWords.of R A n (PiTensorProduct.tprod R x) =
      ReducedTensorWords.of R A n (PiTensorProduct.tprod R (fun i ↦ piece i false)) +
        ∑ f ∈ (Finset.univ : Finset (Fin n.val → Bool)).erase (fun _ ↦ false),
          ReducedTensorWords.of R A n (PiTensorProduct.tprod R (fun i ↦ piece i (f i))) := by
    rw [hsum, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : Fin n.val ↦ false))]
  rw [ReducedTensorWords.map_of_tprod, ReducedTensorWords.map_of_tprod, hof]
  have hfalse : (fun i : Fin n.val ↦ piece i false) =
      fun i ↦ ε.augmentationIdeal.subtype (ε.reducedPart (x i)) := by
    funext i
    simp [piece]
  rw [hfalse, add_sub_cancel_left]

/-- For arity other than two, the Taylor map of an augmented `A∞` algebra depends only on the
reduced-part projection of a pure word. -/
private theorem taylor_of_tprod_eq_of_ne_two (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (hn : n.val ≠ 2) (x : Fin n.val → A) :
    𝒜.taylor (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) =
      𝒜.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
        (ReducedTensorWords.map (R := R) ε.reducedPart
          (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)))) := by
  classical
  rw [← sub_eq_zero, ← map_sub, of_tprod_sub_map_eq_sum_erase, map_sum]
  refine Finset.sum_eq_zero fun f hf ↦ ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (Finset.mem_erase.1 hf).1
  replace hi : f i = true := Bool.eq_true_of_ne_false hi
  set y : Fin n.val → A := fun j ↦ if f j then ε (x j) • ε.unit else (ε.reducedPart (x j) : A)
  have hy : y = Function.update y i (ε (x i) • ε.unit) :=
    (Function.update_eq_self_iff.2 (by simp [y, hi])).symm
  rw [hy, (PiTensorProduct.tprod R).map_update_smul, map_smul, map_smul,
    ε.isStrictUnit.taylor_of_tprod_eq_zero n hn _ ⟨i, by simp⟩, smul_zero]

/-- On a two-letter pure word, `ε ∘ 𝒜.taylor` evaluates to the product of the letter
augmentations. -/
private theorem comp_taylor_two (ε : 𝒜.Augmentation) (a b : A) :
    ε (𝒜.taylor (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![a, b]))) =
      LinearMap.mul' R R (TensorProduct.map
        (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
        (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
        (ReducedTensorWords.deconcatenation R A
          (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])))) := by
  simp [𝒜.taylor_of_two, ε.map_binary, ε.map_koszulTwist,
    ReducedTensorWords.deconcatenation_of_two]

/-- The augmentation of the Taylor map is the product of the augmentations of the two letters on a
two-letter word, and zero in all other arities. -/
theorem comp_taylor (ε : 𝒜.Augmentation) :
    ε.toLinearMap ∘ₗ 𝒜.taylor =
      LinearMap.mul' R R ∘ₗ
        TensorProduct.map
          (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
          (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  refine ReducedTensorWords.linearMap_ext_two_ne_two R A
    (fun a b ↦ by simpa only [LinearMap.comp_apply] using ε.comp_taylor_two a b)
    (fun n hn x ↦ ?_)
  simp only [LinearMap.comp_apply, 𝒜.taylor_of_tprod, ε.map_m_of_ne_two n.val n.property hn]
  exact (ReducedTensorWords.eq_zero_of_factor_letter_pair R A (LinearMap.mul' R R)
    ε.toLinearMap ε.toLinearMap rfl n hn x).symm

/-- The scalar projection `Tᶜ(sA) ⟶ R` extracting the augmentation of the single-letter
component. -/
private noncomputable def scalarPart (ε : 𝒜.Augmentation) : ReducedTensorWords R A →ₗ[R] R :=
  ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A

/-- The left unit-contraction term `z ↦ ∑ ε(letter z₁) • map ε.reducedPart z₂` of
`map ε.reducedPart ∘ₗ 𝒜.barDifferential`. -/
@[expose] noncomputable def leftUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R ε.augmentationIdeal :=
  (TensorProduct.lid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
    TensorProduct.map (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
      (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
    ReducedTensorWords.deconcatenation R A

/-- The right unit-contraction term `z ↦ ∑ ε(letter z₂) • map ε.reducedPart (τ z₁)` of
`map ε.reducedPart ∘ₗ 𝒜.barDifferential`, where `τ` is the degree-one letterwise Koszul twist of
the suspended grading. -/
@[expose] noncomputable def rightUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R ε.augmentationIdeal :=
  (TensorProduct.rid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
    TensorProduct.map
      (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
        ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1))
      (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A) ∘ₗ
    ReducedTensorWords.deconcatenation R A

private theorem leftUnitTerm_eq (ε : 𝒜.Augmentation) :
    ε.leftUnitTerm =
      ((TensorProduct.lid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
        TensorProduct.map ε.scalarPart (ReducedTensorWords.map (R := R) ε.reducedPart)) ∘ₗ
      ReducedTensorWords.deconcatenation R A := by
  simp only [leftUnitTerm, scalarPart, LinearMap.comp_assoc]

private theorem rightUnitTerm_eq (ε : 𝒜.Augmentation) :
    ε.rightUnitTerm =
      ((TensorProduct.rid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
        TensorProduct.map
          (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
            ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1))
          ε.scalarPart) ∘ₗ
      ReducedTensorWords.deconcatenation R A := by
  simp only [rightUnitTerm, scalarPart, LinearMap.comp_assoc]

/-- Coassociativity comparison for `leftUnitTerm`. -/
private theorem deconcatenation_comp_leftUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords.deconcatenation R ε.augmentationIdeal ∘ₗ ε.leftUnitTerm =
      TensorProduct.map ε.leftUnitTerm (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  let π := ReducedTensorWords.map (R := R) ε.reducedPart
  have hπ : ReducedTensorWords.IsCoalgHom R π := ReducedTensorWords.isCoalgHom_map ε.reducedPart
  let fL : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal :=
    (TensorProduct.lid R _).toLinearMap ∘ₗ TensorProduct.map ε.scalarPart π
  let M₁ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    (TensorProduct.lid R _).toLinearMap ∘ₗ
      TensorProduct.map ε.scalarPart (TensorProduct.map π π)
  rw [ε.leftUnitTerm_eq, ← LinearMap.comp_assoc]
  refine ReducedTensorWords.comp_deconcatenation_eq_of_lTensor_eq_assoc_rTensor R A (F := M₁) ?_ ?_
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
      TensorProduct.lid_tmul, map_smul, LinearMap.lTensor_tmul, M₁]
    rw [hπ.deconcatenation_apply]
  · have hleft : TensorProduct.map (fL ∘ₗ ReducedTensorWords.deconcatenation R A) π =
        TensorProduct.map fL π ∘ₗ
          LinearMap.rTensor _ (ReducedTensorWords.deconcatenation R A) := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp
    have hassoc : TensorProduct.map fL π =
        M₁ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap := by
      refine TensorProduct.ext_threefold fun a b c ↦ ?_
      simp [fL, M₁, TensorProduct.smul_tmul]
    rw [hleft, hassoc, LinearMap.comp_assoc]

/-- Coassociativity comparison for `rightUnitTerm`. -/
private theorem deconcatenation_comp_rightUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords.deconcatenation R ε.augmentationIdeal ∘ₗ ε.rightUnitTerm =
      TensorProduct.map (ReducedTensorWords.map (R := R) ε.reducedPart) ε.rightUnitTerm ∘ₗ
        LinearMap.rTensor _ (ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  let π := ReducedTensorWords.map (R := R) ε.reducedPart
  let τ := ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)
  have hπτ : ReducedTensorWords.IsCoalgHom R (π ∘ₗ τ) :=
    (ReducedTensorWords.isCoalgHom_map ε.reducedPart).comp
      (ReducedTensorWords.isCoalgHom_map _)
  let fR : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal :=
    (TensorProduct.rid R _).toLinearMap ∘ₗ TensorProduct.map (π ∘ₗ τ) ε.scalarPart
  let M₃ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    TensorProduct.map (π ∘ₗ τ) fR
  rw [ε.rightUnitTerm_eq]
  simp only [← LinearMap.comp_assoc]
  refine (ReducedTensorWords.comp_deconcatenation_eq_of_lTensor_eq_assoc_rTensor R A (F := M₃)
    ?_ ?_).symm
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp [M₃, fR, π, τ]
  · have hnat : ReducedTensorWords.deconcatenation R _ ∘ₗ fR =
        (TensorProduct.rid R _).toLinearMap ∘ₗ
          TensorProduct.map (TensorProduct.map (π ∘ₗ τ) (π ∘ₗ τ)) ε.scalarPart ∘ₗ
          LinearMap.rTensor _ (ReducedTensorWords.deconcatenation R A) := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
        TensorProduct.rid_tmul, map_smul, LinearMap.rTensor_tmul, fR]
      rw [← LinearMap.comp_apply π τ, hπτ.deconcatenation_apply]
    have hassoc : (TensorProduct.rid R _).toLinearMap ∘ₗ
          TensorProduct.map (TensorProduct.map (π ∘ₗ τ) (π ∘ₗ τ)) ε.scalarPart =
        M₃ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap := by
      refine TensorProduct.ext_threefold fun a b c ↦ ?_
      simp [M₃, fR, TensorProduct.tmul_smul]
    dsimp only [fR, π, τ] at hnat
    rw [LinearMap.comp_assoc, hnat, ← LinearMap.comp_assoc, hassoc, LinearMap.comp_assoc]

/-- Coassociativity cancellation between the cross terms of `leftUnitTerm` and `rightUnitTerm`. -/
private theorem map_leftUnitTerm_comp_deconcatenation (ε : 𝒜.Augmentation) :
    TensorProduct.map (ReducedTensorWords.map (R := R) ε.reducedPart) ε.leftUnitTerm ∘ₗ
        LinearMap.rTensor _ (ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)) ∘ₗ
        ReducedTensorWords.deconcatenation R A =
      TensorProduct.map ε.rightUnitTerm (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  let π := ReducedTensorWords.map (R := R) ε.reducedPart
  let τ := ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)
  let fR : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal :=
    (TensorProduct.rid R _).toLinearMap ∘ₗ TensorProduct.map (π ∘ₗ τ) ε.scalarPart
  let M₂ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    TensorProduct.map (π ∘ₗ τ)
      ((TensorProduct.lid R _).toLinearMap ∘ₗ TensorProduct.map ε.scalarPart π)
  rw [← LinearMap.comp_assoc]
  refine ReducedTensorWords.comp_deconcatenation_eq_of_lTensor_eq_assoc_rTensor R A (F := M₂) ?_ ?_
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp [M₂, leftUnitTerm, scalarPart, π, τ]
  · have hright : TensorProduct.map ε.rightUnitTerm π =
        TensorProduct.map fR π ∘ₗ
          LinearMap.rTensor _ (ReducedTensorWords.deconcatenation R A) := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp [ε.rightUnitTerm_eq, fR, π, τ]
    have hassoc : TensorProduct.map fR π =
        M₂ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap := by
      refine TensorProduct.ext_threefold fun a b c ↦ ?_
      simp [M₂, fR, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    rw [hright, hassoc, LinearMap.comp_assoc]

/-- The combination `ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm` is a graded coderivation along
the letterwise reduced-part projection `ReducedTensorWords.map ε.reducedPart`. -/
theorem isGradedCoderivationAlong_unitTerms (ε : 𝒜.Augmentation) :
    ReducedTensorWords.IsGradedCoderivationAlong (𝒜.grading.shift 1) 1
      (ReducedTensorWords.map (R := R) ε.reducedPart)
      (ReducedTensorWords.map (R := R) ε.reducedPart)
      (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm) := by
  rw [ReducedTensorWords.isGradedCoderivationAlong_iff]
  simp only [LinearMap.comp_add, LinearMap.comp_smul, ε.deconcatenation_comp_leftUnitTerm,
    ε.deconcatenation_comp_rightUnitTerm, TensorProduct.map_add_left,
    TensorProduct.map_smul_left, TensorProduct.map_add_right, TensorProduct.map_smul_right,
    LinearMap.add_comp, LinearMap.smul_comp, ε.map_leftUnitTerm_comp_deconcatenation]
  module

/-- Decomposing `𝒜.m 2 ![𝒜.grading.koszulTwist 1 a, b]` into the reduced binary operation plus
scalar-multiple-of-unit corrections. -/
private theorem m_two_eq_reduced_add (ε : 𝒜.Augmentation) (a b : A) :
    𝒜.m 2 ![𝒜.grading.koszulTwist 1 a, b] =
      (ε.reducedAlgebra.m 2 ![ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a),
        ε.reducedPart b] : A) +
      ε a • (ε.reducedPart b : A) +
      ε b • (ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) : A) +
      (ε a * ε b) • ε.unit := by
  have htwist_a : 𝒜.grading.koszulTwist 1 a =
      (ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) : A) + ε a • ε.unit := by
    rw [ε.reducedAlgebra_grading, ← ε.reducedPart_koszulTwist, ← ε.map_koszulTwist 1 a,
      ε.coe_reducedPart_add_smul_unit]
  have hmul : 𝒜.mul ((ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) : A) +
        ε a • ε.unit) ((ε.reducedPart b : A) + ε b • ε.unit) =
      (ε.reducedAlgebra.m 2 ![ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a),
        ε.reducedPart b] : A) +
      ε a • (ε.reducedPart b : A) +
      ε b • (ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) : A) +
      (ε a * ε b) • ε.unit := by
    rw [reducedAlgebra_m, coe_reducedOperation_two, ← 𝒜.mul_apply]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, 𝒜.mul_apply,
      ε.isStrictUnit.binary_left, ε.isStrictUnit.binary_right, smul_add, smul_smul,
      mul_comm (ε b) (ε a)]
    abel
  rwa [← htwist_a, ε.coe_reducedPart_add_smul_unit, 𝒜.mul_apply] at hmul

private theorem letter_map_apply {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (g : M →ₗ[R] N) (w : ReducedTensorWords R M) :
    ReducedTensorWords.letter R N (ReducedTensorWords.map (R := R) g w) =
      g (ReducedTensorWords.letter R M w) :=
  LinearMap.congr_fun (ReducedTensorWords.letter_comp_map g) w

private theorem letter_comp_deconcatenation_eq_zero (ε : 𝒜.Augmentation)
    {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
    (H : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal)
    (F : P ⊗[R] Q →ₗ[R] ε.augmentationIdeal)
    (f : A →ₗ[R] P) (g : A →ₗ[R] Q)
    (hH : ∀ u v : ReducedTensorWords R A,
      ReducedTensorWords.letter R _ (H (u ⊗ₜ[R] v)) =
        F (f (ReducedTensorWords.letter R A u) ⊗ₜ[R] g (ReducedTensorWords.letter R A v)))
    (n : {n : ℕ // 0 < n}) (hn : n.val ≠ 2) (x : Fin n.val → A) :
    ReducedTensorWords.letter R _
      ((H ∘ₗ ReducedTensorWords.deconcatenation R A)
        (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) = 0 := by
  rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _)]
  refine ReducedTensorWords.eq_zero_of_factor_letter_pair R A F f g ?_ n hn x
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
  refine congrArg (· ∘ₗ ReducedTensorWords.deconcatenation R A) (TensorProduct.ext' fun u v ↦ ?_)
  simpa only [LinearMap.comp_apply, TensorProduct.map_tmul] using hH u v

/-- On pure words of length other than two, the letter component of `leftUnitTerm` vanishes. -/
private theorem letter_leftUnitTerm_of_ne_two (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (hn : n.val ≠ 2) (x : Fin n.val → A) :
    ReducedTensorWords.letter R _
      (ε.leftUnitTerm (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) = 0 := by
  rw [ε.leftUnitTerm_eq]
  exact ε.letter_comp_deconcatenation_eq_zero _
    (TensorProduct.lid R ε.augmentationIdeal).toLinearMap ε.toLinearMap ε.reducedPart
    (fun u v ↦ by simp [scalarPart, letter_map_apply]) n hn x

/-- On pure words of length other than two, the letter component of `rightUnitTerm` vanishes. -/
private theorem letter_rightUnitTerm_of_ne_two (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (hn : n.val ≠ 2) (x : Fin n.val → A) :
    ReducedTensorWords.letter R _
      (ε.rightUnitTerm (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) = 0 := by
  rw [ε.rightUnitTerm_eq]
  exact ε.letter_comp_deconcatenation_eq_zero _
    (TensorProduct.rid R ε.augmentationIdeal).toLinearMap
    (ε.reducedPart ∘ₗ (𝒜.grading.shift 1).koszulTwist 1) ε.toLinearMap
    (fun u v ↦ by simp [scalarPart, letter_map_apply]) n hn x

/-- The Taylor-level letter identity for `map_reducedPart_comp_barDifferential` on a
two-letter word. -/
private theorem taylor_map_reducedPart_two (ε : 𝒜.Augmentation) (a b : A) :
    ε.reducedPart (𝒜.taylor (ReducedTensorWords.of R A (2 : ℕ+)
        (PiTensorProduct.tprod R ![a, b]))) =
      ε.reducedAlgebra.taylor (ReducedTensorWords.map (R := R) ε.reducedPart
        (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![a, b]))) +
        (ReducedTensorWords.letter R _
          (ε.leftUnitTerm (ReducedTensorWords.of R A (2 : ℕ+)
            (PiTensorProduct.tprod R ![a, b]))) +
          (-1 : R) • ReducedTensorWords.letter R _
            (ε.rightUnitTerm (ReducedTensorWords.of R A (2 : ℕ+)
              (PiTensorProduct.tprod R ![a, b])))) := by
  have htwist_red : ε.reducedPart ((𝒜.grading.shift 1).koszulTwist 1 a) =
      -ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) := by
    rw [InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply, map_neg,
      ε.reducedPart_koszulTwist, ε.reducedAlgebra_grading]
  have hπ_two : ReducedTensorWords.map (R := R) ε.reducedPart
        (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])) =
      ReducedTensorWords.of R ε.augmentationIdeal (2 : ℕ+)
        (PiTensorProduct.tprod R ![ε.reducedPart a, ε.reducedPart b]) := by
    rw [← ReducedTensorWords.prepend_ofLetter, ReducedTensorWords.map_prepend,
      ReducedTensorWords.map_ofLetter, ReducedTensorWords.prepend_ofLetter]
  rw [hπ_two, 𝒜.taylor_of_two, ε.reducedAlgebra.taylor_of_two, ε.m_two_eq_reduced_add a b]
  simp only [map_add, map_smul, ε.reducedPart_coe, ε.reducedPart_unit, smul_zero, add_zero,
    leftUnitTerm, rightUnitTerm, LinearMap.comp_apply,
    ReducedTensorWords.deconcatenation_of_two, TensorProduct.map_tmul,
    ReducedTensorWords.letter_ofLetter, ReducedTensorWords.map_ofLetter, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, TensorProduct.rid_tmul, htwist_red, smul_neg, neg_one_smul, neg_neg]
  abel

/-- The Taylor-level letter identity for `map_reducedPart_comp_barDifferential` on pure words
of length other than two. -/
private theorem taylor_map_reducedPart_of_ne_two (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (hn : n.val ≠ 2) (x : Fin n.val → A) :
    ε.reducedPart (𝒜.taylor (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) =
      ε.reducedAlgebra.taylor (ReducedTensorWords.map (R := R) ε.reducedPart
        (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) +
        (ReducedTensorWords.letter R _
          (ε.leftUnitTerm (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) +
          (-1 : R) • ReducedTensorWords.letter R _
            (ε.rightUnitTerm (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)))) := by
  simp only [ε.letter_leftUnitTerm_of_ne_two n hn x, ε.letter_rightUnitTerm_of_ne_two n hn x,
    smul_zero, add_zero, reducedAlgebra_taylor, LinearMap.comp_apply,
    ε.taylor_of_tprod_eq_of_ne_two n hn x]

/-- Reducing the letter-projection comparison for `map_reducedPart_comp_barDifferential` to a
Taylor-map identity. -/
private theorem letter_comp_barDifferential_eq_of_taylor (ε : 𝒜.Augmentation)
    (h : ε.reducedPart ∘ₗ 𝒜.taylor =
      ε.reducedAlgebra.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        (ReducedTensorWords.letter R _ ∘ₗ ε.leftUnitTerm +
          (-1 : R) • (ReducedTensorWords.letter R _ ∘ₗ ε.rightUnitTerm))) :
    ReducedTensorWords.letter R _ ∘ₗ
        (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ 𝒜.barDifferential) =
      ReducedTensorWords.letter R _ ∘ₗ
        (ε.reducedAlgebra.barDifferential ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
          (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm)) := by
  rw [← LinearMap.comp_assoc, ReducedTensorWords.letter_comp_map, LinearMap.comp_assoc,
    AInfinityAlgebra.letter_comp_barDifferential, h]
  simp only [LinearMap.comp_add, LinearMap.comp_smul, ← LinearMap.comp_assoc,
    AInfinityAlgebra.letter_comp_barDifferential]

/-- The letterwise reduced-part projection `π = map reducedPart` intertwines the bar differential
of `𝒜` with that of the reduced algebra `ε.reducedAlgebra`, up to the left and right
unit-contraction terms `ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm`. -/
theorem map_reducedPart_comp_barDifferential (ε : 𝒜.Augmentation) :
    ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ 𝒜.barDifferential =
      ε.reducedAlgebra.barDifferential ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm) := by
  set π := ReducedTensorWords.map (R := R) ε.reducedPart
  have hπ_coalg : ReducedTensorWords.IsCoalgHom R π :=
    ReducedTensorWords.isCoalgHom_map ε.reducedPart
  have hπ_hom : LinearMap.IsHomogeneous π
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
      (ReducedTensorWords.gradedPiece (ε.reducedAlgebra.grading.shift 1)) 0 :=
    ReducedTensorWords.isHomogeneous_map _ _
      (LinearMap.isHomogeneous_shift_piece_iff.2 ε.isHomogeneous_reducedPart)
  have hLHS : ReducedTensorWords.IsGradedCoderivationAlong (𝒜.grading.shift 1) 1 π π
      (π ∘ₗ 𝒜.barDifferential) :=
    hπ_coalg.comp_isGradedCoderivation 𝒜.isGradedCoderivation_barDifferential
  have hRHS : ReducedTensorWords.IsGradedCoderivationAlong (𝒜.grading.shift 1) 1 π π
      (ε.reducedAlgebra.barDifferential ∘ₗ π + (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm)) :=
    (ε.reducedAlgebra.isGradedCoderivation_barDifferential.comp_isCoalgHom hπ_coalg hπ_hom).add
      ε.isGradedCoderivationAlong_unitTerms
  refine hLHS.eq_of_letter_comp_eq hRHS
    (ε.letter_comp_barDifferential_eq_of_taylor
      (ReducedTensorWords.linearMap_ext_two_ne_two R A
        (fun a b ↦ by
          simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply] using
            ε.taylor_map_reducedPart_two a b)
        (fun n hn x ↦ by
          simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply] using
            ε.taylor_map_reducedPart_of_ne_two n hn x)))

end AInfinityAlgebra.Augmentation

end TauCeti
