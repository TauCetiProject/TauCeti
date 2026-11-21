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
  have hpi : Fintype.piFinset (fun _ : Fin n.val ↦ (Finset.univ : Finset Bool)) = Finset.univ := by
    ext f
    simp
  have hsum : PiTensorProduct.tprod R x =
      ∑ f : Fin n.val → Bool, PiTensorProduct.tprod R (fun i ↦ piece i (f i)) := by
    rw [← hpi, ← (PiTensorProduct.tprod R).map_sum_finset]
    exact congrArg _ (funext fun i ↦ (hx i).symm)
  conv_lhs =>
    arg 1
    rw [hsum, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : Fin n.val ↦ false))]
  rw [ReducedTensorWords.map_of_tprod, ReducedTensorWords.map_of_tprod]
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
  have hne : f ≠ fun _ ↦ false := (Finset.mem_erase.1 hf).1
  have htrue : ∃ i, f i = true := by
    by_contra h
    push Not at h
    apply hne
    funext i
    cases hfi : f i
    · rfl
    · exact (h i hfi).elim
  obtain ⟨i, hi⟩ := htrue
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
  rw [𝒜.taylor_of_two, ε.map_binary, ε.map_koszulTwist 1,
    ReducedTensorWords.deconcatenation_of_two, TensorProduct.map_tmul, LinearMap.comp_apply,
    LinearMap.comp_apply, ReducedTensorWords.letter_ofLetter, ReducedTensorWords.letter_ofLetter,
    LinearMap.mul'_apply]

/-- The augmentation of the Taylor map is the product of the augmentations of the two letters on a
two-letter word, and zero in all other arities. -/
theorem comp_taylor (ε : 𝒜.Augmentation) :
    ε.toLinearMap ∘ₗ 𝒜.taylor =
      LinearMap.mul' R R ∘ₗ
        TensorProduct.map
          (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
          (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
  simp only [LinearMap.comp_apply]
  by_cases hn : n.val = 2
  · obtain ⟨k, hk⟩ := n
    simp only at hn
    subst k
    rw [ReducedTensorWords.of_two_tprod R A x]
    exact ε.comp_taylor_two (x 0) (x 1)
  · rw [𝒜.taylor_of_tprod, ε.map_m_of_ne_two n.val n.property hn]
    have h0 := ReducedTensorWords.map_letter_letter_deconcatenation_of_ne_two R A n hn x
    have hfac : TensorProduct.map (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
        (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A) =
        TensorProduct.map ε.toLinearMap ε.toLinearMap ∘ₗ
          TensorProduct.map (ReducedTensorWords.letter R A) (ReducedTensorWords.letter R A) := by
      rw [← TensorProduct.map_comp]
    rw [hfac, LinearMap.comp_apply, h0, map_zero, map_zero]

/-- The scalar projection `Tᶜ(sA) ⟶ R` extracting the augmentation of the single-letter
component. -/
private noncomputable def scalarPart (ε : 𝒜.Augmentation) : ReducedTensorWords R A →ₗ[R] R :=
  ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A

/-- The left unit-contraction term `z ↦ ∑ ε(letter z₁) • π(z₂)` of `π ∘ b_A`. -/
private noncomputable def leftUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R ε.augmentationIdeal :=
  (TensorProduct.lid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
    TensorProduct.map ε.scalarPart (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
    ReducedTensorWords.deconcatenation R A

/-- The right unit-contraction term `z ↦ ∑ ε(letter z₂) • π(τ z₁)` of `π ∘ b_A`, where `τ` is the
degree-one letterwise Koszul twist of the suspended grading. -/
private noncomputable def rightUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R ε.augmentationIdeal :=
  (TensorProduct.rid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
    TensorProduct.map
      (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
        ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1))
      ε.scalarPart ∘ₗ
    ReducedTensorWords.deconcatenation R A

/-- Coassociativity comparison for `leftUnitTerm`. -/
private theorem deconcatenation_comp_leftUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords.deconcatenation R ε.augmentationIdeal ∘ₗ ε.leftUnitTerm =
      TensorProduct.map ε.leftUnitTerm (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  set π := ReducedTensorWords.map (R := R) ε.reducedPart
  have hπ : ReducedTensorWords.IsCoalgHom R π := ReducedTensorWords.isCoalgHom_map ε.reducedPart
  set M₁ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    (TensorProduct.lid R _).toLinearMap ∘ₗ
      TensorProduct.map ε.scalarPart (TensorProduct.map π π)
  rw [leftUnitTerm, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
  refine ReducedTensorWords.comp_deconcatenation_eq_of_lTensor_eq_assoc_rTensor R A (F := M₁) ?_ ?_
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, map_smul, LinearMap.lTensor_tmul, M₁]
    rw [hπ.deconcatenation_apply y]
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    induction ReducedTensorWords.deconcatenation R A x using TensorProduct.inductionOn with
    | tmul u v => simp [M₁, π, TensorProduct.smul_tmul']
    | add u v hu hv => simp only [map_add, TensorProduct.add_tmul, hu, hv]

/-- Coassociativity comparison for `rightUnitTerm`. -/
private theorem deconcatenation_comp_rightUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords.deconcatenation R ε.augmentationIdeal ∘ₗ ε.rightUnitTerm =
      TensorProduct.map (ReducedTensorWords.map (R := R) ε.reducedPart) ε.rightUnitTerm ∘ₗ
        LinearMap.rTensor _ (ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  set π := ReducedTensorWords.map (R := R) ε.reducedPart
  set τ := ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)
  have hπτ : ReducedTensorWords.IsCoalgHom R (π ∘ₗ τ) :=
    (ReducedTensorWords.isCoalgHom_map ε.reducedPart).comp
      (ReducedTensorWords.isCoalgHom_map _)
  set M₃ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    (TensorProduct.rid R _).toLinearMap ∘ₗ
      (TensorProduct.assoc R _ _ R).symm.toLinearMap ∘ₗ
      TensorProduct.map (π ∘ₗ τ) (TensorProduct.map (π ∘ₗ τ) ε.scalarPart)
  rw [rightUnitTerm]
  simp only [← LinearMap.comp_assoc]
  refine (ReducedTensorWords.comp_deconcatenation_eq_of_lTensor_eq_assoc_rTensor R A (F := M₃)
    ?_ ?_).symm
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      LinearMap.lTensor_tmul]
    induction ReducedTensorWords.deconcatenation R A y using TensorProduct.inductionOn with
    | tmul u v => simp [M₃, π, τ, TensorProduct.tmul_smul]
    | add u v hu hv => simp only [map_add, TensorProduct.tmul_add, hu, hv]
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.rid_tmul, map_smul, LinearMap.rTensor_tmul]
    rw [← LinearMap.comp_apply π τ, hπτ.deconcatenation_apply x]
    induction ReducedTensorWords.deconcatenation R A x using TensorProduct.inductionOn with
    | tmul u v => simp [M₃]
    | add u v hu hv => simp only [map_add, TensorProduct.add_tmul, smul_add, hu, hv]

/-- Coassociativity cancellation between the cross terms of `leftUnitTerm` and `rightUnitTerm`. -/
private theorem map_leftUnitTerm_comp_deconcatenation (ε : 𝒜.Augmentation) :
    TensorProduct.map (ReducedTensorWords.map (R := R) ε.reducedPart) ε.leftUnitTerm ∘ₗ
        LinearMap.rTensor _ (ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)) ∘ₗ
        ReducedTensorWords.deconcatenation R A =
      TensorProduct.map ε.rightUnitTerm (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  set π := ReducedTensorWords.map (R := R) ε.reducedPart
  set τ := ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)
  set M₂ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    TensorProduct.map (π ∘ₗ τ)
      ((TensorProduct.lid R _).toLinearMap ∘ₗ TensorProduct.map ε.scalarPart π)
  rw [← LinearMap.comp_assoc]
  refine ReducedTensorWords.comp_deconcatenation_eq_of_lTensor_eq_assoc_rTensor R A (F := M₂) ?_ ?_
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp [M₂, leftUnitTerm, π]
  · refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul, rightUnitTerm]
    induction ReducedTensorWords.deconcatenation R A x using TensorProduct.inductionOn with
    | tmul u v => simp [M₂, π, τ, TensorProduct.smul_tmul]
    | add u v hu hv => simp only [map_add, TensorProduct.add_tmul, hu, hv]

/-- The combination `leftUnitTerm + (-1) • rightUnitTerm` is a graded coderivation along the
letterwise reduced-part projection `π = map reducedPart`. -/
private theorem isGradedCoderivationAlong_unitTerms (ε : 𝒜.Augmentation) :
    ReducedTensorWords.IsGradedCoderivationAlong (𝒜.grading.shift 1) 1
      (ReducedTensorWords.map (R := R) ε.reducedPart)
      (ReducedTensorWords.map (R := R) ε.reducedPart)
      (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm) := by
  rw [ReducedTensorWords.isGradedCoderivationAlong_iff]
  simp only [LinearMap.comp_add, LinearMap.comp_smul, ε.deconcatenation_comp_leftUnitTerm,
    ε.deconcatenation_comp_rightUnitTerm, TensorProduct.map_add_left,
    TensorProduct.map_smul_left, TensorProduct.map_add_right, TensorProduct.map_smul_right,
    LinearMap.add_comp, LinearMap.smul_comp, ε.map_leftUnitTerm_comp_deconcatenation]
  set C := TensorProduct.map ε.rightUnitTerm
    (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
      ReducedTensorWords.deconcatenation R A
  rw [add_assoc, ← add_assoc ((-1 : R) • C)]
  have hzero : (-1 : R) • C + C = 0 := by module
  rw [hzero, zero_add]

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
  have hm2 : (ε.reducedAlgebra.m 2
      ![ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a), ε.reducedPart b] : A) =
      𝒜.m 2 ![(ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) : A),
        (ε.reducedPart b : A)] := by
    rw [reducedAlgebra_m, coe_reducedOperation]
    congr 1
    exact funext <| Fin.forall_fin_two.2 ⟨by simp, by simp⟩
  rw [hm2, ← 𝒜.mul_apply, ← 𝒜.mul_apply, htwist_a]
  conv_lhs => rw [← ε.coe_reducedPart_add_smul_unit b]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, 𝒜.mul_apply,
    ε.isStrictUnit.binary_left, ε.isStrictUnit.binary_right, smul_add, smul_smul,
    mul_comm (ε b) (ε a)]
  abel

/-- On pure words of length other than two, the letter component of `leftUnitTerm` vanishes. -/
private theorem letter_leftUnitTerm_of_ne_two (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (hn : n.val ≠ 2) (x : Fin n.val → A) :
    ReducedTensorWords.letter R _
      (ε.leftUnitTerm (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) = 0 := by
  have hfac : ReducedTensorWords.letter R _ ∘ₗ ε.leftUnitTerm =
      ((TensorProduct.lid R ε.augmentationIdeal).toLinearMap ∘ₗ
        TensorProduct.map ε.toLinearMap ε.reducedPart ∘ₗ
        TensorProduct.map (ReducedTensorWords.letter R A) (ReducedTensorWords.letter R A)) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
    rw [leftUnitTerm]
    simp only [← LinearMap.comp_assoc]
    congr 1
    refine TensorProduct.ext' fun u v ↦ ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, map_smul, scalarPart]
    rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
      ReducedTensorWords.letter_comp_map, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _), hfac, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    ReducedTensorWords.map_letter_letter_deconcatenation_of_ne_two R A n hn x, map_zero, map_zero]

/-- On pure words of length other than two, the letter component of `rightUnitTerm` vanishes. -/
private theorem letter_rightUnitTerm_of_ne_two (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (hn : n.val ≠ 2) (x : Fin n.val → A) :
    ReducedTensorWords.letter R _
      (ε.rightUnitTerm (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) = 0 := by
  have hfac : ReducedTensorWords.letter R _ ∘ₗ ε.rightUnitTerm =
      ((TensorProduct.rid R ε.augmentationIdeal).toLinearMap ∘ₗ
        TensorProduct.map (ε.reducedPart ∘ₗ (𝒜.grading.shift 1).koszulTwist 1) ε.toLinearMap ∘ₗ
        TensorProduct.map (ReducedTensorWords.letter R A) (ReducedTensorWords.letter R A)) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
    rw [rightUnitTerm]
    simp only [← LinearMap.comp_assoc]
    congr 1
    refine TensorProduct.ext' fun u v ↦ ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.rid_tmul, map_smul, scalarPart]
    rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
      ReducedTensorWords.letter_comp_map, LinearMap.comp_apply,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
      ReducedTensorWords.letter_comp_map, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _), hfac, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    ReducedTensorWords.map_letter_letter_deconcatenation_of_ne_two R A n hn x, map_zero, map_zero]

/-- The Taylor-level letter identity for `map_reducedPart_comp_barDifferential_aux` on a
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
    refine (ReducedTensorWords.map_of_tprod (R := R) ε.reducedPart (2 : ℕ+) ![a, b]).trans ?_
    congr 2
    exact funext <| Fin.forall_fin_two.2 ⟨by simp, by simp⟩
  rw [hπ_two, 𝒜.taylor_of_two, ε.reducedAlgebra.taylor_of_two, ε.m_two_eq_reduced_add a b]
  simp only [map_add, map_smul, ε.reducedPart_coe, ε.reducedPart_unit, smul_zero, add_zero,
    leftUnitTerm, rightUnitTerm, LinearMap.comp_apply,
    ReducedTensorWords.deconcatenation_of_two, TensorProduct.map_tmul, scalarPart,
    ReducedTensorWords.letter_ofLetter, ReducedTensorWords.map_ofLetter, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, TensorProduct.rid_tmul, htwist_red, smul_neg, neg_one_smul, neg_neg]
  abel

/-- The Taylor-level letter identity for `map_reducedPart_comp_barDifferential_aux` on pure words
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

/-- Reducing the letter-projection comparison for `map_reducedPart_comp_barDifferential_aux` to a
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
of `𝒜` with that of the reduced algebra `ε.reducedAlgebra`, up to the two unit-contraction terms
`leftUnitTerm + (-1) • rightUnitTerm`. -/
private theorem map_reducedPart_comp_barDifferential_aux (ε : 𝒜.Augmentation) :
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
    (ε.letter_comp_barDifferential_eq_of_taylor (ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply]
  by_cases hn2 : n.val = 2
  · obtain ⟨k, hk⟩ := n
    simp only at hn2
    subst k
    rw [ReducedTensorWords.of_two_tprod R A x]
    exact ε.taylor_map_reducedPart_two (x 0) (x 1)
  · exact ε.taylor_map_reducedPart_of_ne_two n hn2 x

/-- The letterwise reduced-part projection `π = map reducedPart` intertwines the bar differential
of `𝒜` with that of the reduced algebra `ε.reducedAlgebra`, up to the left and right
unit-contraction terms coming from the strict unit acting in arity two. -/
theorem map_reducedPart_comp_barDifferential (ε : 𝒜.Augmentation) :
    ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ 𝒜.barDifferential =
      ε.reducedAlgebra.barDifferential ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        ((TensorProduct.lid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
            TensorProduct.map (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
              (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
            ReducedTensorWords.deconcatenation R A +
          (-1 : R) •
            ((TensorProduct.rid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
              TensorProduct.map
                (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
                  ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1))
                (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A) ∘ₗ
              ReducedTensorWords.deconcatenation R A)) := by
  simpa only [leftUnitTerm, rightUnitTerm, scalarPart] using
    ε.map_reducedPart_comp_barDifferential_aux

end AInfinityAlgebra.Augmentation

end TauCeti
