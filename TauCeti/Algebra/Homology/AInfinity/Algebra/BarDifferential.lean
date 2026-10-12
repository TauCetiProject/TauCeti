/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration.GradedCoderivation

/-!
# Unary and higher parts of the A-infinity bar differential

The bar differential splits into a unary part acting on each letter and a higher part that
strictly lowers tensor length. The corresponding Taylor maps agree with the original Taylor map
on words of their respective arities. The higher part supplies the finite filtration step used
in homological transfer.

See Getzler--Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2, and Keller,
*Introduction to A-infinity algebras and modules*, Section 3.3.
-/

public section

open scoped DirectSum TensorProduct

universe uR uA

namespace TauCeti.AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The Taylor map of the higher bar operations, obtained by removing the unary component. -/
noncomputable def higherTaylor (𝒜 : AInfinityAlgebra R A) :
    ReducedTensorWords R A →ₗ[R] A :=
  𝒜.taylor - (𝒜.taylor ∘ₗ ReducedTensorWords.ofLetter R A) ∘ₗ
    ReducedTensorWords.letter R A

/-- The higher Taylor map vanishes on words of length one. -/
@[simp]
theorem higherTaylor_comp_ofLetter (𝒜 : AInfinityAlgebra R A) :
    𝒜.higherTaylor ∘ₗ ReducedTensorWords.ofLetter R A = 0 := by
  apply LinearMap.ext
  intro a
  simp [higherTaylor, LinearMap.comp_apply, ReducedTensorWords.letter_ofLetter]

/-- On a word of length at least two, the higher Taylor map is the original Taylor map. -/
@[simp]
theorem higherTaylor_of (𝒜 : AInfinityAlgebra R A)
    (n : {n : ℕ // 0 < n}) (hn : 1 < n.1) (x : TensorPower R n.1 A) :
    𝒜.higherTaylor (ReducedTensorWords.of R A n x) =
      𝒜.taylor (ReducedTensorWords.of R A n x) := by
  have hne : n ≠ (1 : {n : ℕ // 0 < n}) := by
    intro h
    have h' : n.1 = 1 := congrArg Subtype.val h
    omega
  simp [higherTaylor, ReducedTensorWords.letter_of_of_ne_one R A hne]

/-- The part of the bar differential that collapses blocks of at least two letters. -/
noncomputable def higherBarDifferential (𝒜 : AInfinityAlgebra R A) :
    Module.End R (ReducedTensorWords R A) :=
  ReducedTensorWords.gradedCoderiv (𝒜.grading.shift 1) 𝒜.higherTaylor 1

/-- The letter projection of the higher bar differential is the higher Taylor map. -/
@[simp]
theorem letter_comp_higherBarDifferential (𝒜 : AInfinityAlgebra R A) :
    ReducedTensorWords.letter R A ∘ₗ 𝒜.higherBarDifferential = 𝒜.higherTaylor := by
  exact ReducedTensorWords.letter_comp_gradedCoderiv (𝒜.grading.shift 1) 𝒜.higherTaylor 1

/-- The arity component of the higher bar differential is the higher Taylor component. -/
@[simp]
theorem higherBarDifferential_taylorComponent (𝒜 : AInfinityAlgebra R A)
    (n : {n : ℕ // 0 < n}) :
    𝒜.higherBarDifferential.taylorComponent n =
      𝒜.higherTaylor ∘ₗ ReducedTensorWords.of R A n := by
  exact ReducedTensorWords.taylorComponent_gradedCoderiv
    (𝒜.grading.shift 1) 𝒜.higherTaylor 1 n

/-- The higher bar differential is a graded coderivation for the suspended grading. -/
theorem isGradedCoderivation_higherBarDifferential (𝒜 : AInfinityAlgebra R A) :
    ReducedTensorWords.IsGradedCoderivation (𝒜.grading.shift 1) 1
      𝒜.higherBarDifferential := by
  exact ReducedTensorWords.isGradedCoderivation_gradedCoderiv
    (𝒜.grading.shift 1) 𝒜.higherTaylor 1

/-- The higher bar differential strictly lowers tensor length. -/
theorem higherBarDifferential_filtration (𝒜 : AInfinityAlgebra R A) (n : ℕ) :
    Submodule.map 𝒜.higherBarDifferential (ReducedTensorWords.filtration R A (n + 1)) ≤
      ReducedTensorWords.filtration R A n := by
  exact ReducedTensorWords.gradedCoderiv_filtration_lowering
    (𝒜.grading.shift 1) 𝒜.higherTaylor 1 𝒜.higherTaylor_comp_ofLetter n

/-- The higher bar differential has no action on single-letter words. -/
@[simp]
theorem higherBarDifferential_ofLetter (𝒜 : AInfinityAlgebra R A) (a : A) :
    𝒜.higherBarDifferential (ReducedTensorWords.ofLetter R A a) = 0 := by
  have h := 𝒜.higherBarDifferential_filtration 0
    ⟨_, ReducedTensorWords.ofLetter_mem_filtration R A a, rfl⟩
  rwa [ReducedTensorWords.filtration_zero] at h

/-- The higher bar differential collapses a two-letter word to the binary operation, with the
suspension sign carried by the degree-one Koszul twist of the first letter. -/
theorem higherBarDifferential_of_two (𝒜 : AInfinityAlgebra R A) (a b : A) :
    𝒜.higherBarDifferential (ReducedTensorWords.of R A (2 : ℕ+)
        (PiTensorProduct.tprod R ![a, b])) =
      ReducedTensorWords.ofLetter R A (𝒜.m 2 ![𝒜.grading.koszulTwist 1 a, b]) := by
  refine ReducedTensorWords.eq_of_deconcatenation_eq_of_letter_eq R A ?_ ?_
  · rw [𝒜.isGradedCoderivation_higherBarDifferential.deconcatenation_apply,
      ReducedTensorWords.deconcatenation_of_two, ReducedTensorWords.deconcatenation_ofLetter]
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, higherBarDifferential_ofLetter,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  · rw [← LinearMap.comp_apply, letter_comp_higherBarDifferential,
      𝒜.higherTaylor_of (2 : ℕ+) (by decide), taylor_of_two, ReducedTensorWords.letter_ofLetter]

/-- The higher bar differential of a three-letter word: the two collapses of adjacent letters to
the binary operation, the second one with the sign of moving the degree-one operation past the
first letter, and the collapse of all three letters to the ternary operation.  Koszul twists carry
the suspension signs. -/
theorem higherBarDifferential_of_three (𝒜 : AInfinityAlgebra R A) (a b c : A) :
    𝒜.higherBarDifferential (ReducedTensorWords.of R A (3 : ℕ+)
        (PiTensorProduct.tprod R ![a, b, c])) =
      ReducedTensorWords.of R A (2 : ℕ+)
          (PiTensorProduct.tprod R ![𝒜.m 2 ![𝒜.grading.koszulTwist 1 a, b], c])
        - ReducedTensorWords.of R A (2 : ℕ+)
            (PiTensorProduct.tprod R
              ![𝒜.grading.koszulTwist 1 a, 𝒜.m 2 ![𝒜.grading.koszulTwist 1 b, c]])
        + ReducedTensorWords.ofLetter R A (𝒜.m 3 ![a, 𝒜.grading.koszulTwist 1 b, c]) := by
  -- Read the three-letter word as the letter `a` prepended to the two-letter word `b c`.
  have h3 : ReducedTensorWords.of R A (3 : ℕ+) (PiTensorProduct.tprod R ![a, b, c]) =
      ReducedTensorWords.prepend R A a
        (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![b, c])) :=
    (ReducedTensorWords.prepend_of_tprod a (2 : ℕ+) ![b, c]).symm
  refine ReducedTensorWords.eq_of_deconcatenation_eq_of_letter_eq R A ?_ ?_
  · rw [𝒜.isGradedCoderivation_higherBarDifferential.deconcatenation_apply, h3,
      ReducedTensorWords.deconcatenation_prepend]
    -- Distribute the two tensor factors of the co-Leibniz rule first, then evaluate the letters.
    simp only [map_add, map_sub, ReducedTensorWords.deconcatenation_of_two,
      ReducedTensorWords.deconcatenation_ofLetter, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      ReducedTensorWords.prepend_ofLetter, higherBarDifferential_ofLetter,
      higherBarDifferential_of_two, ReducedTensorWords.map_ofLetter,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add, add_zero]
    rw [InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply, map_neg,
      TensorProduct.neg_tmul]
    abel
  · rw [← LinearMap.comp_apply, letter_comp_higherBarDifferential,
      𝒜.higherTaylor_of (3 : ℕ+) (by decide), taylor_of_three, map_add, map_sub,
      ReducedTensorWords.letter_of_two, ReducedTensorWords.letter_of_two,
      ReducedTensorWords.letter_ofLetter, sub_zero, zero_add]

/-- The unary part of the bar differential acts on one letter at a time. -/
noncomputable def unaryBarDifferential (𝒜 : AInfinityAlgebra R A) :
    Module.End R (ReducedTensorWords R A) :=
  ReducedTensorWords.gradedCoderiv (𝒜.grading.shift 1)
    ((𝒜.taylor ∘ₗ ReducedTensorWords.ofLetter R A) ∘ₗ ReducedTensorWords.letter R A) 1

/-- The letter projection of the unary bar differential is its unary Taylor map. -/
@[simp]
theorem letter_comp_unaryBarDifferential (𝒜 : AInfinityAlgebra R A) :
    ReducedTensorWords.letter R A ∘ₗ 𝒜.unaryBarDifferential =
      (𝒜.taylor ∘ₗ ReducedTensorWords.ofLetter R A) ∘ₗ
        ReducedTensorWords.letter R A := by
  exact ReducedTensorWords.letter_comp_gradedCoderiv (𝒜.grading.shift 1) _ 1

/-- The arity component of the unary bar differential is its unary Taylor component. -/
@[simp]
theorem unaryBarDifferential_taylorComponent (𝒜 : AInfinityAlgebra R A)
    (n : {n : ℕ // 0 < n}) :
    𝒜.unaryBarDifferential.taylorComponent n =
      ((𝒜.taylor ∘ₗ ReducedTensorWords.ofLetter R A) ∘ₗ
        ReducedTensorWords.letter R A) ∘ₗ ReducedTensorWords.of R A n := by
  exact ReducedTensorWords.taylorComponent_gradedCoderiv (𝒜.grading.shift 1) _ 1 n

/-- The unary bar differential is a graded coderivation for the suspended grading. -/
theorem isGradedCoderivation_unaryBarDifferential (𝒜 : AInfinityAlgebra R A) :
    ReducedTensorWords.IsGradedCoderivation (𝒜.grading.shift 1) 1
      𝒜.unaryBarDifferential := by
  exact ReducedTensorWords.isGradedCoderivation_gradedCoderiv (𝒜.grading.shift 1) _ 1

/-- On a pure tensor word, the unary bar differential acts on each letter with the Koszul twist
on the letters preceding it. -/
theorem unaryBarDifferential_of_tprod (𝒜 : AInfinityAlgebra R A)
    {n : ℕ} (hn : 0 < n) (x : Fin n → A) :
    𝒜.unaryBarDifferential (ReducedTensorWords.of R A ⟨n, hn⟩
      (PiTensorProduct.tprod R x)) =
        ∑ p ∈ Finset.range n, ReducedTensorWords.of R A ⟨n, hn⟩
          (PiTensorProduct.tprod R fun i ↦
            if i.val < p then (𝒜.grading.shift 1).koszulTwist 1 (x i)
            else if i.val = p then 𝒜.m 1 ![x i] else x i) := by
  simpa only [unaryBarDifferential, LinearMap.comp_apply, 𝒜.taylor_ofLetter] using
    ReducedTensorWords.gradedCoderiv_comp_letter_of_tprod (𝒜.grading.shift 1)
      (𝒜.taylor ∘ₗ ReducedTensorWords.ofLetter R A) 1 hn x

/-- The bar differential is the sum of its unary and higher parts. -/
theorem barDifferential_eq_unary_add_higher (𝒜 : AInfinityAlgebra R A) :
    𝒜.barDifferential = 𝒜.unaryBarDifferential + 𝒜.higherBarDifferential := by
  apply ReducedTensorWords.IsGradedCoderivation.eq_of_letter_comp_eq
    𝒜.isGradedCoderivation_barDifferential
  · exact (ReducedTensorWords.mem_gradedCoderivations (𝒜.grading.shift 1)).1
      ((ReducedTensorWords.gradedCoderivations (𝒜.grading.shift 1) 1).add_mem
        ((ReducedTensorWords.mem_gradedCoderivations _).2
          (ReducedTensorWords.isGradedCoderivation_gradedCoderiv _ _ _))
        ((ReducedTensorWords.mem_gradedCoderivations _).2
          (ReducedTensorWords.isGradedCoderivation_gradedCoderiv _ _ _)))
  · rw [𝒜.letter_comp_barDifferential]
    simp only [LinearMap.comp_add, ReducedTensorWords.letter_comp_gradedCoderiv,
      higherTaylor, unaryBarDifferential, higherBarDifferential]
    abel

/-- The unary bar differential applies the unary operation to a single letter. -/
@[simp]
theorem unaryBarDifferential_ofLetter (𝒜 : AInfinityAlgebra R A) (a : A) :
    𝒜.unaryBarDifferential (ReducedTensorWords.ofLetter R A a) =
      ReducedTensorWords.ofLetter R A (𝒜.m 1 ![a]) := by
  have h := 𝒜.barDifferential_ofLetter a
  rw [𝒜.barDifferential_eq_unary_add_higher, LinearMap.add_apply,
    𝒜.higherBarDifferential_ofLetter, add_zero] at h
  exact h

/-- The unary bar differential preserves the tensor-length filtration. -/
theorem unaryBarDifferential_filtration (𝒜 : AInfinityAlgebra R A) (n : ℕ) :
    Submodule.map 𝒜.unaryBarDifferential (ReducedTensorWords.filtration R A n) ≤
      ReducedTensorWords.filtration R A n := by
  rw [Submodule.map_le_iff_le_comap, ReducedTensorWords.filtration_le_iff]
  intro k hk
  rintro _ ⟨z, rfl⟩
  simp only [Submodule.mem_comap]
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
      rw [map_smul, map_smul, unaryBarDifferential,
        ReducedTensorWords.gradedCoderiv_comp_letter_of_tprod]
      apply Submodule.smul_mem
      exact Submodule.sum_mem _ fun _ _ ↦ ReducedTensorWords.of_mem_filtration R A hk _
  | add x y hx hy =>
      rw [map_add, map_add]
      exact add_mem hx hy

/-- On single letters the Taylor map is the differential. -/
theorem taylor_comp_ofLetter (𝒜 : AInfinityAlgebra R A) :
    𝒜.taylor ∘ₗ ReducedTensorWords.ofLetter R A = 𝒜.differential := by
  ext a
  rw [LinearMap.comp_apply, taylor_ofLetter, differential_apply]

/-- The unary bar differential is the letterwise extension of the differential, with the Koszul
signs of the suspended grading. -/
theorem unaryBarDifferential_eq_gradedCoderiv (𝒜 : AInfinityAlgebra R A) :
    𝒜.unaryBarDifferential = ReducedTensorWords.gradedCoderiv (𝒜.grading.shift 1)
      (𝒜.differential ∘ₗ ReducedTensorWords.letter R A) 1 := by
  rw [unaryBarDifferential, taylor_comp_ofLetter]

/-- The unary Taylor map `m₁ ∘ letter` has degree one for the suspended grading. -/
private theorem isHomogeneous_differential_comp_letter (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous (𝒜.differential ∘ₗ ReducedTensorWords.letter R A)
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) (𝒜.grading.shift 1).piece 1 := by
  have hd : LinearMap.IsHomogeneous 𝒜.differential (𝒜.grading.shift 1).piece
      (𝒜.grading.shift 1).piece 1 := by
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    rw [InternalGrading.shift_piece] at hx ⊢
    rw [add_right_comm]
    exact 𝒜.differential_mem_piece hx
  simpa only [zero_add] using
    hd.comp (ReducedTensorWords.isHomogeneous_letter (𝒜.grading.shift 1))

/-- The higher Taylor map has degree one for the suspended grading. -/
theorem isHomogeneous_higherTaylor (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous 𝒜.higherTaylor
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) (𝒜.grading.shift 1).piece 1 := by
  rw [higherTaylor, taylor_comp_ofLetter]
  exact (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree).sub
    𝒜.isHomogeneous_differential_comp_letter

/-- The higher bar differential has degree one for the suspended grading. -/
theorem isHomogeneous_higherBarDifferential (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous 𝒜.higherBarDifferential
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) 1 :=
  ReducedTensorWords.isHomogeneous_gradedCoderiv _ _ 1 1 𝒜.isHomogeneous_higherTaylor

/-- The unary bar differential has degree one for the suspended grading. -/
theorem isHomogeneous_unaryBarDifferential (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous 𝒜.unaryBarDifferential
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) 1 := by
  rw [unaryBarDifferential_eq_gradedCoderiv]
  exact ReducedTensorWords.isHomogeneous_gradedCoderiv _ _ 1 1
    𝒜.isHomogeneous_differential_comp_letter

/-- The unary bar differential squares to zero, since the differential does. -/
@[simp]
theorem unaryBarDifferential_comp_self (𝒜 : AInfinityAlgebra R A) :
    𝒜.unaryBarDifferential ∘ₗ 𝒜.unaryBarDifferential = 0 := by
  have hcod := 𝒜.isGradedCoderivation_unaryBarDifferential
    |>.isCoderivation_comp_self_of_isHomogeneous_one 𝒜.isHomogeneous_unaryBarDifferential
  refine hcod.eq_of_letter_comp_eq
    ((ReducedTensorWords.mem_coderivations R A).1 (ReducedTensorWords.coderivations R A).zero_mem)
    ?_
  rw [← LinearMap.comp_assoc, letter_comp_unaryBarDifferential, taylor_comp_ofLetter,
    LinearMap.comp_assoc, letter_comp_unaryBarDifferential, taylor_comp_ofLetter,
    ← LinearMap.comp_assoc, differential_comp_self_eq_zero, LinearMap.zero_comp,
    LinearMap.comp_zero]

end TauCeti.AInfinityAlgebra
