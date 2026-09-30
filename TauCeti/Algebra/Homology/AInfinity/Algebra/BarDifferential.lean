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
  have hletter : ReducedTensorWords.letter R A (ReducedTensorWords.of R A n x) = 0 := by
    rw [ReducedTensorWords.letter_apply,
      ReducedTensorWords.component_of_of_ne R A hne x, map_zero]
  simp [higherTaylor, hletter]

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

end TauCeti.AInfinityAlgebra
