/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.Algebra.Homology.Contraction.TensorTrick.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration.GradedCoderivation
public import TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# The length-lowering part of an A-infinity bar differential

The bar differential splits into its unary, letterwise part and a higher part. The Taylor map of
the higher part vanishes on single letters, so that part strictly lowers tensor length. Its
composite with the tensor-trick homotopy is locally nilpotent. Thus the unit `1 + δ H` required by
the basic perturbation lemma exists without a completion or a global bound on word length.

This is the finite bar perturbation used in homological transfer. See Gugenheim--Lambe--Stasheff,
*Perturbation theory in differential homological algebra II*, and Keller, *Introduction to
A-infinity algebras and modules*, Section 3.3.
-/

public section

open scoped DirectSum

universe uR uA uH

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

/-- The part of the bar differential that collapses blocks of at least two letters. -/
noncomputable def higherBarDifferential (𝒜 : AInfinityAlgebra R A) :
    Module.End R (ReducedTensorWords R A) :=
  ReducedTensorWords.gradedCoderiv (𝒜.grading.shift 1) 𝒜.higherTaylor 1

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

/-- The higher bar perturbation followed by a tensor-trick homotopy is locally nilpotent. -/
theorem exists_pow_higherBarDifferential_comp_homotopy_eq_zero
    {H : Type uH} [AddCommGroup H] [Module R H]
    {dA : Module.End R A} {dH : Module.End R H}
    (𝒜 : AInfinityAlgebra R A) (c : LinearSpecialContraction dA dH)
    (z : ReducedTensorWords R A) :
    ∃ n, ((𝒜.higherBarDifferential ∘ₗ
        c.reducedTensorWordsHomotopy (𝒜.grading.shift 1)) ^ n) z = 0 :=
  ReducedTensorWords.exists_pow_comp_apply_eq_zero_of_filtration_lowering
    R A 𝒜.higherBarDifferential (c.reducedTensorWordsHomotopy (𝒜.grading.shift 1))
    𝒜.higherBarDifferential_filtration
    (c.reducedTensorWordsHomotopy_filtration (𝒜.grading.shift 1)) z

/-- The unit required by the perturbation lemma exists for the higher bar differential. -/
theorem isUnit_one_add_higherBarDifferential_comp_homotopy
    {H : Type uH} [AddCommGroup H] [Module R H]
    {dA : Module.End R A} {dH : Module.End R H}
    (𝒜 : AInfinityAlgebra R A) (c : LinearSpecialContraction dA dH) :
    IsUnit (1 + 𝒜.higherBarDifferential *
      c.reducedTensorWordsHomotopy (𝒜.grading.shift 1)) := by
  apply Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero
  intro z
  exact 𝒜.exists_pow_higherBarDifferential_comp_homotopy_eq_zero c z

end TauCeti.AInfinityAlgebra
