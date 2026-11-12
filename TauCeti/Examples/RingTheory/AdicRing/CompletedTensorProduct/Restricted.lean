/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct.Restricted

/-!
# Checks for the base change of restricted power series

These checks use only the public interface of
`TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv : A⟨X₁, …, Xₘ⟩ ⊗̂_A C ≃+* C⟨X₁, …, Xₘ⟩`.
With no variables it sends `1 ⊗ c` to the constant series `c`; with one variable it sends the
variable of `A⟨X⟩` to the variable of `C⟨X⟩`, and its inverse sends the variable back.
-/

public section

open TauCeti TauCeti.Huber TauCeti.AdicRing

variable (A C : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [Algebra A C]
  [ContinuousSMul A C]

-- With no variables, the right coefficient `c` goes to the constant series `c`.
example (c : C) :
    CompletedTensorProduct.restrictedEquiv 0 A C
        (CompletedTensorProduct.inr A (restrictedMvPowerSeriesCompletion 0 A) C c) =
      algebraMap C (restrictedMvPowerSeriesCompletion 0 C) c := by
  simp

-- With one variable, the left variable goes to the target variable.
example :
    CompletedTensorProduct.restrictedEquiv 1 A C
        (CompletedTensorProduct.inl A (restrictedMvPowerSeriesCompletion 1 A) C
          ((weightedX _ isWeightFamily_one_weight 0 :
            weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
              restrictedMvPowerSeriesCompletion 1 A)) =
      ((weightedX _ isWeightFamily_one_weight 0 :
        weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set C)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion 1 C) := by
  simp

-- With one variable, the inverse sends the target variable back to `X ⊗ 1`.
example :
    (CompletedTensorProduct.restrictedEquiv 1 A C).symm
        ((weightedX _ isWeightFamily_one_weight 0 :
          weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set C)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion 1 C) =
      CompletedTensorProduct.inl A (restrictedMvPowerSeriesCompletion 1 A) C
        ((weightedX _ isWeightFamily_one_weight 0 :
          weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion 1 A) := by
  simp
