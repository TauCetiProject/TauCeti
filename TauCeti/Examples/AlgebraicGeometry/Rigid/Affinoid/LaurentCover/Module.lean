/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.LaurentCover.Module

/-!
# Algebraic module checks for the Laurent cover

Exercise module gluing on the countable free module and on arbitrary quotient modules.
These do not require a Banach norm or flatness of the module. A nonzero finitely supported
vector remains detectable on the cover, and module maps preserve the augmentation.
-/

public section

open TensorProduct TauCeti TauCeti.LaurentCover

namespace TauCeti.Examples.LaurentCover

variable {K A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A] [NormedAlgebra K A]
  (hA : IsAffinoidAlgebra K A) (f : A)

local notation "L" => LaurentFraction (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A)
local notation "G" => LaurentFraction (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f)

-- Infinitely generated modules have the full augmented exact sequence.
example : Function.Exact (moduleAugmentation (ℕ →₀ A) f) (moduleDiff (ℕ →₀ A) f) :=
  exact_moduleAugmentation_moduleDiff _ _

example (u : L ⊗[A] (ℕ →₀ A)) (v : G ⊗[A] (ℕ →₀ A))
    (h : (leToOverlap f).toLinearMap.rTensor (ℕ →₀ A) u =
      (geToOverlap f).toLinearMap.rTensor (ℕ →₀ A) v) :
    ∃! m : ℕ →₀ A, moduleAugmentation (ℕ →₀ A) f m = (u, v) :=
  existsUnique_module_gluing _ hA f u v h

include hA in
/-- A nonzero basis vector in the countable free module is detected by Laurent restrictions. -/
theorem augmentation_single_ne_zero (i : ℕ) (a : A) (ha : a ≠ 0) :
    moduleAugmentation (ℕ →₀ A) f (Finsupp.single i a) ≠ 0 := by
  intro h
  have hz : Finsupp.single i a = (0 : ℕ →₀ A) :=
    moduleAugmentation_injective _ hA f (by simpa using h)
  exact ha (by simpa using congrArg (fun m : ℕ →₀ A ↦ m i) hz)

-- No flatness or reducedness assumption is imposed on the quotient module.
example (I : Ideal A) (u : L ⊗[A] (A ⧸ I)) (v : G ⊗[A] (A ⧸ I))
    (h : (leToOverlap f).toLinearMap.rTensor (A ⧸ I) u =
      (geToOverlap f).toLinearMap.rTensor (A ⧸ I) v) :
    ∃! m : A ⧸ I, moduleAugmentation (A ⧸ I) f m = (u, v) :=
  existsUnique_module_gluing _ hA f u v h

-- Quotient maps induce the expected map of augmented sequences.
example (I : Ideal A) (a : A) :
    (((Ideal.Quotient.mkₐ A I).toLinearMap.lTensor L).prodMap
      ((Ideal.Quotient.mkₐ A I).toLinearMap.lTensor G)) (moduleAugmentation A f a) =
      moduleAugmentation (A ⧸ I) f (Ideal.Quotient.mk I a) :=
  moduleAugmentation_natural A f (Ideal.Quotient.mkₐ A I).toLinearMap a

-- The zero quotient also satisfies injectivity, with no nontriviality instance.
example : Function.Injective (moduleAugmentation (A ⧸ (⊤ : Ideal A)) f) :=
  moduleAugmentation_injective _ hA f

end TauCeti.Examples.LaurentCover
