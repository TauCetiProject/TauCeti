/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Augmentation.Basic
public import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# A module splitting of augmentation

Choosing an index splits the augmentation sequence as modules: subtract the coefficient sum
at that index to project onto the sum-zero submodule. This projection is not generally
equivariant, since the chosen index need not be fixed. It gives a split presentation of the
augmentation module that remains exact after arbitrary extension of scalars.
-/

public noncomputable section

namespace TauCeti

variable (R : Type*) [Ring R] (G X : Type*) [Monoid G] [MulAction G X]

/-- Project onto the sum-zero permutation module by subtracting the coefficient sum at `x₀`.
This is a module map, not in general an equivariant map: the chosen index need not be fixed. -/
def augmentationProjection (x₀ : X) : MonoidAlgebra R X →ₗ[R]
    (augmentationSubrepresentation R G X).toSubmodule :=
  (LinearMap.id - ((MonoidAlgebra.basis X R).sumCoords).smulRight
    (MonoidAlgebra.single x₀ 1)).codRestrict _ fun v => by
      simp only [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        map_sub, map_smul]
      simp

/-- The projection subtracts the coefficient sum times the basis vector at the chosen index. -/
@[simp]
theorem coe_augmentationProjection (x₀ : X) (v : MonoidAlgebra R X) :
    (augmentationProjection R G X x₀ v : MonoidAlgebra R X) =
      v - (MonoidAlgebra.basis X R).sumCoords v • MonoidAlgebra.single x₀ 1 :=
  (rfl)

/-- The sum-zero projection is a retraction of the augmentation inclusion. -/
@[simp]
theorem augmentationProjection_coe (x₀ : X)
    (v : (augmentationSubrepresentation R G X).toSubmodule) :
    augmentationProjection R G X x₀ v = v := by
  apply Subtype.ext
  simp [mem_augmentationSubrepresentation_iff.mp v.2]

/-- The kernel of the sum-zero projection consists of the multiples of the chosen basis vector. -/
theorem exact_toSpanSingleton_augmentationProjection (x₀ : X) :
    Function.Exact (LinearMap.toSpanSingleton R _ (MonoidAlgebra.single x₀ 1))
      (augmentationProjection R G X x₀) := by
  rw [LinearMap.exact_iff, augmentationProjection, LinearMap.ker_codRestrict,
    Module.Dual.ker_id_sub_smulRight _ (by simp), LinearMap.range_toSpanSingleton]

/-- Every sum-zero vector is in the image of the projection. -/
theorem augmentationProjection_surjective (x₀ : X) :
    Function.Surjective (augmentationProjection R G X x₀) :=
  fun v => ⟨v.1, augmentationProjection_coe R G X x₀ v⟩

end TauCeti
