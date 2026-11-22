/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Augmentation of connected nonnegatively `ℤ`-graded algebras

When a nonnegatively `ℤ`-graded `R`-algebra `A` (`𝒜 : ℤ → Submodule R A`, `∀ i < 0, 𝒜 i = ⊥`) is
connected (`𝒜 0` lies in the image of `algebraMap R A`, with `FaithfulSMul R A`),
`Algebra.ofId R (𝒜 0)` is an `R`-algebra equivalence `gradeZeroAlgEquiv : R ≃ₐ[R] 𝒜 0`. Composing
`TauCeti.GradedAlgebra.projZeroAlgHom` with its inverse defines the canonical `R`-algebra
augmentation `connectedAugmentation : A →ₐ[R] R` annihilating positive degrees and retracting
`algebraMap R A`.

## Main definitions

* `TauCeti.GradedAlgebra.gradeZeroAlgEquiv`: the `R`-algebra equivalence `R ≃ₐ[R] 𝒜 0` for a
  connected graded `R`-algebra.
* `TauCeti.GradedAlgebra.connectedAugmentation`: the canonical augmentation `A →ₐ[R] R` of a
  connected nonnegatively `ℤ`-graded `R`-algebra.

## Main results

* `TauCeti.GradedAlgebra.connectedAugmentation_eq_zero_iff`: the kernel of `connectedAugmentation`
  is `⨆ i > 0, 𝒜 i`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

noncomputable section

open DirectSum

namespace TauCeti.GradedAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]

/-- The `R`-algebra equivalence `R ≃ₐ[R] 𝒜 0` for a connected graded `R`-algebra. -/
def gradeZeroAlgEquiv [FaithfulSMul R A]
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) : R ≃ₐ[R] 𝒜 0 :=
  AlgEquiv.ofBijective (Algebra.ofId R (𝒜 0)) ⟨fun c₁ c₂ h ↦
    FaithfulSMul.algebraMap_injective R A (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨c, hc⟩ := hzero x.val x.property
      exact ⟨c, Subtype.ext hc⟩⟩

/-- Applying `gradeZeroAlgEquiv` embeds scalars via `algebraMap R A`. -/
@[simp]
theorem coe_gradeZeroAlgEquiv_apply [FaithfulSMul R A]
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) (c : R) :
    (gradeZeroAlgEquiv hzero c : A) = algebraMap R A c :=
  congrArg Subtype.val (AlgEquiv.ofBijective_apply (Algebra.ofId R (𝒜 0)) _ c)

/-- `(gradeZeroAlgEquiv hzero).symm` sends the embedded scalar `algebraMap R A c` back to `c`. -/
@[simp]
theorem gradeZeroAlgEquiv_symm_apply [FaithfulSMul R A]
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) (c : R) :
    (gradeZeroAlgEquiv hzero).symm ⟨algebraMap R A c, SetLike.algebraMap_mem_graded 𝒜 c⟩ = c :=
  (gradeZeroAlgEquiv hzero).injective <| Subtype.ext <| by
    rw [AlgEquiv.apply_symm_apply, coe_gradeZeroAlgEquiv_apply]

/-- The canonical augmentation `A →ₐ[R] R` of a connected nonnegatively `ℤ`-graded `R`-algebra,
sending positive-degree elements to zero and identifying `𝒜 0` with `R`. -/
def connectedAugmentation [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) : A →ₐ[R] R :=
  (gradeZeroAlgEquiv hzero).symm.toAlgHom.comp (projZeroAlgHom hneg)

/-- Embedding `connectedAugmentation hneg hzero a` back into `A` recovers the degree-zero
component `decompose 𝒜 a 0`. -/
theorem algebraMap_connectedAugmentation [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) (a : A) :
    algebraMap R A (connectedAugmentation hneg hzero a) = decompose 𝒜 a 0 := by
  rw [← coe_gradeZeroAlgEquiv_apply hzero, connectedAugmentation, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, coe_projZeroAlgHom_apply]

/-- On degree-zero elements, `connectedAugmentation` inverts `algebraMap R A`. -/
@[simp]
theorem algebraMap_connectedAugmentation_of_mem_zero [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) {a : A} (ha : a ∈ 𝒜 0) :
    algebraMap R A (connectedAugmentation hneg hzero a) = a :=
  (algebraMap_connectedAugmentation hneg hzero a).trans (decompose_of_mem_same 𝒜 ha)

/-- Homogeneous elements of strictly positive degree lie in the kernel of `connectedAugmentation`.
-/
theorem connectedAugmentation_eq_zero_of_mem_pos [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) {i : ℤ} (hi : 0 < i)
    {a : A} (ha : a ∈ 𝒜 i) : connectedAugmentation hneg hzero a = 0 := by
  rw [connectedAugmentation, AlgHom.comp_apply, projZeroAlgHom_eq_zero_of_mem_pos hneg hi ha,
    map_zero]

/-- The kernel of `connectedAugmentation` is the positive-degree submodule `⨆ i > 0, 𝒜 i`. -/
theorem connectedAugmentation_eq_zero_iff [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) {a : A} :
    connectedAugmentation hneg hzero a = 0 ↔ a ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
  unfold connectedAugmentation
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    _root_.map_eq_zero_iff _ (gradeZeroAlgEquiv hzero).symm.injective,
    projZeroAlgHom_eq_zero_iff]

end TauCeti.GradedAlgebra
