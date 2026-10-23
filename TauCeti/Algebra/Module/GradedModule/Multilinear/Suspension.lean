/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.LinearAlgebra.Graded.Shift
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# Suspension of dependent homogeneous multilinear operations

Suspension regrades every input and the output by one. An arity-`n` operation of degree
`q + 1 - n` therefore becomes an operation of degree `q`. The commuting suspension square
also requires the tensor-map Koszul sign: input `i` contributes its original degree once
for every input to its right.

`InternalGrading.suspensionEquiv` implements this square for possibly different input modules.
Its inverse uses the same twists, computed from the original gradings, not the suspended ones.
It applies to operations on composable morphisms as well as to algebra and module operations.
The output needs only a family of submodules, not an internal direct-sum grading.

The degree calculation uses `MultilinearMap.isHomogeneous_shift_const_iff`; the sign uses the
existing Koszul twists, hence Mathlib's integer sign character. This generalizes the
Koszul-twist construction of `AInfinity.suspensionTaylor` in
`TauCeti.Algebra.Homology.AInfinity.Coderivation` to dependent input modules.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.6 and 7.1.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped BigOperators

namespace TauCeti.InternalGrading

universe uR uM uN

section KoszulTwists

variable {R : Type uR} [CommRing R] {ι : Type*} [Fintype ι]
  {M : ι → Type uM} {N : Type uN}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid N] [Module R N]
  (G : ∀ i, InternalGrading R (M i)) (ℬ : ℤ → Submodule R N)

/-- Precomposing the inputs by arbitrary Koszul twists preserves and reflects homogeneity.
The input modules and twist parameters may vary from slot to slot. -/
@[simp]
theorem isHomogeneous_comp_koszulTwist_iff (t : ι → ℤ) (q : ℤ)
    (f : MultilinearMap R M N) :
    TauCeti.MultilinearMap.IsHomogeneous
        (f.compLinearMap fun i ↦ (G i).koszulTwist (t i)) (fun i ↦ (G i).piece) ℬ q ↔
      TauCeti.MultilinearMap.IsHomogeneous f (fun i ↦ (G i).piece) ℬ q := by
  constructor
  · intro hf
    rw [TauCeti.MultilinearMap.isHomogeneous_def]
    intro d x hx
    have h := hf.map_mem d (fun i ↦ (G i).koszulTwist (t i) (x i))
      (fun i ↦ (G i).koszulTwist_mem_piece (hx i) (t i))
    simpa only [MultilinearMap.compLinearMap_apply, koszulTwist_koszulTwist] using h
  · intro hf
    rw [TauCeti.MultilinearMap.isHomogeneous_def]
    intro d x hx
    exact hf.map_mem d _ (fun i ↦ (G i).koszulTwist_mem_piece (hx i) (t i))

end KoszulTwists

variable {R : Type uR} [CommRing R] {n : ℕ} {M : Fin n → Type uM} {N : Type uN}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid N] [Module R N]
  (G : ∀ i, InternalGrading R (M i)) (ℬ : ℤ → Submodule R N)

/-- Suspension identifies arity-`n` operations of degree `q + 1 - n` with operations of
degree `q` on the suspended pieces. Both directions twist input `i` by `n - 1 - i`
using its original grading. -/
noncomputable def suspensionEquiv (q : ℤ) :
    (TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ (G i).piece) ℬ (q + 1 - n)) ≃ₗ[R]
    (TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ ((G i).shift 1).piece) (Graded.shift ℬ 1) q) where
  toFun f := ⟨f.val.compLinearMap (fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i)), by
    apply TauCeti.MultilinearMap.mem_homogeneousSubmodule.mpr
    have h := (isHomogeneous_comp_koszulTwist_iff G ℬ
      (fun i ↦ (n : ℤ) - 1 - i) _ f.val).2
      (TauCeti.MultilinearMap.mem_homogeneousSubmodule.mp f.property)
    have hs := (TauCeti.MultilinearMap.isHomogeneous_shift_const_iff
      (f := f.val.compLinearMap fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i))
      (κ := Fin n) (𝒜 := fun i ↦ (G i).piece) (ℬ := ℬ)
      (c := (1 : ℤ)) (q := q)).2 (by simpa using h)
    simpa only [TauCeti.MultilinearMap.isHomogeneous_def, shift_piece,
      Graded.shift_apply] using hs⟩
  invFun f := ⟨f.val.compLinearMap (fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i)), by
    apply TauCeti.MultilinearMap.mem_homogeneousSubmodule.mpr
    have hs : TauCeti.MultilinearMap.IsHomogeneous f.val
        (fun i ↦ Graded.shift (G i).piece 1) (Graded.shift ℬ 1) q := by
      simpa only [TauCeti.MultilinearMap.isHomogeneous_def, shift_piece,
        Graded.shift_apply] using
        (TauCeti.MultilinearMap.mem_homogeneousSubmodule.mp f.property)
    have h := (TauCeti.MultilinearMap.isHomogeneous_shift_const_iff).1 hs
    exact (isHomogeneous_comp_koszulTwist_iff G ℬ _ _ f.val).2 (by simpa using h)⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    simp only [MultilinearMap.compLinearMap_apply, koszulTwist_koszulTwist]
  right_inv f := by
    apply Subtype.ext
    ext x
    simp only [MultilinearMap.compLinearMap_apply, koszulTwist_koszulTwist]
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    rfl

/-- The underlying suspended operation is precomposition by the suspension Koszul twists. -/
theorem suspensionEquiv_val (q : ℤ)
    (f : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ (G i).piece) ℬ (q + 1 - n)) :
    (suspensionEquiv G ℬ q f).val =
      f.val.compLinearMap (fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i)) := (rfl)

/-- Unsuspension uses the same original-grading twists as suspension. -/
theorem suspensionEquiv_symm_val (q : ℤ)
    (f : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ ((G i).shift 1).piece) (Graded.shift ℬ 1) q) :
    ((suspensionEquiv G ℬ q).symm f).val =
      f.val.compLinearMap (fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i)) := (rfl)

/-- On homogeneous inputs the suspension square contributes exactly the tensor-map Koszul sign,
computed from the original input degrees. -/
theorem suspensionEquiv_apply_of_mem (q : ℤ)
    (f : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ (G i).piece) ℬ (q + 1 - n))
    (d : Fin n → ℤ) (x : ∀ i, M i) (hx : ∀ i, x i ∈ (G i).piece (d i)) :
    (suspensionEquiv G ℬ q f).val x =
      negOnePowCast R (∑ i : Fin n, ((n : ℤ) - 1 - i) * d i) • f.val x := by
  rw [suspensionEquiv_val, MultilinearMap.compLinearMap_apply]
  have ht : (fun i : Fin n ↦ (G i).koszulTwist ((n : ℤ) - 1 - i) (x i)) =
      fun i ↦ negOnePowCast R (((n : ℤ) - 1 - i) * d i) • x i := by
    funext i
    rw [(G i).koszulTwist_apply_of_mem (hx i), negOnePowCast_eq_intCast]
  rw [ht, MultilinearMap.map_smul_univ, ← negOnePowCast_sum]

/-- On homogeneous inputs, unsuspension has the identical sign when degrees are measured in
the original gradings. -/
theorem suspensionEquiv_symm_apply_of_mem (q : ℤ)
    (f : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ ((G i).shift 1).piece) (Graded.shift ℬ 1) q)
    (d : Fin n → ℤ) (x : ∀ i, M i) (hx : ∀ i, x i ∈ (G i).piece (d i)) :
    ((suspensionEquiv G ℬ q).symm f).val x =
      negOnePowCast R (∑ i : Fin n, ((n : ℤ) - 1 - i) * d i) • f.val x := by
  have h := suspensionEquiv_apply_of_mem G ℬ q ((suspensionEquiv G ℬ q).symm f) d x hx
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, negOnePowCast_smul_negOnePowCast_smul]

end TauCeti.InternalGrading
