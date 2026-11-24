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
`TauCeti.Algebra.Homology.AInfinity.Coderivation` to dependent input modules. We also record
`InternalGrading.compLinearMap_koszulTwist_compLinearMap` for commuting arbitrary Koszul twists
past precomposition by homogeneous linear maps.

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
  (G : ∀ i, InternalGrading R (M i) ℤ) (ℬ : ℤ → Submodule R N)

/-- Precomposing the inputs by arbitrary Koszul twists preserves and reflects homogeneity.
The input modules and twist parameters may vary from slot to slot. -/
@[simp]
theorem isHomogeneous_comp_koszulTwist_iff (t : ι → ℤ) (q : ℤ)
    (f : MultilinearMap (RingHom.id R) M N) :
    MultilinearMap.IsHomogeneous
        (f.compLinearMap fun i ↦ (G i).koszulTwist (t i)) (fun i ↦ (G i).piece) ℬ q ↔
      MultilinearMap.IsHomogeneous f (fun i ↦ (G i).piece) ℬ q := by
  constructor
  · intro hf
    rw [MultilinearMap.isHomogeneous_def]
    intro d x hx
    have h := hf.map_mem d (fun i ↦ (G i).koszulTwist (t i) (x i))
      (fun i ↦ (G i).koszulTwist_mem_piece (hx i) (t i))
    simpa only [MultilinearMap.compLinearMap_apply, koszulTwist_koszulTwist] using h
  · intro hf
    rw [MultilinearMap.isHomogeneous_def]
    intro d x hx
    exact hf.map_mem d _ (fun i ↦ (G i).koszulTwist_mem_piece (hx i) (t i))

end KoszulTwists

/-- Precomposing by Koszul twists `t i` and then by homogeneous linear maps `g i` of degrees `r i`
pulls out the Koszul sign `(-1)^(∑ i, t i * r i)`. -/
theorem compLinearMap_koszulTwist_compLinearMap {R : Type uR} [CommRing R] {ι : Type*} [Fintype ι]
    {M : ι → Type uM} {M' : ι → Type*} {N : Type uN} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)] [AddCommMonoid N]
    [Module R N] {G : ∀ i, InternalGrading R (M i) ℤ} {G' : ∀ i, InternalGrading R (M' i) ℤ}
    {g : ∀ i, M i →ₗ[R] M' i} {r : ι → ℤ}
    (hg : ∀ i, LinearMap.IsHomogeneous (g i) (G i).piece (G' i).piece (r i)) (t : ι → ℤ)
    (f : MultilinearMap (RingHom.id R) M' N) :
    (f.compLinearMap fun i ↦ (G' i).koszulTwist (t i)).compLinearMap g =
      negOnePowCast R (∑ i, t i * r i) •
        ((f.compLinearMap g).compLinearMap fun i ↦ (G i).koszulTwist (t i)) := by
  ext x
  simp only [MultilinearMap.compLinearMap_apply, smul_apply]
  have ht : (fun i ↦ (G' i).koszulTwist (t i) (g i (x i))) =
      fun i ↦ negOnePowCast R (t i * r i) • g i ((G i).koszulTwist (t i) (x i)) :=
    funext fun i ↦ by rw [(hg i).koszulTwist_apply (t i) (x i), negOnePowCast_eq_intCast]
  rw [ht, MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply, ← negOnePowCast_sum]

variable {R : Type uR} [CommRing R] {n : ℕ} {M : Fin n → Type uM} {N : Type uN}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid N] [Module R N]
  (G : ∀ i, InternalGrading R (M i) ℤ) (ℬ : ℤ → Submodule R N)

/-- Suspension identifies arity-`n` operations of degree `q + 1 - n` with operations of
degree `q` on the suspended pieces. Both directions twist input `i` by `n - 1 - i`
using its original grading. -/
noncomputable def suspensionEquiv (q : ℤ) :
    (MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ (G i).piece) ℬ (q + 1 - n)) ≃ₗ[R]
    (MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ ((G i).shift 1).piece) (Graded.shift ℬ 1) q) where
  toFun f := ⟨f.val.compLinearMap (fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i)), by
    apply MultilinearMap.mem_homogeneousSubmodule.mpr
    have h := (isHomogeneous_comp_koszulTwist_iff G ℬ
      (fun i ↦ (n : ℤ) - 1 - i) _ f.val).2
      (MultilinearMap.mem_homogeneousSubmodule.mp f.property)
    have hs := (MultilinearMap.isHomogeneous_shift_const_iff
      (f := f.val.compLinearMap fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i))
      (κ := Fin n) (𝒜 := fun i ↦ (G i).piece) (ℬ := ℬ)
      (c := (1 : ℤ)) (q := q)).2 (by simpa using h)
    simpa only [MultilinearMap.isHomogeneous_def, shift_piece,
      Graded.shift_apply] using hs⟩
  invFun f := ⟨f.val.compLinearMap (fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i)), by
    apply MultilinearMap.mem_homogeneousSubmodule.mpr
    have hs : MultilinearMap.IsHomogeneous f.val
        (fun i ↦ Graded.shift (G i).piece 1) (Graded.shift ℬ 1) q := by
      simpa only [MultilinearMap.isHomogeneous_def, shift_piece,
        Graded.shift_apply] using
        (MultilinearMap.mem_homogeneousSubmodule.mp f.property)
    have h := (MultilinearMap.isHomogeneous_shift_const_iff).1 hs
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
    (f : MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ (G i).piece) ℬ (q + 1 - n)) :
    (suspensionEquiv G ℬ q f).val =
      f.val.compLinearMap (fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i)) := (rfl)

/-- Unsuspension uses the same original-grading twists as suspension. -/
theorem suspensionEquiv_symm_val (q : ℤ)
    (f : MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ ((G i).shift 1).piece) (Graded.shift ℬ 1) q) :
    ((suspensionEquiv G ℬ q).symm f).val =
      f.val.compLinearMap (fun i ↦ (G i).koszulTwist ((n : ℤ) - 1 - i)) := (rfl)

/-- On homogeneous inputs the suspension square contributes exactly the tensor-map Koszul sign,
computed from the original input degrees. -/
theorem suspensionEquiv_apply_of_mem (q : ℤ)
    (f : MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ (G i).piece) ℬ (q + 1 - n))
    (d : Fin n → ℤ) (x : ∀ i, M i) (hx : ∀ i, x i ∈ (G i).piece (d i)) :
    (suspensionEquiv G ℬ q f).val x =
      negOnePowCast R (∑ i : Fin n, ((n : ℤ) - 1 - i) * d i) • f.val x := by
  rw [suspensionEquiv_val, MultilinearMap.compLinearMap_apply]
  have ht : (fun i : Fin n ↦ (G i).koszulTwist ((n : ℤ) - 1 - i) (x i)) =
      fun i ↦ negOnePowCast R (((n : ℤ) - 1 - i) * d i) • x i := by
    funext i
    rw [(G i).koszulTwist_apply_of_mem (hx i), negOnePowCast_eq_intCast]
  rw [ht, MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]
  rw [← negOnePowCast_sum]

/-- On homogeneous inputs, unsuspension has the identical sign when degrees are measured in
the original gradings. -/
theorem suspensionEquiv_symm_apply_of_mem (q : ℤ)
    (f : MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ ((G i).shift 1).piece) (Graded.shift ℬ 1) q)
    (d : Fin n → ℤ) (x : ∀ i, M i) (hx : ∀ i, x i ∈ (G i).piece (d i)) :
    ((suspensionEquiv G ℬ q).symm f).val x =
      negOnePowCast R (∑ i : Fin n, ((n : ℤ) - 1 - i) * d i) • f.val x := by
  have h := suspensionEquiv_apply_of_mem G ℬ q ((suspensionEquiv G ℬ q).symm f) d x hx
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, negOnePowCast_smul_negOnePowCast_smul]

end TauCeti.InternalGrading
