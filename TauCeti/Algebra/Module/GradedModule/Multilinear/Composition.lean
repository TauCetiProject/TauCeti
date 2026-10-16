/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Multilinear.Basic
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# Signed substitution of dependent graded multilinear maps

Substituting homogeneous operations `gᵢ` into an operation `f` uses the tensor-map Koszul rule.
The operation `gᵢ` crosses all inputs belonging to earlier blocks. Here the outer slots are
ordered by `Fin n`, while the input modules and the finite slot type of each inner operation
may vary with the block. In particular, these modules can be Hom modules along composable
strings in a graded linear quiver.

`InternalGrading.signedCompMultilinearMap` constructs this substitution on the total modules,
not only on a specified tuple of degrees. It precomposes each input by the existing Koszul
twist for the sum of the degrees of the operations to its right. The stored homogeneity of
`f` and each `gᵢ` ensures that the degree parameters actually describe those operations.
The result has degree `deg f + ∑ᵢ deg gᵢ`. Its homogeneous evaluation formula gives the exact
Koszul sign, including the one-slot case, where a degree-`q` operation crosses the prefix.

The flattened input index is a dependent sum. Mathlib's `domDomCongrLinearEquiv'` and
`LinearEquiv.multilinearMapCongrLeft` provide reindexing and coordinate changes without an
interface based on equality casts. Empty input blocks are allowed.

The construction uses Mathlib's dependent `MultilinearMap.compMultilinearMap` and the
homogeneous multilinear-map API of `TauCeti.LinearAlgebra.Graded.Multilinear`.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
-/

public section

open scoped BigOperators

namespace TauCeti.InternalGrading

universe uR uβ uM uP uN

variable {R : Type uR} [CommRing R] {n : ℕ} {β : Fin n → Type uβ}
  [∀ i, Fintype (β i)] {M : (i : Fin n) → β i → Type uM}
  {P : Fin n → Type uP} {N : Type uN}
  [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [AddCommMonoid N] [Module R N]
  (G : ∀ i j, InternalGrading R (M i j))
  (H : ∀ i, ℤ → Submodule R (P i)) (ℬ : ℤ → Submodule R N)
  {p : ℤ} {q : Fin n → ℤ}
  (f : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R) H ℬ p)
  (g : ∀ i, TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
    (fun j ↦ (G i j).piece) (H i) (q i))

/-- Simultaneous Koszul-signed substitution of homogeneous multilinear maps with dependent
input modules. Each input in block `i` is twisted by the sum of the degrees of operations in
later blocks. The output degree is the sum of all inner degrees plus the outer degree. -/
noncomputable def signedCompMultilinearMap :
    TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun ij : Σ i, β i ↦ (G ij.1 ij.2).piece) ℬ ((∑ i, q i) + p) :=
  ⟨(f.val.compMultilinearMap (fun i ↦ (g i).val)).compLinearMap
    (fun ij ↦ (G ij.1 ij.2).koszulTwist (∑ k, if ij.1 < k then q k else 0)), by
    apply TauCeti.MultilinearMap.mem_homogeneousSubmodule.mpr
    rw [TauCeti.MultilinearMap.isHomogeneous_def]
    intro d x hx
    exact ((TauCeti.MultilinearMap.mem_homogeneousSubmodule.mp f.property).compMultilinearMap
      (fun i ↦ TauCeti.MultilinearMap.mem_homogeneousSubmodule.mp (g i).property)).map_mem
        d _ (fun ij ↦ (G ij.1 ij.2).koszulTwist_mem_piece (hx ij) _)⟩

/-- The underlying map is ordinary dependent substitution precomposed with Koszul twists. -/
theorem signedCompMultilinearMap_val :
    (signedCompMultilinearMap G H ℬ f g).val =
      (f.val.compMultilinearMap (fun i ↦ (g i).val)).compLinearMap
        (fun ij ↦ (G ij.1 ij.2).koszulTwist (∑ k, if ij.1 < k then q k else 0)) := (rfl)

/-- On homogeneous inputs, each later operation crosses every earlier input. This formula
uses actual input degrees, not degrees supplied independently of the inputs. -/
theorem signedCompMultilinearMap_apply
    (d : (Σ i, β i) → ℤ) (x : ∀ ij : Σ i, β i, M ij.1 ij.2)
    (hx : ∀ ij, x ij ∈ (G ij.1 ij.2).piece (d ij)) :
    (signedCompMultilinearMap G H ℬ f g).val x =
      negOnePowCast R (∑ ij : Σ i, β i,
        (∑ k, if ij.1 < k then q k else 0) * d ij) •
          f.val (fun i ↦ (g i).val (fun j ↦ x ⟨i, j⟩)) := by
  rw [signedCompMultilinearMap_val, MultilinearMap.compLinearMap_apply]
  have ht : (fun ij : Σ i, β i ↦
      (G ij.1 ij.2).koszulTwist (∑ k, if ij.1 < k then q k else 0) (x ij)) =
      fun ij ↦ negOnePowCast R ((∑ k, if ij.1 < k then q k else 0) * d ij) • x ij := by
    funext ij
    rw [(G ij.1 ij.2).koszulTwist_apply_of_mem (hx ij), negOnePowCast_eq_intCast]
  rw [ht, MultilinearMap.map_smul_univ, ← negOnePowCast_sum]
  rfl

/-- The Koszul exponent can equivalently be summed over operations and their preceding blocks. -/
theorem signedCompMultilinearMap_apply_eq_prefix_sign
    (d : (Σ i, β i) → ℤ) (x : ∀ ij : Σ i, β i, M ij.1 ij.2)
    (hx : ∀ ij, x ij ∈ (G ij.1 ij.2).piece (d ij)) :
    (signedCompMultilinearMap G H ℬ f g).val x =
      negOnePowCast R (∑ k, q k *
        ∑ ij : Σ i, β i, if ij.1 < k then d ij else 0) •
          f.val (fun i ↦ (g i).val (fun j ↦ x ⟨i, j⟩)) := by
  rw [signedCompMultilinearMap_apply G H ℬ f g d x hx]
  congr 2
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  split_ifs <;> simp

/-- Inserting one operation of degree `r` in slot `k`, with degree-zero operations in every
other slot, gives precisely `(-1)^(r * prefix degree)`. In particular, the other operations may
be unary identity maps. -/
theorem signedCompMultilinearMap_apply_of_single_degree
    (k : Fin n) (r : ℤ) (hq : q = fun i ↦ if i = k then r else 0)
    (d : (Σ i, β i) → ℤ) (x : ∀ ij : Σ i, β i, M ij.1 ij.2)
    (hx : ∀ ij, x ij ∈ (G ij.1 ij.2).piece (d ij)) :
    (signedCompMultilinearMap G H ℬ f g).val x =
      negOnePowCast R (r * ∑ ij : Σ i, β i, if ij.1 < k then d ij else 0) •
        f.val (fun i ↦ (g i).val (fun j ↦ x ⟨i, j⟩)) := by
  classical
  rw [signedCompMultilinearMap_apply_eq_prefix_sign G H ℬ f g d x hx]
  simp [hq, ite_mul]

/-- Substitution by degree-zero operations has no Koszul correction. -/
@[simp]
theorem signedCompMultilinearMap_val_of_degree_zero (hq : q = 0) :
    (signedCompMultilinearMap G H ℬ f g).val =
      f.val.compMultilinearMap (fun i ↦ (g i).val) := by
  rw [signedCompMultilinearMap_val]
  simp [hq]

/-- Signed substitution is additive in the outer operation. -/
@[simp]
theorem signedCompMultilinearMap_add
    (f' : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R) H ℬ p) :
    signedCompMultilinearMap G H ℬ (f + f') g =
      signedCompMultilinearMap G H ℬ f g + signedCompMultilinearMap G H ℬ f' g := by
  apply Subtype.ext
  ext x
  simp [signedCompMultilinearMap_val, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply]

/-- Signed substitution respects scalars in the outer operation. -/
@[simp]
theorem signedCompMultilinearMap_smul (c : R) :
    signedCompMultilinearMap G H ℬ (c • f) g = c • signedCompMultilinearMap G H ℬ f g := by
  apply Subtype.ext
  ext x
  simp [signedCompMultilinearMap_val, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply]

/-- Substituting the zero outer operation gives zero. -/
@[simp]
theorem signedCompMultilinearMap_zero :
    signedCompMultilinearMap G H ℬ (0 : TauCeti.MultilinearMap.homogeneousSubmodule
      (R := R) (S := R) H ℬ p) g = 0 := by
  apply Subtype.ext
  ext x
  simp [signedCompMultilinearMap_val, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply]

/-- Signed substitution is additive in each inner operation separately. -/
theorem signedCompMultilinearMap_update_add (k : Fin n)
    (a b : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun j ↦ (G k j).piece) (H k) (q k)) :
    signedCompMultilinearMap G H ℬ f (Function.update g k (a + b)) =
      signedCompMultilinearMap G H ℬ f (Function.update g k a) +
        signedCompMultilinearMap G H ℬ f (Function.update g k b) := by
  classical
  apply Subtype.ext
  ext x
  simp only [signedCompMultilinearMap_val, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply, Submodule.coe_add, add_apply]
  let x' := fun ij : Σ i, β i ↦
    (G ij.1 ij.2).koszulTwist (∑ l, if ij.1 < l then q l else 0) (x ij)
  have he (h : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun j ↦ (G k j).piece) (H k) (q k)) :=
    funext (Function.apply_update (fun i
      (h : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
        (fun j ↦ (G i j).piece) (H i) (q i)) ↦ h.val (Sigma.curry x' i)) g k h)
  rw [he, he, he]
  exact f.val.map_update_add _ k _ _

/-- Signed substitution respects scalars in each inner operation separately. -/
theorem signedCompMultilinearMap_update_smul (k : Fin n) (c : R)
    (a : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun j ↦ (G k j).piece) (H k) (q k)) :
    signedCompMultilinearMap G H ℬ f (Function.update g k (c • a)) =
      c • signedCompMultilinearMap G H ℬ f (Function.update g k a) := by
  classical
  apply Subtype.ext
  ext x
  simp only [signedCompMultilinearMap_val, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply, Submodule.coe_smul, smul_apply]
  let x' := fun ij : Σ i, β i ↦
    (G ij.1 ij.2).koszulTwist (∑ l, if ij.1 < l then q l else 0) (x ij)
  have he (h : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun j ↦ (G k j).piece) (H k) (q k)) :=
    funext (Function.apply_update (fun i
      (h : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
        (fun j ↦ (G i j).piece) (H i) (q i)) ↦ h.val (Sigma.curry x' i)) g k h)
  rw [he, he]
  exact f.val.map_update_smul _ k c _

/-- If any inner operation is zero, the signed substitution is zero. -/
@[simp]
theorem signedCompMultilinearMap_update_zero (k : Fin n) :
    signedCompMultilinearMap G H ℬ f (Function.update g k 0) = 0 := by
  simpa using signedCompMultilinearMap_update_smul G H ℬ f g k 0 (g k)

end TauCeti.InternalGrading
