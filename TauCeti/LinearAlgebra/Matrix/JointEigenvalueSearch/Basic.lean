/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.EigenvalueSearch
public import TauCeti.LinearAlgebra.Matrix.Echelon.KernelBasis

/-!
# Computable common eigenspaces

Stacking the eigenvector equations for a finite family of matrices gives a rectangular
system. Its kernel basis, computed by Gauss–Jordan elimination, spans the common eigenspace.
The basis is nonempty precisely when a nonzero common eigenvector exists, and its length
is the dimension of that eigenspace. Transposing the family gives the corresponding
left-eigenvector statements.

These bases provide the intersection test for successive common-eigenspace refinement.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446–450.
* G. J. A. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601–606.
-/

public section

namespace TauCeti

open Matrix

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {m n : ℕ}

/-- The rectangular matrix formed by stacking the systems
`(Matrix.diagonal (fun _ => a i) - A i) v = 0`, one block of `n` rows for each `i : Fin m`.

The product row index is flattened to `Fin (m * n)` because `TauCeti.kernelBasis` operates on
matrices with `Fin` row and column types. -/
@[expose] def jointEigenspaceMatrix {R : Type u} [NonUnitalNonAssocRing R]
    (A : Fin m → Matrix (Fin n) (Fin n) R)
    (a : Fin m → R) : Matrix (Fin (m * n)) (Fin n) R := fun k j =>
  let ij := finProdFinEquiv.symm k
  (Matrix.diagonal (n := Fin n) (fun _ => a ij.1) - A ij.1) ij.2 j

/-- An entry in the `i`-th block of `TauCeti.jointEigenspaceMatrix`. -/
@[simp]
theorem jointEigenspaceMatrix_apply {R : Type u} [NonUnitalNonAssocRing R]
    (A : Fin m → Matrix (Fin n) (Fin n) R)
    (a : Fin m → R) (i : Fin m) (j k : Fin n) :
    jointEigenspaceMatrix A a (finProdFinEquiv (i, j)) k =
      (Matrix.diagonal (n := Fin n) (fun _ => a i) - A i) j k := by
  simp [jointEigenspaceMatrix]

/-- The stacked matrix annihilates `v` exactly when `v` is an eigenvector (possibly zero) of
every `A i`, with eigenvalue `a i`. -/
theorem jointEigenspaceMatrix_mulVec_eq_zero_iff {R : Type u} [NonUnitalNonAssocRing R]
    (A : Fin m → Matrix (Fin n) (Fin n) R) (a : Fin m → R) (v : Fin n → R) :
    jointEigenspaceMatrix A a *ᵥ v = 0 ↔ ∀ i, A i *ᵥ v = a i • v := by
  constructor
  · intro h i
    have hi : (Matrix.diagonal (n := Fin n) (fun _ => a i) - A i) *ᵥ v = 0 := by
      funext j
      simpa only [Matrix.mulVec, jointEigenspaceMatrix_apply, Pi.zero_apply] using
        congrFun h (finProdFinEquiv (i, j))
    rw [scalar_sub_mulVec_eq_zero_iff] at hi
    exact hi
  · intro h
    funext k
    rcases hidx : finProdFinEquiv.symm k with ⟨i, j⟩
    have hi : (Matrix.diagonal (n := Fin n) (fun _ => a i) - A i) *ᵥ v = 0 := by
      rw [scalar_sub_mulVec_eq_zero_iff]
      exact h i
    rw [← finProdFinEquiv.apply_symm_apply k]
    rw [hidx]
    simpa only [Matrix.mulVec, jointEigenspaceMatrix_apply, Pi.zero_apply] using
      congrFun hi j

/-- A computable basis of the simultaneous eigenspace for the eigenvalue tuple `a`.

This is the kernel basis of the stacked system, so the `TauCeti.kernelBasis` API applies to it
verbatim: `TauCeti.linearIndepOn_kernelBasis (jointEigenspaceMatrix A a)` and
`TauCeti.nodup_kernelBasis (jointEigenspaceMatrix A a)` are its linear independence and `Nodup`,
with no unfolding needed. -/
@[expose] def jointEigenspaceBasis (A : Fin m → Matrix (Fin n) (Fin n) F)
    (a : Fin m → F) : List (Fin n → F) :=
  kernelBasis (jointEigenspaceMatrix A a)

omit [Fintype F] in
/-- Every vector returned by `TauCeti.jointEigenspaceBasis` satisfies all the eigenvector
equations. -/
theorem mulVec_eq_smul_of_mem_jointEigenspaceBasis
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} {v : Fin n → F}
    (hv : v ∈ jointEigenspaceBasis A a) : ∀ i, A i *ᵥ v = a i • v := by
  rw [← jointEigenspaceMatrix_mulVec_eq_zero_iff A a v]
  exact mulVec_eq_zero_of_mem_kernelBasis _ hv

omit [Fintype F] in
/-- The computed basis spans the common eigenspace: a vector lies in its span exactly when it
satisfies every eigenvector equation. -/
theorem mem_span_jointEigenspaceBasis
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) (v : Fin n → F) :
    v ∈ Submodule.span F {w : Fin n → F | w ∈ jointEigenspaceBasis A a} ↔
      ∀ i, A i *ᵥ v = a i • v := by
  rw [jointEigenspaceBasis, span_kernelBasis, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    jointEigenspaceMatrix_mulVec_eq_zero_iff]

omit [Fintype F] in
/-- The number of computed basis vectors is the nullity of the stacked system. Comparing this
length with `1` is the executable test that Dixon--Schneider refinement has reached a
one-dimensional common eigenspace. -/
theorem length_jointEigenspaceBasis
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    (jointEigenspaceBasis A a).length = n - (jointEigenspaceMatrix A a).rank :=
  length_kernelBasis _

omit [Fintype F] in
/-- The common-eigenspace basis is nonempty exactly when the eigenvalue tuple has a nonzero
common eigenvector. -/
theorem jointEigenspaceBasis_ne_nil_iff
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    jointEigenspaceBasis A a ≠ [] ↔ ∃ v ≠ 0, ∀ i, A i *ᵥ v = a i • v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨v, (linearIndepOn_kernelBasis (jointEigenspaceMatrix A a)).ne_zero hv,
      mulVec_eq_smul_of_mem_jointEigenspaceBasis hv⟩
  · rintro ⟨v, hv, heig⟩ hnil
    have hmem := (mem_span_jointEigenspaceBasis A a v).mpr heig
    rw [hnil] at hmem
    simp only [List.not_mem_nil, Set.ofPred_false, Submodule.span_empty,
      Submodule.mem_bot] at hmem
    exact hv hmem

/-! ## Left-eigenvector characterizations -/

omit [Fintype F] in
/-- Every vector returned for the transposed family is a left eigenvector of every original
matrix. -/
theorem vecMul_eq_smul_of_mem_jointEigenspaceBasis_transpose
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} {v : Fin n → F}
    (hv : v ∈ jointEigenspaceBasis (fun i => (A i)ᵀ) a) : ∀ i, v ᵥ* A i = a i • v := by
  intro i
  simpa [Matrix.mulVec_transpose] using
    mulVec_eq_smul_of_mem_jointEigenspaceBasis (A := fun i => (A i)ᵀ) (a := a) hv i

omit [Fintype F] in
/-- The common-eigenspace basis for the transposed family is nonempty exactly when the tuple
admits a nonzero common eigenrow. -/
theorem jointEigenspaceBasis_transpose_ne_nil_iff
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    jointEigenspaceBasis (fun i => (A i)ᵀ) a ≠ [] ↔
      ∃ v ≠ 0, ∀ i, v ᵥ* A i = a i • v := by
  simpa [Matrix.mulVec_transpose] using
    jointEigenspaceBasis_ne_nil_iff (fun i => (A i)ᵀ) a

end TauCeti
