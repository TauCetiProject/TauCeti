/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fintype
import TauCeti.LinearAlgebra.Basis.Exact
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Diagonalization of possibly singular matrices over a PID

Every square matrix over a principal ideal domain admits unimodular row and column
transformations to a diagonal matrix, including matrices with nontrivial kernel.
No divisibility ordering or normalization of the diagonal entries is asserted.

The construction uses Mathlib's `Submodule.smithNormalForm` on the image. Since the
image is free, its basis lifts along the matrix map; adjoining a basis of the kernel
gives a basis of the source. A finite permutation aligns the lifted basis with the
image's diagonal positions. Thus zero diagonal positions are retained, as required
when computing fixed modules of integral automorphisms after scalar extension.

The basis-level Smith form is due to Mathlib's finite-free PID development. The
kernel/image basis assembly uses `Module.Basis.ofExactLift`. The matrix
conversion uses `Module.Basis.toMatrix_eq_diagonal_iff`, change-of-basis identities and
`Equiv.Perm.exists_extending_pair` to align the nonzero diagonal positions.
-/

public section

namespace Matrix

/-- Every square matrix over a principal ideal domain is equivalent to a diagonal
matrix by transformations of unit determinant. The matrix may be singular, and
zero diagonal entries are allowed; no divisibility chain is asserted. -/
theorem exists_mul_mul_eq_diagonal {R ι : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) :
    ∃ (L Q : Matrix ι ι R) (d : ι → R),
      IsUnit L.det ∧ IsUnit Q.det ∧ L * A * Q = diagonal d := by
  classical
  let f := A.mulVecLin
  let e₀ := Pi.basisFun R ι
  obtain ⟨n, snf⟩ := (LinearMap.range f).smithNormalForm e₀
  -- Split the map onto its free image, keeping the kernel as a separate summand.
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let K := LinearMap.ker f.rangeRestrict
  -- Align the lifted image basis with the target Smith positions; the remaining
  -- source basis vectors lie in the kernel and therefore have diagonal entry zero.
  let bK := Module.Free.chooseBasis R K
  let b := Module.Basis.ofExactLift K.injective_subtype
    (LinearMap.exact_subtype_ker_map f.rangeRestrict) bK snf.bN
    (fun j ↦ s (snf.bN j)) (fun j ↦ LinearMap.congr_fun hs (snf.bN j))
  let e := b.indexEquiv e₀
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun j : Fin n ↦ e (Sum.inr j)) snf.f (e.injective.comp Sum.inr_injective)
    snf.f.injective
  let r := b.reindex e
  let c := snf.bM.reindex σ.symm
  let d : ι → R := fun i ↦ Sum.elim (fun _ ↦ 0) snf.a (e.symm i)
  have hr (j) : r (e j) = b j := by simp [r]
  have hc (j) : c (e (Sum.inr j)) = snf.bM (snf.f j) := by simp [c, hσ]
  have hdK (j) : d (e (Sum.inl j)) = 0 := by simp [d]
  have hdN (j) : d (e (Sum.inr j)) = snf.a j := by simp [d]
  have hscale (i : ι) : f (r i) = d i • c i := by
    obtain ⟨j, rfl⟩ := e.surjective i
    rw [hr]
    cases j with
    | inl j =>
      simp only [b, Module.Basis.ofExactLift_inl, hdK, zero_smul]
      exact congrArg Subtype.val (bK j).property
    | inr j =>
      simp only [b, Module.Basis.ofExactLift_inr, hdN, hc]
      exact (congrArg Subtype.val (LinearMap.congr_fun hs (snf.bN j))).trans (snf.snf j)
  -- Convert the diagonal basis equations to unimodular matrix transformations.
  have hdiag := (Module.Basis.toMatrix_eq_diagonal_iff r c f d).2 hscale
  refine ⟨c.toMatrix e₀, e₀.toMatrix r, d, ?_, ?_, ?_⟩
  · exact isUnit_det_of_right_inverse (c.toMatrix_mul_toMatrix_flip e₀)
  · exact isUnit_det_of_right_inverse (e₀.toMatrix_mul_toMatrix_flip r)
  · have hA : LinearMap.toMatrix e₀ e₀ f = A := by
      simp only [f, e₀, LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply',
        LinearMap.toMatrix'_toLin']
    rw [← hdiag, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix r e₀ c e₀, hA]

end Matrix
