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
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fintype

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
matrix conversion uses its change-of-basis identities and
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
  have hs_apply (x : LinearMap.range f) : f (s x) = x :=
    congrArg Subtype.val (LinearMap.congr_fun hs x)
  let ψ : LinearMap.range f × LinearMap.ker f →ₗ[R] (ι → R) :=
    s.coprod (LinearMap.ker f).subtype
  have hψ (x : LinearMap.range f × LinearMap.ker f) : f (ψ x) = x.1 := by
    simp [ψ, hs_apply, LinearMap.mem_ker.mp x.2.property]
  have hbij : Function.Bijective ψ := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hx₁ : x.1 = 0 := by
        apply Subtype.ext
        simpa only [LinearMap.mem_ker.mp hx, map_zero, Submodule.coe_zero] using (hψ x).symm
      have hx₂ : x.2 = 0 := by
        apply Subtype.ext
        simpa [ψ, hx₁] using LinearMap.mem_ker.mp hx
      exact Prod.ext hx₁ hx₂
    · intro x
      let y : LinearMap.range f := f.rangeRestrict x
      refine ⟨(y, ⟨x - s y, ?_⟩), ?_⟩
      · simp [LinearMap.mem_ker, hs_apply, y]
      · simp [ψ]
  -- Align the lifted image basis with the target Smith positions; the remaining
  -- source basis vectors lie in the kernel and therefore have diagonal entry zero.
  let bK := Module.Free.chooseBasis R (LinearMap.ker f)
  let b := (snf.bN.prod bK).map (LinearEquiv.ofBijective ψ hbij)
  let e := b.indexEquiv e₀
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun j : Fin n ↦ e (Sum.inl j)) snf.f (e.injective.comp Sum.inl_injective)
    snf.f.injective
  let r := b.reindex e
  let c := snf.bM.reindex σ.symm
  let d : ι → R := fun i ↦ Sum.elim snf.a (fun _ ↦ 0) (e.symm i)
  have hr (i : ι) : f (r i) = d i • c i := by
    obtain ⟨j, rfl⟩ := e.surjective i
    cases j with
    | inl j =>
      simpa [r, b, ψ, d, c, hσ, hs_apply] using snf.snf j
    | inr j =>
      simp [r, b, ψ, d, LinearMap.mem_ker.mp (bK j).property]
  -- Convert the diagonal basis equations to unimodular matrix transformations.
  have hdiag : LinearMap.toMatrix r c f = diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, hr, map_smul, c.repr_self, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  refine ⟨c.toMatrix e₀, e₀.toMatrix r, d, ?_, ?_, ?_⟩
  · exact isUnit_det_of_right_inverse (c.toMatrix_mul_toMatrix_flip e₀)
  · exact isUnit_det_of_right_inverse (e₀.toMatrix_mul_toMatrix_flip r)
  · have hA : LinearMap.toMatrix e₀ e₀ f = A := by
      simp only [f, e₀, LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply',
        LinearMap.toMatrix'_toLin']
    rw [← hdiag, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix r e₀ c e₀, hA]

end Matrix
