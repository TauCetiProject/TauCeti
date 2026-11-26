/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Algebra.Bilinear
public import TauCeti.LinearAlgebra.FiniteDimensional.ScalarTower

/-!
# The characteristic polynomial on an invariant submodule and its quotient

An endomorphism `f` of a module `V` that preserves a submodule `W` restricts to an endomorphism
`f.restrict _` of `W` and induces an endomorphism `Submodule.mapQ W W f _` of `V ⧸ W`. When `W` and
`V ⧸ W` are free of finite rank, the characteristic polynomial of `f` is the product of those of
the two induced endomorphisms. In a basis of `V` made of a basis of `W` and a lift of a basis of
`V ⧸ W` (`Module.Basis.sumQuot`), the matrix of `f` is block upper triangular with these two
endomorphisms on the diagonal. This is the characteristic-polynomial analogue of Mathlib's
`LinearMap.det_eq_det_mul_det`, and its proof is the same.

No complement of `W` is chosen, so `W` need not be a direct summand stable under `f`: over a field
this computes the characteristic polynomial of `f` on `W` from those of `f` on `V` and on `V ⧸ W`
in every characteristic.

## Main results

* `LinearMap.charpoly_dvd_of_injective_of_comp_eq_comp`: the characteristic polynomial of an
  endomorphism divides that of any endomorphism containing it through an injective intertwiner.

* `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`: the characteristic polynomial of
  `f` is the product of those of its restriction to `W` and of the endomorphism it induces on
  `V ⧸ W`.

* `Submodule.charpoly_lsmul_eq_mul_quotient`: for an algebra `A` over a field `k` and an
  `A`-submodule `P` of a finite-dimensional `A`-module `M`, the characteristic polynomial of
  `a : A` on `M` is the product of those on `P` and on `M ⧸ P`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Chapter I, §5,
  p.21, for the characteristic-polynomial product on an invariant subspace and its quotient.
-/

public section

open Module Module.Basis

namespace LinearMap

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V] (W : Submodule R V) [Module.Free R W] [Module.Finite R W]
  [Module.Free R (V ⧸ W)] [Module.Finite R (V ⧸ W)]

/-- **The characteristic polynomial is multiplicative on an invariant submodule and its
quotient.** If `f` preserves `W`, then the characteristic polynomial of `f` is the product of the
characteristic polynomials of the restriction of `f` to `W` and of the endomorphism of `V ⧸ W`
induced by `f`. -/
theorem charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (f : V →ₗ[R] V) (hf : W ≤ W.comap f) :
    f.charpoly = (f.restrict hf).charpoly * (W.mapQ W f hf).charpoly := by
  classical
  let bW := Module.Free.chooseBasis R W
  let bQ := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let B := Matrix.of fun i l ↦ (b.repr (f (b (Sum.inr l)))) (Sum.inl i)
  suffices toMatrix b b f =
      Matrix.fromBlocks (toMatrix bW bW (f.restrict hf)) B 0 (toMatrix bQ bQ (W.mapQ W f hf)) by
    rw [← charpoly_toMatrix f b, this, Matrix.charpoly_fromBlocks_zero₂₁, charpoly_toMatrix,
      charpoly_toMatrix]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (f (bW k)) = 0 by simp [toMatrix_apply, b, this]
      rw [← mem_ker, Submodule.ker_mkQ]
      exact hf (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [toMatrix_apply, sumQuot_repr_inr, Matrix.fromBlocks_apply₂₂, b]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply, Submodule.mkQ_apply]

end LinearMap

namespace LinearMap

variable {K V U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]

/-- If an injective linear map `j` satisfies `j.comp f = g.comp j`, the characteristic polynomial
of `f` divides that of `g`. -/
theorem charpoly_dvd_of_injective_of_comp_eq_comp (f : V →ₗ[K] V) (g : U →ₗ[K] U)
    (j : V →ₗ[K] U) (hj : Function.Injective j) (h : j.comp f = g.comp j) :
    f.charpoly ∣ g.charpoly := by
  let W := j.range
  have hW : W ≤ W.comap g := by
    rintro y ⟨x, rfl⟩
    exact ⟨f x, DFunLike.congr_fun h x⟩
  let e : V ≃ₗ[K] W := LinearEquiv.ofInjective j hj
  have he : e.conj f = g.restrict hW := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    dsimp only [e]
    simp only [LinearEquiv.conj_apply_apply, LinearMap.restrict_apply]
    exact (DFunLike.congr_fun h (e.symm x)).trans
      (congrArg g (LinearEquiv.ofInjective_symm_apply j x))
  refine ⟨(W.mapQ W g hW).charpoly, ?_⟩
  rw [charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W g hW, ← he, e.charpoly_conj]

end LinearMap

namespace Submodule

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module A M]
  [Module k M] [IsScalarTower k A M] [FiniteDimensional k M]

/-- The characteristic polynomial of `a` on `M` is the product of those on an `A`-submodule `P`
and on `M ⧸ P`. -/
theorem charpoly_lsmul_eq_mul_quotient (P : Submodule A M) (a : A) :
    (Algebra.lsmul k k M a).charpoly =
      (Algebra.lsmul k k P a).charpoly * (Algebra.lsmul k k (M ⧸ P) a).charpoly := by
  let W := P.restrictScalars k
  have hW : W ≤ W.comap (Algebra.lsmul k k M a) := fun x hx ↦ by
    simpa [W] using P.smul_mem a hx
  let eW := (P.restrictScalarsEquiv k A M).restrictScalars k
  let eQ := Submodule.Quotient.restrictScalarsEquiv k P
  -- `Submodule.restrictScalarsEquiv` is the identity on elements, and Mathlib's
  -- `Submodule.restrictScalarsEquiv_apply` is stated through this same definitional equality,
  -- so `simp` cannot use it here: both sides send `x` to `a • x`.
  have hP : eW.conj ((Algebra.lsmul k k M a).restrict hW) = Algebra.lsmul k k P a :=
    LinearMap.ext fun _ ↦ rfl
  have hQ : eQ.conj (W.mapQ W _ hW) = Algebra.lsmul k k (M ⧸ P) a := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    simp [eQ, LinearEquiv.conj_apply, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
      Submodule.Quotient.restrictScalarsEquiv_mk, Submodule.mapQ_apply]
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W _ hW, ← hP, ← hQ,
    LinearEquiv.charpoly_conj, LinearEquiv.charpoly_conj]

end Submodule
