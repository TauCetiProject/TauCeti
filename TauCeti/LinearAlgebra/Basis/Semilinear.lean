/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Transporting coordinates along a ring homomorphism

Let `σ : R →+* S` be a ring homomorphism, `b` a basis of an `R`-module `M` and `b'` a basis of an
`S`-module `M'`, indexed by the same type. Applying `σ` to the coordinates in `b` and reading the
result in `b'` gives the `σ`-semilinear map

`Module.Basis.semilinearMap σ b b' : ∑ₖ aₖ bₖ ↦ ∑ₖ σ(aₖ) b'ₖ`.

This is the comparison map between a based module and its scalar extension along `σ`, presented by
a basis of the extension rather than by a tensor product. It applies `σ` to the matrices of linear
maps and to determinants: a linear map `g` whose matrix in the bases `b'` is the image under `σ` of
the matrix of a linear map `f` in the bases `b` is intertwined with `f`, and the determinant in `b'`
of the image of a family is `σ` of its determinant in `b`. This is how invariants computed from
matrices, such as the torsion of a based chain complex, are compared along a homomorphism of fields.

## Main declarations

* `Module.Basis.semilinearMap`: the `σ`-semilinear map sending each `b k` to `b' k`.
* `Module.Basis.repr_semilinearMap_apply`: its coordinates are the images of the coordinates under
  `σ`.
* `Module.Basis.semilinearMap_comp_apply_of_toMatrix_eq`: it intertwines two linear maps whose
  matrices correspond under `σ`.
* `Module.Basis.det_comp_semilinearMap`: the determinant of the image of a family is the image of
  its determinant.
-/

public section

noncomputable section

namespace Module.Basis

section Semiring

variable {ι R S M M' : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module S M']
  (b : Basis ι R M) (b' : Basis ι S M')

/-- The `σ`-semilinear map `∑ₖ aₖ bₖ ↦ ∑ₖ σ(aₖ) b'ₖ`, which applies the ring homomorphism `σ` to
the coordinates in the basis `b` and reads the result in the basis `b'`. -/
def semilinearMap : M →ₛₗ[σ] M' :=
  b'.repr.symm.toLinearMap ∘ₛₗ Finsupp.mapRange.linearMap σ.toSemilinearMap ∘ₛₗ b.repr.toLinearMap

/-- The coordinates of the image of a vector are the images of its coordinates. -/
@[simp]
theorem repr_semilinearMap_apply (x : M) (k : ι) :
    b'.repr (b.semilinearMap σ b' x) k = σ (b.repr x k) := by
  simp [semilinearMap]

/-- The map `semilinearMap σ b b'` sends the basis vector `b k` to `b' k`. -/
@[simp]
theorem semilinearMap_apply_self (k : ι) : b.semilinearMap σ b' (b k) = b' k :=
  b'.repr.injective <| Finsupp.ext fun l ↦ by
    classical
    rw [repr_semilinearMap_apply, repr_self, repr_self, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp

end Semiring

section CommSemiring

variable {ι κ R S M M' N N' : Type*} [CommSemiring R] [CommSemiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module S M']
  [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module S N']
  [Fintype ι] [DecidableEq ι] [Finite κ]

/-- Let `f : M → N` and `g : M' → N'` be linear maps whose matrices correspond under `σ`: the
matrix of `g` in the bases `b'` and `c'` is the image under `σ` of the matrix of `f` in the bases
`b` and `c`. Then `g` is intertwined with `f` by the maps `semilinearMap σ b b'` and
`semilinearMap σ c c'`. -/
theorem semilinearMap_comp_apply_of_toMatrix_eq {b : Basis ι R M} {b' : Basis ι S M'}
    {c : Basis κ R N} {c' : Basis κ S N'} {f : M →ₗ[R] N} {g : M' →ₗ[S] N'}
    (h : LinearMap.toMatrix b' c' g = (LinearMap.toMatrix b c f).map σ) (x : M) :
    g (b.semilinearMap σ b' x) = c.semilinearMap σ c' (f x) := by
  have hcomp : g ∘ₛₗ b.semilinearMap σ b' = c.semilinearMap σ c' ∘ₛₗ f :=
    b.ext fun k ↦ c'.repr.injective <| Finsupp.ext fun l ↦ by
      have hkl := congrFun (congrFun h l) k
      simp only [LinearMap.toMatrix_apply, Matrix.map_apply] at hkl
      simp [hkl]
  exact LinearMap.congr_fun hcomp x

end CommSemiring

section CommRing

variable {ι R S M M' : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module S M'] [Fintype ι] [DecidableEq ι]

/-- The determinant in the basis `b'` of the image of a family `v` is the image under `σ` of the
determinant of `v` in the basis `b`. -/
theorem det_comp_semilinearMap (b : Basis ι R M) (b' : Basis ι S M') (v : ι → M) :
    b'.det (b.semilinearMap σ b' ∘ v) = σ (b.det v) := by
  rw [det_apply, det_apply, RingHom.map_det]
  congr 1
  ext k l
  simp [toMatrix_apply]

end CommRing

end Module.Basis
