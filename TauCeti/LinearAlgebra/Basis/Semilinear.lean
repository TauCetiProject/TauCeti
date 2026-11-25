/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.Pi
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

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
of the image of a family is `σ` of its determinant in `b`. When `σ` is injective and `S` is a
domain, a family is linearly independent exactly when its image is. This is how invariants
computed from matrices, such as the torsion of a based chain complex, are compared along a
homomorphism of fields.

When `σ` is invertible, a `σ`-semilinear equivalence `f : M ≃ₛₗ[σ] M'` carries a basis `b` of `M`
to the basis `f ∘ b` of `M'` (`Module.Basis.mapₛₗ`), and so preserves `finrank`
(`LinearEquiv.finrank_eqₛₗ`). For instance, a conjugate-linear equivalence of complex vector spaces
carries complex bases to complex bases. Over any commutative star semiring, a finite basis `b`
induces the conjugate-linear coordinate equivalence `Module.Basis.conjEquivFun`.

## Main declarations

* `Module.Basis.semilinearMap`: the `σ`-semilinear map sending each `b k` to `b' k`.
* `Module.Basis.repr_semilinearMap_apply`: its coordinates are the images of the coordinates under
  `σ`.
* `Module.Basis.semilinearMap_comp_apply_of_toMatrix_eq`: it intertwines two linear maps whose
  matrices correspond under `σ`.
* `Module.Basis.det_comp_semilinearMap`: the determinant of the image of a family is the image of
  its determinant.
* `Module.Basis.linearIndependent_semilinearMap_comp_iff`: along an injective homomorphism into a
  domain, a family is linearly independent exactly when its image is.
* `Module.Basis.mapₛₗ`: the image of a basis under a semilinear equivalence.
* `Module.Basis.conjEquivFun`: the conjugate-linear coordinate equivalence `M ≃ₛₗ[starRingEnd R]
  (ι → R)` of a finite basis.
* `LinearEquiv.finrank_eqₛₗ`: semilinear equivalences along ring isomorphisms preserve `finrank`.
* `LinearMap.map_sum_smul_eq_of_eq_single`: a `σ`-semilinear map to `ι → S` sending a family to
  the standard basis applies `σ` to the coefficients of a linear combination of the family.
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

section Domain

variable {ι K L M M' : Type*} [CommRing K] [CommRing L] [IsDomain L] (σ : K →+* L)
  [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module L M'] [Finite ι]

/-- Along an injective ring homomorphism `σ` into a domain, a family `v` of vectors is linearly
independent exactly when its image under `semilinearMap σ b b'` is. -/
theorem linearIndependent_semilinearMap_comp_iff (hσ : Function.Injective σ) (b : Basis ι K M)
    (b' : Basis ι L M') {κ : Type*} {v : κ → M} :
    LinearIndependent L (b.semilinearMap σ b' ∘ v) ↔ LinearIndependent K v := by
  have := Fintype.ofFinite ι
  let := σ.toAlgebra
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 hσ
  -- In the coordinates of `b'`, the image of `v` is the coordinates of `v` in `b`, mapped by `σ`.
  have hw : b'.equivFun.toLinearMap ∘ (b.semilinearMap σ b' ∘ v) =
      fun k ↦ algebraMap K L ∘ (b.equivFun.toLinearMap ∘ v) k := by
    ext k i
    simp [RingHom.algebraMap_toAlgebra]
  rw [← LinearMap.linearIndependent_iff b'.equivFun.toLinearMap (LinearEquiv.ker _), hw,
    linearIndependent_algebraMap_comp_iff,
    LinearMap.linearIndependent_iff b.equivFun.toLinearMap (LinearEquiv.ker _)]

end Domain

section Map

variable {ι R S M M' : Type*} [Semiring R] [Semiring S] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module S M']

/-- The image `f ∘ b` of a basis `b` under a `σ`-semilinear equivalence `f`, a basis over the
target scalars. This is the semilinear version of `Module.Basis.map`. -/
def mapₛₗ (b : Basis ι R M) (f : M ≃ₛₗ[σ] M') : Basis ι S M' :=
  .mk (v := f ∘ b)
    (b.linearIndependent.map_of_injective_injectiveₛ σ' f.toAddEquiv.toAddMonoidHom
      (fun r s h ↦ by simpa using congrArg σ h) f.injective fun r x ↦ by
        simp [map_smulₛₗ])
    (by
      rw [Set.range_comp, ← LinearEquiv.coe_coe, ← Submodule.map_span, b.span_eq,
        Submodule.map_top, LinearEquiv.range])

@[simp]
theorem mapₛₗ_apply (b : Basis ι R M) (f : M ≃ₛₗ[σ] M') (i : ι) : b.mapₛₗ f i = f (b i) :=
  mk_apply _ _ _

end Map

section ConjEquivFun

variable {ι R M : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]

/-- The conjugate-linear equivalence `M ≃ₛₗ[starRingEnd R] (ι → R)` sending a vector to the
entrywise conjugate of its coordinate tuple in the basis `b`, dual to `Module.Basis.equivFun`. -/
def conjEquivFun [Finite ι] (b : Basis ι R M) : M ≃ₛₗ[starRingEnd R] (ι → R) :=
  b.equivFun.trans (starLinearEquiv R)

/-- Evaluating `b.conjEquivFun` at a vector returns its conjugated coordinate tuple. -/
@[simp]
theorem conjEquivFun_apply [Finite ι] (b : Basis ι R M) (m : M) (i : ι) :
    b.conjEquivFun m i = star (b.repr m i) := by
  simp [conjEquivFun]

/-- Evaluating `b.conjEquivFun.symm` reconstructs a vector from conjugated coordinates. -/
theorem conjEquivFun_symm_apply [Fintype ι] (b : Basis ι R M) (x : ι → R) :
    b.conjEquivFun.symm x = ∑ i, star (x i) • b i := by
  simp [conjEquivFun, equivFun_symm_apply]

/-- `b.conjEquivFun` sends the `j`-th basis vector to the `j`-th standard basis vector. -/
@[simp]
theorem conjEquivFun_self [Finite ι] (b : Basis ι R M) (j : ι) :
    b.conjEquivFun (b j) = Pi.basisFun R ι j := by
  classical
  ext i
  simp [conjEquivFun, Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply,
    apply_ite star, eq_comm]

end ConjEquivFun

end Module.Basis

namespace LinearEquiv

variable {R S M M' : Type*} [Semiring R] [Semiring S] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module S M']

/-- A semilinear equivalence along a ring isomorphism preserves `finrank`. This is the semilinear
version of `LinearEquiv.finrank_eq`. -/
theorem finrank_eqₛₗ (f : M ≃ₛₗ[σ] M') : Module.finrank R M = Module.finrank S M' := by
  have := lift_rank_eq_of_equiv_equiv σ f.toAddEquiv
    ⟨fun r s h ↦ by simpa using congrArg σ' h, fun r ↦ ⟨σ' r, by simp⟩⟩ (map_smulₛₗ f)
  simpa [Module.finrank] using congrArg Cardinal.toNat this

end LinearEquiv

namespace LinearMap

variable {ι R S M : Type*} [Semiring R] [Semiring S] {σ : R →+* S} [AddCommMonoid M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/-- A `σ`-semilinear map `f` to `ι → S` sending a family `e` to the standard basis sends
`∑ᵢ cᵢ • eᵢ` to the family of images `σ (cᵢ)` of the coefficients. -/
theorem map_sum_smul_eq_of_eq_single (f : M →ₛₗ[σ] ι → S) {e : ι → M}
    (he : ∀ i, f (e i) = Pi.single i 1) (c : ι → R) : f (∑ i, c i • e i) = fun i ↦ σ (c i) := by
  ext j
  simp [map_sum, he, Finset.sum_apply, Pi.single_apply]

end LinearMap
