/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
public import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# The graded tensor product of two internally graded algebras is graded

Mathlib's `GradedTensorProduct R 𝒜 ℬ`, written `𝒜 ᵍ⊗[R] ℬ`, is the tensor product `A ⊗[R] B`
with the Koszul-signed multiplication

`(a ᵍ⊗ₜ b) * (a' ᵍ⊗ₜ b') = (-1) ^ (|b| * |a'|) • (a * a') ᵍ⊗ₜ (b * b')`,

for any Koszul-signed degree semiring `ι` (`[CommSemiring ι] [DecidableEq ι]
[Module ι (Additive ℤˣ)]`, in particular `ℤ`, `ℕ`, and `ZMod 2`).

Mathlib stops at the ring and algebra structures.  This file supplies the grading they are
compatible with: the total-degree grading of the underlying tensor product of graded modules turns
`𝒜 ᵍ⊗[R] ℬ` into an internally `ι`-graded algebra.  It also records unsigned multiplicative
compatibility on `A ⊗[R] B` (`SetLike.GradedOne`, `SetLike.GradedMul` and `SetLike.GradedMonoid`
for gradings by a commutative monoid, and `TauCeti.tensorProductGradedAlgebra` for `ℤ`-gradings),
degree-zero homogeneity of `LinearMap.mul'` (`TauCeti.isHomogeneous_mul'`), and how the
bihomogeneous projections `π i ⊗ π j` act on the total-degree pieces.

## Main definitions

* `TauCeti.tensorProductGradedAlgebra`: unsigned total-degree `GradedAlgebra` on `A ⊗[R] B`
  (`instance_reducible` so it cannot conflict with `GradedAlgebra.baseChange`).
* `TauCeti.gradedTensorGrading`: the total-degree grading of `𝒜 ᵍ⊗[R] ℬ`, whose degree-`n` piece
  is the sum of the images of `𝒜 p ⊗ ℬ q` over `p + q = n`.
* `TauCeti.gradedTensorLift`: the graded universal-property map induced by two graded algebra maps
  whose images satisfy the Koszul commutation rule.
* `TauCeti.gradedTensorIncludeLeft` and `TauCeti.gradedTensorIncludeRight`: the inclusions
  `a ↦ a ᵍ⊗ₜ 1` and `b ↦ 1 ᵍ⊗ₜ b` of the two factors, as homomorphisms of graded algebras.
* `TauCeti.gradedTensorHomOfMemZero`: the homomorphism `E ⊗ F → 𝒜 ᵍ⊗ ℬ`, `a ⊗ b ↦ ρ₁(a) ⊗ ρ₂(b)`,
  induced by two homomorphisms of nonunital algebras into degree zero.

## Main results

* `TauCeti.InternalGrading.instGradedOneTensorProductPiece`,
  `TauCeti.InternalGrading.instGradedMulTensorProductPiece`,
  `TauCeti.InternalGrading.instGradedMonoidTensorProductPiece`, and `TauCeti.isHomogeneous_mul'`:
  unsigned total-degree multiplication compatibility and degree-zero homogeneity of multiplication.
* `TauCeti.GradedAlgebra.map_proj_eq_zero_of_mem_tensorProduct` and
  `TauCeti.GradedAlgebra.sum_map_proj_of_mem_tensorProduct`: on the degree-`n` piece of
  `A ⊗[R] B`, `π i ⊗ π j` vanishes unless `i + j = n`, and these projections over `i + j = n` sum
  to the identity.
* `TauCeti.gradedTensorHomOfMemZero_comm`: maps induced by degree-zero homomorphisms
  intertwine the ordinary tensor flip with Mathlib's Koszul symmetry.
* `TauCeti.tmul_mem_gradedTensorGrading`: degrees add on pure tensors.
* `TauCeti.instGradedAlgebraGradedTensorGrading`: the graded tensor product of two internally
  `ι`-graded algebras is an internally `ι`-graded algebra.
* `TauCeti.gradedTensorGrading_le_of_add_eq` and (over a commutative ring `ι`)
  `TauCeti.gradedTensorGrading_le`: a submodule containing every homogeneous pure tensor of total
  degree `n` contains the whole degree-`n` piece; `TauCeti.gradedTensor_eq_top_of_tmul_mem` and
  `TauCeti.gradedTensor_linearMap_ext` are the corresponding statements for the whole graded
  tensor product and for maps out of it.  These are the tools with which a statement about
  the graded tensor product is reduced to pure tensors of homogeneous elements, which is where
  the Koszul sign is available.
* `TauCeti.gradedTensorAlgHom_ext`: graded algebra maps out of the tensor product are determined by
  their restrictions to the two factors.
* `TauCeti.gradedTensor_tmul_one_mul_one_tmul_comm`: the images of homogeneous elements of the two
  factors supercommute.

The grading of the underlying module is `TauCeti.InternalGrading.tensorProduct` and the Koszul
multiplication is Mathlib's `GradedTensorProduct`; only their compatibility is proved here.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §4.7, example (2).
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe uR uA uB uC uι

section UnsignedTensorProduct

namespace InternalGrading

/-- The pieces of `ofDecomposition 𝒜` are those of `𝒜`, so they inherit its graded-monoid
structure. -/
instance instGradedMonoidOfDecompositionPiece {R : Type uR} {A : Type uA} {ι : Type uι}
    [CommSemiring R] [Semiring A] [Algebra R A] [DecidableEq ι] [AddMonoid ι]
    (𝒜 : ι → Submodule R A) [DirectSum.Decomposition 𝒜] [SetLike.GradedMonoid 𝒜] :
    SetLike.GradedMonoid (ofDecomposition 𝒜).piece := by
  rw [ofDecomposition_piece]
  infer_instance

/-- On the ordinary tensor product `A ⊗[R] B`, if `1 ∈ GA.piece 0` and `1 ∈ GB.piece 0`, then
`1 ∈ (GA.tensorProduct GB).piece 0`. -/
instance instGradedOneTensorProductPiece {R : Type uR} {A : Type uA} {B : Type uB} {ι : Type uι}
    [CommSemiring R] [AddCommMonoidWithOne A] [AddCommMonoidWithOne B] [Module R A] [Module R B]
    [DecidableEq ι] [AddZeroClass ι] (GA : InternalGrading R A ι) (GB : InternalGrading R B ι)
    [SetLike.GradedOne GA.piece] [SetLike.GradedOne GB.piece] :
    SetLike.GradedOne (GA.tensorProduct GB).piece where
  one_mem := by
    rw [Algebra.TensorProduct.one_def, ← add_zero (0 : ι)]
    exact GA.tmul_mem_tensorProduct GB (SetLike.one_mem_graded GA.piece)
      (SetLike.one_mem_graded GB.piece)

/-- Unsigned multiplication on `A ⊗[R] B` adds total degrees in `(GA.tensorProduct GB).piece`. -/
instance instGradedMulTensorProductPiece {R : Type uR} {A : Type uA} {B : Type uB} {ι : Type uι}
    [CommSemiring R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [Module R A] [Module R B] [SMulCommClass R A A] [IsScalarTower R A A]
    [SMulCommClass R B B] [IsScalarTower R B B] [DecidableEq ι] [AddCommMonoid ι]
    (GA : InternalGrading R A ι) (GB : InternalGrading R B ι)
    [SetLike.GradedMul GA.piece] [SetLike.GradedMul GB.piece] :
    SetLike.GradedMul (GA.tensorProduct GB).piece where
  mul_mem i j z₁ z₂ hz₁ hz₂ := by
    refine GA.tensorProduct_piece_le_of_add_eq GB
      (C := ((GA.tensorProduct GB).piece (i + j)).comap (_root_.LinearMap.mulRight R z₂))
      (fun p q hpq a₁ ha₁ b₁ hb₁ => GA.tensorProduct_piece_le_of_add_eq GB
        (C := ((GA.tensorProduct GB).piece (i + j)).comap
          (_root_.LinearMap.mulLeft R (a₁ ⊗ₜ[R] b₁))) (fun p' q' hpq' a₂ ha₂ b₂ hb₂ => ?_) hz₂) hz₁
    rw [Submodule.mem_comap, _root_.LinearMap.mulLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
      ← hpq, ← hpq', add_add_add_comm]
    exact GA.tmul_mem_tensorProduct GB (SetLike.mul_mem_graded ha₁ ha₂)
      (SetLike.mul_mem_graded hb₁ hb₂)

/-- Unsigned multiplication and unit on `A ⊗[R] B` form a `SetLike.GradedMonoid` for the
total-degree grading `(GA.tensorProduct GB).piece`. -/
instance instGradedMonoidTensorProductPiece {R : Type uR} {A : Type uA} {B : Type uB}
    {ι : Type uι} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [DecidableEq ι] [AddCommMonoid ι] (GA : InternalGrading R A ι) (GB : InternalGrading R B ι)
    [SetLike.GradedMonoid GA.piece] [SetLike.GradedMonoid GB.piece] :
    SetLike.GradedMonoid (GA.tensorProduct GB).piece where

end InternalGrading

/-- The total-degree grading turns the ordinary tensor product `A ⊗[R] B` of two `ℤ`-graded
`R`-algebras into a `ℤ`-graded `R`-algebra (`instance_reducible` rather than a global instance so
it cannot form an instance diamond with `GradedAlgebra.baseChange`). -/
@[instance_reducible]
noncomputable def tensorProductGradedAlgebra {R : Type uR} {A : Type uA} {B : Type uB}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    GradedAlgebra (((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ)).piece) :=
  (((InternalGrading.ofDecomposition 𝒜).tensorProduct
    (InternalGrading.ofDecomposition ℬ)).isInternal).gradedAlgebra

/-- Multiplication on an internally `ℤ`-graded `R`-algebra is homogeneous of degree `0` from the
total-degree tensor-product grading to `𝒜`. -/
theorem isHomogeneous_mul' {R : Type uR} {A : Type uA} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜] :
    LinearMap.IsHomogeneous (_root_.LinearMap.mul' R A)
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece 𝒜 0 := by
  let G := InternalGrading.ofDecomposition 𝒜
  refine LinearMap.isHomogeneous_def.mpr fun n z hz => ?_
  rw [add_zero]
  refine G.tensorProduct_piece_le G (C := (𝒜 n).comap (_root_.LinearMap.mul' R A))
    (fun p x hx y hy => ?_) hz
  rw [InternalGrading.ofDecomposition_piece] at hx hy
  have hdeg : n = p + (n - p) := by omega
  rw [Submodule.mem_comap, _root_.LinearMap.mul'_apply, hdeg]
  exact SetLike.mul_mem_graded hx hy

section Proj

variable {R : Type uR} {A : Type uA} {B : Type uB} {ι : Type uι}
  [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [DecidableEq ι] [AddMonoid ι]
  (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- A bihomogeneous projection `π i ⊗ π j` with `i + j ≠ n` kills the degree-`n` piece of the
total-degree grading of `A ⊗[R] B`. -/
theorem GradedAlgebra.map_proj_eq_zero_of_mem_tensorProduct {n i j : ι} {t : A ⊗[R] B}
    (ht : t ∈ ((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ)).piece n) (hij : i + j ≠ n) :
    TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 i) (_root_.GradedAlgebra.proj ℬ j) t = 0 := by
  refine InternalGrading.tensorProduct_piece_le_of_add_eq _ _
    (C := _root_.LinearMap.ker (TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 i)
      (_root_.GradedAlgebra.proj ℬ j))) (fun k l hkl a ha b hb => ?_) ht
  rw [InternalGrading.ofDecomposition_piece] at ha hb
  rw [_root_.LinearMap.mem_ker, TensorProduct.map_tmul]
  by_cases hik : k = i
  · rw [GradedAlgebra.proj_of_mem_ne hb fun hlj => hij (by rw [← hik, ← hlj, hkl]),
      TensorProduct.tmul_zero]
  · rw [GradedAlgebra.proj_of_mem_ne ha hik, TensorProduct.zero_tmul]

/-- The bihomogeneous projections `π p.1 ⊗ π p.2` over the pairs `p` with `p.1 + p.2 = n` sum to
the identity on the degree-`n` piece of the total-degree grading of `A ⊗[R] B`. -/
theorem GradedAlgebra.sum_map_proj_of_mem_tensorProduct [Finset.HasAntidiagonal ι] {n : ι}
    {t : A ⊗[R] B} (ht : t ∈ ((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ)).piece n) :
    ∑ p ∈ Finset.antidiagonal n,
      TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 p.1) (_root_.GradedAlgebra.proj ℬ p.2) t =
        t := by
  have hle : ((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ)).piece n ≤
        _root_.LinearMap.eqLocus (∑ p ∈ Finset.antidiagonal n,
          TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 p.1) (_root_.GradedAlgebra.proj ℬ p.2))
          _root_.LinearMap.id := by
    refine InternalGrading.tensorProduct_piece_le_of_add_eq _ _ fun k l hkl a ha b hb => ?_
    rw [InternalGrading.ofDecomposition_piece] at ha hb
    rw [_root_.LinearMap.mem_eqLocus, _root_.LinearMap.sum_apply,
      Finset.sum_eq_single (k, l) (fun p _ hne => ?_)
        (fun h => absurd (Finset.mem_antidiagonal.mpr hkl) h),
      TensorProduct.map_tmul, GradedAlgebra.proj_of_mem_same ha,
      GradedAlgebra.proj_of_mem_same hb, _root_.LinearMap.id_apply]
    rw [TensorProduct.map_tmul]
    by_cases hik : k = p.1
    · rw [GradedAlgebra.proj_of_mem_ne hb fun hl => hne (Prod.ext hik.symm hl.symm),
        TensorProduct.tmul_zero]
    · rw [GradedAlgebra.proj_of_mem_ne ha hik, TensorProduct.zero_tmul]
  simpa [_root_.LinearMap.sum_apply] using hle ht

end Proj

end UnsignedTensorProduct

variable {R : Type uR} {A : Type uA} {B : Type uB} {ι : Type uι}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [CommSemiring ι] [DecidableEq ι] [Module ι (Additive ℤˣ)]

variable (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The total-degree grading of the graded tensor product `𝒜 ᵍ⊗[R] ℬ`: the degree-`n` piece is the
sum of the images of `𝒜 p ⊗ ℬ q` over pairs `(p, q)` with `p + q = n`. -/
noncomputable def gradedTensorGrading (n : ι) : Submodule R (𝒜 ᵍ⊗[R] ℬ) :=
  (((InternalGrading.ofDecomposition 𝒜).tensorProduct
    (InternalGrading.ofDecomposition ℬ)).map (GradedTensorProduct.of R 𝒜 ℬ)).piece n

/-- The homogeneous pieces of the graded tensor product form an internal direct sum. -/
theorem isInternal_gradedTensorGrading :
    DirectSum.IsInternal (gradedTensorGrading 𝒜 ℬ) :=
  InternalGrading.isInternal _

/-- A pure tensor of homogeneous elements is homogeneous, of the sum of their degrees. -/
theorem tmul_mem_gradedTensorGrading {p q : ι} {a : A} {b : B} (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) :
    a ᵍ⊗ₜ[R] b ∈ gradedTensorGrading 𝒜 ℬ (p + q) := by
  rw [gradedTensorGrading, InternalGrading.map_piece]
  exact Submodule.mem_map_of_mem (InternalGrading.tmul_mem_tensorProduct
    (InternalGrading.ofDecomposition 𝒜) (InternalGrading.ofDecomposition ℬ)
    (by simpa only [InternalGrading.ofDecomposition_piece] using ha)
    (by simpa only [InternalGrading.ofDecomposition_piece] using hb))

/-- A submodule containing every homogeneous pure tensor whose degrees sum to `n` contains the
whole degree-`n` piece of the graded tensor product. -/
theorem gradedTensorGrading_le_of_add_eq {n : ι} {C : Submodule R (𝒜 ᵍ⊗[R] ℬ)}
    (h : ∀ p q : ι, p + q = n → ∀ a ∈ 𝒜 p, ∀ b ∈ ℬ q, a ᵍ⊗ₜ[R] b ∈ C) :
    gradedTensorGrading 𝒜 ℬ n ≤ C := by
  rw [gradedTensorGrading, InternalGrading.map_piece, Submodule.map_le_iff_le_comap]
  refine InternalGrading.tensorProduct_piece_le_of_add_eq
    (InternalGrading.ofDecomposition 𝒜) (InternalGrading.ofDecomposition ℬ)
    fun p q hpq a ha b hb ↦ ?_
  rw [InternalGrading.ofDecomposition_piece] at ha hb
  exact h p q hpq a ha b hb

/-- A submodule containing every homogeneous pure tensor of total degree `n` contains the whole
degree-`n` piece of the graded tensor product (subtraction form for ring-valued degrees). -/
theorem gradedTensorGrading_le {ι' : Type*} [CommRing ι'] [DecidableEq ι']
    [Module ι' (Additive ℤˣ)] (𝒜' : ι' → Submodule R A) (ℬ' : ι' → Submodule R B)
    [GradedAlgebra 𝒜'] [GradedAlgebra ℬ'] {n : ι'} {C : Submodule R (𝒜' ᵍ⊗[R] ℬ')}
    (h : ∀ p : ι', ∀ a ∈ 𝒜' p, ∀ b ∈ ℬ' (n - p), a ᵍ⊗ₜ[R] b ∈ C) :
    gradedTensorGrading 𝒜' ℬ' n ≤ C := by
  rw [gradedTensorGrading, InternalGrading.map_piece,
    InternalGrading.tensorProduct_piece_eq_iSup, InternalGrading.ofDecomposition_piece,
    InternalGrading.ofDecomposition_piece, Submodule.map_le_iff_le_comap]
  exact iSup_le fun p ↦ Submodule.map₂_le.2 fun a ha b hb ↦ h p a ha b hb

/-- A submodule containing every homogeneous pure tensor is the whole graded tensor product. -/
theorem gradedTensor_eq_top_of_tmul_mem {C : Submodule R (𝒜 ᵍ⊗[R] ℬ)}
    (h : ∀ p q : ι, ∀ a ∈ 𝒜 p, ∀ b ∈ ℬ q, a ᵍ⊗ₜ[R] b ∈ C) :
    C = ⊤ := by
  refine top_le_iff.1 ?_
  rw [← (isInternal_gradedTensorGrading 𝒜 ℬ).submodule_iSup_eq_top]
  exact iSup_le fun n ↦ gradedTensorGrading_le_of_add_eq 𝒜 ℬ fun p q _ a ha b hb ↦ h p q a ha b hb

/-- Multiplying a homogeneous pure tensor into a homogeneous element adds degrees. -/
private theorem tmul_mul_mem_gradedTensorGrading {p q n : ι} {a : A} {b : B} {y : 𝒜 ᵍ⊗[R] ℬ}
    (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) (hy : y ∈ gradedTensorGrading 𝒜 ℬ n) :
    (a ᵍ⊗ₜ[R] b) * y ∈ gradedTensorGrading 𝒜 ℬ (p + q + n) := by
  refine gradedTensorGrading_le_of_add_eq 𝒜 ℬ (C := Submodule.comap
    (GradedTensorProduct.mulHom 𝒜 ℬ (a ᵍ⊗ₜ[R] b)) (gradedTensorGrading 𝒜 ℬ (p + q + n)))
    (fun r s hrs a' ha' b' hb' ↦ ?_) hy
  rw [Submodule.mem_comap, ← GradedTensorProduct.mul_def,
    GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 ℬ a ⟨b, hb⟩ ⟨a', ha'⟩ b']
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  have hdeg : p + r + (q + s) = p + q + n := by rw [add_add_add_comm, hrs]
  rw [← hdeg]
  exact tmul_mem_gradedTensorGrading 𝒜 ℬ (SetLike.mul_mem_graded ha ha')
    (SetLike.mul_mem_graded hb hb')

/-- The Koszul multiplication of the graded tensor product adds degrees. -/
instance instGradedMonoidGradedTensorGrading :
    SetLike.GradedMonoid (gradedTensorGrading 𝒜 ℬ) where
  one_mem := by
    have h : (1 : 𝒜 ᵍ⊗[R] ℬ) = (1 : A) ᵍ⊗ₜ[R] (1 : B) := rfl
    rw [h]
    simpa only [add_zero] using tmul_mem_gradedTensorGrading 𝒜 ℬ (SetLike.one_mem_graded 𝒜)
      (SetLike.one_mem_graded ℬ)
  mul_mem := by
    intro m n x y hx hy
    refine gradedTensorGrading_le_of_add_eq 𝒜 ℬ (C := Submodule.comap
      ((GradedTensorProduct.mulHom 𝒜 ℬ).flip y) (gradedTensorGrading 𝒜 ℬ (m + n)))
      (fun p q hpq a ha b hb ↦ ?_) hx
    rw [Submodule.mem_comap, LinearMap.flip_apply, ← GradedTensorProduct.mul_def, ← hpq]
    exact tmul_mul_mem_gradedTensorGrading 𝒜 ℬ ha hb hy

/-- The graded tensor product of two internally `ι`-graded algebras is an internally `ι`-graded
algebra for the total-degree grading. -/
noncomputable instance instGradedAlgebraGradedTensorGrading :
    GradedAlgebra (gradedTensorGrading 𝒜 ℬ) :=
  (isInternal_gradedTensorGrading 𝒜 ℬ).gradedAlgebra

section Lift

variable {C : Type uC} [Ring C] [Algebra R C]
  (𝒞 : ι → Submodule R C) [GradedAlgebra 𝒞]

private theorem gradedTensorLift_map_mem (F : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C)
    (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞) (hF : ∀ a b, F (a ᵍ⊗ₜ[R] b) = f a * g b)
    {n : ι} {x : 𝒜 ᵍ⊗[R] ℬ} (hx : x ∈ gradedTensorGrading 𝒜 ℬ n) : F x ∈ 𝒞 n := by
  refine gradedTensorGrading_le_of_add_eq 𝒜 ℬ (C := Submodule.comap
    F.toLinearMap (𝒞 n)) (fun p q hpq a ha b hb ↦ ?_) hx
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, hF, ← hpq]
  exact SetLike.mul_mem_graded (f.map_mem ha) (g.map_mem hb)

/-- The graded algebra map out of a graded tensor product induced by two graded algebra maps whose
images satisfy the Koszul commutation rule. -/
noncomputable def gradedTensorLift (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)) :
    gradedTensorGrading 𝒜 ℬ →ₐᵍ[R] 𝒞 := by
  have h' : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j),
      f.toAlgHom a * g.toAlgHom b = (-1 : ℤˣ) ^ (j * i) •
        (g.toAlgHom b * f.toAlgHom a) := by
    intro i j a b
    -- Mathlib's lift accepts the stored `AlgHom`s, whose applications are definitionally the
    -- applications of the graded maps in the supplied commutation hypothesis.
    change f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)
    exact h a b
  let F : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C :=
    GradedTensorProduct.lift 𝒜 ℬ f.toAlgHom g.toAlgHom h'
  exact { F with
    map_mem := by
      apply gradedTensorLift_map_mem 𝒜 ℬ 𝒞
        (F := F) (f := f) (g := g)
      intro a b
      -- The local `F` is Mathlib's underlying lift; expose its stored factor maps to use its
      -- pure-tensor computation theorem.
      change F (a ᵍ⊗ₜ[R] b) = f.toAlgHom a * g.toAlgHom b
      exact GradedTensorProduct.lift_tmul 𝒜 ℬ f.toAlgHom g.toAlgHom h' a b }

/-- The graded tensor lift sends a pure tensor to the product of the two factor maps. -/
@[simp]
theorem gradedTensorLift_tmul (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)) (a : A) (b : B) :
    gradedTensorLift 𝒜 ℬ 𝒞 f g h (a ᵍ⊗ₜ[R] b) = f a * g b := by
  apply GradedTensorProduct.lift_tmul 𝒜 ℬ f.toAlgHom g.toAlgHom
  intro i j a b
  simpa only [GradedAlgHom.coe_toAlgHom] using h a b

end Lift

/-- A pure tensor of the graded tensor product is additive in its left factor. -/
@[simp]
theorem gradedTensor_add_tmul (a₁ a₂ : A) (b : B) :
    (a₁ + a₂) ᵍ⊗ₜ[R] b = (a₁ ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) + a₂ ᵍ⊗ₜ[R] b := by
  simp [GradedTensorProduct.tmul, TensorProduct.add_tmul]

/-- A pure tensor of the graded tensor product is additive in its right factor. -/
@[simp]
theorem gradedTensor_tmul_add (a : A) (b₁ b₂ : B) :
    a ᵍ⊗ₜ[R] (b₁ + b₂) = (a ᵍ⊗ₜ[R] b₁ : 𝒜 ᵍ⊗[R] ℬ) + a ᵍ⊗ₜ[R] b₂ := by
  simp [GradedTensorProduct.tmul, TensorProduct.tmul_add]

/-- Scalars pass from the left factor of a pure tensor to the tensor. -/
@[simp]
theorem gradedTensor_smul_tmul (r : R) (a : A) (b : B) :
    (r • a) ᵍ⊗ₜ[R] b = r • (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) := by
  simp only [GradedTensorProduct.tmul, ← map_smul, TensorProduct.smul_tmul']

/-- Scalars pass from the right factor of a pure tensor to the tensor. -/
@[simp]
theorem gradedTensor_tmul_smul (r : R) (a : A) (b : B) :
    a ᵍ⊗ₜ[R] (r • b) = r • (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) := by
  simp only [GradedTensorProduct.tmul, ← map_smul, TensorProduct.tmul_smul]

/-- A pure tensor of the graded tensor product vanishes when its left factor does. -/
@[simp]
theorem gradedTensor_zero_tmul (b : B) : (0 : A) ᵍ⊗ₜ[R] b = (0 : 𝒜 ᵍ⊗[R] ℬ) := by
  simp [GradedTensorProduct.tmul]

/-- A pure tensor of the graded tensor product vanishes when its right factor does. -/
@[simp]
theorem gradedTensor_tmul_zero (a : A) : a ᵍ⊗ₜ[R] (0 : B) = (0 : 𝒜 ᵍ⊗[R] ℬ) := by
  simp [GradedTensorProduct.tmul]

/-- Two linear maps out of the graded tensor product agree as soon as they agree on the pure
tensors of homogeneous elements. -/
theorem gradedTensor_linearMap_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] M}
    (h : ∀ p q : ι, ∀ a ∈ 𝒜 p, ∀ b ∈ ℬ q, f (a ᵍ⊗ₜ[R] b) = g (a ᵍ⊗ₜ[R] b)) :
    f = g := by
  refine LinearMap.ext fun x ↦ sub_eq_zero.1 ?_
  have hx : x ∈ (⊤ : Submodule R (𝒜 ᵍ⊗[R] ℬ)) := trivial
  rw [← gradedTensor_eq_top_of_tmul_mem 𝒜 ℬ (C := LinearMap.ker (f - g))
    fun p q a ha b hb ↦ by simp [h p q a ha b hb]] at hx
  simpa using hx

/-- The inclusion `a ↦ a ᵍ⊗ₜ 1` of the left factor, as a homomorphism of graded algebras. -/
noncomputable def gradedTensorIncludeLeft : 𝒜 →ₐᵍ[R] gradedTensorGrading 𝒜 ℬ :=
  { GradedTensorProduct.includeLeft 𝒜 ℬ with
    map_mem := fun {i x} hx ↦ by
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GradedTensorProduct.includeLeft_apply,
        add_zero] using tmul_mem_gradedTensorGrading 𝒜 ℬ hx (SetLike.one_mem_graded ℬ) }

@[simp]
theorem gradedTensorIncludeLeft_apply (a : A) :
    gradedTensorIncludeLeft 𝒜 ℬ a = a ᵍ⊗ₜ[R] (1 : B) := (rfl)

/-- The inclusion `b ↦ 1 ᵍ⊗ₜ b` of the right factor, as a homomorphism of graded algebras. -/
noncomputable def gradedTensorIncludeRight : ℬ →ₐᵍ[R] gradedTensorGrading 𝒜 ℬ :=
  { GradedTensorProduct.includeRight 𝒜 ℬ with
    map_mem := fun {i x} hx ↦ by
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GradedTensorProduct.includeRight_apply,
        zero_add] using tmul_mem_gradedTensorGrading 𝒜 ℬ (SetLike.one_mem_graded 𝒜) hx }

@[simp]
theorem gradedTensorIncludeRight_apply (b : B) :
    gradedTensorIncludeRight 𝒜 ℬ b = (1 : A) ᵍ⊗ₜ[R] b := (rfl)

/-- The images `a ᵍ⊗ₜ 1` and `1 ᵍ⊗ₜ b` of homogeneous elements of the two factors supercommute,
with the Koszul sign of their degrees. -/
theorem gradedTensor_tmul_one_mul_one_tmul_comm {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {p q : ι} {a : A} {b : B}
    (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) :
    (a ᵍ⊗ₜ[R] (1 : B) * (1 : A) ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) =
      ((-1 : ℤˣ) ^ (p * q)) • ((1 : A) ᵍ⊗ₜ[R] b * a ᵍ⊗ₜ[R] (1 : B)) := by
  rw [GradedTensorProduct.tmul_one_mul_one_tmul,
    GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 ℬ (1 : A) ⟨b, hb⟩ ⟨a, ha⟩ (1 : B),
    one_mul, mul_one, smul_smul, mul_comm q p, Int.units_mul_self, one_smul]

/-! ### The tensor product of two homomorphisms into degree zero -/

section HomOfMemZero

variable {𝒜 ℬ} {E F : Type*} [NonUnitalSemiring E] [Module R E] [SMulCommClass R E E]
  [IsScalarTower R E E] [NonUnitalSemiring F] [Module R F] [SMulCommClass R F F]
  [IsScalarTower R F F]

variable (ρ₁ : E →ₙₐ[R] A) (ρ₂ : F →ₙₐ[R] B)

/-- The homomorphism `a ⊗ b ↦ ρ₁(a) ⊗ ρ₂(b)` from `E ⊗ F` to the graded tensor product, for two
homomorphisms of nonunital algebras with values in degree zero, where the Koszul sign is
trivial. -/
noncomputable def gradedTensorHomOfMemZero (hρ₁ : ∀ a, ρ₁ a ∈ 𝒜 0) (hρ₂ : ∀ b, ρ₂ b ∈ ℬ 0) :
    E ⊗[R] F →ₙₐ[R] 𝒜 ᵍ⊗[R] ℬ where
  toFun := (GradedTensorProduct.of R 𝒜 ℬ).toLinearMap ∘ₗ
    TensorProduct.map (ρ₁ : E →ₗ[R] A) (ρ₂ : F →ₗ[R] B)
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
      | tmul a' b' =>
        simp only [LinearMap.comp_apply, Algebra.TensorProduct.tmul_mul_tmul,
          TensorProduct.map_tmul, LinearEquiv.coe_coe, LinearMap.coe_ofClass, map_mul]
        exact (GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜 ℬ (ρ₁ a) ⟨ρ₂ b, hρ₂ b⟩
          ⟨ρ₁ a', hρ₁ a'⟩ (ρ₂ b')).symm

variable {ρ₁ ρ₂} (hρ₁ : ∀ a, ρ₁ a ∈ 𝒜 0) (hρ₂ : ∀ b, ρ₂ b ∈ ℬ 0)

/-- The homomorphism induced by two homomorphisms into degree zero, on a pure tensor. -/
@[simp]
theorem gradedTensorHomOfMemZero_tmul (a : E) (b : F) :
    gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂ (a ⊗ₜ b) = ρ₁ a ᵍ⊗ₜ[R] ρ₂ b :=
  (rfl)

/-- The homomorphism `a ⊗ b ↦ ρ₁(a) ⊗ ρ₂(b)` lands in degree zero. -/
theorem gradedTensorHomOfMemZero_mem (x : E ⊗[R] F) :
    gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂ x ∈ gradedTensorGrading 𝒜 ℬ 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul a b =>
    simpa using tmul_mem_gradedTensorGrading 𝒜 ℬ (hρ₁ a) (hρ₂ b)

/-- The tensor homomorphism induced by two maps into degree zero intertwines the ordinary
flip on its source with the Koszul symmetry on its target. -/
theorem gradedTensorHomOfMemZero_comm (x : E ⊗[R] F) :
    gradedTensorHomOfMemZero ρ₂ ρ₁ hρ₂ hρ₁ (TensorProduct.comm R E F x) =
      GradedTensorProduct.comm 𝒜 ℬ (gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [TensorProduct.comm_tmul, gradedTensorHomOfMemZero_tmul,
      gradedTensorHomOfMemZero_tmul,
      GradedTensorProduct.comm_coe_tmul_coe 𝒜 ℬ ⟨ρ₁ a, hρ₁ a⟩ ⟨ρ₂ b, hρ₂ b⟩]
    simp

end HomOfMemZero

/-- Two graded algebra morphisms from the graded tensor product agree if their compositions with
the left and right factor inclusions agree. -/
@[ext]
theorem gradedTensorAlgHom_ext {C : Type uC} [Ring C] [Algebra R C]
    (𝒞 : ι → Submodule R C) [GradedAlgebra 𝒞]
    ⦃f g : gradedTensorGrading 𝒜 ℬ →ₐᵍ[R] 𝒞⦄
    (ha : f.comp (gradedTensorIncludeLeft 𝒜 ℬ) = g.comp (gradedTensorIncludeLeft 𝒜 ℬ))
    (hb : f.comp (gradedTensorIncludeRight 𝒜 ℬ) = g.comp (gradedTensorIncludeRight 𝒜 ℬ)) :
    f = g := by
  apply GradedAlgHom.coe_toAlgHom_injective
  apply GradedTensorProduct.algHom_ext
  · simpa only [GradedAlgHom.comp_toAlgHom, gradedTensorIncludeLeft] using
      congrArg GradedAlgHom.toAlgHom ha
  · simpa only [GradedAlgHom.comp_toAlgHom, gradedTensorIncludeRight] using
      congrArg GradedAlgHom.toAlgHom hb

end TauCeti
