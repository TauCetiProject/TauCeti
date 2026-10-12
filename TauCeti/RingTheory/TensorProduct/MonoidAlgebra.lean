/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of a monoid algebra

For a commutative semiring `R`, an `R`-algebra `S` and a monoid `G`, the base change
`R[G] ⊗[R] S` of the monoid algebra is the monoid algebra `S[G]`: `x ⊗ s` is sent to `s • x'`,
where `x'` is `x` with its coefficients pushed forward to `S`. Mathlib's
`MonoidAlgebra.scalarTensorEquiv` is this isomorphism, with the two tensor factors in the other
order, for a *commutative* monoid and coefficient semiring; the version here requires neither
`G` nor `S` to be commutative, so it applies to the group algebra of a nonabelian finite group.

The application is semisimplicity. When `k` is a field in which the order of a finite group `G`
is nonzero, Maschke's theorem makes `k[G]` semisimple, hence so is the base change `R[G] ⊗[R] k`
of the group algebra over any commutative ring `R` mapping to `k`. The rationalisation
`ℤ_p[G] ⊗[ℤ_p] ℚ_p` of an integral group ring is the case this is used for.

## Main definitions

* `MonoidAlgebra.tensorAlgEquiv`: the `R`-algebra isomorphism `R[G] ⊗[R] S ≃ₐ[R] S[G]`.

## Main results

* `MonoidAlgebra.isSemisimpleRing_tensor`: `R[G] ⊗[R] k` is a semisimple ring when `k` is
  a field in which the order of the finite group `G` is nonzero.
-/

public section

namespace MonoidAlgebra

open TensorProduct

section Equiv

variable (R : Type*) [CommSemiring R] (S : Type*) [Semiring S] [Algebra R S]
  (G : Type*) [Monoid G]

private theorem commute_mapAlgHom_single (x : MonoidAlgebra R G) (s : S) :
    Commute (mapAlgHom G (Algebra.ofId R S) x) (single 1 s) := by
  rw [Commute, SemiconjBy]
  ext m
  simp [coeff_mul_single_one, coeff_single_one_mul, Algebra.commutes]

/-- The forward direction of `tensorAlgEquiv`, as an `R`-algebra homomorphism out of the tensor
product: `x ⊗ s ↦ x' * s`, where `x'` has the coefficients of `x` pushed forward to `S`. -/
private noncomputable def toMonoidAlgebra :
    MonoidAlgebra R G ⊗[R] S →ₐ[R] MonoidAlgebra S G :=
  Algebra.TensorProduct.lift (mapAlgHom G (Algebra.ofId R S))
    singleOneAlgHom (commute_mapAlgHom_single R S G)

/-- The inverse direction of `tensorAlgEquiv`, as an `R`-algebra homomorphism:
`single m s ↦ single m 1 ⊗ s`. -/
private noncomputable def ofMonoidAlgebra :
    MonoidAlgebra S G →ₐ[R] MonoidAlgebra R G ⊗[R] S :=
  liftNCAlgHom
    (Algebra.TensorProduct.includeRight (R := R) (A := MonoidAlgebra R G) (B := S))
    ((Algebra.TensorProduct.includeLeftRingHom (R := R) (A := MonoidAlgebra R G)
      (B := S)).toMonoidHom.comp (of R G))
    fun s m ↦ (Commute.one_left (of R G m)).tmul (Commute.one_right s)

private theorem toMonoidAlgebra_tmul (x : MonoidAlgebra R G) (s : S) :
    toMonoidAlgebra R S G (x ⊗ₜ s) = mapAlgHom G (Algebra.ofId R S) x * single 1 s := by
  exact Algebra.TensorProduct.lift_tmul (mapAlgHom G (Algebra.ofId R S))
    singleOneAlgHom (commute_mapAlgHom_single R S G) x s

private theorem ofMonoidAlgebra_single (m : G) (s : S) :
    ofMonoidAlgebra R S G (single m s) = single m 1 ⊗ₜ s := by
  simp [ofMonoidAlgebra, Algebra.TensorProduct.tmul_mul_tmul]

private theorem toMonoidAlgebra_comp_ofMonoidAlgebra :
    (toMonoidAlgebra R S G).comp (ofMonoidAlgebra R S G) = AlgHom.id R _ := by
  ext <;> simp [ofMonoidAlgebra_single, toMonoidAlgebra_tmul]

private theorem ofMonoidAlgebra_comp_toMonoidAlgebra :
    (ofMonoidAlgebra R S G).comp (toMonoidAlgebra R S G) = AlgHom.id R _ := by
  ext <;> simp [ofMonoidAlgebra_single, toMonoidAlgebra_tmul, ← one_def]

/-- **Base change of a monoid algebra.** For an `R`-algebra `S`, the base change
`R[G] ⊗[R] S` of the monoid algebra of an arbitrary monoid `G` is the monoid algebra `S[G]`,
by `x ⊗ s ↦ s • x'` where `x'` has the coefficients of `x` pushed forward to `S`. -/
noncomputable def tensorAlgEquiv : MonoidAlgebra R G ⊗[R] S ≃ₐ[R] MonoidAlgebra S G :=
  AlgEquiv.ofAlgHom (toMonoidAlgebra R S G)
    (ofMonoidAlgebra R S G) (toMonoidAlgebra_comp_ofMonoidAlgebra R S G)
    (ofMonoidAlgebra_comp_toMonoidAlgebra R S G)

@[simp]
theorem tensorAlgEquiv_tmul (x : MonoidAlgebra R G) (s : S) :
    tensorAlgEquiv R S G (x ⊗ₜ s) = s • mapAlgHom G (Algebra.ofId R S) x := by
  rw [tensorAlgEquiv, AlgEquiv.ofAlgHom_apply, toMonoidAlgebra_tmul,
    (commute_mapAlgHom_single R S G x s).eq]
  ext m
  simp [coeff_single_one_mul]

@[simp]
theorem tensorAlgEquiv_symm_single (m : G) (s : S) :
    (tensorAlgEquiv R S G).symm (single m s) = single m 1 ⊗ₜ s :=
  (AlgEquiv.symm_apply_eq _).mpr (by simp)

end Equiv

/-- **Maschke's theorem after base change.** If `k` is a field in which the order of the finite
group `G` is nonzero, then the base change `R[G] ⊗[R] k` of the group algebra over any commutative
ring `R` mapping to `k` is a semisimple ring, being isomorphic to `k[G]`. -/
instance isSemisimpleRing_tensor (R : Type*) [CommRing R] (k : Type*) [Field k] [Algebra R k]
    (G : Type*) [Group G] [Finite G] [NeZero (Nat.card G : k)] :
    IsSemisimpleRing (MonoidAlgebra R G ⊗[R] k) :=
  (tensorAlgEquiv R k G).symm.toRingEquiv.isSemisimpleRing

end MonoidAlgebra
