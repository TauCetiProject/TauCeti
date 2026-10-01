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
# Base change of a monoid algebra along a commutative algebra

For a commutative ring `R`, a commutative `R`-algebra `S` and a monoid `G`, the base change
`R[G] ⊗[R] S` of the monoid algebra is the monoid algebra `S[G]`: `x ⊗ s` is sent to `s • x'`,
where `x'` is `x` with its coefficients pushed forward to `S`. Mathlib's
`MonoidAlgebra.scalarTensorEquiv` is this isomorphism, with the two tensor factors in the other
order, for a *commutative* monoid; the version here has no commutativity hypothesis on `G`, so
that it applies to the group algebra of a nonabelian finite group.

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

variable (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]
  (G : Type*) [Monoid G]

private theorem commute_mapAlgHom_algebraMap (x : MonoidAlgebra R G) (s : S) :
    Commute (mapAlgHom G (Algebra.ofId R S) x)
      (((Algebra.ofId S (MonoidAlgebra S G)).restrictScalars R) s) :=
  (Algebra.commutes s _).symm

/-- The forward direction of `tensorAlgEquiv`, as an `R`-algebra homomorphism out of the tensor
product: `x ⊗ s ↦ x' * s`, where `x'` has the coefficients of `x` pushed forward to `S`. -/
private noncomputable def toMonoidAlgebra :
    MonoidAlgebra R G ⊗[R] S →ₐ[R] MonoidAlgebra S G :=
  Algebra.TensorProduct.lift (mapAlgHom G (Algebra.ofId R S))
    ((Algebra.ofId S (MonoidAlgebra S G)).restrictScalars R) (commute_mapAlgHom_algebraMap R S G)

/-- The inverse direction of `tensorAlgEquiv`, as a ring homomorphism out of the monoid algebra:
`single m s ↦ single m 1 ⊗ s`. -/
private noncomputable def ofMonoidAlgebra :
    MonoidAlgebra S G →+* MonoidAlgebra R G ⊗[R] S :=
  liftNCRingHom
    (Algebra.TensorProduct.includeRight (R := R) (A := MonoidAlgebra R G) (B := S)).toRingHom
    ((Algebra.TensorProduct.includeLeftRingHom (R := R) (A := MonoidAlgebra R G)
      (B := S)).toMonoidHom.comp (of R G))
    fun s m ↦ by
      rw [Commute, SemiconjBy]
      simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem toMonoidAlgebra_tmul (x : MonoidAlgebra R G) (s : S) :
    toMonoidAlgebra R S G (x ⊗ₜ s) = mapAlgHom G (Algebra.ofId R S) x * single 1 s := by
  simp [toMonoidAlgebra, coe_algebraMap]

private theorem ofMonoidAlgebra_single (m : G) (s : S) :
    ofMonoidAlgebra R S G (single m s) = single m 1 ⊗ₜ s := by
  simp [ofMonoidAlgebra, Algebra.TensorProduct.tmul_mul_tmul]

private theorem toMonoidAlgebra_comp_ofMonoidAlgebra :
    (toMonoidAlgebra R S G).toRingHom.comp (ofMonoidAlgebra R S G) = RingHom.id _ := by
  refine ringHom_ext (fun r ↦ ?_) fun m ↦ ?_
  all_goals simp [ofMonoidAlgebra_single, toMonoidAlgebra_tmul, single_mul_single]

private theorem ofMonoidAlgebra_comp_toMonoidAlgebra :
    (ofMonoidAlgebra R S G).comp (toMonoidAlgebra R S G).toRingHom = RingHom.id _ := by
  refine Algebra.TensorProduct.ringHom_ext ?_ ?_
  · refine ringHom_ext (fun r ↦ ?_) fun m ↦ ?_
    · simp only [RingHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply, RingHom.id_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, toMonoidAlgebra_tmul, mapAlgHom_single,
        Algebra.ofId_apply, mul_one, single_mul_single, ofMonoidAlgebra_single]
      rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul, smul_single', mul_one]
    · simp [ofMonoidAlgebra_single, toMonoidAlgebra_tmul]
  · ext s
    simp [ofMonoidAlgebra_single, toMonoidAlgebra_tmul, ← one_def]

/-- **Base change of a monoid algebra.** For a commutative `R`-algebra `S`, the base change
`R[G] ⊗[R] S` of the monoid algebra of an arbitrary monoid `G` is the monoid algebra `S[G]`,
by `x ⊗ s ↦ s • x'` where `x'` has the coefficients of `x` pushed forward to `S`. -/
noncomputable def tensorAlgEquiv : MonoidAlgebra R G ⊗[R] S ≃ₐ[R] MonoidAlgebra S G :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (toMonoidAlgebra R S G).toRingHom
    (ofMonoidAlgebra R S G) (toMonoidAlgebra_comp_ofMonoidAlgebra R S G)
    (ofMonoidAlgebra_comp_toMonoidAlgebra R S G)) fun r ↦ (toMonoidAlgebra R S G).commutes r

private theorem tensorAlgEquiv_apply (x : MonoidAlgebra R G ⊗[R] S) :
    tensorAlgEquiv R S G x = toMonoidAlgebra R S G x :=
  rfl

@[simp]
theorem tensorAlgEquiv_tmul (x : MonoidAlgebra R G) (s : S) :
    tensorAlgEquiv R S G (x ⊗ₜ s) = s • mapAlgHom G (Algebra.ofId R S) x := by
  rw [tensorAlgEquiv_apply, toMonoidAlgebra_tmul, Algebra.smul_def, Algebra.commutes]
  rfl

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
