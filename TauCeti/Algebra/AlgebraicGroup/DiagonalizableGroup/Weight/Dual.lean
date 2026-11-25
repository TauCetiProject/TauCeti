/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation

/-!
# Weight spaces of duals

Let `π : C → R[X]` be a bialgebra morphism out of a Hopf algebra, so that corestriction along `π`
restricts a representation of the group with coordinate Hopf algebra `C` to the diagonalizable
group `D(X)`. This file shows that the weight spaces of `TauCeti.DiagonalizableGroup.weightSpace`
are compatible with duals: a functional of weight `x` pairs trivially with every vector of weight
`y` unless `x * y = 1`.

## Main results

* `TauCeti.DiagonalizableGroup.apply_eq_zero_of_mem_weightSpace_dual`: on a finite projective
  comodule over a Hopf algebra, a functional of weight `x` for the dual coaction vanishes on every
  vector of weight `y` with `x * y ≠ 1`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed. (2003), Part I, §2.11.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.DiagonalizableGroup

variable {R : Type*} [CommSemiring R] {X : Type*} [CommMonoid X]
variable {C : Type*} [Semiring C] [HopfAlgebra R C]
variable {V : Type*} [AddCommMonoid V] [Module R V] [Comodule R C V] [Module.Finite R V]
  [Module.Projective R V]

attribute [local instance] Comodule.dual

/-- **Weights negate in the dual.** For a bialgebra morphism `π : C → R[X]` out of a Hopf
algebra, a functional `φ` of weight `x` for the dual coaction on a finite projective comodule `V`
vanishes on every vector `v` of weight `y` with `x * y ≠ 1`. -/
theorem apply_eq_zero_of_mem_weightSpace_dual (π : C →ₐc[R] MonoidAlgebra R X) {x y : X}
    {φ : Module.Dual R V} {v : V}
    (hφ : φ ∈ weightSpace (Module.Dual R V) (π : C →ₗc[R] MonoidAlgebra R X) x)
    (hv : v ∈ weightSpace V (π : C →ₗc[R] MonoidAlgebra R X) y) (hxy : x * y ≠ 1) :
    φ v = 0 := by
  have h := TauCeti.Comodule.baseChangeEvaluation_dual_endOfPoint_invariant (R := R) (H := C)
    (M := V) (A := MonoidAlgebra R X) (toConv (π : C →ₐ[R] MonoidAlgebra R X))
    (1 ⊗ₜ[R] φ) (1 ⊗ₜ[R] v)
  rw [ofConv_toConv, ← AlgHom.id_comp (π : C →ₐ[R] MonoidAlgebra R X)] at h
  rw [endOfPoint_tmul_of_mem_weightSpace _ π (AlgHom.id R (MonoidAlgebra R X)) 1 hφ,
    endOfPoint_tmul_of_mem_weightSpace _ π (AlgHom.id R (MonoidAlgebra R X)) 1 hv] at h
  simp only [TauCeti.Module.Dual.baseChangeEvaluation_tmul, AlgHom.coe_id, id_eq, one_mul,
    MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    MonoidAlgebra.single_mul_single, mul_one] at h
  by_contra h₀
  exact hxy ((MonoidAlgebra.single_left_inj h₀).mp h)

end TauCeti.DiagonalizableGroup
