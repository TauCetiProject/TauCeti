/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.OfMulAction
import TauCeti.RepresentationTheory.Invariants

/-!
# Change of coefficients for invariants of permutation representations

Let a group `I` act on a set `X`. Over a commutative ring `k`, the invariants of the permutation
representation `k[X]` are free on the finite orbits, with the orbit sums as basis
(`TauCeti.invariantFiniteOrbitSumBasis`). Hence for every commutative `k`-algebra `B`, flat or
not, the comparison map `B ⊗_k k[X]^I → (B ⊗_k k[X])^I` (`Representation.invariantsBaseChangeMap`)
is bijective (`Representation.invariantsBaseChangeMap_ofMulAction_bijective`): after identifying
`B ⊗_k k[X]` with `B[X]` (`TauCeti.baseChangeOfMulActionEquiv`), it sends the base change of the
orbit-sum basis over `k` to the orbit-sum basis over `B`. For subgroups `U, U'` of a group `G`
this gives `B ⊗ A[G/U']^U ≅ (B ⊗ A[G/U'])^U`, the permutation-module case of change of
coefficients for smooth representations.

## Main results

* `Representation.invariantsBaseChangeMap_ofMulAction_bijective`: for any commutative
  `k`-algebra `B`, `B ⊗_k k[X]^I → (B ⊗_k k[X])^I` is bijective.
-/

public section

open MonoidAlgebra MulAction TensorProduct TauCeti

namespace Representation

variable {k B I X : Type*} [CommRing k] [CommRing B] [Algebra k B] [Group I] [MulAction I X]

/-- **Change of coefficients commutes with the invariants of a permutation representation.**
For a group `I` acting on a set `X` and any commutative `k`-algebra `B`, flat or not, the
comparison map `B ⊗_k k[X]^I → (B ⊗_k k[X])^I` is bijective: both sides are free on the finite
orbits, and the map matches the orbit sums. -/
theorem invariantsBaseChangeMap_ofMulAction_bijective :
    Function.Bijective (invariantsBaseChangeMap (A := B) (ofMulAction k I X)) := by
  let e := (baseChangeOfMulActionEquiv k B I X).invariantsLinearEquiv
  let β := (invariantFiniteOrbitSumBasis k I X).baseChange B
  let f := β.equiv (invariantFiniteOrbitSumBasis B I X) (_root_.Equiv.refl _)
  -- After `e`, the comparison map is the identification of the two orbit-sum bases.
  have h : e.toLinearMap ∘ₗ invariantsBaseChangeMap (ofMulAction k I X) = f.toLinearMap := by
    refine β.ext fun ω ↦ ?_
    simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, _root_.Equiv.refl_apply]
    ext x
    simp only [e, β, Module.Basis.baseChange_apply, Equiv.coe_invariantsLinearEquiv_apply,
      coe_invariantsBaseChangeMap_tmul, coeff_baseChangeOfMulActionEquiv_one_tmul,
      coeff_invariantFiniteOrbitSumBasis]
    by_cases hx : x ∈ ω.val.orbit <;> simp [hx]
  have hb : Function.Bijective (e.toLinearMap ∘ₗ invariantsBaseChangeMap (ofMulAction k I X)) := by
    rw [h]
    exact f.bijective
  exact (e.bijective.of_comp_iff' _).1 hb

end Representation
