/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.LinearAlgebra.GeneralLinearGroup.InvariantRestrict
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction

/-!
# Conjugating an integral nilpotent exponential by an intertwining automorphism

Let `V` be a module over a `ℚ`-algebra `A`, let `M ≤ V` be an additive subgroup, and let
`θ : V ≃ₗ[ℚ] V` be a `ℚ`-linear automorphism restricting to a bijection of `M`. If `θ` carries the
action of `x : A` to the action of `y : A`, in the sense that `θ (x • v) = y • θ v`, then it carries
every divided power of `x` to the corresponding divided power of `y`, and hence conjugates the
base-changed divided-power exponential of `x` into that of `y`:

```text
θ_R ∘ E_R(x, t) = E_R(y, t) ∘ θ_R,     θ_R = R ⊗ θ|_M.
```

The intertwining hypothesis is imposed only on `x` itself. Divided powers divide by factorials in
`A`, so `θ` must be `ℚ`-linear for the transported statement to make sense; the *conclusion* is
nonetheless an identity of integral operators on `R ⊗[ℤ] M` over an arbitrary commutative ring `R`.

This is a mechanism used to construct graph automorphisms of Chevalley groups: a symmetry of the
ambient Lie-algebra data that permutes the distinguished root vectors conjugates the corresponding
root subgroups into one another, permuted the same way. Its application to Kostant root subgroups
is in `TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/NumberedSymmetry.lean`.

## Main definitions and results

* `LinearEquiv.baseChange_invariantRestrict_baseChangeExp`: the conjugation formula for the
  base-changed exponential.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
-/

public section

namespace LinearEquiv

open TauCeti TensorProduct

universe u v

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type u} [AddCommGroup V] [Module ℚ V] [Module A V] [IsScalarTower ℚ A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

variable (θ : V ≃ₗ[ℚ] V) {x y : A}

/-! ## Conjugating the base-changed exponential -/

-- Use the module structure carried by the explicit `ℤ`-algebra, matching `baseChangeExp`.
attribute [local instance high] Algebra.toModule

variable {R : Type v} [CommRing R] [Algebra ℤ R]

/-- Conjugating the base-changed divided-power exponential of `x` by an intertwiner produces the
base-changed divided-power exponential of `y`, with the same parameter.

The two nilpotent elements may have different nilpotency indices; the finite-sum comparison
uses a common bound internally. -/
theorem baseChange_invariantRestrict_baseChangeExp (M : S) (hθ : ∀ v, θ v ∈ M ↔ v ∈ M)
    (hxy : ∀ v, θ (x • v) = y • θ v)
    (hx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hnilx : IsNilpotent x) (hnily : IsNilpotent y) (t : R) (z : R ⊗[ℤ] M) :
    (θ.toAddEquiv.invariantRestrict M hθ).baseChange ℤ R M M
        (baseChangeExp x M hx t z) =
      baseChangeExp y M (θ.dividedPower_smul_mem_of_intertwines M M hθ hxy hx) t
        ((θ.toAddEquiv.invariantRestrict M hθ).baseChange ℤ R M M z) := by
  obtain ⟨kx, hkx⟩ := hnilx
  obtain ⟨ky, hky⟩ := hnily
  have hkx' : x ^ max kx ky = 0 := pow_eq_zero_of_le (Nat.le_max_left _ _) hkx
  have hky' : y ^ max kx ky = 0 := pow_eq_zero_of_le (Nat.le_max_right _ _) hky
  induction z using TensorProduct.inductionOn with
  | tmul r v =>
      rw [baseChangeExp_tmul_of_pow_eq_zero x M hx hkx', map_sum,
        LinearEquiv.baseChange_tmul, baseChangeExp_tmul_of_pow_eq_zero y M
          (θ.dividedPower_smul_mem_of_intertwines M M hθ hxy hx) hky']
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LinearEquiv.baseChange_tmul]
      congr 1
      refine Subtype.ext ?_
      rw [AddEquiv.coe_invariantRestrict_apply, coe_integralDividedPower_apply,
        coe_integralDividedPower_apply, AddEquiv.coe_invariantRestrict_apply]
      simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toAddEquiv,
        LinearEquiv.coe_addEquiv_apply] using
        θ.toLinearMap.map_dividedPower_smul_of_intertwines hxy n (v : V)
  | add z w hz hw => simp only [map_add, hz, hw]

end LinearEquiv
