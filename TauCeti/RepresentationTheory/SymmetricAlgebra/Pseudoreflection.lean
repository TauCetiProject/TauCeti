/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.Dual.Lemmas
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.SymmetricAlgebra.DividedDifference

/-!
# Polynomial divided differences from pseudoreflections

Let `ρ` act on a vector space `V`, and suppose the fixed space of `g` has codimension one,
as it does for a pseudoreflection. This hyperplane is the kernel of a nonzero form `ℓ`.
On polynomial functions `Sym(V*)`, every difference
`p - g • p` is divisible by `ℓ`, and there is a unique linear operator over the invariant
algebra satisfying `ℓ * δ p = p - g • p`. This operator lowers homogeneous degree by one.

This connects the geometric codimension-one condition with the divided-difference construction
and its operator identity in `TauCeti.RepresentationTheory.SymmetricAlgebra.DividedDifference`.
It requires neither finite-dimensionality nor any assumption on the characteristic or the order
of the ambient group. Finite order is not needed: the codimension-one condition suffices.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §§ 17–18.
* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), § 7.2.
-/

public section

namespace Representation

open TauCeti.SymmetricAlgebra

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
variable (ρ : Representation K G V) (g : G)

/-- If the fixed space of `g` has codimension one, it has a defining form and a unique
divided-difference operator on polynomial functions, linear over the invariant algebra.
The operator lowers homogeneous degree by one. In particular this constructs the
divided difference of every pseudoreflection, without requiring its order to be two. -/
theorem exists_unique_symmetricAlgebraDividedDifference_of_finrank_quotient_eq_one
    (hg : Module.finrank K (V ⧸ (ρ g).fixedSubmodule) = 1) :
    ∃ ℓ : Module.Dual K V, ℓ ≠ 0 ∧ LinearMap.ker ℓ = (ρ g).fixedSubmodule ∧
      ∃ δ : SymmetricAlgebra K (Module.Dual K V) →ₗ[ρ.dual.symmetricAlgebraInvariants]
          SymmetricAlgebra K (Module.Dual K V),
        (∀ p, SymmetricAlgebra.ι K (Module.Dual K V) ℓ * δ p =
          p - ρ.dual.symmetricAlgebra g p) ∧
        (∀ n p, p ∈ homogeneousSubmodule K (Module.Dual K V) (n + 1) →
          δ p ∈ homogeneousSubmodule K (Module.Dual K V) n) ∧
        (∀ δ' : SymmetricAlgebra K (Module.Dual K V) →ₗ[ρ.dual.symmetricAlgebraInvariants]
            SymmetricAlgebra K (Module.Dual K V),
          (∀ p, SymmetricAlgebra.ι K (Module.Dual K V) ℓ * δ' p =
            p - ρ.dual.symmetricAlgebra g p) → δ' = δ) := by
  obtain ⟨ℓ, hℓ, hker⟩ :=
    (ρ g).fixedSubmodule.exists_dual_ker_eq_of_finrank_quotient_eq_one hg
  have hfix : LinearMap.ker ℓ ≤ LinearMap.ker (ρ g - 1) := by
    rw [hker, LinearMap.fixedSubmodule_eq_ker, Module.End.one_eq_id]
  have hσ := ρ.sub_dual_apply_mem_span_singleton hfix
  have hreg := SymmetricAlgebra.isLeftRegular_ι (R := K) hℓ
  have hident (p) : SymmetricAlgebra.ι K (Module.Dual K V) ℓ *
      ρ.dual.symmetricAlgebraDividedDifference g ℓ hσ hreg p =
      p - ρ.dual.symmetricAlgebra g p := by
    rw [symmetricAlgebraDividedDifference_apply, symmetricAlgebra_apply]
    exact SymmetricAlgebra.ι_mul_dividedDifference p
  refine ⟨ℓ, hℓ, hker, ρ.dual.symmetricAlgebraDividedDifference g ℓ hσ hreg,
    hident, ?_, ?_⟩
  · intro n p hp
    rw [symmetricAlgebraDividedDifference_apply]
    exact SymmetricAlgebra.dividedDifference_mem_homogeneousSubmodule hp
  · intro δ hδ
    ext p
    exact hreg ((hδ p).trans (hident p).symm)

end Representation
