/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Eigenvector
public import TauCeti.Algebra.Lie.Killing.AdNilpotent
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Ad-nilpotent elements in finite-dimensional representations

Over a field of characteristic zero, an ad-nilpotent element of a finite-dimensional Lie
algebra with nondegenerate Killing form acts nilpotently in every finite-dimensional
representation. This is the semisimple part of the nilpotence-preservation argument in
Hochschild's strengthening of Ado's theorem.

The Killing form supplies `t` with `⁅x, t⁆ = x`. Applying a representation gives a nonzero
commutator eigenvalue for the operator representing `x`. This operator is algebraic because
the representation is finite dimensional, so the associative derivation result proves it
nilpotent. Neither algebraic closedness nor a choice of `sl₂`-triple is needed.

## Main results

* `TauCeti.isNilpotent_apply_of_lie_eq_smul`: a nonzero adjoint eigenvalue forces nilpotence
  in every finite-dimensional representation.
* `TauCeti.isNilpotent_toEnd_of_isNilpotent_ad`: ad-nilpotence in a finite-dimensional Killing
  Lie algebra implies nilpotence in every finite-dimensional Lie module.
* `TauCeti.isNilpotent_apply_of_isNilpotent_ad`: the same result for an explicit Lie
  homomorphism into an endomorphism algebra.

## References

* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966), 531–533.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

-- Endomorphism algebras carry the associative commutator bracket locally.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- An element with nonzero eigenvalue for an adjoint action has nilpotent image in every
finite-dimensional representation in characteristic zero. The Lie algebra need not be
finite dimensional or semisimple. -/
theorem isNilpotent_apply_of_lie_eq_smul {ρ : L →ₗ⁅K⁆ Module.End K M}
    {x y : L} {c : K} (hc : c ≠ 0) (hxy : ⁅y, x⁆ = c • x) : IsNilpotent (ρ x) := by
  apply derivationLieAlgebra.isNilpotent_of_isAlgebraic_of_apply_eq_smul
    (innerDerivation K (ρ y)) (IsAlgebraic.of_finite K _) hc
  rw [coe_innerDerivation, ad_apply, ← LieHom.map_lie, hxy, map_smul]

/-- An ad-nilpotent element has nilpotent image under every finite-dimensional representation
of a Killing Lie algebra over a characteristic-zero field. -/
theorem isNilpotent_apply_of_isNilpotent_ad [FiniteDimensional K L] [IsKilling K L]
    {ρ : L →ₗ⁅K⁆ Module.End K M} {x : L} (hx : IsNilpotent (ad K L x)) :
    IsNilpotent (ρ x) := by
  obtain ⟨t, ht⟩ := exists_lie_eq_self_of_isNilpotent_ad hx
  apply isNilpotent_apply_of_lie_eq_smul (y := t) (c := -1) (by simp)
  simpa [ht] using (lie_skew t x).symm

/-- An ad-nilpotent element of a finite-dimensional Killing Lie algebra acts nilpotently in
every finite-dimensional Lie module over a characteristic-zero field. -/
theorem isNilpotent_toEnd_of_isNilpotent_ad [LieRingModule L M] [LieModule K L M]
    [FiniteDimensional K L] [IsKilling K L] {x : L} (hx : IsNilpotent (ad K L x)) :
    IsNilpotent (toEnd K L M x) :=
  isNilpotent_apply_of_isNilpotent_ad hx

end TauCeti
