/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.CoadjointNilpotentCone
import TauCeti.Algebra.DualNumber.Basic

/-!
# The coadjoint nilpotent cone of the multiplicative group

The multiplicative group `𝔾ₘ = Spec k[T;T⁻¹]` over a field `k` is commutative, so its coadjoint
action is trivial and its coadjoint nilpotent cone is the origin of the line `𝔤*`: the ideal of
the cone is the augmentation ideal. The cone is not cut out by vanishing at geometric points
alone. Over the dual numbers `k[ε]`, the point `ε` of `𝔤*`, the linear function on the Lie algebra
`𝔤 ≅ k` given by `x ↦ x ε`, becomes zero at every geometric point, but the invariant linear
coordinate takes the value `ε ≠ 0` on it, so it does not lie on the cone.

## Main results

* `TauCeti.MultiplicativeGroup.coadjointNilpotentConeIdeal_eq_ker_algebraMapInv`: the ideal of the
  coadjoint nilpotent cone of `𝔾ₘ` is the augmentation ideal.
* `TauCeti.MultiplicativeGroup.not_coadjointNilpotentConeIdeal_le_ker_lift_smulRight_eps`: the
  point `ε` over the dual numbers is not on the cone.
-/

public section

open scoped LaurentPolynomial DualNumber

namespace TauCeti.MultiplicativeGroup

universe u

variable (k : Type u) [Field k]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k k[T;T⁻¹])

/-- **The coadjoint nilpotent cone of `𝔾ₘ` is the origin.** Its ideal is the augmentation ideal of
the polynomial functions on `𝔤*`. -/
theorem coadjointNilpotentConeIdeal_eq_ker_algebraMapInv :
    coadjointNilpotentConeIdeal k k[T;T⁻¹] =
      RingHom.ker (SymmetricAlgebra.algebraMapInv : SymmetricAlgebra k 𝔤 →ₐ[k] k) :=
  coadjointNilpotentConeIdeal_eq_ker_algebraMapInv_of_isCocomm (CommHopfAlgCat.of k k[T;T⁻¹])

/-- **The point `ε` of `𝔤*` over the dual numbers is not on the coadjoint nilpotent cone.** The
covector `x ↦ x(T) ε` on the Lie algebra of `𝔾ₘ`, with values in `k[ε]`, vanishes modulo `ε`, but
the invariant linear coordinate, which lies in the ideal of the cone, takes the value `ε ≠ 0`
there. -/
theorem not_coadjointNilpotentConeIdeal_le_ker_lift_smulRight_eps :
    ¬ coadjointNilpotentConeIdeal k k[T;T⁻¹] ≤ RingHom.ker (SymmetricAlgebra.lift
      (((tangentLinearEquiv (R := k) (B := k)).toLinearMap ∘ₗ
        (Derivation.cotangentLinearEquiv (R := k) (A := k[T;T⁻¹]) (B := k)).toLinearMap).smulRight
          (ε : k[ε]))) := by
  refine (coadjointNilpotentConeIdeal_le_ker_lift_iff_of_isCocomm
    (CommHopfAlgCat.of k k[T;T⁻¹])).not.mpr fun h ↦ DualNumber.eps_ne_zero (R := k) ?_
  -- Evaluate at the tangent vector with coordinate one.
  have h1 := LinearMap.congr_fun h ((Derivation.cotangentLinearEquiv (R := k) (A := k[T;T⁻¹])
    (B := k)).symm ((tangentLinearEquiv (R := k) (B := k)).symm 1))
  simpa using h1

end TauCeti.MultiplicativeGroup
