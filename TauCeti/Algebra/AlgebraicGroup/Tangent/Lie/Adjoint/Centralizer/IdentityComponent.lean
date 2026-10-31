/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# The identity component of a centralizer

Let `G = Spec H` be a finite-type affine group over an algebraically closed field `k`, with Lie
algebra `𝔤`, and let `x ∈ 𝔤`. The centralizer `C_G(x)` is a closed subgroup scheme, possibly
disconnected. Its identity component `C_G(x)⁰` is the closed subgroup
`(centralizerHopfIdeal H x).identityComponent` of `G`.

* `C_G(x)⁰` has the same Lie algebra `ker (ad x)` as `C_G(x)`, and in characteristic zero the
  same dimension `dim ker (ad x)`.
* For a rational point `g` of `G`, `C_G(Ad(g) x)⁰ = g C_G(x)⁰ g⁻¹`, as closed subgroup schemes.

The finite component group `A(x) = π₀(C_G(x))` is the group of connected components of
`Spec (H ⧸ C_G(x))`. Conjugation by `g` identifies `A(x)` with `A(Ad(g) x)`: this is
`TauCeti.HopfIdeal.componentGroupConjugationMulEquiv` applied to the equality of Hopf ideals
`TauCeti.centralizerHopfIdeal_basePointsRepresentation`, and it sends the component of a rational
point `y` of `C_G(x)` to the component of `gyg⁻¹`.

In the theory of nilpotent orbits these are the centralizer data attached to a nilpotent element
`x`: the identity component and the component group `A(x)` of its centralizer.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §§1.3 and 6.1.
* J. S. Milne, *Algebraic Groups* (2017), Section 5 and Chapter 10.
-/

public section

namespace TauCeti

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

attribute [local instance] Derivation.adjointComodule

/-- **The identity component of a centralizer.** The identity component of `C_G(x)` has the
same Lie algebra as `C_G(x)`, the kernel of `ad x`. -/
theorem lieSubalgebra_identityComponent_centralizerHopfIdeal
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    ((centralizerHopfIdeal H x).identityComponent.lieSubalgebra (B := k)).toSubmodule =
      LinearMap.ker (LieAlgebra.ad k (Derivation k H (Bialgebra.CounitAlgebra k H k))
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) := by
  rw [HopfIdeal.lieSubalgebra_identityComponent, lieSubalgebra_centralizerHopfIdeal]

/-- **The dimension of the identity component of a centralizer.** Over an algebraically closed
field of characteristic zero, `dim C_G(x)⁰ = dim ker (ad x)`. -/
theorem ringKrullDim_quotient_identityComponent_centralizerHopfIdeal [CharZero k]
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    ringKrullDim (H ⧸ (centralizerHopfIdeal H x).identityComponent.toIdeal) =
      Module.finrank k
        (LinearMap.ker (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)) := by
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H (centralizerHopfIdeal H x)) :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k _)
  rw [HopfIdeal.ringKrullDim_quotient_identityComponent_of_smooth,
    ringKrullDim_quotient_centralizerHopfIdeal]

/-- **Conjugation of identity components of centralizers.** For a rational point `g`,
`C_G(Ad(g) x)⁰ = g C_G(x)⁰ g⁻¹`. -/
theorem identityComponent_centralizerHopfIdeal_basePointsRepresentation
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (g : WithConv (H →ₐ[k] k)) :
    (centralizerHopfIdeal H
        (Comodule.basePointsRepresentation (H := H) _ g x)).identityComponent =
      (centralizerHopfIdeal H x).identityComponent.conjugate g := by
  rw [centralizerHopfIdeal_basePointsRepresentation, HopfIdeal.identityComponent_conjugate]

end TauCeti
