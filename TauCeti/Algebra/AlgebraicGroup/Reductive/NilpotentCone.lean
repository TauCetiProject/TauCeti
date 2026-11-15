/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Lie
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone

/-!
# The nilpotent cone of a reductive group

Let `G = Spec H` be a reductive affine group over an algebraically closed field `k` of
characteristic zero, with Lie algebra `𝔤`. Then `𝔤` is reductive, `𝔤 = Z(𝔤) ⊕ ⁅𝔤, 𝔤⁆`, and the
invariant polynomial functions on `𝔤` include the linear functions vanishing on `⁅𝔤, 𝔤⁆`. So the
nilpotent cone, the zero fibre of the adjoint quotient (`TauCeti.nilpotentConeIdeal`), has zero
central coordinate: its `k`-points are the `ad`-nilpotent elements of the derived ideal.

This is smaller than the set of `ad`-nilpotent elements of `𝔤` as soon as the center of `𝔤` is
nonzero: every central element is `ad`-nilpotent, and the `ad`-nilpotent elements are the sums of a
central element and a point of the cone (`TauCeti.isNilpotent_ad_iff_exists_mem_center_add`). When
the Killing form of `𝔤` is nondegenerate the two sets agree
(`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff`).

## Main results

* `nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad`, in the namespace
  `TauCeti.reductiveCommHopfAlgProperty`: the `k`-points of the nilpotent cone of a reductive group
  are the `ad`-nilpotent elements of `⁅𝔤, 𝔤⁆`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §1.3.
* B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. 85 (1963),
  327–404.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **The rational points of the nilpotent cone of a reductive group.** For a reductive affine
group over an algebraically closed field of characteristic zero, an element `x` of the Lie algebra
`𝔤` lies on the nilpotent cone, that is evaluation at `x` kills its ideal, exactly when `x` lies in
the derived ideal `⁅𝔤, 𝔤⁆` and `ad x` is nilpotent. In particular a nonzero central element of `𝔤`
does not lie on the cone. -/
theorem nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad
    (hH : reductiveCommHopfAlgProperty k H) {x : 𝔤} :
    nilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 x)) ↔
      x ∈ LieAlgebra.derivedSeries k 𝔤 1 ∧ IsNilpotent (LieAlgebra.ad k 𝔤 x) :=
  have := hH.geometricallyConnected.connectedSpace k H.obj
  have := hH.hasCentralRadical_dual_cotangentSpace
  TauCeti.nilpotentConeIdeal_le_ker_lift_eval_iff_mem_derivedSeries_and_isNilpotent_ad

end TauCeti.reductiveCommHopfAlgProperty
