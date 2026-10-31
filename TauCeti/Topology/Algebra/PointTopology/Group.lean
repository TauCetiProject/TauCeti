/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Topology.Algebra.PointTopology.Basic

/-!
# The topological group of points of an affine group scheme

Let `H` be a Hopf algebra over `k` and `R` a commutative topological `k`-algebra. The points
`WithConv (H →ₐ[k] R)` form a group under convolution, with `(f * g)(h) = ∑ f(h₍₁₎) * g(h₍₂₎)` and
`f⁻¹ = f ∘ S` for the antipode `S`. When `H` is commutative, these are the `R`-points of the affine
group scheme `Spec H`. With the point topology, the coarsest topology making every evaluation
continuous, this group is a topological group. Each value of a product is a finite sum of products
of values of the factors, so multiplication is continuous when `R` is a topological semiring; each
value of an inverse is a value of the point itself, so inversion is continuous for every topology
on `R`. The coefficients `R` must be commutative, but `H` need not be, and no finiteness or
separation hypothesis on `H` or `R` is needed.

This is the topology on rational points used for groups of points over local fields and adeles:
for an affine group `G` over a nonarchimedean local field `E`, the group `G(E)` is a topological
group in this way, as is `𝒢(O)` for an affine group `𝒢` over the valuation ring `O` of `E`. When
`G` is of finite type over `E`, the points are locally compact
(`TauCeti.PointTopology.locallyCompactSpace_of_finiteType`), so these topological groups carry
the Haar measures and the open subgroups of local representation theory. Without a finiteness
hypothesis the points need not be locally compact: for a polynomial ring in infinitely many
variables they form an infinite product of copies of `E`.

The group of points is functorial in both variables, and the induced maps are continuous: a
bialgebra map `H₁ → H₂` induces the continuous homomorphism `BialgHom.mapDomain` from the points of
`H₂` to those of `H₁`, and a continuous algebra map `R → R'` of coefficients induces the continuous
homomorphism `AlgHom.mapValue`.

## Main declarations

* `TauCeti.PointTopology.instContinuousMulWithConv`: the convolution product on the points of a
  bialgebra is continuous.
* `TauCeti.PointTopology.instContinuousInvWithConv`: the convolution inverse on the points of a
  Hopf algebra is continuous.
* `TauCeti.PointTopology.isTopologicalGroup`: the points of a Hopf algebra form a topological
  group.
* `BialgHom.continuous_mapDomain` and `AlgHom.continuous_mapValue`: functoriality of the points is
  continuous in the coordinate algebra and in continuous maps of coefficients.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and the discussion after it, p. 2.
-/

public section

open Coalgebra WithConv

namespace TauCeti.PointTopology

variable {k H R : Type*} [CommSemiring k] [Semiring H] [CommSemiring R] [Algebra k R]
  [TopologicalSpace R]

section Bialgebra

variable [Bialgebra k H] [IsTopologicalSemiring R]

/-- The convolution product on the points of a bialgebra is continuous for the point topology,
when the coefficients form a topological semiring. -/
instance instContinuousMulWithConv : ContinuousMul (WithConv (H →ₐ[k] R)) where
  continuous_mul := continuous_withConv_iff.2 fun h ↦ by
    -- Writing `Δ h = ∑ i, h₁ i ⊗ h₂ i`, the value of `f * g` at `h` is `∑ i, f (h₁ i) * g (h₂ i)`.
    have hsum (p : WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] R)) : (p.1 * p.2).ofConv h =
        ∑ i ∈ (ℛ k h).index, p.1.ofConv ((ℛ k h).left i) * p.2.ofConv ((ℛ k h).right i) := by
      rw [AlgHom.convMul_apply, ← (ℛ k h).eq, map_sum]
      simp
    simp_rw [hsum]
    refine continuous_finsetSum _ fun i _ ↦ .mul ?_ ?_
    · exact (continuous_eval_ofConv _).comp continuous_fst
    · exact (continuous_eval_ofConv _).comp continuous_snd

end Bialgebra

section HopfAlgebra

variable [HopfAlgebra k H]

/-- The convolution inverse `f ↦ f ∘ S` on the points of a Hopf algebra is continuous for the
point topology, for every topology on the coefficients. -/
instance instContinuousInvWithConv : ContinuousInv (WithConv (H →ₐ[k] R)) where
  continuous_inv := continuous_withConv_iff.2 fun h ↦ by
    simp_rw [WithConv.algHom_inv_apply]
    exact continuous_eval_ofConv _

/-- The points `WithConv (H →ₐ[k] R)` of a Hopf algebra, with the convolution group structure and
the point topology, form a topological group when the coefficients form a topological semiring. -/
instance isTopologicalGroup [IsTopologicalSemiring R] :
    IsTopologicalGroup (WithConv (H →ₐ[k] R)) where

end HopfAlgebra

end TauCeti.PointTopology

section Functoriality

variable {k H₁ H₂ R R' : Type*} [CommSemiring k] [Semiring H₁] [Bialgebra k H₁] [Semiring H₂]
  [Bialgebra k H₂] [CommSemiring R] [Algebra k R] [TopologicalSpace R] [CommSemiring R']
  [Algebra k R'] [TopologicalSpace R']

open TauCeti.PointTopology

/-- Precomposition with a bialgebra map `φ : H₁ → H₂` is a continuous homomorphism from the points
of `H₂` to those of `H₁`. -/
@[continuity, fun_prop]
theorem BialgHom.continuous_mapDomain (φ : H₁ →ₐc[k] H₂) :
    Continuous (mapDomain (A := R) φ) :=
  continuous_withConv_iff.2 fun h ↦ by
    simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    exact continuous_eval_ofConv _

/-- Postcomposition with a continuous algebra map `ψ : R → R'` of coefficients is a continuous
homomorphism from the points with values in `R` to those with values in `R'`. -/
@[fun_prop]
theorem AlgHom.continuous_mapValue {ψ : R →ₐ[k] R'} (hψ : Continuous ψ) :
    Continuous (mapValue (H := H₁) ψ) :=
  continuous_withConv_iff.2 fun h ↦ by
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    exact hψ.comp (continuous_eval_ofConv _)

end Functoriality
