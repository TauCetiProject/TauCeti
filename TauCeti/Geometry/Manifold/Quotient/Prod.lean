/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Prod
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Topology.Algebra.GroupAction.Prod
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# Products of quotient manifolds

The quotient of `M × N` by the independent action of `G × K` is canonically diffeomorphic to
`(M / G) × (N / K)`. Both quotients retain Mathlib's installed quotient atlases. The comparison
sends the orbit of `(x, y)` to the pair of the orbits of `x` and `y`.

The result holds at any regularity over any nontrivially normed field. In particular, at infinite
regularity over `ℂ` it is the biholomorphism between these complex quotient manifolds, provided
the actions are holomorphic. Use `open scoped TauCeti.IndependentProd` for the independent
product action.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

open scoped Manifold ContDiff TauCeti.IndependentProd

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M N G K : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [Group G] [Group K]
  [MulAction G M] [MulAction K N] {n : ℕ∞ω}
  [ContinuousConstSMul G M] [ContinuousConstSMul K N]
  [ProperlyDiscontinuousSMul G M] [ProperlyDiscontinuousSMul K N]
  [IsCancelSMul G M] [IsCancelSMul K N]
  [T2Space M] [T2Space N] [LocallyCompactSpace M] [LocallyCompactSpace N]
  [IsManifold I n M] [IsManifold J n N]
  [ContMDiffConstSMul I n G M] [ContMDiffConstSMul J n K N]

/-- The quotient of a product by independent free properly discontinuous `C^n` actions is
canonically `C^n` diffeomorphic to the product of the quotients, on their installed atlases. -/
@[to_additive AddAction.orbitRelQuotientProdDiffeomorph /-- The quotient of a product by independent
free properly discontinuous `C^n` additive actions is canonically `C^n` diffeomorphic to the product
of the quotients, on their installed atlases. -/]
def MulAction.orbitRelQuotientProdDiffeomorph :
    Diffeomorph (I.prod J) (I.prod J)
      (MulAction.orbitRel.Quotient (G × K) (M × N))
      (MulAction.orbitRel.Quotient G M × MulAction.orbitRel.Quotient K N) n where
  toEquiv := MulAction.orbitRelQuotientProdEquiv
  contMDiff_toFun := by
    rw [← (isLocalDiffeomorph_quotientMk (I := I.prod J) (n := n)
      (G := G × K)).contMDiff_comp_iff Quotient.mk_surjective le_rfl]
    apply ((isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G) (M := M)).contMDiff.prodMap
      (isLocalDiffeomorph_quotientMk (I := J) (n := n) (G := K) (M := N)).contMDiff).congr
    intro x
    exact MulAction.orbitRelQuotientProdEquiv_mk (G := G) (K := K) x
  contMDiff_invFun := by
    rw [← ((isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G)).prodMap
      (isLocalDiffeomorph_quotientMk (I := J) (n := n) (G := K))).contMDiff_comp_iff
        (Quotient.mk_surjective.prodMap Quotient.mk_surjective) le_rfl]
    apply (isLocalDiffeomorph_quotientMk (I := I.prod J) (n := n)
      (G := G × K) (M := M × N)).contMDiff.congr
    intro x
    exact MulAction.orbitRelQuotientProdEquiv_symm_mk x.1 x.2

/-- The diffeomorphism sends the orbit of a pair to its component orbits. -/
@[to_additive (attr := simp) AddAction.orbitRelQuotientProdDiffeomorph_mk /-- The diffeomorphism
sends the orbit of a pair to its component orbits. -/]
theorem MulAction.orbitRelQuotientProdDiffeomorph_mk (x : M × N) :
    MulAction.orbitRelQuotientProdDiffeomorph (I := I) (J := J) (n := n) (G := G) (K := K)
      (Quotient.mk _ x) = (Quotient.mk _ x.1, Quotient.mk _ x.2) :=
  MulAction.orbitRelQuotientProdEquiv_mk x

/-- The inverse diffeomorphism sends a pair of orbits to the orbit of a pair. -/
@[to_additive (attr := simp) AddAction.orbitRelQuotientProdDiffeomorph_symm_mk /-- The inverse
diffeomorphism sends a pair of orbits to the orbit of a pair. -/]
theorem MulAction.orbitRelQuotientProdDiffeomorph_symm_mk (x : M) (y : N) :
    (MulAction.orbitRelQuotientProdDiffeomorph (I := I) (J := J) (n := n) (G := G) (K := K)).symm
      (Quotient.mk _ x, Quotient.mk _ y) = Quotient.mk _ (x, y) :=
  MulAction.orbitRelQuotientProdEquiv_symm_mk x y

/-- The quotient-product diffeomorphism preserves the canonical topological comparison. -/
@[to_additive (attr := simp) AddAction.orbitRelQuotientProdDiffeomorph_toHomeomorph /-- The
quotient-product diffeomorphism preserves the canonical topological comparison. -/]
theorem MulAction.orbitRelQuotientProdDiffeomorph_toHomeomorph :
    (MulAction.orbitRelQuotientProdDiffeomorph (I := I) (J := J) (n := n)
      (G := G) (K := K) (M := M) (N := N)).toHomeomorph =
        MulAction.orbitRelQuotientProdHomeomorph := by
  apply Homeomorph.ext
  intro q
  induction q using Quotient.inductionOn with | h x =>
  simp

end TauCeti
