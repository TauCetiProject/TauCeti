/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# Descending maps to quotient manifolds

Let a group `G` act freely and properly discontinuously by `C^n` maps on a `C^n` manifold `M`. The
orbit space `MulAction.orbitRel.Quotient G M` is then a `C^n` manifold whose orbit projection is a
surjective `C^n` local diffeomorphism (`TauCeti.isLocalDiffeomorph_quotientMk`). A map `f : M → N`
that is invariant under `G` descends to the orbit space
(`TauCeti.MulAction.orbitRelQuotientLift`). This file shows that the descended map is `C^m` for
`m ≤ n` exactly when `f` is (continuity is `TauCeti.continuous_orbitRelQuotientLift_iff`), and that
an equivariant `C^m` map between two such manifolds induces a `C^m` map of their orbit spaces
(`MulActionHom.orbitRelQuotientMap`).

Over `𝕜 = ℂ` with `n = m = ∞` this is holomorphic descent: an invariant holomorphic map on a
complex manifold descends to a holomorphic map on the quotient by a free properly discontinuous
group of biholomorphisms. Conversely, a map on the quotient is the descent of its pullback along
the orbit projection (`TauCeti.MulAction.eq_orbitRelQuotientLift_iff`), so it is holomorphic
exactly when that pullback is. The hypotheses ask for an action by holomorphic maps; an action
that is only smooth after restricting scalars to `ℝ` gives the real statement instead.

## Main results

* `TauCeti.contMDiffAt_orbitRelQuotientLift_iff` and `TauCeti.contMDiff_orbitRelQuotientLift_iff`:
  the descent of an invariant map is `C^m`, at the orbit of a point or globally, exactly when the
  map is.
* `TauCeti.contMDiff_orbitRelQuotientMap`: the map of orbit spaces induced by an equivariant
  `C^m` map is `C^m`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§4–5 (holomorphic maps through coverings).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {G M N : Type*} [Group G] [MulAction G M] [TopologicalSpace M] [TopologicalSpace N]
  {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x}
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [ChartedSpace H' N] {m n : ℕ∞ω}
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M]
  [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, the
descent of a `G`-invariant map is `C^m` at the orbit of `x` exactly when the map is `C^m` at
`x`. -/
theorem contMDiffAt_orbitRelQuotientLift_iff (hm : m ≤ n) {x : M} :
    ContMDiffAt I I' m (MulAction.orbitRelQuotientLift f hf)
        (Quotient.mk (MulAction.orbitRel G M) x) ↔ ContMDiffAt I I' m f x := by
  rw [← (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G) x).contMDiffAt_comp_iff hm,
    MulAction.orbitRelQuotientLift_comp_mk]

/-- For a free properly discontinuous action by `C^n` maps on a `C^n` manifold and `m ≤ n`, the
descent of a `G`-invariant map is `C^m` exactly when the map is. For holomorphic actions on complex
manifolds, this is the holomorphic descent of invariant holomorphic maps. -/
theorem contMDiff_orbitRelQuotientLift_iff (hm : m ≤ n) :
    ContMDiff I I' m (MulAction.orbitRelQuotientLift f hf) ↔ ContMDiff I I' m f := by
  rw [← (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G)).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulAction.orbitRelQuotientLift_comp_mk]

variable {K N' : Type*} [Group K] [MulAction K N'] [TopologicalSpace N'] [ChartedSpace H' N']
  [ProperlyDiscontinuousSMul K N'] [ContinuousConstSMul K N'] [IsCancelSMul K N'] [T2Space N']
  [LocallyCompactSpace N'] [IsManifold I' n N'] [ContMDiffConstSMul I' n K N'] {σ : G → K}

/-- For free properly discontinuous actions by `C^n` maps on `C^n` manifolds and `m ≤ n`, a
`C^m` map carrying one action to the other along `σ` induces a `C^m` map of orbit spaces. -/
theorem contMDiff_orbitRelQuotientMap (hm : m ≤ n) {φ : M →ₑ[σ] N'}
    (hφ : ContMDiff I I' m φ) : ContMDiff I I' m (MulActionHom.orbitRelQuotientMap φ) := by
  rw [← (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G)).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((isLocalDiffeomorph_quotientMk (I := I') (n := n) (G := K)).contMDiff.of_le hm).comp hφ

end TauCeti
