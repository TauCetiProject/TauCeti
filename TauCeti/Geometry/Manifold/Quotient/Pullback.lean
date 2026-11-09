/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Equivariant
public import TauCeti.Geometry.Manifold.Instances.Comap

/-!
# Manifold comparison with the pullback of an orbit space

For an equivariant map `p : X → Y` and a quotient covering `β : Y → Z`, the map
`x ↦ (p x, [x])` identifies `X` with the literal pullback `Y ×_Z (X/G)`.
If the orbit projection `X → X/G` is a local diffeomorphism, this identification is a
diffeomorphism for the atlas pulled back from `X/G` through the second projection.
No atlas on the fibre product is an input. Its topology is inherited from the product.

In particular, the comparison is biholomorphic for holomorphic quotient families,
including those with nontrivial monodromy around a puncture.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 21
  (quotient manifolds).
-/

public section

open Function
open scoped Manifold ContDiff

namespace MulActionHom

variable {G X Y Z : Type*} [Group G] [MulAction G X] [MulAction G Y]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [ContinuousConstSMul G X]
  (p : X →[G] Y) (β : Y → Z) (f : MulAction.orbitRel.Quotient G X → Z)
  (hf : ∀ x, f (Quotient.mk _ x) = β (p x))
  (hp : Continuous p) (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f)
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V : Type*} [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 V H}
  [ChartedSpace H X] [ChartedSpace H (MulAction.orbitRel.Quotient G X)] {n : ℕ∞ω}

/-- The canonical comparison with the pullback of the orbit space is a `C^n` diffeomorphism.
The target atlas is constructed by lifting the orbit space atlas through local inverse
branches of the base covering, via the second pullback projection. -/
noncomputable def orbitRelQuotientPullbackDiffeomorph
    (hq : IsLocalDiffeomorph I I n (Quotient.mk (MulAction.orbitRel G X))) :
    letI := (hβ.isLocalHomeomorph.pullback_snd hfc).chartedSpaceComap (H := H)
    Diffeomorph I I X (β.Pullback f) n := by
  let e := p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc
  let hs := hβ.isLocalHomeomorph.pullback_snd hfc
  let _ := hs.chartedSpaceComap (H := H)
  refine { e.toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply hs.contMDiff_chartedSpaceComap_iff.2
    refine ⟨e.continuous, ?_⟩
    -- The second projection of the comparison is exactly the orbit projection.
    simpa only [comp_def, e, Homeomorph.coe_toEquiv, orbitRelQuotientPullbackHomeomorph_apply,
      Pullback.snd, orbitRelQuotientPullback_val] using hq.contMDiff
  · apply ContMDiff.of_comp_isLocalDiffeomorph hq e.symm.continuous
    simpa only [comp_def, e, mk_orbitRelQuotientPullbackHomeomorph_symm] using
      hs.isLocalDiffeomorph_chartedSpaceComap.contMDiff (I := I) (n := n)

/-- The underlying homeomorphism of the differentiable comparison is the canonical
homeomorphism of the literal pullback. -/
@[simp] theorem orbitRelQuotientPullbackDiffeomorph_toHomeomorph
    (hq : IsLocalDiffeomorph I I n (Quotient.mk (MulAction.orbitRel G X))) :
    letI := (hβ.isLocalHomeomorph.pullback_snd hfc).chartedSpaceComap (H := H)
    (p.orbitRelQuotientPullbackDiffeomorph β f hf hp hβ hfc hq).toHomeomorph =
      p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc := (rfl)

end MulActionHom
