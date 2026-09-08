/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
public import TauCeti.Topology.Homotopy.Covering

/-!
# Semilocal simple connectivity and covering maps

This file relates semilocal simple connectivity to local homeomorphisms and covering maps.

The mechanism for descending semilocal simple connectivity is a local section. If `p : E → X`
is a local homeomorphism and `e : E`, then `p` restricts to a homeomorphism from a neighbourhood
of `e` onto an open set `U ∋ p e`, so a loop inside `U` is the image under `p` of a loop in `E`.
If that loop in `E` is null-homotopic, so is its image. Only local injectivity is used, never path
lifting, so the hypothesis on the total space is stated as "every loop in `E` is null-homotopic
in `E`", which is weaker than `SimplyConnectedSpace E`: it does not ask `E` to be
path-connected, and so applies to a cover whose components are separately simply connected.

The same neighbourhoods run the other way as well: the preimage of a witnessing neighbourhood is
one upstairs, because a covering map is injective on the Hom-sets of the fundamental groupoid.

## Main results

* `TauCeti.semilocallySimplyConnectedAt_of_isLocalHomeomorph`: the image of a point under a local
  homeomorphism whose source has only null-homotopic loops is a point of semilocal simple
  connectivity, in the unbased sense of `SemilocallySimplyConnectedAt`.
* `TauCeti.SemilocallySimplyConnectedSpace.of_isLocalHomeomorph` and
  `TauCeti.SemilocallySimplyConnectedSpace.of_isCoveringMap`: the space-level forms, the second
  saying that the base of a surjective covering map with simply connected total space is
  semilocally simply connected.
* `IsCoveringMap.semilocallySimplyConnectedSpace`: conversely, the total space of a covering map
  over a semilocally simply connected base is semilocally simply connected.

## References

The necessity argument is the classical one from Hatcher, *Algebraic Topology*, the discussion
following Proposition 1.36.
-/

public section

open Set Topology

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- **The image of a local homeomorphism is semilocally simply connected at every point, as soon
as every loop in the source is null-homotopic.**

The witnessing neighbourhood of `p e` is the source of the local inverse of `p` at `e`; a loop
inside it is carried by that local inverse to a loop in `E`, which is null-homotopic by
hypothesis, and pushing the null-homotopy forward along `p` returns the original loop. The
conclusion is the unbased predicate `SemilocallySimplyConnectedAt`, so it covers loops based at
any point of the neighbourhood, not only at `p e`. -/
theorem semilocallySimplyConnectedAt_of_isLocalHomeomorph (hp : IsLocalHomeomorph p)
    (hE : ∀ (e : E) (γ : Path e e), γ.Homotopic (Path.refl e)) (e : E) :
    SemilocallySimplyConnectedAt (p e) := by
  set φ := hp.localInverseAt e
  refine semilocallySimplyConnectedAt_iff.mpr
    ⟨φ.source, φ.open_source, hp.apply_self_mem_localInverseAt_source, ?_⟩
  intro u γ hγ
  have hmem : ∀ t, γ t ∈ φ.source := fun t ↦ hγ ⟨t, rfl⟩
  have hu : u ∈ φ.source := γ.source ▸ hmem 0
  have hpu : p (φ u) = u := hp.apply_localInverseAt_of_mem hu
  -- The local inverse of `p` at `e` carries `γ` to a loop at `φ u` in `E`.
  have key := hE (φ u) (γ.map' (φ.continuousOn_toFun.mono hγ))
  -- Pushing that loop forward along `p` returns `γ`, up to relabelling its endpoints by `hpu`.
  have hdesc : (γ.map' (φ.continuousOn_toFun.mono hγ)).map
      (map_continuous (⟨p, hp.continuous⟩ : C(E, X))) = γ.cast hpu hpu := by
    ext t
    exact hp.apply_localInverseAt_of_mem (hmem t)
  have hrefl : (Path.refl (φ u)).map (map_continuous (⟨p, hp.continuous⟩ : C(E, X)))
      = (Path.refl u).cast hpu hpu := by
    ext t
    exact hpu
  refine (Path.Homotopic.cast_iff hpu hpu).mp ?_
  obtain ⟨F⟩ := key.map (⟨p, hp.continuous⟩ : C(E, X))
  exact ⟨F.cast hdesc hrefl⟩

/-- **A space that is the image of a local homeomorphism whose source has only null-homotopic
loops is semilocally simply connected.** -/
theorem SemilocallySimplyConnectedSpace.of_isLocalHomeomorph (hp : IsLocalHomeomorph p)
    (hsurj : Function.Surjective p)
    (hE : ∀ (e : E) (γ : Path e e), γ.Homotopic (Path.refl e)) :
    SemilocallySimplyConnectedSpace X :=
  .of_forall_semilocallySimplyConnectedAt fun x ↦ by
    obtain ⟨e, rfl⟩ := hsurj x
    exact semilocallySimplyConnectedAt_of_isLocalHomeomorph hp hE e

/-- **The base of a surjective covering map whose total space is simply connected is semilocally
simply connected.** So the standing hypothesis under which the universal cover is built is not
just sufficient but necessary. -/
theorem SemilocallySimplyConnectedSpace.of_isCoveringMap [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    SemilocallySimplyConnectedSpace X :=
  .of_isLocalHomeomorph hp.isLocalHomeomorph hsurj
    fun e γ ↦ (simply_connected_iff_loops_nullhomotopic.mp ‹_›).2 e γ

/-- **Semilocal simple connectivity passes to the total space of a covering map.** A loop in the
preimage of a witnessing neighbourhood downstairs projects to a null-homotopic loop, and a
covering map is injective on the Hom-sets of the fundamental groupoid, so the loop upstairs is
null-homotopic as well.

Together with `IsLocalHomeomorph.locallyPathConnectedSpace` this says that a covering space of a
space satisfying the standing hypotheses of the universal-cover construction satisfies them
again, so covers can be iterated. -/
theorem _root_.IsCoveringMap.semilocallySimplyConnectedSpace [SemilocallySimplyConnectedSpace X]
    (hp : IsCoveringMap p) : SemilocallySimplyConnectedSpace E where
  exists_mem_nhds_loops_nullhomotopic e := by
    obtain ⟨U, hU, hloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_mem_nhds_loops_nullhomotopic (p e)
    refine ⟨p ⁻¹' U, hp.continuous.continuousAt.preimage_mem_nhds hU, fun γ hγ ↦ ?_⟩
    have hdown := hloop (γ.map (map_continuous (⟨p, hp.continuous⟩ : C(E, X)))) hγ
    have key : Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (Path.refl e) := by
      refine hp.injective_path_homotopic_map e e ?_
      simp only [← Path.Homotopic.Quotient.mk_map, Path.map_refl]
      exact Quotient.sound hdown
    exact Quotient.exact key

end TauCeti
