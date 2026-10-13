/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import TauCeti.Topology.Algebra.IsUniformGroup.Quotient
public import TauCeti.Topology.Algebra.IsUniformGroup.Submodule
public import TauCeti.Topology.Algebra.ZeroSequenceOfUnits

/-!
# Modules over a ring with a zero sequence of units

Let `A` be a topological ring admitting a sequence of units converging to zero, such as a Tate ring.
Over such a ring a topological module has no proper submodule with nonempty interior
(Mathlib's `Submodule.eq_top_of_nonempty_interior'`, through the instance
`TauCeti.HasZeroSequenceOfUnits.nhdsWithin_isUnit_neBot`), and this file draws two consequences of
that for complete metrisable modules.

The first concerns Banach's theorem for Tate rings, Wedhorn's Theorem 6.16: for an `A`-linear map
`u : M → N` out of a complete first-countable module, any two of *(a) `N` is complete*, *(b) `u` is
surjective* and *(c) `u` is open* imply the third. That (a) and (b) imply (c) is Henkel's open
mapping theorem, `TauCeti.HasZeroSequenceOfUnits.isOpenMap`, which asks in addition that `u` be
continuous at zero, `M` nonarchimedean and `N` a Hausdorff Baire space. The other two
implications are proved here. An open linear map is surjective outright, its range being an open
submodule, so (c) alone implies (b). A continuous open linear map is then an open quotient map, so
its target is complete by `IsOpenQuotientMap.completeSpace`: (c) implies (a) for continuous `u`.

The second is the converse half of Wedhorn's Proposition 6.17: a complete first-countable module all
of whose submodules are closed is noetherian. Given an ascending chain of submodules, their union
`S` is closed, hence complete and so a Baire space. The members of the chain are closed in `S` and
cover it, so one of them has interior in `S`. That member is then an open submodule of `S`, hence
all of `S`, and the chain stops there.

Over a complete Hausdorff Tate ring the forward half, that every submodule of a noetherian module is
closed, is `TauCeti.Huber.isClosed_of_isNoetherian`; the two halves are assembled into Wedhorn's
equivalence in `TauCeti.Huber.isNoetherian_iff_forall_isClosed`.

## Main results

* `TauCeti.HasZeroSequenceOfUnits.surjective_of_isOpenMap`: an open linear map is surjective.
* `TauCeti.HasZeroSequenceOfUnits.completeSpace_of_isOpenMap`: a continuous open linear map out of
  a complete first-countable module has a complete target.
* `TauCeti.HasZeroSequenceOfUnits.isNoetherian_of_forall_isClosed`: a complete first-countable
  module whose submodules are all closed is noetherian.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 6.16 and
  Proposition 6.17.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Topology
open scoped Uniformity

namespace TauCeti

namespace HasZeroSequenceOfUnits

variable {A : Type*} [Ring A] [TopologicalSpace A] [HasZeroSequenceOfUnits A]

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- **An open linear map is surjective** (Wedhorn, Theorem 6.16, *(c) ⇒ (b)*). Its range is an
open submodule, and a submodule with nonempty interior is everything when zero is a limit of
units. No topology on `M` is involved beyond the openness of `f`. -/
theorem surjective_of_isOpenMap [TopologicalSpace M] [TopologicalSpace N] [ContinuousAdd N]
    [ContinuousSMul A N] (f : M →ₗ[A] N) (hf : IsOpenMap f) : Function.Surjective f := by
  refine LinearMap.range_eq_top.mp <| Submodule.eq_top_of_nonempty_interior' _ ⟨0, ?_⟩
  rw [LinearMap.coe_range, hf.isOpen_range.interior_eq]
  exact ⟨0, map_zero f⟩

/-- **A continuous open linear map out of a complete first-countable module has a complete
target** (Wedhorn, Theorem 6.16, *(b) and (c) ⇒ (a)*). The map is surjective by
`TauCeti.HasZeroSequenceOfUnits.surjective_of_isOpenMap`, hence an open quotient map, and an
open quotient of a complete first-countable group is complete. -/
theorem completeSpace_of_isOpenMap [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
    [(𝓤 M).IsCountablyGenerated] [UniformSpace N] [IsUniformAddGroup N] [ContinuousSMul A N]
    (f : M →ₗ[A] N) (hfc : Continuous f) (hf : IsOpenMap f) : CompleteSpace N :=
  IsOpenQuotientMap.completeSpace (f := f) ⟨surjective_of_isOpenMap f hf, hfc, hf⟩

/-- **A complete first-countable module all of whose submodules are closed is noetherian**
(Wedhorn, Proposition 6.17, *if* direction).

Given an ascending chain of submodules, the union `S` of the chain is closed, so it is complete
and, being metrisable, a Baire space. The members of the chain are closed in `S` and cover it, so
one of them has nonempty interior in `S`. It is then all of `S` by
`Submodule.eq_top_of_nonempty_interior'`, so the chain is constant from there on. -/
theorem isNoetherian_of_forall_isClosed [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
    [(𝓤 M).IsCountablyGenerated] [ContinuousSMul A M]
    (h : ∀ N : Submodule A M, IsClosed (N : Set M)) : IsNoetherian A M := by
  refine monotone_stabilizes_iff_noetherian.mp fun f ↦ ?_
  let S : Submodule A M := ⨆ n, f n
  have : CompleteSpace S := (h S).completeSpace_coe
  -- The members of the chain, seen inside `S`, are closed and cover `S`.
  let C : ℕ → Submodule A S := fun n ↦ (f n).comap S.subtype
  have hC : ∀ n, IsClosed (C n : Set S) := fun n ↦ (h (f n)).preimage continuous_subtype_val
  have hcover : ⋃ n, (C n : Set S) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    exact (Submodule.mem_iSup_of_directed f f.monotone.directed_le).mp x.2
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hC hcover
  -- That member is open in `S`, hence all of `S`.
  have hS : S ≤ f n :=
    Submodule.comap_subtype_eq_top.mp (Submodule.eq_top_of_nonempty_interior' _ hn)
  exact ⟨n, fun m hm ↦ le_antisymm (f.monotone hm) ((le_iSup f m).trans hS)⟩

end HasZeroSequenceOfUnits

end TauCeti
