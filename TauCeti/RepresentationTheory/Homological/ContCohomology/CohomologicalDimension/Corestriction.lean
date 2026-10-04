/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.TraceExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Torsion

/-!
# Corestriction in the top degree of strict cohomological dimension

Let `G` be a profinite group with `scd_p G ≤ n` and `U` an open subgroup. Then every `p`-primary
class of `Hⁿ(G, M)` is the corestriction of a `p`-primary class of `Hⁿ(U, M)`, for every discrete
`G`-module `M` (the surjectivity half of NSW (3.3.11)). In the class-module theorem for groups of
strict cohomological dimension two, this is what makes the transfer `G^ab(p) → U^ab(p)` injective.

The proof follows NSW. Corestriction is the inverse of Shapiro's isomorphism followed by the trace
`Coind_U^G M → M`, so its image is the kernel of the connecting map
`δ : Hⁿ(G, M) → Hⁿ⁺¹(G, traceKer G U M)` of the trace short exact sequence
(`TauCeti.ContinuousCohomology.exact_corestriction_delta`). A `p`-primary class has a `p`-primary
connecting image, and the `p`-primary part of `Hⁿ⁺¹(G, -)` vanishes because `scd_p G ≤ n`, so
every `p`-primary class is a corestriction. A preimage can then be chosen `p`-primary:

* in positive degree `Hⁿ(U, M)` is torsion, and a `p`-primary image of a torsion element is the
  image of a `p`-primary element (`TauCeti.exists_mem_primaryComponent_apply_eq`);
* in degree zero a class killed by `p ^ k` comes from `H⁰(G, M[p ^ k])`, the argument applies to
  the `G`-submodule `M[p ^ k]`, whose cohomology over `U` is killed by `p ^ k`, and corestriction
  is natural in the coefficients.

## Main results

* `TauCeti.StrictCohomologicalDimensionLE.corestriction_surjOn_primaryComponent`: under
  `StrictCohomologicalDimensionLE p G n`, corestriction maps the `p`-primary component of
  `Hⁿ(U, M)` onto that of `Hⁿ(G, M)`.
* `TauCeti.corestriction_surjOn_primaryComponent_of_strictCohomologicalDimensionAt_le`: the same
  statement under `scd_p G ≤ n`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.11).
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology _root_.TauCeti.ContinuousCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {U : Subgroup G} [U.FiniteIndex]

/-- Under `StrictCohomologicalDimensionLE p G n`, every `p`-primary class of `Hⁿ(G, M)` is a
corestriction from an open subgroup, of a class that need not be `p`-primary. -/
private theorem StrictCohomologicalDimensionLE.exists_corestriction_eq {n : ℕ}
    (h : StrictCohomologicalDimensionLE.{u} p G n) (hU : IsOpen (U : Set G)) (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
    [ContinuousSMul G M] {x : continuousCohomology n (ofDiscreteModule ℤ G M)}
    (hx : x ∈ AddCommGroup.primaryComponent _ p) :
    ∃ y, corestriction U M hU n y = x := by
  refine ((exact_corestriction_delta U M hU n) x).1 ?_
  obtain ⟨k, hk⟩ := hx
  have hδ : (DiscreteCoind.traceShortExact G U M hU).delta n x ∈
      AddCommGroup.primaryComponent _ p :=
    ⟨k, by rw [← map_nsmul, hk, _root_.map_zero]⟩
  rwa [strictCohomologicalDimensionLE_iff.1 h _ (n + 1) n.lt_succ_self,
    AddSubgroup.mem_bot] at hδ

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- In degree zero, a class of `H⁰(G, M)` killed by `p ^ k` is the image of a class of
`H⁰(G, M[p ^ k])`, where `M[p ^ k]` is the `G`-submodule killed by `p ^ k`. -/
private theorem exists_coeffMap_ker_nsmul_eq (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] {k : ℕ}
    (hK : ∀ g : G, ∀ m ∈ (nsmulAddMonoidHom k : M →+ M).ker, g • m ∈ (nsmulAddMonoidHom k).ker)
    {x : continuousCohomology 0 (ofDiscreteModule ℤ G M)} (hx : k • x = 0) :
    letI := (nsmulAddMonoidHom k : M →+ M).ker.restrictDistribMulAction hK
    ∃ z : continuousCohomology 0 (ofDiscreteModule ℤ G (nsmulAddMonoidHom k : M →+ M).ker),
      coeffMap (ofDiscreteModuleMap (nsmulAddMonoidHom k : M →+ M).ker.subtype.toIntLinearMap
        ((nsmulAddMonoidHom k : M →+ M).ker.restrictDistribMulAction_coe_smul hK)) 0 z = x := by
  set K := (nsmulAddMonoidHom k : M →+ M).ker
  let := K.restrictDistribMulAction hK
  set e := explicitH0IsoContinuousCohomology G M
  -- the invariant element `m` underlying `x` is killed by `k`
  set m : H0 G M := e.inv x
  have hm : k • (m : M) = 0 := by
    rw [← AddSubgroup.coe_nsmul, ← map_nsmul, hx, _root_.map_zero, AddSubgroup.coe_zero]
  let ι : K →+[G] M :=
    { K.subtype with map_smul' := K.restrictDistribMulAction_coe_smul hK }
  let mK : H0 G K := ⟨⟨m, hm⟩, (FixedPoints.mem_addSubgroup G K _).2 fun g ↦ Subtype.ext <|
    (K.restrictDistribMulAction_coe_smul hK g _).trans
      ((FixedPoints.mem_addSubgroup G M _).1 m.2 g)⟩
  refine ⟨(explicitH0IsoContinuousCohomology G K).hom mK, ?_⟩
  have hmK : explicitCoeff0 G K ι mK = m := Subtype.ext (coe_explicitCoeff0 G K ι mK)
  have := explicitH0Iso_coeffMap G K M ι mK
  rw [hmK] at this
  exact this.trans (Iso.inv_hom_id_apply e x)

/-- **Corestriction in the top degree of strict cohomological dimension** (NSW (3.3.11),
surjectivity). For a profinite group `G` with `StrictCohomologicalDimensionLE p G n`, a prime `p`
and an open subgroup `U`, every `p`-primary class of `Hⁿ(G, M)` is the corestriction of a
`p`-primary class of `Hⁿ(U, M)`, for every discrete `G`-module `M`. -/
theorem StrictCohomologicalDimensionLE.corestriction_surjOn_primaryComponent (hp : p.Prime)
    {n : ℕ} (h : StrictCohomologicalDimensionLE.{u} p G n) (hU : IsOpen (U : Set G)) (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
    [ContinuousSMul G M] :
    Set.SurjOn (corestriction U M hU n)
      (AddCommGroup.primaryComponent (continuousCohomology n (ofDiscreteModule ℤ U M)) p)
      (AddCommGroup.primaryComponent (continuousCohomology n (ofDiscreteModule ℤ G M)) p) := by
  intro x hx
  have : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  cases n with
  | succ n =>
    -- `Hⁿ⁺¹(U, M)` is torsion, so a preimage of `x` can be replaced by a `p`-primary one
    obtain ⟨y, rfl⟩ := h.exists_corestriction_eq hU M hx
    exact exists_mem_primaryComponent_apply_eq (corestriction U M hU (n + 1)).hom hp
      (isAddTorsion_continuousCohomology n y) hx
  | zero =>
    -- `x` comes from `H⁰(G, M[p ^ k])`, whose classes are corestrictions of classes killed by
    -- `p ^ k`
    obtain ⟨k, hk⟩ := hx
    set K := (nsmulAddMonoidHom (p ^ k) : M →+ M).ker
    have hK : ∀ g : G, ∀ m ∈ K, g • m ∈ K := fun g m hm ↦ by
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hm ⊢
      rw [smul_comm, hm, smul_zero]
    let := K.restrictDistribMulAction hK
    have : ContinuousSMul G K := K.restrictDistribMulAction_continuousSMul hK
    let ι : K →+[G] M :=
      { K.subtype with map_smul' := K.restrictDistribMulAction_coe_smul hK }
    have hKk (v : K) : p ^ k • v = 0 := Subtype.ext (AddMonoidHom.mem_ker.1 v.2)
    obtain ⟨z, rfl⟩ := exists_coeffMap_ker_nsmul_eq M hK hk
    obtain ⟨y, rfl⟩ := h.exists_corestriction_eq hU K
      ⟨k, nsmul_continuousCohomology_eq_zero (X := ofDiscreteModule ℤ G K) hKk 0 z⟩
    refine ⟨coeffMap (ofDiscreteModuleMap (G := U) ι.toAddMonoidHom.toIntLinearMap
      fun u m ↦ _root_.map_smul ι (u : G) m) 0 y, ⟨k, ?_⟩, ?_⟩
    · rw [← map_nsmul, nsmul_continuousCohomology_eq_zero (X := ofDiscreteModule ℤ U K) hKk 0 y,
        _root_.map_zero]
    · exact (ConcreteCategory.congr_hom (corestriction_naturality U K hU ι 0) y).symm

/-- **Corestriction in the top degree of strict cohomological dimension** (NSW (3.3.11),
surjectivity), stated through `scd_p G ≤ n`: for an open subgroup `U` of a profinite group `G`,
corestriction maps the `p`-primary component of `Hⁿ(U, M)` onto that of `Hⁿ(G, M)`. -/
theorem corestriction_surjOn_primaryComponent_of_strictCohomologicalDimensionAt_le (hp : p.Prime)
    {n : ℕ} (h : strictCohomologicalDimensionAt.{u} p G ≤ n) (hU : IsOpen (U : Set G)) (M : Type u)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
    [ContinuousSMul G M] :
    Set.SurjOn (corestriction U M hU n)
      (AddCommGroup.primaryComponent (continuousCohomology n (ofDiscreteModule ℤ U M)) p)
      (AddCommGroup.primaryComponent (continuousCohomology n (ofDiscreteModule ℤ G M)) p) :=
  ((strictCohomologicalDimensionAt_le_iff p G n).1 h).corestriction_surjOn_primaryComponent hp hU M

end TauCeti
