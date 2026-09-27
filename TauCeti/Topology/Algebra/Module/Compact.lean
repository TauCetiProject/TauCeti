/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import TauCeti.Topology.Algebra.Module.Quotient
public import TauCeti.Topology.Algebra.Nonarchimedean.Profinite
public import TauCeti.Topology.Algebra.Nonarchimedean.Quotient

/-!
# Compact modules over a compact ring

A **compact module** over a topological ring `R` is a topological `R`-module `M` that is a
compact, totally disconnected topological additive group with continuous scalar action. For `R`
compact these are the modules that are inverse limits of finite modules with surjective transition
maps: the profinite modules. The case of interest is `R = ℤ_p⟦Γ⟧`, the completed group algebra of
a profinite group `Γ`, whose compact modules are the objects Iwasawa theory and the classification
of Demushkin groups compute with.

Two facts make a compact module accessible level by level. First, when `R` is compact, the open
submodules of a nonarchimedean topological `R`-module form a basis of neighbourhoods of zero: an
open additive subgroup `V` contains an open submodule, because by compactness of `R` and
continuity of the action there is a neighbourhood `W` of zero with `R • W ⊆ V`, and the
submodule spanned by `W` is open and lies in `V`. This is Mathlib's `IsLinearTopology R M`, and
in a `T1` module it gives separatedness: an element lying in every open submodule is zero.
Second, when `M` is compact, a compatible family of elements of the quotients `M ⧸ N`, `N` ranging
over the open submodules, comes from an element of `M`, by Cantor's intersection theorem applied
to the closed cosets it describes. Together these are the inverse-limit description
`M ≅ lim_N M ⧸ N` of a compact module over a compact ring.

The predicate `IsCompactModule R M` packages the four topological hypotheses so that they can be
carried as a single hypothesis on a module whose topology is given by hand; its API restates the
two facts above for it, shows that it passes to quotients by closed submodules, and records the
witness that a compact totally disconnected topological ring is a compact module over itself.

## Main definitions

* `TauCeti.IsCompactModule R M`: `M` is a compact totally disconnected topological `R`-module.

## Main results

* `Submodule.FG.isCompact`: over a compact semiring, a finitely generated submodule of a
  topological module is compact.
* `Submodule.span_eq_top_of_dense_closure`: over a compact ring, a finite set spans a Hausdorff
  module as soon as a subset of its span generates a dense additive subgroup.
* `OpenAddSubgroup.exists_submodule_isOpen_subset`: over a compact ring, an open additive subgroup
  of a topological module contains an open submodule.
* `TauCeti.NonarchimedeanAddGroup.isLinearTopology`: over a compact ring, a nonarchimedean
  topological module is linearly topologized.
* `TauCeti.IsLinearTopology.eq_zero_of_forall_mem_of_isOpen`,
  `TauCeti.IsLinearTopology.sInf_isOpen_eq_bot`: in a `T1` linearly topologized module the open
  submodules intersect in zero.
* `TauCeti.IsLinearTopology.continuous_iff_forall_continuous_mkQ`: a map into a linearly
  topologized module is continuous exactly when it is continuous modulo every open submodule.
* `TauCeti.exists_forall_mkQ_eq`: for a compact topological module, the map to compatible
  families in its quotients by open submodules is surjective.
* `TauCeti.existsUnique_forall_mkQ_eq`: a compact `T1` linearly topologized module is the
  inverse limit of its quotients by open submodules.
* `TauCeti.IsCompactModule.isLinearTopology`,
  `TauCeti.IsCompactModule.eq_zero_of_forall_mem_of_isOpen`,
  `TauCeti.IsCompactModule.existsUnique_forall_mkQ_eq`, `TauCeti.IsCompactModule.quotient`,
  `TauCeti.IsCompactModule.self`: the same statements for the predicate, its stability under
  quotients by closed submodules, and the self-module witness.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.1.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 1.5.
-/

public section

open Filter Topology

section CompactSemiring

variable {R M : Type*} [Semiring R] [TopologicalSpace R] [CompactSpace R] [AddCommMonoid M]
  [Module R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M]

/-- **A finitely generated submodule of a topological module over a compact semiring is compact.**
Unlike Mathlib's `Submodule.isCompact_of_fg`, the semiring need not be commutative; the completed
group algebra of a nonabelian profinite group is the case that needs this. -/
theorem Submodule.FG.isCompact {N : Submodule R M} (hN : N.FG) : IsCompact (N : Set M) := by
  -- The proof is that of Mathlib's `Submodule.isCompact_of_fg` (Andrew Yang): the submodule is the
  -- image of a finite power of `R` under the continuous linear-combination map. Commutativity of
  -- `R` is never used.
  obtain ⟨s, hs⟩ := hN
  have : LinearMap.range (Fintype.linearCombination R (α := s) Subtype.val) = N := by
    simp [hs]
  rw [← this]
  refine isCompact_range ?_
  simp only [Fintype.linearCombination, Finset.univ_eq_attach, LinearMap.coe_mk, AddHom.coe_mk]
  fun_prop

end CompactSemiring

section CompactRing

variable {R M : Type*} [Ring R] [TopologicalSpace R] [CompactSpace R] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [T2Space M] [ContinuousAdd M] [ContinuousSMul R M]

/-- **A finite set spans a Hausdorff module over a compact ring as soon as a subset of its span
generates a dense additive subgroup**: the span is compact, hence closed, and contains a dense
set. -/
theorem Submodule.span_eq_top_of_dense_closure {T S : Set M} (hT : T.Finite)
    (hS : S ⊆ Submodule.span R T) (hd : Dense (AddSubgroup.closure S : Set M)) :
    Submodule.span R T = ⊤ := by
  have hle : (AddSubgroup.closure S : Set M) ⊆ Submodule.span R T := by
    rw [← Submodule.coe_toAddSubgroup]
    exact SetLike.coe_subset_coe.2 ((AddSubgroup.closure_le _).2 hS)
  exact top_unique fun x _ ↦ closure_minimal hle (Submodule.fg_span hT).isCompact.isClosed (hd x)

end CompactRing

namespace TauCeti

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]

section CompactRing

variable [TopologicalSpace R] [CompactSpace R] [ContinuousSMul R M]

/-- Over a compact ring `R`, every open additive subgroup `V` of a topological `R`-module
contains an open submodule: by compactness of `R` there is a neighbourhood `W` of zero with
`R • W ⊆ V`, and the submodule spanned by `W` is open and contained in `V`. -/
theorem _root_.OpenAddSubgroup.exists_submodule_isOpen_subset [SeparatelyContinuousAdd M]
    (V : OpenAddSubgroup M) : ∃ N : Submodule R M, IsOpen (N : Set M) ∧ (N : Set M) ⊆ V := by
  -- For each scalar `r`, continuity of `(r, 0) ↦ r • 0 = 0` gives neighbourhoods `U r` of `r`
  -- and `W r` of `0` with `U r • W r ⊆ V`.
  have key : ∀ r : R, ∃ U ∈ 𝓝 r, ∃ W ∈ 𝓝 (0 : M), ∀ s ∈ U, ∀ m ∈ W, s • m ∈ V := by
    intro r
    have h : (fun p : R × M ↦ p.1 • p.2) ⁻¹' (V : Set M) ∈ 𝓝 (r, 0) :=
      (continuous_smul.continuousAt (x := (r, 0))).preimage_mem_nhds
        (by simpa using V.mem_nhds_zero)
    obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp h
    exact ⟨U, hU, W, hW, fun s hs m hm ↦ hUW (Set.mk_mem_prod hs hm)⟩
  choose U hU W hW hUW using key
  -- Finitely many of the `U r` cover `R`, and the intersection `W₀` of the corresponding `W r`
  -- is a neighbourhood of zero with `R • W₀ ⊆ V`.
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U fun r _ ↦ hU r
  have hW₀ : (⋂ r ∈ t, W r) ∈ 𝓝 (0 : M) := (biInter_finset_mem t).mpr fun r _ ↦ hW r
  have hsmul : ∀ s : R, ∀ m ∈ ⋂ r ∈ t, W r, s • m ∈ V := by
    intro s m hm
    obtain ⟨r, hr, hs⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ s))
    exact hUW r s hs m (Set.mem_iInter₂.mp hm r hr)
  refine ⟨Submodule.span R (⋂ r ∈ t, W r), ?_, fun m hm ↦ ?_⟩
  · exact (Submodule.span R _).toAddSubgroup.isOpen_of_mem_nhds
      (mem_of_superset hW₀ Submodule.subset_span)
  · -- Every element of the span is killed into `V` by every scalar, by induction on the span.
    suffices ∀ s : R, s • m ∈ V by simpa using this 1
    refine Submodule.span_induction (p := fun m _ ↦ ∀ s : R, s • m ∈ V) ?_ ?_ ?_ ?_ hm
    · exact fun m hm s ↦ hsmul s m hm
    · intro s
      rw [smul_zero]
      exact zero_mem V
    · intro x y _ _ hx hy s
      rw [smul_add]
      exact add_mem (hx s) (hy s)
    · intro a x _ hx s
      rw [smul_smul]
      exact hx (s * a)

variable (R M) in
/-- Over a compact ring, a nonarchimedean topological module is linearly topologized: its open
submodules form a basis of neighbourhoods of zero. -/
instance (priority := 100) NonarchimedeanAddGroup.isLinearTopology [NonarchimedeanAddGroup M] :
    IsLinearTopology R M := by
  refine .mk_of_hasBasis' R (S := Submodule R M) (p := fun N : Submodule R M ↦ IsOpen (N : Set M))
    (s := id) (hasBasis_iff.mpr fun U ↦ ⟨fun hU ↦ ?_, ?_⟩) fun N r m hm ↦ N.smul_mem r hm
  · obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
    obtain ⟨N, hN, hNV⟩ := V.exists_submodule_isOpen_subset (R := R)
    exact ⟨N, hN, hNV.trans hV⟩
  · rintro ⟨N, hN, hNU⟩
    exact mem_of_superset (hN.mem_nhds N.zero_mem) hNU

end CompactRing

section Separated

variable [ContinuousAdd M] [IsLinearTopology R M] [T1Space M]

/-- In a `T1` linearly topologized module, an element lying in every open submodule is zero. -/
theorem IsLinearTopology.eq_zero_of_forall_mem_of_isOpen {x : M}
    (h : ∀ N : Submodule R M, IsOpen (N : Set M) → x ∈ N) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN, hNx⟩ := (IsLinearTopology.hasBasis_open_submodule R (M := M)).mem_iff.mp
    (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr (Ne.symm hx)))
  exact hNx (h N hN) rfl

variable (R M) in
/-- In a `T1` linearly topologized module, the open submodules intersect in zero. -/
@[simp]
theorem IsLinearTopology.sInf_isOpen_eq_bot :
    sInf {N : Submodule R M | IsOpen (N : Set M)} = ⊥ :=
  eq_bot_iff.mpr fun _ hx ↦ (Submodule.mem_bot R).mpr <|
    IsLinearTopology.eq_zero_of_forall_mem_of_isOpen fun N hN ↦ Submodule.mem_sInf.mp hx N hN

end Separated

section Continuity

variable [IsTopologicalAddGroup M] [IsLinearTopology R M]

variable (R) in
/-- **Continuity level by level.** A map into a linearly topologized topological module is
continuous exactly when its compositions with the quotient maps onto the quotients by the open
submodules are continuous. -/
theorem IsLinearTopology.continuous_iff_forall_continuous_mkQ {X : Type*} [TopologicalSpace X]
    {f : X → M} :
    Continuous f ↔ ∀ N : Submodule R M, IsOpen (N : Set M) → Continuous (N.mkQ ∘ f) := by
  refine ⟨fun hf N _ ↦ N.continuous_mkQ.comp hf, fun h ↦ continuous_iff_continuousAt.2 fun x ↦ ?_⟩
  rw [ContinuousAt, ← map_add_left_nhds_zero (f x),
    ((IsLinearTopology.hasBasis_open_submodule R).map _).tendsto_right_iff]
  intro N hN
  have := Submodule.Quotient.discreteTopology_of_isOpen N hN
  filter_upwards [((h N hN).isOpen_preimage _ (isOpen_discrete {N.mkQ (f x)})).mem_nhds
    (by simp)] with z hz
  exact ⟨f z - f x, (Submodule.Quotient.eq N).1 hz, add_sub_cancel _ _⟩

end Continuity

section Compact

variable [CompactSpace M]

/-- **Surjectivity onto compatible families of open quotients.** Every family of elements of
`M ⧸ N`, with `N` ranging over the open submodules, that is compatible along the factor maps
`M ⧸ N → M ⧸ N'` for `N ≤ N'` comes from an element of `M`, for `M` compact with separately
continuous addition. The element is unique when `M` moreover has continuous addition and is `T1`
and linearly topologized (`TauCeti.existsUnique_forall_mkQ_eq`). -/
theorem exists_forall_mkQ_eq [SeparatelyContinuousAdd M]
    (x : ∀ N : {N : Submodule R M // IsOpen (N : Set M)}, M ⧸ N.1)
    (hx : ∀ ⦃N N' : {N : Submodule R M // IsOpen (N : Set M)}⦄ (h : N.1 ≤ N'.1),
      Submodule.factor h (x N) = x N') :
    ∃ m : M, ∀ N, N.1.mkQ m = x N := by
  -- The fibres `C N` of `mkQ` over `x N` are cosets of open, hence closed, subgroups of the
  -- compact space `M`; they are nonempty and decrease along intersections, so Cantor's
  -- intersection theorem produces a common point.
  set C : {N : Submodule R M // IsOpen (N : Set M)} → Set M := fun N ↦ N.1.mkQ ⁻¹' {x N} with hC
  have hclosed : ∀ N, IsClosed (C N) := fun N ↦ by
    have := Submodule.Quotient.discreteTopology_of_isOpen N.1 N.2
    exact isClosed_singleton.preimage N.1.continuous_mkQ
  have hne : ∀ N, (C N).Nonempty := fun N ↦ N.1.mkQ_surjective (x N)
  have hdir : Directed (· ⊇ ·) C := by
    intro N N'
    have hopen : IsOpen ((N.1 ⊓ N'.1 : Submodule R M) : Set M) := by
      rw [Submodule.coe_inf]
      exact N.2.inter N'.2
    refine ⟨⟨N.1 ⊓ N'.1, hopen⟩, fun m hm ↦ ?_, fun m hm ↦ ?_⟩
    · rw [hC, Set.mem_preimage, Set.mem_singleton_iff] at hm ⊢
      rw [← hx (N := ⟨N.1 ⊓ N'.1, hopen⟩) inf_le_left, ← hm, Submodule.factor_mk]
    · rw [hC, Set.mem_preimage, Set.mem_singleton_iff] at hm ⊢
      rw [← hx (N := ⟨N.1 ⊓ N'.1, hopen⟩) inf_le_right, ← hm, Submodule.factor_mk]
  have : Nonempty {N : Submodule R M // IsOpen (N : Set M)} := ⟨⟨⊤, by simp⟩⟩
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun N ↦ (hclosed N).isCompact) hclosed
  exact ⟨m, fun N ↦ Set.mem_iInter.mp hm N⟩

/-- **The inverse-limit description of a compact linearly topologized module**: a compatible
family of elements of the quotients `M ⧸ N` by the open submodules comes from exactly one element
of `M`. -/
theorem existsUnique_forall_mkQ_eq [ContinuousAdd M] [IsLinearTopology R M] [T1Space M]
    (x : ∀ N : {N : Submodule R M // IsOpen (N : Set M)}, M ⧸ N.1)
    (hx : ∀ ⦃N N' : {N : Submodule R M // IsOpen (N : Set M)}⦄ (h : N.1 ≤ N'.1),
      Submodule.factor h (x N) = x N') :
    ∃! m : M, ∀ N, N.1.mkQ m = x N := by
  obtain ⟨m, hm⟩ := exists_forall_mkQ_eq x hx
  refine ⟨m, hm, fun m' (hm' : ∀ N, N.1.mkQ m' = x N) ↦ ?_⟩
  rw [← sub_eq_zero]
  refine IsLinearTopology.eq_zero_of_forall_mem_of_isOpen (R := R) fun N hN ↦ ?_
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hm' ⟨N, hN⟩, hm ⟨N, hN⟩,
    sub_self]

end Compact

variable [TopologicalSpace R]

variable (R M) in
-- The predicate and API are adapted from `IsCompactModule` in
-- `TauCetiRoadmap/ProfiniteProPGroups/Suggested.lean` (`CompactModules`).
/-- A **compact module** over a topological ring `R`: a topological `R`-module that is a compact,
totally disconnected topological additive group with continuous scalar action. Over a compact ring
these are the modules that are inverse limits of finite modules with surjective transition maps.
The four conditions are bundled as one predicate so that a module whose topology is given by hand
can carry them as a single hypothesis. -/
structure IsCompactModule : Prop where
  /-- the module is a topological additive group -/
  isTopologicalAddGroup : IsTopologicalAddGroup M
  /-- the scalar action is continuous -/
  continuousSMul : ContinuousSMul R M
  /-- the module is compact -/
  compactSpace : CompactSpace M
  /-- the module is totally disconnected -/
  totallyDisconnectedSpace : TotallyDisconnectedSpace M

namespace IsCompactModule

/-- A compact totally disconnected topological ring is a compact module over itself. -/
theorem self [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R] :
    IsCompactModule R R :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

variable (hM : IsCompactModule R M)
include hM

/-- A compact module is nonarchimedean: every neighbourhood of zero contains an open additive
subgroup. -/
theorem nonarchimedeanAddGroup : NonarchimedeanAddGroup M :=
  have := hM.isTopologicalAddGroup
  have := hM.compactSpace
  have := hM.totallyDisconnectedSpace
  inferInstance

/-- A compact module is Hausdorff. -/
theorem t2Space : T2Space M :=
  have := hM.isTopologicalAddGroup
  have := hM.totallyDisconnectedSpace
  inferInstance

/-- A compact module over a compact ring is linearly topologized: its open submodules form a
basis of neighbourhoods of zero. -/
theorem isLinearTopology [CompactSpace R] : IsLinearTopology R M :=
  have := hM.nonarchimedeanAddGroup
  have := hM.continuousSMul
  inferInstance

/-- **Separatedness.** In a compact module over a compact ring, an element lying in every open
submodule is zero. -/
theorem eq_zero_of_forall_mem_of_isOpen [CompactSpace R] {x : M}
    (h : ∀ N : Submodule R M, IsOpen (N : Set M) → x ∈ N) : x = 0 :=
  have := hM.isTopologicalAddGroup
  have := hM.totallyDisconnectedSpace
  have := hM.isLinearTopology
  IsLinearTopology.eq_zero_of_forall_mem_of_isOpen h

/-- **The inverse-limit description.** A compact module over a compact ring is the inverse limit
of its quotients by the open submodules: a compatible family of elements of those quotients comes
from exactly one element of the module. -/
theorem existsUnique_forall_mkQ_eq [CompactSpace R]
    (x : ∀ N : {N : Submodule R M // IsOpen (N : Set M)}, M ⧸ N.1)
    (hx : ∀ ⦃N N' : {N : Submodule R M // IsOpen (N : Set M)}⦄ (h : N.1 ≤ N'.1),
      Submodule.factor h (x N) = x N') :
    ∃! m : M, ∀ N, N.1.mkQ m = x N :=
  have := hM.isTopologicalAddGroup
  have := hM.compactSpace
  have := hM.totallyDisconnectedSpace
  have := hM.isLinearTopology
  TauCeti.existsUnique_forall_mkQ_eq x hx

/-- **Quotients stay compact.** The quotient of a compact module by a closed submodule is a
compact module. Closedness is what makes the quotient Hausdorff, and with the nonarchimedean
property it gives total disconnectedness. -/
theorem quotient (N : Submodule R M) (hN : IsClosed (N : Set M)) : IsCompactModule R (M ⧸ N) := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.nonarchimedeanAddGroup
  have : IsClosed (N : Set M) := hN
  refine ⟨inferInstance, inferInstance, ⟨?_⟩, inferInstance⟩
  rw [← Set.image_univ_of_surjective N.mkQ_surjective]
  exact isCompact_univ.image N.continuous_mkQ

end IsCompactModule

end TauCeti
