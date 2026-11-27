/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.Topology.Compactness.LocallyCompact

/-!
# The residual action of a quotient group on an orbit space

Let a group `G` with separately continuous multiplication act on a space `X`, and let `N` be a
normal subgroup of `G`. The quotient group `G ⧸ N` acts on the orbit space `X ⧸ N` by
`[g] • [x] = [g • x]` (`MulAction.orbitRel.Quotient.instMulActionQuotientGroup`). This file shows
that this residual action inherits continuity and properness from the action of `G`.

* **Continuity.** If `G` acts continuously, so does `G ⧸ N`
  (`MulAction.orbitRel.Quotient.continuousSMul_quotientGroup`): both projections `G → G ⧸ N` and
  `X → X ⧸ N` are open quotient maps, so their product is a quotient map, and on representatives
  the residual action is the action of `G` followed by the projection.
* **Properness.** If `G` acts properly on a weakly locally compact space `X` and `N` is closed, then
  `G ⧸ N` acts properly on `X ⧸ N` (`MulAction.orbitRel.Quotient.properSMul_quotientGroup`). The
  orbit space is Hausdorff, since the closed subgroup `N` acts properly
  (`t2Space_quotient_mulAction_of_properSMul`), and weakly locally compact, so properness is tested
  on compact sets (`MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty`). Every compact
  set `U'` of `X ⧸ N` is the image of a compact set `U` of `X`, the intersection of the preimage of
  `U'` with a compact set whose image covers `U'` (`IsOpenMap.exists_isCompact_subset_image`). For
  compact sets `U` and `V` of `X` with images `U'` and `V'`, the elements `[g]` with
  `[g] • U' ∩ V' ≠ ∅` are the images of the elements `h` with `h • U ∩ V ≠ ∅`: if `n • g • u = v`
  with `n ∈ N`, then `h = n g` has the same image as `g`. These form a compact set because `G`
  acts properly, so their image in `G ⧸ N` is compact.

This is the topological input for reduction in stages: a Lie group acting properly on a regular
level, reduced first by a closed normal subgroup, leaves a proper action of the quotient group on
the first-stage reduced space. Properness is one of the hypotheses of the quotient manifold theorem
for the second stage; freeness and smoothness of the residual action are supplied elsewhere.

## Main results

* `MulAction.orbitRel.Quotient.continuousSMul_quotientGroup`: the residual action is continuous.
* `MulAction.orbitRel.Quotient.properSMul_quotientGroup`: the residual action is proper.

## References

* N. Bourbaki, *General Topology*, Chapter III, §4 (proper actions and their quotients).
* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 5 (the residual action in
  reduction by a normal subgroup).
-/

public section

open Set Topology

namespace MulAction.orbitRel.Quotient

variable {G X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X] [MulAction G X]
  (N : Subgroup G) [N.Normal]

/-- **The residual action is continuous.** If a group `G` with separately continuous
multiplication acts continuously on `X`, then for a normal subgroup `N` the quotient group `G ⧸ N`
acts continuously on the orbit space `X ⧸ N` by `[g] • [x] = [g • x]`. -/
@[to_additive /-- **The residual action is continuous.** If an additive group `G` with separately
continuous addition acts continuously on `X`, then for a normal subgroup `N` the quotient group
`G ⧸ N` acts continuously on the orbit space `X ⧸ N` by `[g] +ᵥ [x] = [g +ᵥ x]`. -/]
instance continuousSMul_quotientGroup [SeparatelyContinuousMul G] [ContinuousSMul G X] :
    ContinuousSMul (G ⧸ N) (orbitRel.Quotient N X) where
  continuous_smul := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk.prodMap
      MulAction.isOpenQuotientMap_quotientMk).continuous_comp_iff]
    -- On representatives the residual action is the action of `G` followed by the projection.
    have hcomp : (fun p : (G ⧸ N) × orbitRel.Quotient N X ↦ p.1 • p.2) ∘
        Prod.map QuotientGroup.mk (Quotient.mk _) = Quotient.mk _ ∘ fun p : G × X ↦ p.1 • p.2 :=
      funext fun p ↦ mk_smul_mk N p.1 p.2
    rw [hcomp]
    exact continuous_quot_mk.comp continuous_smul

/-- **The residual action is proper.** If a group `G` with separately continuous multiplication
acts properly on a weakly locally compact space `X`, then for a closed normal subgroup `N` the
quotient group `G ⧸ N` acts properly on the orbit space `X ⧸ N` by `[g] • [x] = [g • x]`. -/
@[to_additive /-- **The residual action is proper.** If an additive group `G` with separately
continuous addition acts properly on a weakly locally compact space `X`, then for a closed normal
subgroup `N` the quotient group `G ⧸ N` acts properly on the orbit space `X ⧸ N` by
`[g] +ᵥ [x] = [g +ᵥ x]`. -/]
instance properSMul_quotientGroup [SeparatelyContinuousMul G] [ProperSMul G X]
    [WeaklyLocallyCompactSpace X] [IsClosed (N : Set G)] :
    ProperSMul (G ⧸ N) (orbitRel.Quotient N X) := by
  have hπ : IsOpenQuotientMap (Quotient.mk (orbitRel N X)) :=
    MulAction.isOpenQuotientMap_quotientMk
  have := hπ.weaklyLocallyCompactSpace
  -- Every compact set of the orbit space is the image of a compact set of `X`.
  have hlift {U' : Set (orbitRel.Quotient N X)} (hU' : IsCompact U') :
      ∃ U : Set X, IsCompact U ∧ Quotient.mk _ '' U = U' := by
    obtain ⟨K, hK, hU'K⟩ := hπ.isOpenMap.exists_isCompact_subset_image hU'
      (hπ.surjective.range_eq ▸ subset_univ _)
    refine ⟨K ∩ Quotient.mk _ ⁻¹' U', hK.inter_right (hU'.isClosed.preimage hπ.continuous), ?_⟩
    rw [image_inter_preimage, inter_eq_right.2 hU'K]
  rw [MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty]
  intro U' V' hU' hV'
  obtain ⟨U, hU, rfl⟩ := hlift hU'
  obtain ⟨V, hV, rfl⟩ := hlift hV'
  convert (ProperSMul.isCompact_setOfPred_inter_nonempty (G := G) hU hV).image
    QuotientGroup.continuous_mk using 1
  ext q
  induction q using QuotientGroup.induction_on with | H g =>
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, v, hv, hgv⟩
    -- `[g] • [u] = [v]` means `n • g • u = v` for some `n ∈ N`, and `[n * g] = [g]`.
    rw [← Quotient.mk''_eq_mk] at hgv
    simp only [mk_smul_mk] at hgv
    obtain ⟨n, hn⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact' hgv))
    refine ⟨n * g, ⟨v, ⟨u, hu, by simpa only [mul_smul, ← Subgroup.smul_def] using hn⟩, hv⟩, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 n.property, one_mul]
  · rintro ⟨h, ⟨_, ⟨u, hu, rfl⟩, hv⟩, hhg⟩
    exact ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, ⟨h • u, hv, by rw [← hhg]; exact mk_smul_mk N h u⟩⟩

end MulAction.orbitRel.Quotient
