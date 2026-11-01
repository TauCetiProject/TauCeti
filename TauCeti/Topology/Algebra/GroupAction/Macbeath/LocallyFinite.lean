/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.Macbeath.Basic
public import TauCeti.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Macbeath's theorem for a closed set with locally finite translates

Macbeath's theorem, `TauCeti.macbeathHom_injective`, presents a group acting on a simply
connected space from an *open* path-connected set whose translates cover the space. A
fundamental polygon or other tile of a tessellation is closed rather than open. This file
proves that the presentation read off from the tile itself is already correct: the generators
are the elements `g` with `g • P` meeting `P`, and the relations come from triples of translates
of `P` with a common point.

The bridge is a thickening. Let a group act by isometries on a locally path-connected
pseudometric space, and let `P` be closed and connected with locally finite translates. Each
point `z` has a radius `r z > 0` such that every translate of `P` meeting the ball of radius
`r z` about `z` contains `z`. The union `V` of the balls of radius `r z / 2` about points of `P`
is an open neighbourhood of `P`. Its connected component `U` containing `P` is open and
path-connected. If finitely many translates `gᵢ • U` share a point `x`, choose `zᵢ ∈ P` with
`x` within `r zᵢ / 2` of `gᵢ • zᵢ`, and let `z₀` have the largest radius among them. Every
`gᵢ • zᵢ` then lies within `r z₀` of `g₀ • z₀`, so `g₀ • z₀` lies in every `gᵢ • P`. Hence
`U` and `P` have the same Macbeath generators and the same Macbeath relations, and the two
presented groups are canonically isomorphic.

## Main results

* `TauCeti.exists_isOpen_isPathConnected_superset_of_locallyFinite`: a path-connected open
  thickening `U` of `P` such that finitely many translates of `U` meet only if the
  corresponding translates of `P` do.
* `TauCeti.macbeathHom_surjective_of_locallyFinite`: the Macbeath generators of `P` generate
  the group when the translates of `P` cover a connected space.
* `TauCeti.macbeathHom_injective_of_locallyFinite`: the Macbeath relations of `P` are complete
  when the space is simply connected.
* `TauCeti.ker_lift_eq_normalClosure_macbeathRels_of_locallyFinite`: the kernel of evaluating
  words in the Macbeath generators of `P` is the normal closure of its Macbeath relations.

## References

* A. M. Macbeath, *Groups of homeomorphisms of a simply connected space*, Ann. of Math. (2) 79
  (1964), 473–488.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 9 (presentations from locally finite fundamental polygons).
-/

public section

namespace TauCeti

open Set Function Metric Topology
open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

/-! ### Comparing the Macbeath presentations of two sets -/

/-- If the Macbeath generators and relations of `V` are among those of `U`, sending each
generator of `V` to the same element regarded as a generator of `U` defines a homomorphism of
presented groups. -/
private def macbeathMap {U V : Set X} (hgen : macbeathGenerators G V ⊆ macbeathGenerators G U)
    (hrel : ∀ s u : G, (V ∩ s • V ∩ u • V).Nonempty → (U ∩ s • U ∩ u • U).Nonempty) :
    PresentedGroup (macbeathRels G V) →* PresentedGroup (macbeathRels G U) :=
  PresentedGroup.toGroup (f := fun s ↦ PresentedGroup.of (inclusion hgen s)) <| by
    intro _ hr
    obtain ⟨s, t, u, hu, h, rfl⟩ := mem_macbeathRels.1 hr
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [macbeath_of_mul_of (u := inclusion hgen u) hu (hrel _ _ h), mul_inv_cancel]

private theorem macbeathMap_of {U V : Set X}
    (hgen : macbeathGenerators G V ⊆ macbeathGenerators G U)
    (hrel : ∀ s u : G, (V ∩ s • V ∩ u • V).Nonempty → (U ∩ s • U ∩ u • U).Nonempty)
    (s : macbeathGenerators G V) :
    macbeathMap hgen hrel (PresentedGroup.of s) = PresentedGroup.of (inclusion hgen s) :=
  PresentedGroup.toGroup.of _

private theorem macbeathHom_comp_macbeathMap {U V : Set X}
    (hgen : macbeathGenerators G V ⊆ macbeathGenerators G U)
    (hrel : ∀ s u : G, (V ∩ s • V ∩ u • V).Nonempty → (U ∩ s • U ∩ u • U).Nonempty) :
    (macbeathHom G U).comp (macbeathMap hgen hrel) = macbeathHom G V :=
  PresentedGroup.ext fun s ↦ by simp [macbeathMap_of]

/-! ### The thickening of a closed set with locally finite translates -/

section Metric

variable [PseudoMetricSpace X] [IsIsometricSMul G X] {P : Set X}

/-- **The thickening of a tile.** Let `G` act isometrically on a locally path-connected
pseudometric space, and let `P` be closed and connected with locally finite translates. Then `P`
has a path-connected open neighbourhood `U` such that finitely many translates of `U` have a common
point only if the corresponding translates of `P` do. -/
theorem exists_isOpen_isPathConnected_superset_of_locallyFinite [LocallyPathConnectedSpace X]
    (hPc : IsClosed P) (hP : IsConnected P) (hlf : LocallyFinite fun g : G ↦ g • P) :
    ∃ U : Set X, IsOpen U ∧ IsPathConnected U ∧ P ⊆ U ∧
      ∀ s : Finset G, (⋂ g ∈ s, g • U).Nonempty → (⋂ g ∈ s, g • P).Nonempty := by
  choose r hr hball using exists_pos_forall_mem_of_mem_ball (fun g : G ↦ hPc.smul g) hlf
  let V : Set X := ⋃ z ∈ P, ball z (r z / 2)
  have hVo : IsOpen V := isOpen_biUnion fun _ _ ↦ isOpen_ball
  have hPV : P ⊆ V := fun z hz ↦ mem_biUnion hz (mem_ball_self (half_pos (hr z)))
  obtain ⟨z₀, hz₀⟩ := hP.nonempty
  -- The connected set `P` lies in one component of `V`, which is open and path-connected.
  let U := connectedComponentIn V z₀
  have hUo : IsOpen U := hVo.connectedComponentIn
  have hUV : U ⊆ V := connectedComponentIn_subset _ _
  refine ⟨U, hUo, hUo.isConnected_iff_isPathConnected.1
    (isConnected_connectedComponentIn_iff.2 (hPV hz₀)),
    hP.isPreconnected.subset_connectedComponentIn hz₀ hPV, ?_⟩
  rintro s ⟨x, hx⟩
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨x, by simp⟩
  -- each translate `g • U` contains `x` through a point `z g ∈ P` with `x` near `g • z g`
  have hnear (g : G) (hg : g ∈ s) : ∃ z ∈ P, dist x (g • z) < r z / 2 := by
    obtain ⟨z, hz, hxz⟩ :=
      mem_iUnion₂.1 (hUV (mem_smul_set_iff_inv_smul_mem.1 (mem_iInter₂.1 hx g hg)))
    refine ⟨z, hz, ?_⟩
    rw [← dist_smul g⁻¹, inv_smul_smul]
    exact mem_ball.1 hxz
  have : Nonempty X := ⟨x⟩
  choose! z hzP hzx using hnear
  -- the point with the largest radius lies in every translate
  obtain ⟨g₀, hg₀, hmax⟩ := s.exists_max_image (fun g ↦ r (z g)) hs
  refine ⟨g₀ • z g₀, mem_iInter₂.2 fun g hg ↦ ?_⟩
  have hdist : dist (g₀⁻¹ • g • z g) (z g₀) < r (z g₀) := by
    rw [← dist_smul g₀, smul_inv_smul]
    calc dist (g • z g) (g₀ • z g₀) ≤ dist x (g • z g) + dist x (g₀ • z g₀) :=
          dist_triangle_left _ _ _
      _ < r (z g) / 2 + r (z g₀) / 2 := add_lt_add (hzx g hg) (hzx g₀ hg₀)
      _ ≤ r (z g₀) / 2 + r (z g₀) / 2 := by gcongr; exact hmax g hg
      _ = r (z g₀) := add_halves _
  have hmem : g₀⁻¹ • g • z g ∈ (g₀⁻¹ * g) • P := by
    rw [mul_smul]
    exact smul_mem_smul_set (smul_mem_smul_set (hzP g hg))
  have h := hball (z g₀) (g₀⁻¹ * g) _ (mem_ball.2 hdist) hmem
  rw [mul_smul] at h
  simpa using smul_mem_smul_set (a := g₀) h

/-! ### Macbeath's theorem for a closed set -/

/-- A closed connected set with locally finite translates covering the space has a
path-connected open thickening whose translates also cover the space, with a presented group
isomorphic to that of the set, compatibly with evaluation in `G`. -/
private theorem exists_macbeathCongr [LocallyPathConnectedSpace X] (hPc : IsClosed P)
    (hP : IsConnected P) (hlf : LocallyFinite fun g : G ↦ g • P)
    (hcover : ⋃ g : G, g • P = univ) :
    ∃ U : Set X, IsOpen U ∧ IsPathConnected U ∧ ⋃ g : G, g • U = univ ∧
      ∃ e : PresentedGroup (macbeathRels G P) ≃* PresentedGroup (macbeathRels G U),
        (macbeathHom G U).comp e.toMonoidHom = macbeathHom G P := by
  classical
  obtain ⟨U, hUo, hUc, hPU, hU⟩ :=
    exists_isOpen_isPathConnected_superset_of_locallyFinite hPc hP hlf
  have hgen : macbeathGenerators G P = macbeathGenerators G U := by
    ext g
    simp only [mem_macbeathGenerators]
    refine ⟨fun h ↦ h.mono (inter_subset_inter hPU (smul_set_mono hPU)), fun h ↦ ?_⟩
    simpa [Finset.set_biInter_insert] using hU {1, g} (by simpa [Finset.set_biInter_insert] using h)
  have hrel (s u : G) : (P ∩ s • P ∩ u • P).Nonempty ↔ (U ∩ s • U ∩ u • U).Nonempty := by
    refine ⟨fun h ↦ h.mono (inter_subset_inter (inter_subset_inter hPU (smul_set_mono hPU))
      (smul_set_mono hPU)), fun h ↦ ?_⟩
    simpa [Finset.set_biInter_insert, inter_assoc] using
      hU {1, s, u} (by simpa [Finset.set_biInter_insert, inter_assoc] using h)
  -- the two inclusions of generators are mutually inverse on the presented groups
  refine ⟨U, hUo, hUc, eq_univ_of_univ_subset (hcover ▸ iUnion_mono fun g ↦ smul_set_mono hPU),
    MonoidHom.toMulEquiv (macbeathMap hgen.subset fun s u ↦ (hrel s u).1)
      (macbeathMap hgen.symm.subset fun s u ↦ (hrel s u).2)
      (PresentedGroup.ext fun s ↦ by simp [macbeathMap_of])
      (PresentedGroup.ext fun s ↦ by simp [macbeathMap_of]),
    macbeathHom_comp_macbeathMap hgen.subset fun s u ↦ (hrel s u).1⟩

end Metric

section Topological

variable [TopologicalSpace X] [ContinuousConstSMul G X] {P : Set X}

/-- **The Macbeath generators of a tile generate the group.** If the translates of a closed set
`P` are locally finite and cover a connected topological space on which `G` acts continuously,
then the elements `g` with `g • P` meeting `P` generate `G`. -/
theorem macbeathHom_surjective_of_locallyFinite [ConnectedSpace X]
    (hPc : IsClosed P) (hlf : LocallyFinite fun g : G ↦ g • P)
    (hcover : ⋃ g : G, g • P = univ) : Surjective (macbeathHom G P) := by
  let H := Subgroup.closure (macbeathGenerators G P)
  let A := ⋃ h : H, (h : G) • P
  let B := ⋃ g : {g : G // g ∉ H}, (g : G) • P
  have hmem {h g : G} (hh : h ∈ H) (hinter : (h • P ∩ g • P).Nonempty) : g ∈ H := by
    have hh' : h ∈ (macbeathHom G P).range := by
      rw [range_macbeathHom]
      exact hh
    have hg := mem_range_macbeathHom_of_nonempty hh' hinter
    rw [range_macbeathHom] at hg
    exact hg
  have hAlf : LocallyFinite fun h : H ↦ (h : G) • P := by
    simpa [Function.comp_def] using hlf.comp_injective (g := fun h : H ↦ (h : G))
      Subtype.val_injective
  have hBlf : LocallyFinite fun g : {g : G // g ∉ H} ↦ (g : G) • P := by
    simpa [Function.comp_def] using
      hlf.comp_injective (g := fun g : {g : G // g ∉ H} ↦ (g : G)) Subtype.val_injective
  have hAc : IsClosed A := hAlf.isClosed_iUnion fun h ↦ hPc.smul (h : G)
  have hBc : IsClosed B := hBlf.isClosed_iUnion fun g ↦ hPc.smul (g : G)
  have hAB : Aᶜ = B := by
    ext x
    simp only [mem_compl_iff]
    constructor
    · intro hx
      obtain ⟨g, hxg⟩ := mem_iUnion.1 (hcover ▸ mem_univ x)
      have hg : g ∉ H := fun hg ↦ hx (mem_iUnion.2 ⟨⟨g, hg⟩, hxg⟩)
      exact mem_iUnion.2 ⟨⟨g, hg⟩, hxg⟩
    · intro hx hxA
      obtain ⟨g, hxg⟩ := mem_iUnion.1 hx
      obtain ⟨h, hxh⟩ := mem_iUnion.1 hxA
      exact g.2 (hmem h.2 ⟨x, hxh, hxg⟩)
  have hAo : IsOpen A := by
    rw [← isClosed_compl_iff, hAB]
    exact hBc
  have hP : P.Nonempty := by
    obtain ⟨g, hg⟩ := mem_iUnion.1 (hcover ▸ mem_univ (Classical.arbitrary X))
    exact smul_set_nonempty.1 ⟨_, hg⟩
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hP
    exact ⟨x, mem_iUnion.2 ⟨⟨1, H.one_mem⟩, by simpa⟩⟩
  have hA : A = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ hAne
  rw [← MonoidHom.range_eq_top, range_macbeathHom]
  apply top_unique
  intro g _
  obtain ⟨x, hxg⟩ := hP.smul_set (a := g)
  obtain ⟨h, hxh⟩ := mem_iUnion.1 (hA ▸ mem_univ x)
  exact hmem h.2 ⟨x, hxh, hxg⟩

end Topological

section Metric

variable [PseudoMetricSpace X] [IsIsometricSMul G X] {P : Set X}

/-- **Macbeath's theorem for a tile.** If the translates of a closed connected set `P` are
locally finite and cover a simply connected, locally path-connected pseudometric space on which `G`
acts isometrically, then every relation among the Macbeath generators of `P` is a consequence of
the Macbeath relations of `P`. -/
theorem macbeathHom_injective_of_locallyFinite [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] (hPc : IsClosed P) (hP : IsConnected P)
    (hlf : LocallyFinite fun g : G ↦ g • P) (hcover : ⋃ g : G, g • P = univ) :
    Injective (macbeathHom G P) := by
  obtain ⟨U, hUo, hUc, hUcover, e, he⟩ := exists_macbeathCongr hPc hP hlf hcover
  rw [← he]
  exact (macbeathHom_injective hUo hUc hUcover).comp e.injective

/-- **Macbeath's theorem for a tile**, as a description of the relations: under the hypotheses
of `TauCeti.macbeathHom_injective_of_locallyFinite`, the kernel of the evaluation of words in
the Macbeath generators of `P` is the normal closure of the Macbeath relations of `P`. -/
theorem ker_lift_eq_normalClosure_macbeathRels_of_locallyFinite [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] (hPc : IsClosed P) (hP : IsConnected P)
    (hlf : LocallyFinite fun g : G ↦ g • P) (hcover : ⋃ g : G, g • P = univ) :
    (FreeGroup.lift (Subtype.val : macbeathGenerators G P → G)).ker =
      Subgroup.normalClosure (macbeathRels G P) := by
  ext x
  rw [MonoidHom.mem_ker, ← macbeathHom_mk,
    (injective_iff_map_eq_one' _).1 (macbeathHom_injective_of_locallyFinite hPc hP hlf hcover),
    PresentedGroup.mk_eq_one_iff]

end Metric

end TauCeti
