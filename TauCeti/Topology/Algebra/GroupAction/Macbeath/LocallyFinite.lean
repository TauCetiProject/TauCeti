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

The bridge is a thickening. Let a group act by isometries on a locally path-connected metric
space, and let `P` be closed and path-connected with locally finite translates. Each point `z`
has a radius `r z > 0` such that every translate of `P` meeting the ball of radius `2 * r z`
about `z` contains `z`. The union `U` of path-connected open neighbourhoods of the points of
`P`, each inside the ball of radius `r z`, is open and path-connected and contains `P`. If
finitely many translates `gᵢ • U` share a point `x`, choose `zᵢ ∈ P` with `x` within `r zᵢ` of
`gᵢ • zᵢ`, and let `z₀` have the largest radius among them. Every `gᵢ • zᵢ` then lies within
`2 * r z₀` of `g₀ • z₀`, so `g₀ • z₀` lies in every `gᵢ • P`. Hence `U` and `P` have the same
Macbeath generators and the same Macbeath relations, and the two presented groups are
canonically isomorphic.

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

variable [PseudoMetricSpace X] [IsIsometricSMul G X] {P : Set X}

/-- Around each point `z` there is a ball such that every translate of `P` meeting it
contains `z`; its radius is recorded as `2 * r`. -/
private theorem exists_pos_forall_mem_smul_of_mem_ball (hPc : IsClosed P)
    (hlf : LocallyFinite fun g : G ↦ g • P) (z : X) :
    ∃ r > 0, ∀ (g : G), ∀ y ∈ ball z (2 * r), y ∈ g • P → z ∈ g • P := by
  obtain ⟨ε, hε, hball⟩ :=
    exists_pos_forall_mem_of_mem_ball (fun g ↦ hPc.smul g) hlf z
  exact ⟨ε / 2, half_pos hε, fun g y hy hyg ↦
    hball g y (by rwa [mul_div_cancel₀ _ two_ne_zero] at hy) hyg⟩

/-- A closed set with locally finite translates has an open neighbourhood whose Macbeath
generators are already Macbeath generators of the original set. -/
private theorem exists_isOpen_superset_macbeathGenerators_of_locallyFinite (hPc : IsClosed P)
    (hlf : LocallyFinite fun g : G ↦ g • P) :
    ∃ U : Set X, IsOpen U ∧ P ⊆ U ∧ macbeathGenerators G U ⊆ macbeathGenerators G P := by
  choose r hr hball using exists_pos_forall_mem_smul_of_mem_ball hPc hlf
  let U := ⋃ z ∈ P, ball z (r z)
  refine ⟨U, isOpen_biUnion fun _ _ ↦ isOpen_ball,
    fun z hz ↦ mem_biUnion hz (mem_ball_self (hr z)), ?_⟩
  intro g hg
  rw [mem_macbeathGenerators] at hg ⊢
  obtain ⟨x, hxU, hxgU⟩ := hg
  obtain ⟨z, hzP, hxz⟩ := mem_iUnion₂.1 hxU
  obtain ⟨w, hwP, hxw⟩ :=
    mem_iUnion₂.1 (mem_smul_set_iff_inv_smul_mem.1 hxgU)
  have hxz' : dist x z < r z := mem_ball.1 hxz
  have hxw' : dist (g⁻¹ • x) w < r w := mem_ball.1 hxw
  rcases le_total (r w) (r z) with hwz | hzw
  · refine ⟨z, hzP, hball z g (g • w) (mem_ball.2 ?_) (smul_mem_smul_set hwP)⟩
    have hxgw : dist x (g • w) < r w := by
      calc
        dist x (g • w) = dist (g⁻¹ • x) (g⁻¹ • (g • w)) := (dist_smul g⁻¹ x (g • w)).symm
        _ = dist (g⁻¹ • x) w := by rw [inv_smul_smul]
        _ < r w := hxw'
    rw [two_mul]
    calc
      dist (g • w) z ≤ dist x (g • w) + dist x z := dist_triangle_left _ _ _
      _ < r w + r z := add_lt_add hxgw hxz'
      _ ≤ r z + r z := add_le_add hwz le_rfl
  · have hzinv : dist (g⁻¹ • x) (g⁻¹ • z) < r z := by
      rw [dist_smul]
      exact hxz'
    have hw : w ∈ g⁻¹ • P := hball w g⁻¹ (g⁻¹ • z) (mem_ball.2 <| by
      rw [two_mul]
      calc
        dist (g⁻¹ • z) w ≤
            dist (g⁻¹ • x) (g⁻¹ • z) + dist (g⁻¹ • x) w :=
          dist_triangle_left _ _ _
        _ < r z + r w := add_lt_add hzinv hxw'
        _ ≤ r w + r w := add_le_add hzw le_rfl)
      (smul_mem_smul_set hzP)
    exact ⟨g • w, mem_inv_smul_set_iff.1 hw, smul_mem_smul_set hwP⟩

/-- **The thickening of a tile.** Let `G` act isometrically on a locally path-connected metric
space, and let `P` be closed and path-connected with locally finite translates. Then `P` has a
path-connected open neighbourhood `U` such that finitely many translates of `U` have a common
point only if the corresponding translates of `P` do. -/
theorem exists_isOpen_isPathConnected_superset_of_locallyFinite [LocallyPathConnectedSpace X]
    (hPc : IsClosed P) (hP : IsPathConnected P) (hlf : LocallyFinite fun g : G ↦ g • P) :
    ∃ U : Set X, IsOpen U ∧ IsPathConnected U ∧ P ⊆ U ∧
      ∀ s : Finset G, (⋂ g ∈ s, g • U).Nonempty → (⋂ g ∈ s, g • P).Nonempty := by
  choose r hr hball using exists_pos_forall_mem_smul_of_mem_ball hPc hlf
  have hW (z : X) : ∃ W : Set X, IsOpen W ∧ z ∈ W ∧ IsPathConnected W ∧ W ⊆ ball z (r z) :=
    let ⟨W, ⟨hWo, hzW, hWc⟩, hWb⟩ :=
      (isOpen_isPathConnected_basis z).mem_iff.1 (ball_mem_nhds z (hr z))
    ⟨W, hWo, hzW, hWc, hWb⟩
  choose W hWo hzW hWc hWb using hW
  refine ⟨⋃ z ∈ P, W z, isOpen_biUnion fun z _ ↦ hWo z, ?_,
    fun z hz ↦ mem_biUnion hz (hzW z), ?_⟩
  · -- every point of `W z` is joined to `z ∈ P`, and `P` is path-connected
    obtain ⟨z₀, hz₀⟩ := hP.nonempty
    have hsub (z : X) (hz : z ∈ P) : W z ⊆ ⋃ z ∈ P, W z := subset_biUnion_of_mem hz
    refine ⟨z₀, mem_biUnion hz₀ (hzW z₀), fun {y} hy ↦ ?_⟩
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 hy
    exact ((hP.joinedIn z₀ hz₀ z hz).mono fun w hw ↦ mem_biUnion hw (hzW w)).trans
      (((hWc z).joinedIn z (hzW z) y hyz).mono (hsub z hz))
  · rintro s ⟨x, hx⟩
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨x, by simp⟩
    -- each translate `g • U` contains `x` through a point `z g ∈ P` with `x` near `g • z g`
    have hnear (g : G) (hg : g ∈ s) : ∃ z ∈ P, dist x (g • z) < r z := by
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (mem_smul_set_iff_inv_smul_mem.1 (mem_iInter₂.1 hx g hg))
      refine ⟨z, hz, ?_⟩
      rw [← dist_smul g⁻¹, inv_smul_smul]
      exact hWb z hxz
    have : Nonempty X := ⟨x⟩
    choose! z hzP hzx using hnear
    -- the point with the largest radius lies in every translate
    obtain ⟨g₀, hg₀, hmax⟩ := s.exists_max_image (fun g ↦ r (z g)) hs
    refine ⟨g₀ • z g₀, mem_iInter₂.2 fun g hg ↦ ?_⟩
    have hdist : dist (g₀⁻¹ • g • z g) (z g₀) < 2 * r (z g₀) := by
      rw [← dist_smul g₀, smul_inv_smul, two_mul]
      calc dist (g • z g) (g₀ • z g₀) ≤ dist x (g • z g) + dist x (g₀ • z g₀) :=
            dist_triangle_left _ _ _
        _ < r (z g) + r (z g₀) := add_lt_add (hzx g hg) (hzx g₀ hg₀)
        _ ≤ r (z g₀) + r (z g₀) := by gcongr; exact hmax g hg
    have hmem : g₀⁻¹ • g • z g ∈ (g₀⁻¹ * g) • P := by
      rw [mul_smul]
      exact smul_mem_smul_set (smul_mem_smul_set (hzP g hg))
    have h := hball (z g₀) (g₀⁻¹ * g) _ (mem_ball.2 hdist) hmem
    rw [mul_smul] at h
    simpa using smul_mem_smul_set (a := g₀) h

/-! ### Macbeath's theorem for a closed set -/

/-- A closed path-connected set with locally finite translates covering the space has a
path-connected open thickening whose translates also cover the space, with a presented group
isomorphic to that of the set, compatibly with evaluation in `G`. -/
private theorem exists_macbeathCongr [LocallyPathConnectedSpace X] (hPc : IsClosed P)
    (hP : IsPathConnected P) (hlf : LocallyFinite fun g : G ↦ g • P)
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

/-- **The Macbeath generators of a tile generate the group.** If the translates of a closed set
`P` are locally finite and cover a connected metric space on which `G` acts isometrically, then
the elements `g` with `g • P` meeting `P` generate `G`. -/
theorem macbeathHom_surjective_of_locallyFinite [ConnectedSpace X]
    (hPc : IsClosed P) (hlf : LocallyFinite fun g : G ↦ g • P)
    (hcover : ⋃ g : G, g • P = univ) : Surjective (macbeathHom G P) := by
  obtain ⟨U, hUo, hPU, hgen⟩ :=
    exists_isOpen_superset_macbeathGenerators_of_locallyFinite hPc hlf
  have hUcover : ⋃ g : G, g • U = univ :=
    eq_univ_of_univ_subset (hcover ▸ iUnion_mono fun g ↦ smul_set_mono hPU)
  rw [← MonoidHom.range_eq_top, range_macbeathHom]
  apply top_unique
  rw [← closure_macbeathGenerators_eq_top hUo hUcover]
  exact Subgroup.closure_mono hgen

/-- **Macbeath's theorem for a tile.** If the translates of a closed path-connected set `P` are
locally finite and cover a simply connected, locally path-connected metric space on which `G`
acts isometrically, then every relation among the Macbeath generators of `P` is a consequence of
the Macbeath relations of `P`. -/
theorem macbeathHom_injective_of_locallyFinite [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] (hPc : IsClosed P) (hP : IsPathConnected P)
    (hlf : LocallyFinite fun g : G ↦ g • P) (hcover : ⋃ g : G, g • P = univ) :
    Injective (macbeathHom G P) := by
  obtain ⟨U, hUo, hUc, hUcover, e, he⟩ := exists_macbeathCongr hPc hP hlf hcover
  rw [← he]
  exact (macbeathHom_injective hUo hUc hUcover).comp e.injective

/-- **Macbeath's theorem for a tile**, as a description of the relations: under the hypotheses
of `TauCeti.macbeathHom_injective_of_locallyFinite`, the kernel of the evaluation of words in
the Macbeath generators of `P` is the normal closure of the Macbeath relations of `P`. -/
theorem ker_lift_eq_normalClosure_macbeathRels_of_locallyFinite [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] (hPc : IsClosed P) (hP : IsPathConnected P)
    (hlf : LocallyFinite fun g : G ↦ g • P) (hcover : ⋃ g : G, g • P = univ) :
    (FreeGroup.lift (Subtype.val : macbeathGenerators G P → G)).ker =
      Subgroup.normalClosure (macbeathRels G P) := by
  ext x
  rw [MonoidHom.mem_ker, ← macbeathHom_mk,
    (injective_iff_map_eq_one' _).1 (macbeathHom_injective_of_locallyFinite hPc hP hlf hcover),
    PresentedGroup.mk_eq_one_iff]

end TauCeti
