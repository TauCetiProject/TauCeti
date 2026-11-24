/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Discrete subgroups with compact coset space

Let `Γ` be a discrete subgroup of a locally compact topological group `G` whose coset space
`G ⧸ Γ` is compact. This file proves three facts about such a pair.

* **Finite generation.** If `G` is connected, then `Γ` is finitely generated
  (`Subgroup.fg_of_compactSpace_quotient`). Choose an open neighbourhood `U` of `1` inside a
  compact set `K` whose right translates by `Γ` cover `G`; the finitely many elements of `Γ` lying
  in `K⁻¹ K` generate a subgroup `H`, and `U H` is open, closed and nonempty, hence all of `G`.
* **Real cocycles.** Every homomorphism `χ : Γ → ℝ` is the coboundary of a continuous function:
  there is a continuous `f : G → ℝ` with `f (g γ) = f g + χ γ` for all `g ∈ G` and `γ ∈ Γ`
  (`Subgroup.exists_continuousMap_mul_eq_add`). It is `f = -(∑ᶠ γ, ψ(g γ) χ γ) / ∑ᶠ γ, ψ(g γ)`,
  for a compactly supported bump function `ψ` equal to `1` on a compact set meeting every coset
  `g Γ`; both sums are locally finite because `Γ` meets every compact set in a finite set
  (`Subgroup.finite_preimage_coe_of_isCompact`).
* **Compactness.** If `Γ` is compact, in particular finite, then `G` is compact
  (`Subgroup.compactSpace_of_compactSpace_subgroup`), as the projection `G → G ⧸ Γ` is proper.
  This uses neither discreteness nor local compactness.

Real homomorphisms are written multiplicatively, as `χ : Γ →* Multiplicative ℝ`, so that they
apply to groups written multiplicatively.

These are the topological inputs of the averaging argument that extends real characters from a
discrete central subgroup with compact quotient, and so of Weyl's theorem that a compact connected
Lie group with semisimple Lie algebra has finite fundamental group.

## Main results

* `Subgroup.finite_preimage_coe_of_isCompact`: a discrete subgroup meets every compact set in a
  finite set.
* `Subgroup.compactSpace_of_compactSpace_subgroup`: if `Γ` and `G ⧸ Γ` are compact, `G` is
  compact.
* `Subgroup.exists_isOpen_isCompact_forall_exists_mul_mem`: an open neighbourhood of `1` inside a
  compact set, meeting every coset `g Γ`.
* `Subgroup.fg_of_compactSpace_quotient`: a discrete subgroup with compact coset space of a
  connected locally compact group is finitely generated.
* `Subgroup.exists_continuousMap_mul_eq_add`: every real homomorphism on `Γ` is
  `γ ↦ f (g γ) - f g` for a continuous `f : G → ℝ`.

## References

* M. S. Raghunathan, *Discrete Subgroups of Lie Groups*, Springer (1972), for the finite
  generation of discrete subgroups with compact quotient.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012), Chapter 12,
  for Weyl's theorem on compact semisimple Lie groups.
-/

public section

open Filter Function Set Topology

open scoped Pointwise

namespace Subgroup

/-- A discrete subgroup meets every compact set in a finite set. -/
@[to_additive /-- A discrete additive subgroup meets every compact set in a finite set. -/]
theorem finite_preimage_coe_of_isCompact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G}
    (hK : IsCompact K) : ((↑) ⁻¹' K : Set Γ).Finite :=
  tendsto_cofinite_cocompact_iff.mp
    (Γ.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr ‹_›)) K hK

/-- **A compact subgroup with compact coset space has compact ambient group.** If `Γ` and
`G ⧸ Γ` are compact, then `G` is compact: the projection `G → G ⧸ Γ` is closed with compact
fibres `g Γ`, hence proper. Neither local compactness nor discreteness is needed. A finite `Γ`
is compact by `Finite.compactSpace`. -/
theorem compactSpace_of_compactSpace_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Γ : Subgroup G) [CompactSpace Γ] [CompactSpace (G ⧸ Γ)] :
    CompactSpace G := by
  have hΓ : IsCompact (Γ : Set G) := isCompact_iff_compactSpace.mpr ‹_›
  have hp : IsProperMap ((↑) : G → G ⧸ Γ) :=
    isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨QuotientGroup.continuous_mk,
      QuotientGroup.isClosedMap_coe hΓ, QuotientGroup.mk_surjective.forall.mpr fun g ↦ by
        simpa [← image_singleton, QuotientGroup.preimage_image_mk_eq_mul] using
          isCompact_singleton.mul hΓ⟩
  exact ⟨by simpa using hp.isCompact_preimage isCompact_univ⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)]

/-- **A compact set meeting every coset.** If the coset space `G ⧸ Γ` is compact and `G` is locally
compact, some open neighbourhood `U` of `1`, contained in a compact set `K`, meets every coset
`g Γ`. -/
theorem exists_isOpen_isCompact_forall_exists_mul_mem :
    ∃ U K : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ IsCompact K ∧ U ⊆ K ∧
      ∀ g : G, ∃ γ ∈ Γ, g * γ ∈ U := by
  -- Some compact `L` meets every coset; thicken it by a compact neighbourhood `K₀` of `1`.
  obtain ⟨L, hL, hLcov⟩ := (QuotientGroup.isOpenMap_coe (N := Γ)).exists_isCompact_subset_image
    isCompact_univ (by simp [QuotientGroup.mk_surjective.range_eq])
  obtain ⟨K₀, hK₀, hK₀1⟩ := exists_compact_mem_nhds (1 : G)
  have hV1 : (1 : G) ∈ interior K₀ := mem_interior_iff_mem_nhds.mpr hK₀1
  refine ⟨L * interior K₀ ∪ interior K₀, L * K₀ ∪ K₀,
    isOpen_interior.mul_left.union isOpen_interior, Or.inr hV1, (hL.mul hK₀).union hK₀,
    union_subset_union (mul_subset_mul_left interior_subset) interior_subset, fun g ↦ ?_⟩
  obtain ⟨l, hl, hlg⟩ := hLcov (mem_univ (g : G ⧸ Γ))
  refine ⟨g⁻¹ * l, QuotientGroup.eq.mp hlg.symm, Or.inl ?_⟩
  rw [mul_inv_cancel_left]
  exact ⟨l, hl, 1, hV1, mul_one l⟩

/-- **A discrete subgroup with compact coset space of a connected group is finitely generated.**
Let `G` be a connected locally compact group and `Γ` a discrete subgroup with `G ⧸ Γ` compact.
Then `Γ` is generated by its finitely many elements lying in `K⁻¹ K`, for a compact set `K`
containing an open neighbourhood `U` of `1` that meets every coset `g Γ`. -/
theorem fg_of_compactSpace_quotient [ConnectedSpace G] [DiscreteTopology Γ] : Group.FG Γ := by
  obtain ⟨U, K, hU, hU1, hK, hUK, hcov⟩ := Γ.exists_isOpen_isCompact_forall_exists_mul_mem
  set S : Set Γ := (↑) ⁻¹' (K⁻¹ * K)
  set H := closure S
  -- If `g γ` and `g δ` both lie in `U` and `γ ∈ H`, then `δ ∈ H`, since `γ⁻¹ δ ∈ U⁻¹ U ∩ Γ ⊆ S`.
  have key : ∀ (g : G) (γ δ : Γ), γ ∈ H → g * γ ∈ U → g * δ ∈ U → δ ∈ H := by
    intro g γ δ hγ hgγ hgδ
    have hS : γ⁻¹ * δ ∈ S := by
      simp only [S, mem_preimage, coe_mul, coe_inv]
      exact ⟨(g * γ)⁻¹, inv_mem_inv.mpr (hUK hgγ), g * δ, hUK hgδ, by group⟩
    simpa using mul_mem hγ (subset_closure hS)
  -- The set `A` of `g` with `g γ ∈ U` for some `γ ∈ H` is open and closed.
  set A : Set G := ⋃ γ ∈ H, (· * (γ : G)) ⁻¹' U
  have hA : IsClopen A := by
    refine ⟨?_, isOpen_biUnion fun γ _ ↦ hU.preimage (continuous_mul_const _)⟩
    rw [← isOpen_compl_iff]
    convert isOpen_biUnion (s := (H : Set Γ)ᶜ)
      fun δ _ ↦ hU.preimage (continuous_mul_const (δ : G)) using 1
    ext g
    simp only [A, mem_compl_iff, mem_iUnion, mem_preimage, not_exists, SetLike.mem_coe]
    refine ⟨fun h ↦ ?_, fun ⟨δ, hδ, hgδ⟩ γ hγ hgγ ↦ hδ (key g γ δ hγ hgγ hgδ)⟩
    obtain ⟨δ, hδΓ, hgδ⟩ := hcov g
    exact ⟨⟨δ, hδΓ⟩, fun hδ ↦ h _ hδ hgδ, hgδ⟩
  have hAuniv : A = univ := hA.eq_univ ⟨1, mem_iUnion₂.mpr ⟨1, H.one_mem, by simpa using hU1⟩⟩
  refine Group.fg_iff.mpr ⟨S, eq_top_iff.mpr fun γ _ ↦ ?_,
    Γ.finite_preimage_coe_of_isCompact (hK.inv.mul hK)⟩
  obtain ⟨η, hη, hγη⟩ := mem_iUnion₂.mp (hAuniv ▸ mem_univ (γ : G))
  simpa using key γ η γ⁻¹ hη hγη (by simpa using hU1)

/-- **Real homomorphisms on a discrete cocompact subgroup are coboundaries.** Let `Γ` be a
discrete subgroup with compact coset space of a locally compact group `G`. For every
homomorphism `χ : Γ → ℝ` there is a continuous `f : G → ℝ` with `f (g γ) = f g + χ γ`. -/
theorem exists_continuousMap_mul_eq_add [DiscreteTopology Γ]
    (χ : Γ →* Multiplicative ℝ) :
    ∃ f : C(G, ℝ), ∀ (g : G) (γ : Γ), f (g * γ) = f g + (χ γ).toAdd := by
  obtain ⟨U, K, -, -, hK, hUK, hcov⟩ := Γ.exists_isOpen_isCompact_forall_exists_mul_mem
  obtain ⟨ψ, hψK, -, hψc, hψ01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  set w : Γ → G → ℝ := fun γ g ↦ ψ (g * γ)
  have hwc : ∀ γ, Continuous (w γ) := fun γ ↦ ψ.continuous.comp (continuous_mul_const _)
  -- The translates of `ψ` along `Γ` form a locally finite family.
  have hlf : LocallyFinite fun γ ↦ support (w γ) := by
    intro g
    obtain ⟨N, hN, hgN⟩ := exists_compact_mem_nhds g
    refine ⟨N, hgN, (Γ.finite_preimage_coe_of_isCompact (hN.inv.mul hψc)).subset ?_⟩
    rintro γ ⟨x, hxγ, hxN⟩
    exact ⟨x⁻¹, inv_mem_inv.mpr hxN, x * γ, subset_tsupport _ hxγ, by group⟩
  have hfin : ∀ g, (support fun γ ↦ w γ g).Finite := hlf.point_finite
  set S : G → ℝ := fun g ↦ ∑ᶠ γ, w γ g
  set T : G → ℝ := fun g ↦ ∑ᶠ γ, w γ g * (χ γ).toAdd
  have hS : Continuous S := continuous_finsum hwc hlf
  have hT : Continuous T := continuous_finsum (fun γ ↦ (hwc γ).mul continuous_const)
    (hlf.subset fun γ ↦ support_mul_subset_left _ _)
  have hS1 : ∀ g, 1 ≤ S g := fun g ↦ by
    obtain ⟨γ, hγΓ, hgγ⟩ := hcov g
    have h1 : w ⟨γ, hγΓ⟩ g = 1 := hψK (hUK hgγ)
    exact h1 ▸ single_le_finsum _ (hfin g) fun δ ↦ (hψ01 _).1
  have hS0 : ∀ g, S g ≠ 0 := fun g ↦ (zero_lt_one.trans_le (hS1 g)).ne'
  -- Translating by `γ` permutes the terms of `S` and shifts those of `T` by `χ γ`.
  have hSγ : ∀ g (γ : Γ), S (g * γ) = S g := fun g γ ↦ by
    simp only [S, w, mul_assoc, ← coe_mul]
    exact finsum_comp_equiv (Equiv.mulLeft γ) (f := fun δ ↦ ψ (g * δ))
  have hTγ : ∀ g (γ : Γ), T (g * γ) = T g - (χ γ).toAdd * S g := fun g γ ↦ by
    calc T (g * γ) = ∑ᶠ δ, w δ g * (χ (γ⁻¹ * δ)).toAdd := by
          simp only [T, w, mul_assoc, ← coe_mul]
          refine Eq.trans ?_ (finsum_comp_equiv (Equiv.mulLeft γ)
            (f := fun δ ↦ ψ (g * δ) * (χ (γ⁻¹ * δ)).toAdd))
          simp
      _ = ∑ᶠ δ, (w δ g * (χ δ).toAdd - w δ g * (χ γ).toAdd) :=
          finsum_congr fun δ ↦ by simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]; ring
      _ = T g - (χ γ).toAdd * S g := by
          rw [finsum_sub_distrib ((hfin g).subset (support_mul_subset_left _ _))
            ((hfin g).subset (support_mul_subset_left _ _)), ← finsum_mul, mul_comm]
  refine ⟨⟨fun g ↦ -T g / S g, hT.neg.div hS hS0⟩, fun g γ ↦ ?_⟩
  have hSg := hS0 g
  simp only [ContinuousMap.coe_mk, hSγ, hTγ]
  field_simp
  ring

end Subgroup
