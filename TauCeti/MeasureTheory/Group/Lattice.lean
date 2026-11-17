/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Quotient
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.MeasureTheory.Group.ProperlyDiscontinuous

/-!
# Lattices in locally compact groups

A *lattice* in a locally compact group `G` is a discrete subgroup `Γ` of finite covolume: the
right action of `Γ` on `G`, `g ↦ g γ`, has a measurable fundamental domain of finite Haar
measure. The quotient `G ⧸ Γ` is the space of left cosets `g Γ`. A lattice is *uniform* if
`G = K Γ` for a compact set `K`.

The theory is set in a unimodular group: `μ` is a left Haar measure which is also right
invariant, so that the measure of a fundamental domain of the right action does not depend on the
choice of domain. A discrete subgroup of a second countable, locally compact Hausdorff group has
a measurable fundamental domain; the lattice condition asks that it have finite measure.

## Main definitions

* `Subgroup.IsLattice Γ μ`: `Γ` is discrete and the right action of `Γ` on `G` has a fundamental
  domain of finite `μ`-measure.
* `Subgroup.IsUniformLattice Γ μ`: a lattice `Γ` with `K * Γ = G` for some compact `K`.

## Main results

* `Subgroup.exists_isFundamentalDomain_op`: a discrete subgroup of a second countable, locally
  compact Hausdorff group has a measurable fundamental domain for its right action.
* `Subgroup.isLattice_iff_covolume_lt_top`: for discrete `Γ` in a unimodular group, `Γ` is a
  lattice exactly when `MeasureTheory.covolume Γ.op G μ` is finite.
* `Subgroup.IsLattice.of_isHaarMeasure`: being a lattice does not depend on the Haar measure.
* `Subgroup.IsLattice.isFiniteMeasure_quotient`: the quotient measure on `G ⧸ Γ` of a lattice is
  finite.
* `QuotientGroup.lintegral_eq_lintegral_automorphize`: **Weil's formula** for nonnegative
  measurable functions, `∫ f = ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ)`, for a right-invariant measure on `G`
  and the quotient measure on `G ⧸ Γ`.
* `QuotientGroup.compactSpace_iff_exists_isCompact_mul_eq_univ`: in a locally compact group,
  `G ⧸ Γ` is compact exactly when `K * Γ = G` for a compact set `K`.
* `Subgroup.isUniformLattice_iff_isLattice_and_compactSpace`: a lattice is uniform exactly when
  `G ⧸ Γ` is compact.
* `Subgroup.isUniformLattice_iff_discreteTopology_and_compactSpace`: in a unimodular second
  countable group, a discrete subgroup with compact quotient has finite covolume, so it is a
  uniform lattice.

## References

* Frederick M. Goodman, Pierre de la Harpe, Vaughan F. R. Jones, *Coxeter Graphs and Towers of
  Algebras*, Springer, 1989, §3.3.
* Dave Witte Morris, *Introduction to Arithmetic Groups*, Deductive Press, 2015, §4.1.
-/

public section

open MeasureTheory Set TopologicalSpace

open scoped Pointwise ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G]

namespace Subgroup

/-- A subgroup `Γ` of `G` is a **lattice** with respect to the measure `μ` if it is discrete and
the right action of `Γ` on `G`, `g ↦ g γ`, has a fundamental domain of finite `μ`-measure. The
intended setting is a unimodular locally compact group `G` with Haar measure `μ`; then the
condition does not depend on the Haar measure (`Subgroup.IsLattice.of_isHaarMeasure`) nor on the
fundamental domain, and it says that `MeasureTheory.covolume Γ.op G μ` is finite
(`Subgroup.isLattice_iff_covolume_lt_top`). -/
structure IsLattice [TopologicalSpace G] (Γ : Subgroup G) (μ : Measure G) : Prop where
  /-- A lattice is a discrete subgroup. -/
  discreteTopology : DiscreteTopology Γ
  /-- A lattice has a fundamental domain of finite measure. -/
  exists_isFundamentalDomain_measure_lt_top :
    ∃ s : Set G, IsFundamentalDomain Γ.op s μ ∧ μ s < ∞

/-- A subgroup `Γ` of `G` is a **uniform lattice** with respect to `μ` if it is a lattice and
`K * Γ = G` for some compact set `K`. When `G` is locally compact this says that `G ⧸ Γ` is
compact (`Subgroup.isUniformLattice_iff_isLattice_and_compactSpace`). -/
structure IsUniformLattice [TopologicalSpace G] (Γ : Subgroup G) (μ : Measure G) : Prop
    extends Γ.IsLattice μ where
  /-- A uniform lattice is cocompact: some compact set meets every left coset. -/
  exists_isCompact_mul_eq_univ : ∃ K : Set G, IsCompact K ∧ K * (Γ : Set G) = univ

variable [TopologicalSpace G] {Γ : Subgroup G} {μ : Measure G}

omit [MeasurableSpace G] in
/-- A discrete subgroup of a second countable group is countable. -/
theorem countable_of_discreteTopology [SecondCountableTopology G] [DiscreteTopology Γ] :
    Countable Γ :=
  separableSpace_iff_countable.mp inferInstance

/-- A lattice in a second countable group is countable. -/
theorem IsLattice.countable [SecondCountableTopology G] (h : Γ.IsLattice μ) : Countable Γ :=
  have := h.discreteTopology
  countable_of_discreteTopology

/-- A lattice has a fundamental domain for its right action. -/
theorem IsLattice.hasFundamentalDomain (h : Γ.IsLattice μ) : HasFundamentalDomain Γ.op G μ :=
  ⟨h.exists_isFundamentalDomain_measure_lt_top.imp fun _ ↦ And.left⟩

variable [IsTopologicalGroup G]

/-- A discrete subgroup `Γ` of a second countable, locally compact Hausdorff group `G` has a
measurable fundamental domain for its right action on `G`, for every measure. -/
theorem exists_isFundamentalDomain_op [OpensMeasurableSpace G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [DiscreteTopology Γ] (μ : Measure G) :
    ∃ s : Set G, MeasurableSet s ∧ IsFundamentalDomain Γ.op s μ := by
  have : Countable Γ := countable_of_discreteTopology
  have : ProperlyDiscontinuousSMul Γ.op G :=
    Γ.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite
      (Γ.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr ‹_›))
  have hfree : (TauCeti.freeLocus Γ.op G : Set G) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    rw [SetLike.mem_coe, TauCeti.mem_freeLocus, eq_bot_iff]
    intro γ hγ
    rw [MulAction.mem_stabilizer_iff] at hγ
    rw [Subgroup.mem_bot]
    exact Subtype.ext (MulOpposite.unop_injective (mul_eq_left.mp hγ))
  obtain ⟨s, hs, -, h⟩ :=
    μ.exists_isFundamentalDomain_of_properlyDiscontinuousSMul (G := Γ.op) (by simp [hfree])
  exact ⟨s, hs, h⟩

/-- In a second countable, locally compact Hausdorff group, a discrete subgroup has a
fundamental domain for its right action. -/
theorem hasFundamentalDomain_op [OpensMeasurableSpace G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [DiscreteTopology Γ] (μ : Measure G) :
    HasFundamentalDomain Γ.op G μ :=
  ⟨(exists_isFundamentalDomain_op μ).imp fun _ ↦ And.right⟩

/-- Being a lattice does not depend on the choice of Haar measure. -/
theorem IsLattice.of_isHaarMeasure [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] {ν : Measure G} [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (h : Γ.IsLattice μ) : Γ.IsLattice ν := by
  obtain ⟨s, hs, hμs⟩ := h.exists_isFundamentalDomain_measure_lt_top
  refine ⟨h.discreteTopology, s, hs.mono (Measure.absolutelyContinuous_isHaarMeasure ν μ), ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul ν μ, Measure.coe_nnreal_smul_apply]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hμs

section Unimodular

variable [BorelSpace G] [μ.IsMulRightInvariant]

/-- In a unimodular group, a lattice has finite covolume. -/
theorem IsLattice.covolume_lt_top [SecondCountableTopology G] (h : Γ.IsLattice μ) :
    covolume Γ.op G μ < ∞ := by
  have := h.countable
  obtain ⟨s, hs, hμs⟩ := h.exists_isFundamentalDomain_measure_lt_top
  rwa [hs.covolume_eq_volume]

/-- In a unimodular, second countable, locally compact Hausdorff group, a subgroup is a lattice
exactly when it is discrete and its right action has finite covolume. -/
theorem isLattice_iff_covolume_lt_top [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] :
    Γ.IsLattice μ ↔ DiscreteTopology Γ ∧ covolume Γ.op G μ < ∞ := by
  refine ⟨fun h ↦ ⟨h.discreteTopology, h.covolume_lt_top⟩, fun ⟨hd, hcov⟩ ↦ ⟨hd, ?_⟩⟩
  have : Countable Γ := countable_of_discreteTopology
  obtain ⟨s, -, hs⟩ := exists_isFundamentalDomain_op (Γ := Γ) μ
  exact ⟨s, hs, hs.covolume_eq_volume μ ▸ hcov⟩

end Unimodular

omit [IsTopologicalGroup G] in
/-- The quotient measure on `G ⧸ Γ` of a lattice `Γ` is finite. -/
theorem IsLattice.isFiniteMeasure_quotient (h : Γ.IsLattice μ) (ν : Measure (G ⧸ Γ))
    [QuotientMeasureEqMeasurePreimage μ ν] : IsFiniteMeasure ν := by
  obtain ⟨s, hs, hμs⟩ := h.exists_isFundamentalDomain_measure_lt_top
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs.ne
  rw [hs.projection_respects_measure ν]
  infer_instance

end Subgroup

/-- **Weil's formula** for nonnegative measurable functions. Let `μ` be a right-invariant measure
on `G`, let the right action of a countable subgroup `Γ` on `G` have a fundamental domain, and let
`ν` be the quotient measure on `G ⧸ Γ`. Then `∫ f dμ = ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν(g Γ)`; the
inner sum is `QuotientGroup.automorphize f`, which is constant on each left coset `g Γ`. -/
theorem QuotientGroup.lintegral_eq_lintegral_automorphize [MeasurableMul G] {Γ : Subgroup G}
    [Countable Γ] {μ : Measure G} [μ.IsMulRightInvariant] [HasFundamentalDomain Γ.op G μ]
    (ν : Measure (G ⧸ Γ)) [QuotientMeasureEqMeasurePreimage μ ν] {f : G → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ x, automorphize f x ∂ν := by
  obtain ⟨s, hs⟩ := ‹HasFundamentalDomain Γ.op G μ›.ExistsIsFundamentalDomain
  have hmeas : Measurable (automorphize f : G ⧸ Γ → ℝ≥0∞) :=
    measurable_from_quotient.mpr (Measurable.tsum fun γ ↦ hf.comp (measurable_const_smul _))
  have hπ := measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage μ hs ν
  rw [← hπ.lintegral_comp hmeas, hs.lintegral_eq_tsum'' f]
  exact (lintegral_tsum fun γ ↦ (hf.comp (measurable_const_smul _)).aemeasurable).symm

namespace QuotientGroup

variable [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G}

omit [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A set `K` meets every left coset of `Γ` exactly when `K * Γ = G`. -/
theorem image_mk_eq_univ_iff {K : Set G} :
    ((↑) '' K : Set (G ⧸ Γ)) = univ ↔ K * (Γ : Set G) = univ := by
  rw [← preimage_image_mk_eq_mul]
  refine ⟨fun h ↦ by rw [h, preimage_univ], fun h ↦ eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨g, rfl⟩ := mk_surjective x
  exact (h ▸ mem_univ g : g ∈ _)

omit [MeasurableSpace G] in
/-- In a locally compact group, `G ⧸ Γ` is compact exactly when `K * Γ = G` for some compact
set `K`. -/
theorem compactSpace_iff_exists_isCompact_mul_eq_univ [LocallyCompactSpace G] :
    CompactSpace (G ⧸ Γ) ↔ ∃ K : Set G, IsCompact K ∧ K * (Γ : Set G) = univ := by
  simp_rw [← image_mk_eq_univ_iff]
  refine ⟨fun _ ↦ ?_, fun ⟨K, hK, hKΓ⟩ ↦ ⟨hKΓ ▸ hK.image continuous_mk⟩⟩
  choose K hK hKg using fun g : G ↦ exists_compact_mem_nhds g
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun g ↦ ((↑) '' interior (K g) : Set (G ⧸ Γ)))
    (fun g ↦ isOpenMap_coe _ isOpen_interior)
    fun x _ ↦ by
      obtain ⟨g, rfl⟩ := mk_surjective x
      exact mem_iUnion.mpr ⟨g, g, mem_interior_iff_mem_nhds.mpr (hKg g), rfl⟩
  refine ⟨⋃ g ∈ t, K g, t.isCompact_biUnion fun g _ ↦ hK g,
    eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨g, hg, y, hy, rfl⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  exact ⟨y, mem_iUnion₂.mpr ⟨g, hg, interior_subset hy⟩, rfl⟩

end QuotientGroup

namespace Subgroup

variable [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G} {μ : Measure G}

/-- In a locally compact group, a lattice is uniform exactly when `G ⧸ Γ` is compact. -/
theorem isUniformLattice_iff_isLattice_and_compactSpace [LocallyCompactSpace G] :
    Γ.IsUniformLattice μ ↔ Γ.IsLattice μ ∧ CompactSpace (G ⧸ Γ) :=
  ⟨fun h ↦ ⟨h.toIsLattice, QuotientGroup.compactSpace_iff_exists_isCompact_mul_eq_univ.mpr
    h.exists_isCompact_mul_eq_univ⟩,
    fun ⟨h, hc⟩ ↦ ⟨h, QuotientGroup.compactSpace_iff_exists_isCompact_mul_eq_univ.mp hc⟩⟩

/-- In a unimodular, second countable, locally compact Hausdorff group, a discrete subgroup with
compact quotient `G ⧸ Γ` has finite covolume: a fundamental domain has measure at most that of a
compact set `K` with `K * Γ = G`. So it is a uniform lattice. -/
theorem isUniformLattice_iff_discreteTopology_and_compactSpace [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] :
    Γ.IsUniformLattice μ ↔ DiscreteTopology Γ ∧ CompactSpace (G ⧸ Γ) := by
  refine ⟨fun h ↦ ⟨h.discreteTopology,
    (isUniformLattice_iff_isLattice_and_compactSpace.mp h).2⟩, fun ⟨hd, hc⟩ ↦ ?_⟩
  obtain ⟨K, hK, hKΓ⟩ := QuotientGroup.compactSpace_iff_exists_isCompact_mul_eq_univ.mp hc
  have : Countable Γ := countable_of_discreteTopology
  obtain ⟨s, -, hs⟩ := exists_isFundamentalDomain_op (Γ := Γ) μ
  refine ⟨⟨hd, s, hs, ?_⟩, K, hK, hKΓ⟩
  calc μ s ≤ μ (⋃ γ : Γ.op, γ • K ∩ s) := measure_mono fun x hx ↦ ?_
    _ ≤ ∑' γ : Γ.op, μ (γ • K ∩ s) := measure_iUnion_le _
    _ = μ K := (hs.measure_eq_tsum K).symm
    _ < ∞ := hK.measure_lt_top
  obtain ⟨k, hk, γ, hγ, rfl⟩ : x ∈ K * (Γ : Set G) := hKΓ ▸ mem_univ x
  exact mem_iUnion.mpr ⟨⟨MulOpposite.op γ, hγ⟩, ⟨⟨k, hk, rfl⟩, hx⟩⟩

end Subgroup
