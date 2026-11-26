/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.MeasureTheory.Group.ProperlyDiscontinuous
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# Lattices in locally compact groups

A *lattice* in a unimodular locally compact group `G` is a discrete subgroup `Γ` of finite
covolume: the right action of `Γ` on `G`, `g ↦ g γ`, has a measurable fundamental domain of finite
Haar measure. The quotient `G ⧸ Γ` is the space of left cosets `g Γ`. A lattice is *uniform* if
`G = K Γ` for a compact set `K`.

The theory is set in a unimodular group: the lattice condition asks that `μ` be a Haar measure
that is right invariant, so that the measure of a fundamental domain of the right action does not
depend on the choice of domain. Without this the finiteness of the measure of one fundamental
domain says nothing: a group containing a lattice is unimodular, while in the non-unimodular
`ax + b` group the discrete subgroup `{(2ⁿ, 0)}` has fundamental domains of both finite and
infinite left Haar measure.

A discrete subgroup of a second countable, locally compact Hausdorff group has a measurable
fundamental domain (`Subgroup.exists_isFundamentalDomain_op`); the lattice condition asks that it
have finite measure. Integrals over `G` unfold to integrals over `G ⧸ Γ` by Weil's
formula (`QuotientGroup.lintegral_eq_lintegral_automorphize`), and `G ⧸ Γ` is compact exactly when
`K * Γ = G` for a compact set `K` (`QuotientGroup.compactSpace_iff_exists_isCompact_mul_eq_univ`).

## Main definitions

* `Subgroup.IsLattice Γ μ`: `μ` is a right invariant Haar measure, `Γ` is discrete and the right
  action of `Γ` on `G` has a fundamental domain of finite `μ`-measure.
* `Subgroup.IsUniformLattice Γ μ`: a lattice `Γ` with `K * Γ = G` for some compact `K`.

## Main results

* `Subgroup.isLattice_iff_discreteTopology_and_covolume_lt_top`: for a right invariant Haar
  measure `μ`, `Γ` is a lattice exactly when it is discrete and `MeasureTheory.covolume Γ.op G μ`
  is finite.
* `Subgroup.IsLattice.of_isHaarMeasure`, `Subgroup.IsUniformLattice.of_isHaarMeasure`: being a
  (uniform) lattice does not depend on the Haar measure.
* `Subgroup.IsLattice.isFiniteMeasure_quotient`: the quotient measure on `G ⧸ Γ` of a lattice is
  finite.
* `Subgroup.IsUniformLattice.compactSpace`: the quotient by a uniform lattice is compact.
* `Subgroup.isUniformLattice_iff_isLattice_and_compactSpace`: in a weakly locally compact group,
  a lattice is uniform exactly when `G ⧸ Γ` is compact.
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

/-- A subgroup `Γ` of `G` is a **lattice** with respect to the measure `μ` if `μ` is a right
invariant Haar measure, `Γ` is discrete and the right action of `Γ` on `G`, `g ↦ g γ`, has a
fundamental domain of finite `μ`-measure. The intended setting is a unimodular locally compact
group `G`; asking for a Haar measure rules out degenerate measures such as `0`, right invariance
makes the condition independent of the fundamental domain, it does not depend on the Haar measure
(`Subgroup.IsLattice.of_isHaarMeasure`), and for discrete `Γ` it says that
`MeasureTheory.covolume Γ.op G μ` is finite
(`Subgroup.isLattice_iff_discreteTopology_and_covolume_lt_top`). -/
structure IsLattice [TopologicalSpace G] (Γ : Subgroup G) (μ : Measure G) : Prop where
  /-- The covolume of a lattice is measured by a Haar measure. -/
  isHaarMeasure : μ.IsHaarMeasure
  /-- A lattice lives in a unimodular group: the measure is right invariant. -/
  isMulRightInvariant : μ.IsMulRightInvariant
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

/-- A lattice in a hereditarily Lindelöf (for instance second countable) group is countable. -/
theorem IsLattice.countable [HereditarilyLindelofSpace G] (h : Γ.IsLattice μ) : Countable Γ :=
  have := h.discreteTopology
  countable_of_Lindelof_of_discrete

/-- A lattice has a fundamental domain for its right action. -/
theorem IsLattice.hasFundamentalDomain (h : Γ.IsLattice μ) : HasFundamentalDomain Γ.op G μ :=
  ⟨h.exists_isFundamentalDomain_measure_lt_top.imp fun _ ↦ And.left⟩

/-- The quotient of `G` by a uniform lattice is compact. -/
theorem IsUniformLattice.compactSpace (h : Γ.IsUniformLattice μ) : CompactSpace (G ⧸ Γ) :=
  have ⟨_, hK, hKΓ⟩ := h.exists_isCompact_mul_eq_univ
  ⟨QuotientGroup.image_mk_eq_univ_iff.mpr hKΓ ▸ hK.image QuotientGroup.continuous_mk⟩

variable [IsTopologicalGroup G]

/-- Being a lattice does not depend on the choice of Haar measure. -/
theorem IsLattice.of_isHaarMeasure [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] {ν : Measure G} [ν.IsHaarMeasure]
    (h : Γ.IsLattice μ) : Γ.IsLattice ν := by
  have := h.isHaarMeasure
  have := h.isMulRightInvariant
  obtain ⟨s, hs, hμs⟩ := h.exists_isFundamentalDomain_measure_lt_top
  -- `ν` is a constant multiple of `μ`, so it is right invariant as well
  have hνμ := Measure.isMulLeftInvariant_eq_smul ν μ
  have : ν.IsMulRightInvariant := by rw [hνμ]; infer_instance
  refine ⟨inferInstance, inferInstance, h.discreteTopology, s, ?_⟩
  rw [hνμ, Measure.coe_nnreal_smul_apply]
  exact ⟨hs.mono Measure.smul_absolutelyContinuous, ENNReal.mul_lt_top ENNReal.coe_lt_top hμs⟩

/-- Being a uniform lattice does not depend on the choice of Haar measure. -/
theorem IsUniformLattice.of_isHaarMeasure [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] {ν : Measure G} [ν.IsHaarMeasure]
    (h : Γ.IsUniformLattice μ) : Γ.IsUniformLattice ν :=
  ⟨h.toIsLattice.of_isHaarMeasure, h.exists_isCompact_mul_eq_univ⟩

omit [IsTopologicalGroup G] in
/-- A lattice has finite covolume. -/
theorem IsLattice.covolume_lt_top [MeasurableConstSMul Gᵐᵒᵖ G] [Countable Γ] (h : Γ.IsLattice μ) :
    covolume Γ.op G μ < ∞ := by
  have := h.isMulRightInvariant
  obtain ⟨s, hs, hμs⟩ := h.exists_isFundamentalDomain_measure_lt_top
  rwa [hs.covolume_eq_volume]

/-- For a right invariant Haar measure on a second countable, locally compact Hausdorff group, a
subgroup is a lattice exactly when it is discrete and its right action has finite covolume. -/
theorem isLattice_iff_discreteTopology_and_covolume_lt_top [BorelSpace G] [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] :
    Γ.IsLattice μ ↔ DiscreteTopology Γ ∧ covolume Γ.op G μ < ∞ := by
  refine ⟨fun h ↦ ⟨h.discreteTopology, have := h.countable; h.covolume_lt_top⟩,
    fun ⟨hd, hcov⟩ ↦ ⟨inferInstance, inferInstance, hd, ?_⟩⟩
  have : Countable Γ := countable_of_Lindelof_of_discrete
  obtain ⟨s, -, hs⟩ := Γ.exists_isFundamentalDomain_op μ
  exact ⟨s, hs, hs.covolume_eq_volume μ ▸ hcov⟩

omit [IsTopologicalGroup G] in
/-- The quotient measure on `G ⧸ Γ` of a lattice `Γ` is finite. -/
theorem IsLattice.isFiniteMeasure_quotient (h : Γ.IsLattice μ) (ν : Measure (G ⧸ Γ))
    [QuotientMeasureEqMeasurePreimage μ ν] : IsFiniteMeasure ν := by
  obtain ⟨s, hs, hμs⟩ := h.exists_isFundamentalDomain_measure_lt_top
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs.ne
  rw [hs.projection_respects_measure ν]
  infer_instance

end Subgroup

namespace Subgroup

variable [TopologicalSpace G] {Γ : Subgroup G} {μ : Measure G}

/-- In a weakly locally compact group with separately continuous multiplication, a lattice is
uniform exactly when `G ⧸ Γ` is compact. -/
theorem isUniformLattice_iff_isLattice_and_compactSpace [SeparatelyContinuousMul G]
    [WeaklyLocallyCompactSpace G] :
    Γ.IsUniformLattice μ ↔ Γ.IsLattice μ ∧ CompactSpace (G ⧸ Γ) :=
  ⟨fun h ↦ ⟨h.toIsLattice, h.compactSpace⟩,
    fun ⟨h, hc⟩ ↦ ⟨h, QuotientGroup.compactSpace_iff_exists_isCompact_mul_eq_univ.mp hc⟩⟩

/-- In a unimodular, second countable, locally compact Hausdorff group, a discrete subgroup with
compact quotient `G ⧸ Γ` has finite covolume: a fundamental domain has measure at most that of a
compact set `K` with `K * Γ = G`. So it is a uniform lattice. -/
theorem isUniformLattice_iff_discreteTopology_and_compactSpace [IsTopologicalGroup G]
    [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] :
    Γ.IsUniformLattice μ ↔ DiscreteTopology Γ ∧ CompactSpace (G ⧸ Γ) := by
  refine ⟨fun h ↦ ⟨h.discreteTopology, h.compactSpace⟩, fun ⟨hd, hc⟩ ↦ ?_⟩
  obtain ⟨K, hK, hKΓ⟩ := QuotientGroup.compactSpace_iff_exists_isCompact_mul_eq_univ.mp hc
  have : Countable Γ := countable_of_Lindelof_of_discrete
  obtain ⟨s, -, hs⟩ := Γ.exists_isFundamentalDomain_op μ
  -- `K * Γ = G` says the right `Γ`-translates of `K` cover `G`
  have hcov : s ⊆ ⋃ γ : Γ.op, γ • K := fun x _ ↦ by
    obtain ⟨k, hk, γ, hγ, rfl⟩ : x ∈ K * (Γ : Set G) := hKΓ ▸ mem_univ x
    refine mem_iUnion.mpr ⟨⟨MulOpposite.op γ, Subgroup.mem_op.mpr hγ⟩, k, hk, ?_⟩
    simp only [Subgroup.mk_smul, op_smul_eq_mul]
  exact ⟨⟨inferInstance, inferInstance, hd, s, hs,
    (hs.measure_le_of_subset_iUnion_smul hcov).trans_lt hK.measure_lt_top⟩, K, hK, hKΓ⟩

end Subgroup
