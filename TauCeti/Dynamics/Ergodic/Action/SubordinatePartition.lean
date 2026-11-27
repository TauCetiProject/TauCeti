/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Partitions subordinate to a subgroup

Let a topological group `G` act on a measurable space `X` carrying a measure `μ`, and let `V` be
a subgroup of `G`, with the subspace topology. A measurable partition of `X` is given by a label
`a : X → Y` into a standard Borel space `Y`; the atom of `x` is `a ⁻¹' {a x}`. The space `Y` may
be uncountable, so the partition may have uncountably many atoms.

The partition is *subordinate to `V`* (`TauCeti.SubordinatePartition μ V Y`) if for almost every
`x` the atom of `x` is contained in `K • x` for some compact `K ⊆ V` and contains `U • x` for some
open identity neighbourhood `U` of `V` (`TauCeti.IsSubordinateAt`). In particular almost every
atom lies in a single `V`-orbit. The compact set lives in `V`; no compact preimage in `V` is asked
for the atom, which matters when the orbit map has a noncompact stabilizer.

## Main results

* `TauCeti.SubordinatePartition.ae_atom_subset_orbit`: almost every atom lies in one `V`-orbit.
* `TauCeti.SubordinatePartition.relabel`: relabeling by a measurable equivalence of standard Borel
  spaces.
* `TauCeti.SubordinatePartition.ofAbsolutelyContinuous`: passage to an absolutely continuous
  measure.
* `TauCeti.SubordinatePartition.translate`: transport by an element `g` of the normalizer of `V`;
  the translated partition `x ↦ a (g⁻¹ • x)` is subordinate to `V` for the pushforward of `μ`
  under `g • ·`.

## References

* G. A. Margulis and G. M. Tomanov, Invariant measures for actions of unipotent groups over local
  fields on homogeneous spaces, Invent. Math. 116 (1994), 347–392, §9.3, pp. 381–383,
  doi:10.1007/BF01231565.
-/

public section

open MeasureTheory Set
open scoped Pointwise

namespace TauCeti

variable {G X Y Y' : Type*} [Group G] [TopologicalSpace G] [MulAction G X]

/-- The label `a` is *subordinate to the subgroup `V` at `x`*: the atom `a ⁻¹' {a x}` of `x` is
contained in `K • x` for some compact `K ⊆ V` and contains `U • x` for some open identity
neighbourhood `U` of `V`, `V` carrying the subspace topology. -/
def IsSubordinateAt (V : Subgroup G) (a : X → Y) (x : X) : Prop :=
  (∃ K : Set V, IsCompact K ∧ a ⁻¹' {a x} ⊆ (fun v : V ↦ (v : G) • x) '' K) ∧
    ∃ U : Set V, IsOpen U ∧ (1 : V) ∈ U ∧ (fun v : V ↦ (v : G) • x) '' U ⊆ a ⁻¹' {a x}

theorem isSubordinateAt_iff {V : Subgroup G} {a : X → Y} {x : X} :
    IsSubordinateAt V a x ↔
      (∃ K : Set V, IsCompact K ∧ a ⁻¹' {a x} ⊆ (fun v : V ↦ (v : G) • x) '' K) ∧
        ∃ U : Set V, IsOpen U ∧ (1 : V) ∈ U ∧ (fun v : V ↦ (v : G) • x) '' U ⊆ a ⁻¹' {a x} :=
  Iff.rfl

/-- At a point where a label is subordinate to `V`, the atom lies in the `V`-orbit. -/
theorem IsSubordinateAt.atom_subset_orbit {V : Subgroup G} {a : X → Y} {x : X}
    (h : IsSubordinateAt V a x) : a ⁻¹' {a x} ⊆ MulAction.orbit V x := by
  obtain ⟨⟨K, -, hK⟩, -⟩ := h
  intro y hy
  obtain ⟨v, -, rfl⟩ := hK hy
  exact ⟨v, rfl⟩

/-- Subordination at `x` depends only on the atoms: it is unchanged by an injective relabeling. -/
theorem IsSubordinateAt.comp_injective {V : Subgroup G} {a : X → Y} {x : X}
    (h : IsSubordinateAt V a x) {e : Y → Y'} (he : Function.Injective e) :
    IsSubordinateAt V (e ∘ a) x := by
  have hatom : (e ∘ a) ⁻¹' {(e ∘ a) x} = a ⁻¹' {a x} := by
    ext y
    simp [he.eq_iff]
  unfold IsSubordinateAt
  rw [hatom]
  exact h

variable [MeasurableSpace Y] [StandardBorelSpace Y] {mX : MeasurableSpace X}

variable (G) in
/-- A measurable partition of `X`, given by a label into a standard Borel space `Y`, *subordinate
to the subgroup `V`* for the measure `μ`: for `μ`-almost every `x`, the atom of `x` is contained
in `K • x` for a compact `K ⊆ V` and contains `U • x` for an open identity neighbourhood `U` of
`V`. -/
structure SubordinatePartition (μ : Measure X) (V : Subgroup G) (Y : Type*) [MeasurableSpace Y]
    [StandardBorelSpace Y] where
  /-- The label of the partition; its atoms are the fibres. -/
  label : X → Y
  measurable_label : Measurable label
  ae_isSubordinateAt : ∀ᵐ x ∂μ, IsSubordinateAt V label x

namespace SubordinatePartition

variable {μ ν : Measure X} {V : Subgroup G}

/-- Almost every atom of a subordinate partition lies in a single `V`-orbit. -/
theorem ae_atom_subset_orbit (η : SubordinatePartition G μ V Y) :
    ∀ᵐ x ∂μ, η.label ⁻¹' {η.label x} ⊆ MulAction.orbit V x :=
  η.ae_isSubordinateAt.mono fun _ hx ↦ hx.atom_subset_orbit

/-- Relabeling a subordinate partition by a measurable equivalence of standard Borel spaces gives a
subordinate partition with the same atoms. -/
@[expose, simps]
def relabel (η : SubordinatePartition G μ V Y) [MeasurableSpace Y'] [StandardBorelSpace Y']
    (e : Y ≃ᵐ Y') : SubordinatePartition G μ V Y' where
  label := e ∘ η.label
  measurable_label := e.measurable.comp η.measurable_label
  ae_isSubordinateAt := η.ae_isSubordinateAt.mono fun _ hx ↦ hx.comp_injective e.injective

/-- A partition subordinate to `V` for `μ` is subordinate to `V` for every measure absolutely
continuous with respect to `μ`. -/
@[expose, simps]
def ofAbsolutelyContinuous (η : SubordinatePartition G μ V Y) (h : ν ≪ μ) :
    SubordinatePartition G ν V Y where
  label := η.label
  measurable_label := η.measurable_label
  ae_isSubordinateAt := h.ae_le η.ae_isSubordinateAt

/-- Conjugation by an element `g` of the normalizer of `V`, as a homeomorphism of `V`. -/
@[expose]
def conjHomeomorph [IsTopologicalGroup G] {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    V ≃ₜ V where
  toFun v := ⟨g * v * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg v).1 v.property⟩
  invFun v := ⟨g⁻¹ * v * g, (Subgroup.mem_normalizer_iff''.1 hg v).1 v.property⟩
  left_inv v := by ext; simp [mul_assoc]
  right_inv v := by ext; simp [mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem conjHomeomorph_apply [IsTopologicalGroup G] {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (v : V) :
    (conjHomeomorph hg v : G) = g * v * g⁻¹ :=
  rfl

omit [MeasurableSpace Y] [StandardBorelSpace Y] in
/-- The translate of a label subordinate to `V` at `g⁻¹ • x` by an element `g` of the normalizer
of `V` is subordinate to `V` at `x`. -/
theorem _root_.TauCeti.IsSubordinateAt.translate [IsTopologicalGroup G] {a : X → Y} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) {x : X} (h : IsSubordinateAt V a (g⁻¹ • x)) :
    IsSubordinateAt V (fun y ↦ a (g⁻¹ • y)) x := by
  set c := conjHomeomorph hg
  have himage (S : Set V) : (fun v : V ↦ (v : G) • x) '' (c '' S) =
      (g • ·) '' ((fun v : V ↦ (v : G) • g⁻¹ • x) '' S) := by
    rw [image_image, image_image]
    refine image_congr fun v _ ↦ ?_
    simp [c, conjHomeomorph_apply, mul_smul]
  obtain ⟨⟨K, hK, hKa⟩, U, hU, hU1, hUa⟩ := h
  refine ⟨⟨c '' K, hK.image c.continuous, fun y hy ↦ ?_⟩,
    c '' U, c.isOpenMap U hU, ⟨1, hU1, by ext; simp [c, conjHomeomorph_apply]⟩, ?_⟩
  · rw [himage]
    exact ⟨g⁻¹ • y, hKa hy, by simp⟩
  · rw [himage]
    rintro _ ⟨z, hz, rfl⟩
    simpa using hUa hz

variable [MeasurableConstSMul G X]

/-- **Transport by the normalizer.** For `g` in the normalizer of `V`, the translate
`x ↦ η.label (g⁻¹ • x)` of a partition subordinate to `V` for `μ` is subordinate to `V` for the
pushforward of `μ` under `g • ·`. -/
@[expose, simps]
def translate [IsTopologicalGroup G] (η : SubordinatePartition G μ V Y) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) : SubordinatePartition G (μ.map (g • ·)) V Y where
  label x := η.label (g⁻¹ • x)
  measurable_label := η.measurable_label.comp (measurable_const_smul g⁻¹)
  ae_isSubordinateAt := by
    rw [(measurableEmbedding_const_smul g).ae_map_iff]
    exact η.ae_isSubordinateAt.mono fun x hx ↦ IsSubordinateAt.translate hg (by simpa using hx)

end SubordinatePartition

end TauCeti
