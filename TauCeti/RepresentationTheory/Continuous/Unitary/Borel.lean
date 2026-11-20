/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.StrongUnitary.Borel
public import TauCeti.RepresentationTheory.Continuous.Unitary.StronglyContinuous
public import TauCeti.Topology.Algebra.Group.Baire

/-!
# Borel unitary representations and automatic strong continuity

On a separable Hilbert space `H`, `TauCeti.StrongUnitary 𝕜 H` is a Polish topological group whose
Borel σ-algebra is generated both by the matrix-coefficient maps `u ↦ ⟪d i, u (d j)⟫_𝕜` and by the
evaluation maps `u ↦ u (d i)` along any countable dense family `d : ι → H` (when `𝕜`, respectively
`H`, carries its Borel σ-algebra). For a unitary group representation `π : ContRepresentation 𝕜 G H`
with `hπ : π.IsUnitary`, the matrix coefficients `g ↦ ⟪d i, π g (d j)⟫_𝕜` and orbits
`g ↦ π g (d i)` are the pullbacks of these coordinate maps along
`hπ.toStrongUnitaryHom : G →* TauCeti.StrongUnitary 𝕜 H`.

Combining the resulting four measurability equivalences (specializing `StrongUnitary/Borel.lean`
along `ContRepresentation.IsUnitary.toStrongUnitaryHom`) with Pettis automatic continuity
(`TauCeti.continuous_of_measurable_monoidHom`) yields **automatic strong continuity of Borel
unitary representations**: on any Baire Borel topological group `G` (in particular any Polish group
or any locally compact Hausdorff group), a unitary representation on a separable Hilbert space is
strongly continuous as soon as either its matrix coefficients or its orbits along a countable dense
subset of `H` are Borel-measurable.

## Main declarations

* `ContRepresentation.IsUnitary.measurable_toStrongUnitaryHom_iff_inner_of_dense`,
  `ContRepresentation.IsUnitary.measurable_toStrongUnitaryHom_iff_inner`,
  `ContRepresentation.IsUnitary.measurable_toStrongUnitaryHom_iff_apply_of_dense`, and
  `ContRepresentation.IsUnitary.measurable_toStrongUnitaryHom_iff_apply`: the four-way
  characterization of Borel measurability of `hπ.toStrongUnitaryHom`.
* `ContRepresentation.IsUnitary.continuous_apply_of_measurable_inner_of_dense`,
  `ContRepresentation.IsUnitary.continuous_apply_of_measurable_inner`,
  `ContRepresentation.IsUnitary.continuous_apply_iff_measurable_inner_of_dense`, and
  `ContRepresentation.IsUnitary.continuous_apply_iff_measurable_inner`: automatic strong continuity
  from measurable matrix coefficients.
* `ContRepresentation.IsUnitary.continuous_apply_of_measurable_apply_of_dense`,
  `ContRepresentation.IsUnitary.continuous_apply_of_measurable_apply`,
  `ContRepresentation.IsUnitary.continuous_apply_iff_measurable_apply_of_dense`, and
  `ContRepresentation.IsUnitary.continuous_apply_iff_measurable_apply`: automatic strong continuity
  from measurable orbits.

## References

* D. P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs 134, AMS,
  2007, Theorem D.11 and Lemmas D.42–D.43.
-/

public noncomputable section

open MeasureTheory Topology TopologicalSpace
open scoped InnerProductSpace

namespace ContRepresentation.IsUnitary

variable {𝕜 G H : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] {π : ContRepresentation 𝕜 G H}

section Measurable

variable [MeasurableSpace G]

section Inner

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Borel measurability of `hπ.toStrongUnitaryHom` is equivalent to measurability of matrix
coefficients along any countable dense family in `H`. -/
theorem measurable_toStrongUnitaryHom_iff_inner_of_dense {ι : Type*} [Countable ι] {d : ι → H}
    (hπ : π.IsUnitary) (hd : DenseRange d) :
    Measurable hπ.toStrongUnitaryHom ↔ ∀ i j : ι, Measurable fun g => ⟪d i, π g (d j)⟫_𝕜 := by
  simp_rw [TauCeti.StrongUnitary.measurable_iff_forall_measurable_inner_of_dense hd,
    hπ.toStrongUnitaryHom_apply]

/-- Borel measurability of `hπ.toStrongUnitaryHom` is equivalent to measurability of all matrix
coefficients `g ↦ ⟪ξ, π g η⟫_𝕜`. -/
theorem measurable_toStrongUnitaryHom_iff_inner [SeparableSpace H] (hπ : π.IsUnitary) :
    Measurable hπ.toStrongUnitaryHom ↔ ∀ ξ η : H, Measurable fun g => ⟪ξ, π g η⟫_𝕜 := by
  simp_rw [TauCeti.StrongUnitary.measurable_iff_forall_measurable_inner,
    hπ.toStrongUnitaryHom_apply]

end Inner

section Apply

variable [MeasurableSpace H] [BorelSpace H]

/-- Borel measurability of `hπ.toStrongUnitaryHom` is equivalent to Borel measurability of orbits
`g ↦ π g (d i)` along any countable dense family in `H`. -/
theorem measurable_toStrongUnitaryHom_iff_apply_of_dense {ι : Type*} [Countable ι] {d : ι → H}
    (hπ : π.IsUnitary) (hd : DenseRange d) :
    Measurable hπ.toStrongUnitaryHom ↔ ∀ i : ι, Measurable fun g => π g (d i) := by
  simp_rw [TauCeti.StrongUnitary.measurable_iff_forall_measurable_apply_of_dense hd,
    hπ.toStrongUnitaryHom_apply]

/-- Borel measurability of `hπ.toStrongUnitaryHom` is equivalent to Borel measurability of all
orbits `g ↦ π g η`. -/
theorem measurable_toStrongUnitaryHom_iff_apply [SeparableSpace H] (hπ : π.IsUnitary) :
    Measurable hπ.toStrongUnitaryHom ↔ ∀ η : H, Measurable fun g => π g η := by
  simp_rw [TauCeti.StrongUnitary.measurable_iff_forall_measurable_apply,
    hπ.toStrongUnitaryHom_apply]

end Apply

end Measurable

section AutomaticContinuity

variable [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]
  [MeasurableSpace G] [BorelSpace G]

section Inner

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- **Automatic strong continuity of Borel unitary representations (matrix coefficients).** On a
Baire Borel topological group `G` (such as any Polish group or any locally compact Hausdorff group),
if the matrix coefficients `g ↦ ⟪d i, π g (d j)⟫_𝕜` of a unitary representation `π` are measurable
along a countable dense family `d : ι → H`, then every orbit `g ↦ π g ξ` is continuous. -/
theorem continuous_apply_of_measurable_inner_of_dense {ι : Type*} [Countable ι] {d : ι → H}
    (hπ : π.IsUnitary) (hd : DenseRange d)
    (hm : ∀ i j : ι, Measurable fun g => ⟪d i, π g (d j)⟫_𝕜) (ξ : H) :
    Continuous fun g => π g ξ := by
  have : SeparableSpace H := .of_denseRange d hd
  exact (hπ.continuous_toStrongUnitaryHom_iff.1 <|
    TauCeti.continuous_of_measurable_monoidHom hπ.toStrongUnitaryHom
      ((hπ.measurable_toStrongUnitaryHom_iff_inner_of_dense hd).2 hm)) ξ

/-- If all matrix coefficients `g ↦ ⟪ξ, π g η⟫_𝕜` of a unitary representation of a Baire Borel
topological group on a separable Hilbert space are measurable, then `π` is strongly continuous. -/
theorem continuous_apply_of_measurable_inner [SeparableSpace H] (hπ : π.IsUnitary)
    (hm : ∀ ξ η : H, Measurable fun g => ⟪ξ, π g η⟫_𝕜) (ξ : H) :
    Continuous fun g => π g ξ := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  exact hπ.continuous_apply_of_measurable_inner_of_dense hd (fun i j => hm (d i) (d j)) ξ

/-- On a Baire Borel topological group `G`, strong continuity of a unitary representation is
equivalent to Borel measurability of its matrix coefficients on any countable dense subset of
`H`. -/
theorem continuous_apply_iff_measurable_inner_of_dense {ι : Type*} [Countable ι] {d : ι → H}
    (hπ : π.IsUnitary) (hd : DenseRange d) :
    (∀ ξ, Continuous fun g => π g ξ) ↔ ∀ i j : ι, Measurable fun g => ⟪d i, π g (d j)⟫_𝕜 :=
  ⟨fun hc _ j => (continuous_const.inner (hc (d j))).measurable,
    hπ.continuous_apply_of_measurable_inner_of_dense hd⟩

/-- On a Baire Borel topological group `G` and separable Hilbert space `H`, strong continuity of a
unitary representation is equivalent to Borel measurability of all its matrix coefficients. -/
theorem continuous_apply_iff_measurable_inner [SeparableSpace H] (hπ : π.IsUnitary) :
    (∀ ξ, Continuous fun g => π g ξ) ↔ ∀ ξ η : H, Measurable fun g => ⟪ξ, π g η⟫_𝕜 :=
  ⟨fun hc _ η => (continuous_const.inner (hc η)).measurable,
    hπ.continuous_apply_of_measurable_inner⟩

end Inner

section Apply

variable [MeasurableSpace H] [BorelSpace H]

/-- **Automatic strong continuity of Borel unitary representations (dense orbits).** On a Baire
Borel topological group `G`, if the orbits `g ↦ π g (d i)` of a unitary representation `π` are
Borel-measurable along a countable dense family `d : ι → H`, then every orbit `g ↦ π g ξ` is
continuous. -/
theorem continuous_apply_of_measurable_apply_of_dense {ι : Type*} [Countable ι] {d : ι → H}
    (hπ : π.IsUnitary) (hd : DenseRange d)
    (hm : ∀ i : ι, Measurable fun g => π g (d i)) (ξ : H) :
    Continuous fun g => π g ξ := by
  have : SeparableSpace H := .of_denseRange d hd
  exact (hπ.continuous_toStrongUnitaryHom_iff.1 <|
    TauCeti.continuous_of_measurable_monoidHom hπ.toStrongUnitaryHom
      ((hπ.measurable_toStrongUnitaryHom_iff_apply_of_dense hd).2 hm)) ξ

/-- If all orbits `g ↦ π g η` of a unitary representation of a Baire Borel topological group on a
separable Hilbert space are Borel-measurable, then `π` is strongly continuous. -/
theorem continuous_apply_of_measurable_apply [SeparableSpace H] (hπ : π.IsUnitary)
    (hm : ∀ η : H, Measurable fun g => π g η) (ξ : H) :
    Continuous fun g => π g ξ := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  exact hπ.continuous_apply_of_measurable_apply_of_dense hd (fun i => hm (d i)) ξ

/-- On a Baire Borel topological group `G`, strong continuity of a unitary representation is
equivalent to Borel measurability of its orbits along any countable dense subset of `H`. -/
theorem continuous_apply_iff_measurable_apply_of_dense {ι : Type*} [Countable ι] {d : ι → H}
    (hπ : π.IsUnitary) (hd : DenseRange d) :
    (∀ ξ, Continuous fun g => π g ξ) ↔ ∀ i : ι, Measurable fun g => π g (d i) :=
  ⟨fun hc i => (hc (d i)).measurable, hπ.continuous_apply_of_measurable_apply_of_dense hd⟩

/-- On a Baire Borel topological group `G` and separable Hilbert space `H`, strong continuity of a
unitary representation is equivalent to Borel measurability of all its orbits. -/
theorem continuous_apply_iff_measurable_apply [SeparableSpace H] (hπ : π.IsUnitary) :
    (∀ ξ, Continuous fun g => π g ξ) ↔ ∀ η : H, Measurable fun g => π g η :=
  ⟨fun hc η => (hc η).measurable, hπ.continuous_apply_of_measurable_apply⟩

end Apply

end AutomaticContinuity

end ContRepresentation.IsUnitary
