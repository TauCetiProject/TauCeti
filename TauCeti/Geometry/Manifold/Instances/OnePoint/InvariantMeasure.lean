/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import TauCeti.Geometry.Manifold.Instances.OnePoint.ContinuousSMul
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.GroupTheory.Amenable.Abelian
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.MeasureTheory.Group.Action
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
import TauCeti.Topology.Algebra.Projectivization
import TauCeti.Topology.Compactification.OnePoint.Amenable

/-!
# Invariant measures on the projective line and Furstenberg's lemma

An escaping sequence of Möbius transformations in `PSL(2, 𝕜)` over a proper nontrivially normed
field `𝕜` degenerates along a subsequence to a constant `b : OnePoint 𝕜` away from an exceptional
point `a` (`OnePoint.exists_tendsto_psl_smul_of_tendsto_cocompact`). Passing to a further
subsequence so that the image of `a` also converges to a point `c`, every open neighborhood `W` of
`{b, c}` eventually absorbs the orbit of every point of `OnePoint 𝕜`. If a finite Borel measure `μ`
on `OnePoint 𝕜` is preserved by the sequence, monotone continuity from below shows that `W` carries
full `μ`-measure; writing `{b, c}` as a countable intersection of open sets concludes that `μ` is
supported on `{b, c}`.

This is Furstenberg's boundary concentration lemma in rank one. When `μ` is nonzero, at least one
of `b` or `c` is an atom of `μ`. For a subgroup `Γ ≤ PSL(2, 𝕜)` preserving `μ`, any atom has finite
`Γ`-orbit (`MeasureTheory.finite_orbit_of_measure_singleton_ne_zero`). When `Γ` is discrete in
`PSL(2, 𝕜)`:

* if `Γ` is finite, it is amenable;
* if `Γ` is infinite, it is closed in `PSL(2, 𝕜)` with discrete topology, so an enumeration of a
  countable infinite subset escapes to `cocompact PSL(2, 𝕜)`, producing an atom with finite
  `Γ`-orbit; since point stabilizers in `PSL(2, 𝕜)` are amenable
  (`OnePoint.amenable_psl_stabilizer`), `Γ` is amenable (`TauCeti.Amenable.of_finite_orbit`).

Specializing to `𝕜 = ℝ`, any group `G` admitting an injective homomorphism `ι : G →* SL(2, ℤ)` that
preserves a nonzero finite Borel measure on `OnePoint ℝ` through `sl2zToPSL2R` is amenable: its
projective image in `PSL(2, ℝ)` is discrete (`Subgroup.discreteTopology_map_sl2zToPSL2R`), and the
kernel of `sl2zToPSL2R ∘ ι` embeds into the center of `SL(2, ℤ)`.

## Main results

* `OnePoint.exists_measure_compl_pair_eq_zero_of_tendsto_psl_cocompact`: a finite Borel measure on
  `OnePoint 𝕜` preserved by an escaping sequence in `PSL(2, 𝕜)` is supported on at most two points.
* `OnePoint.exists_measure_singleton_ne_zero_of_tendsto_psl_cocompact`: if the measure is nonzero,
  it has an atom.
* `Subgroup.amenable_of_discreteTopology_psl`: a discrete subgroup of `PSL(2, 𝕜)` preserving a
  nonzero finite Borel measure on `OnePoint 𝕜` is amenable.
* `TauCeti.amenable_of_injective_sl2z_of_map_smul_eq` and
  `TauCeti.hasFoelnerSets_of_injective_sl2z_of_map_smul_eq`: a group embedding into `SL(2, ℤ)` and
  preserving a nonzero finite Borel measure on `OnePoint ℝ` is amenable and has Følner sets.

## References

* H. Furstenberg, *A Poisson formula for semi-simple Lie groups*, Annals of Mathematics 77 (1963),
  335–386.
* R. J. Zimmer, *Ergodic Theory and Semisimple Groups*, Monographs in Mathematics 81, Birkhäuser,
  1984, §3.2.
-/

public section

open Filter Topology MeasureTheory Set Matrix
open scoped ENNReal MatrixGroups Pointwise

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]
  {_ : MeasurableSpace (OnePoint 𝕜)} [BorelSpace (OnePoint 𝕜)]

namespace OnePoint

/-- **Furstenberg's concentration lemma on the projective line.** If a sequence `g : ℕ → PSL(2, 𝕜)`
escapes every compact subset of `PSL(2, 𝕜)` and preserves a finite Borel measure `μ` on
`OnePoint 𝕜`, then `μ` is supported on a set of at most two points. -/
theorem exists_measure_compl_pair_eq_zero_of_tendsto_psl_cocompact
    {μ : Measure (OnePoint 𝕜)} [IsFiniteMeasure μ] {g : ℕ → PSL(2, 𝕜)}
    (hg : Tendsto g atTop (cocompact PSL(2, 𝕜)))
    (hinv : ∀ n, Measure.map (g n • ·) μ = μ) :
    ∃ b c : OnePoint 𝕜, μ ({b, c}ᶜ) = 0 := by
  have : SecondCountableTopology (OnePoint 𝕜) :=
    (diffeomorphProjectivization 𝕜 0).toHomeomorph.secondCountableTopology
  obtain ⟨φ, a, b, -, hlim⟩ := exists_tendsto_psl_smul_of_tendsto_cocompact hg
  obtain ⟨c, -, ψ, hψ, hlim_a⟩ := isSeqCompact_univ.subseq_of_frequently_in
    (Frequently.of_forall fun n ↦ mem_univ (g (φ n) • a))
  let h : ℕ → PSL(2, 𝕜) := fun n ↦ g (φ (ψ n))
  refine ⟨b, c, Measure.measure_compl_eq_zero_of_isGδ_of_tendsto
    (Set.toFinite ({b, c} : Set (OnePoint 𝕜))).isGδ
    (fun n ↦ (continuous_const_smul (h n)).measurable)
    (fun n ↦ hinv (φ (ψ n))) fun x ↦ ?_⟩
  by_cases hxa : x = a
  · exact ⟨c, by simp, hxa ▸ hlim_a⟩
  · exact ⟨b, by simp, (hlim hxa tendsto_const_nhds).comp hψ.tendsto_atTop⟩

/-- If a nonzero finite Borel measure on `OnePoint 𝕜` is preserved by an escaping sequence in
`PSL(2, 𝕜)`, then it has an atom. -/
theorem exists_measure_singleton_ne_zero_of_tendsto_psl_cocompact
    {μ : Measure (OnePoint 𝕜)} [IsFiniteMeasure μ] (hμ : μ ≠ 0) {g : ℕ → PSL(2, 𝕜)}
    (hg : Tendsto g atTop (cocompact PSL(2, 𝕜)))
    (hinv : ∀ n, Measure.map (g n • ·) μ = μ) :
    ∃ b : OnePoint 𝕜, μ {b} ≠ 0 := by
  obtain ⟨b, c, hbc⟩ := exists_measure_compl_pair_eq_zero_of_tendsto_psl_cocompact hg hinv
  obtain ⟨x, -, hx⟩ :=
    (Set.toFinite ({b, c} : Set (OnePoint 𝕜))).countable.exists_mem_measure_singleton_ne_zero
      hμ hbc
  exact ⟨x, hx⟩

end OnePoint

namespace Subgroup

/-- A discrete subgroup of `PSL(2, 𝕜)` that preserves a nonzero finite Borel measure on
`OnePoint 𝕜` is amenable. -/
theorem amenable_of_discreteTopology_psl (Γ : Subgroup PSL(2, 𝕜)) [DiscreteTopology Γ]
    {μ : Measure (OnePoint 𝕜)} [IsFiniteMeasure μ] [SMulInvariantMeasure Γ (OnePoint 𝕜) μ]
    (hμ : μ ≠ 0) : TauCeti.Amenable Γ := by
  by_cases hfin : Finite Γ
  · exact inferInstance
  · have : Infinite Γ := not_finite_iff_infinite.mp hfin
    have hcl : IsClosed (Γ : Set PSL(2, 𝕜)) := Subgroup.isClosed_of_discreteTopology
    let e : ℕ ↪ Γ := Infinite.natEmbedding Γ
    have he_cocompact : Tendsto (fun n ↦ (e n : PSL(2, 𝕜))) atTop (cocompact PSL(2, 𝕜)) :=
      hcl.isClosedEmbedding_subtypeVal.tendsto_cocompact.comp
        (Filter.cocompact_eq_cofinite Γ ▸ Nat.cofinite_eq_atTop ▸ e.injective.tendsto_cofinite)
    have he_inv (n : ℕ) : Measure.map ((e n : PSL(2, 𝕜)) • ·) μ = μ :=
      MeasureTheory.map_smul (e n) μ
    obtain ⟨x₀, hx₀⟩ :=
      OnePoint.exists_measure_singleton_ne_zero_of_tendsto_psl_cocompact hμ he_cocompact he_inv
    have : Finite (MulAction.orbit Γ x₀) := finite_orbit_of_measure_singleton_ne_zero hx₀
    have hcomap : (MulAction.stabilizer PSL(2, 𝕜) x₀).comap Γ.subtype =
        MulAction.stabilizer Γ x₀ := by
      ext
      simp [Subgroup.smul_def]
    have : TauCeti.Amenable (MulAction.stabilizer Γ x₀) :=
      hcomap ▸ Γ.subtype.amenable_comap_onePoint_psl_stabilizer Γ.subtype_injective x₀
    exact TauCeti.Amenable.of_finite_orbit x₀

end Subgroup

end NormedField

namespace TauCeti

open scoped IsMulCommutative

/-- A topological group admitting an injective homomorphism into `SL(2, ℤ)` that preserves a
nonzero finite Borel measure on `OnePoint ℝ` through `sl2zToPSL2R` is amenable. -/
theorem amenable_of_injective_sl2z_of_map_smul_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {ι : G →* SL(2, ℤ)} (hι : Function.Injective ι)
    {_ : MeasurableSpace (OnePoint ℝ)} [BorelSpace (OnePoint ℝ)]
    {μ : Measure (OnePoint ℝ)} [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ g : G, Measure.map (sl2zToPSL2R (ι g) • ·) μ = μ) :
    Amenable G := by
  apply Amenable.of_discrete
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let Γ : Subgroup PSL(2, ℝ) := ι.range.map sl2zToPSL2R
  have hSMul : SMulInvariantMeasure Γ (OnePoint ℝ) μ := ⟨fun γ s hs ↦ by
    obtain ⟨_, ⟨g, rfl⟩, hγ⟩ := γ.property
    simp only [Subgroup.smul_def, ← hγ]
    rw [← Measure.map_apply (continuous_const_smul _).measurable hs, hinv g]⟩
  have : Amenable Γ := Γ.amenable_of_discreteTopology_psl hμ
  let φ : G →* Γ := (sl2zToPSL2R.comp ι).codRestrict Γ fun g ↦ ⟨ι g, ⟨g, rfl⟩, rfl⟩
  let : TopologicalSpace SL(2, ℤ) := ⊥
  let : DiscreteTopology SL(2, ℤ) := ⟨rfl⟩
  let ψ : φ.ker →* Subgroup.center SL(2, ℤ) :=
    (ι.comp φ.ker.subtype).codRestrict (Subgroup.center SL(2, ℤ)) fun g ↦ by
      rw [← sl2zToPSL2R_ker, MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp g.property)
  have hψ : Function.Injective ψ :=
    (MonoidHom.injective_codRestrict _ _ _).mpr (hι.comp φ.ker.subtype_injective)
  have : Amenable φ.ker := Amenable.of_injective ψ hψ
  exact Amenable.of_ker_le_range φ.ker.subtype φ (by simp)

/-- A group admitting an injective homomorphism into `SL(2, ℤ)` that preserves a nonzero finite
Borel measure on `OnePoint ℝ` through `sl2zToPSL2R` has Følner sets. -/
theorem hasFoelnerSets_of_injective_sl2z_of_map_smul_eq {G : Type*} [Group G]
    {ι : G →* SL(2, ℤ)} (hι : Function.Injective ι)
    {_ : MeasurableSpace (OnePoint ℝ)} [BorelSpace (OnePoint ℝ)]
    {μ : Measure (OnePoint ℝ)} [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ g : G, Measure.map (sl2zToPSL2R (ι g) • ·) μ = μ) :
    HasFoelnerSets G := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  have : Amenable G := amenable_of_injective_sl2z_of_map_smul_eq hι hμ hinv
  exact Amenable.hasFoelnerSets

end TauCeti
