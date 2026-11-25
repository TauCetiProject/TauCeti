/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.Topology.Algebra.Projectivization.Action
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Instances.Int
import TauCeti.Analysis.Matrix.Normed
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.Finite
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.MeasureTheory.Group.Action
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import TauCeti.Topology.Compactification.OnePoint.Amenable

/-!
# Invariant probability measures on the projective line

Let `𝕜` be `ℝ` or `ℂ`, and let `G` be a group represented faithfully in `GL(2, 𝕜)` by matrices with
`‖det(φ g)‖ = 1` which escape compact sets of `Matrix (Fin 2) (Fin 2) 𝕜` along the cofinite filter.
If `G` preserves a Borel probability measure `μ` on the projective line `ℙ 𝕜 (Fin 2 → 𝕜)`, then `G`
has Følner sets (`TauCeti.HasFoelnerSets G`) and is amenable for every group topology
(`TauCeti.Amenable G`). This is the `GL(2, 𝕜)` case of Furstenberg's lemma on projective invariant
measures.

When `G` is finite the conclusion is immediate. When `G` is infinite, an enumeration of a countable
infinite subset of `G` produces matrices escaping every compact set with unit determinant norm,
which after scalar normalization subconverge to a nonzero singular `2 × 2` matrix `B`
(`Matrix.exists_tendsto_inv_smul_of_tendsto_cocompact`). By
`Projectivization.exists_linearProjectionDomain_eq_and_linearProjection_eq_of_det_eq_zero`,
`Projectivization.linearProjection B.mulVecLin` is defined away from a point `p` and takes a
constant value `q` there, so away from `p` the orbit of every point converges to `q`
(`Projectivization.tendsto_smul_of_tendsto_smul_coe`); passing to a further subsequence, the orbit
of `p` also converges to some `r`. Measure concentration on the `Gδ` pair `{q, r}`
(`MeasureTheory.Measure.measure_compl_eq_zero_of_isGδ_of_tendsto`) then gives `μ` an atom `x₀`
(`Set.Countable.exists_mem_measure_singleton_ne_zero`). Under the action of `φ.range`, `x₀` has a
finite orbit (`MeasureTheory.finite_orbit_of_measure_singleton_ne_zero`) and amenable stabilizer
(`Projectivization.amenable_gl_stabilizer`), so `φ.range` and hence `G` are amenable
(`TauCeti.Amenable.of_finite_orbit`).

Specializing to closed discrete subgroups of `SL(2, 𝕜)` (Fuchsian and Kleinian groups) and to
injective homomorphisms into `GL(2, ℤ)` complements
`TauCeti.Geometry.Manifold.Instances.OnePoint.InvariantMeasure`: whereas that module treats
`PSL(2, 𝕜)` acting on `OnePoint 𝕜` over any proper nontrivially normed field (with
`[DecidableEq 𝕜]`), this module treats unimodular `GL(2, 𝕜)` (including `det = -1` reflections in
`GL(2, ℤ)` and complex unit-modulus determinants) and `SL(2, 𝕜)` directly on `ℙ 𝕜 (Fin 2 → 𝕜)`
without `[DecidableEq 𝕜]`.

## Main results

* `TauCeti.hasFoelnerSets_of_map_smul_projectivization_eq`,
  `TauCeti.amenable_of_map_smul_projectivization_eq`: a group with a proper unimodular
  representation in `GL(2, 𝕜)` preserving a Borel probability measure on `ℙ 𝕜 (Fin 2 → 𝕜)` has
  Følner sets, hence is amenable.
* `TauCeti.hasFoelnerSets_of_injective_gl_int_of_map_smul_projectivization_eq`,
  `TauCeti.amenable_of_injective_gl_int_of_map_smul_projectivization_eq`: specialization to groups
  embedding in `GL(2, ℤ)`.
* `Subgroup.hasFoelnerSets_of_map_smul_projectivization_eq`,
  `Subgroup.amenable_of_map_smul_projectivization_eq`: specialization to discrete subgroups of
  `SL(2, 𝕜)` (in the root `Subgroup` namespace for dot notation on `H : Subgroup SL(2, 𝕜)`).

## References

* H. Furstenberg, *Boundary theory and stochastic processes on homogeneous spaces*, Proc. Sympos.
  Pure Math. 26 (1973), 193–229.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Lemma 4.2.3 and Proposition 4.2.4.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory MulAction Set Topology
open scoped LinearAlgebra.Projectivization MatrixGroups

namespace TauCeti

section Furstenberg

variable {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))]
  [BorelSpace (ℙ 𝕜 (Fin 2 → 𝕜))]

/-- **Furstenberg's lemma on the projective line.** If a group `G` admits an injective homomorphism
`φ : G →* GL (Fin 2) 𝕜` (`𝕜 = ℝ` or `ℂ`) with `‖(φ g).det‖ = 1` and `φ g` escaping compact sets of
`Matrix (Fin 2) (Fin 2) 𝕜` along `cofinite`, and `G` preserves a Borel probability measure `μ` on
`ℙ 𝕜 (Fin 2 → 𝕜)`, then `G` has Følner sets. -/
theorem hasFoelnerSets_of_map_smul_projectivization_eq {G : Type*} [Group G]
    {φ : G →* GL (Fin 2) 𝕜} (hφ : Function.Injective φ)
    (hdet : ∀ g : G, ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜).det‖ = 1)
    (hproper : Tendsto (fun g : G => (φ g : Matrix (Fin 2) (Fin 2) 𝕜)) cofinite
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)))
    {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, Measure.map (φ g • ·) μ = μ) :
    HasFoelnerSets G := by
  let _ : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  rw [← amenable_iff_hasFoelnerSets]
  by_cases hfin : Finite G
  · exact Amenable.of_finite
  have : Infinite G := not_finite_iff_infinite.mp hfin
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  let u : ℕ ↪ G := Infinite.natEmbedding G
  have hu_cocompact : Tendsto (fun n => (φ (u n) : Matrix (Fin 2) (Fin 2) 𝕜)) atTop
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)) :=
    hproper.comp (Nat.cofinite_eq_atTop ▸ u.injective.tendsto_cofinite)
  obtain ⟨m, k₁, B, -, hB0, hB_det, hBk₁⟩ :=
    Matrix.exists_tendsto_inv_smul_of_tendsto_cocompact hu_cocompact
      (isBoundedUnder_of ⟨1, fun n => (hdet (u n)).le⟩)
  obtain ⟨p, q, hp_dom, hpq⟩ :=
    Projectivization.exists_linearProjectionDomain_eq_and_linearProjection_eq_of_det_eq_zero
      hB0 hB_det
  obtain ⟨r, -, k₂, hk₂, hrk₂⟩ :=
    isCompact_univ.tendsto_subseq (x := fun n => φ (u (k₁ n)) • p) (fun _ => mem_univ _)
  let gseq : ℕ → G := fun n => u (k₁ (k₂ n))
  have hqr : μ ({q, r}ᶜ) = 0 :=
    Measure.measure_compl_eq_zero_of_isGδ_of_tendsto
      (Set.toFinite ({q, r} : Set (ℙ 𝕜 (Fin 2 → 𝕜)))).isGδ
      (fun n => (continuous_const_smul (φ (gseq n))).measurable)
      (fun n => hμ (gseq n)) fun y => by
        by_cases hy : y = p
        · exact ⟨r, by simp, hy ▸ hrk₂⟩
        · have hy_dom : y ∈ Projectivization.linearProjectionDomain B.mulVecLin :=
            hp_dom.symm ▸ Set.mem_compl_singleton_iff.mpr hy
          refine ⟨q, by simp, ?_⟩
          simpa [hpq y hy] using Projectivization.tendsto_smul_of_tendsto_smul_coe
            (hBk₁.comp hk₂.tendsto_atTop) tendsto_const_nhds hy_dom
  obtain ⟨x₀, -, hx₀⟩ :=
    (Set.toFinite ({q, r} : Set (ℙ 𝕜 (Fin 2 → 𝕜)))).countable.exists_mem_measure_singleton_ne_zero
      (IsProbabilityMeasure.ne_zero μ) hqr
  have : SMulInvariantMeasure φ.range (ℙ 𝕜 (Fin 2 → 𝕜)) μ :=
    ⟨fun ⟨_, g, rfl⟩ s hs =>
      (Measure.map_apply (continuous_const_smul (φ g)).measurable hs).symm.trans
        (congrArg (· s) (hμ g))⟩
  have : Finite (orbit φ.range x₀) := finite_orbit_of_measure_singleton_ne_zero hx₀
  let _ : TopologicalSpace (GL (Fin 2) 𝕜) := ⊥
  have : DiscreteTopology (GL (Fin 2) 𝕜) := ⟨rfl⟩
  have : Amenable (stabilizer (GL (Fin 2) 𝕜) x₀) := Projectivization.amenable_gl_stabilizer x₀
  have : Amenable (stabilizer φ.range x₀) := by
    rw [← stabilizer_subgroupOf]
    infer_instance
  have : Amenable φ.range := Amenable.of_finite_orbit x₀
  exact Amenable.of_injective φ.rangeRestrict (φ.rangeRestrict_injective_iff.mpr hφ)

/-- Topological-group version of `hasFoelnerSets_of_map_smul_projectivization_eq`: the group is
amenable for every group topology. -/
theorem amenable_of_map_smul_projectivization_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G →* GL (Fin 2) 𝕜} (hφ : Function.Injective φ)
    (hdet : ∀ g : G, ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜).det‖ = 1)
    (hproper : Tendsto (fun g : G => (φ g : Matrix (Fin 2) (Fin 2) 𝕜)) cofinite
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)))
    {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, Measure.map (φ g • ·) μ = μ) :
    Amenable G :=
  .of_hasFoelnerSets (hasFoelnerSets_of_map_smul_projectivization_eq hφ hdet hproper hμ)

/-- A group `G` embedding in `GL(2, ℤ)` and preserving a Borel probability measure on
`ℙ 𝕜 (Fin 2 → 𝕜)` (`𝕜 = ℝ` or `ℂ`) has Følner sets. -/
theorem hasFoelnerSets_of_injective_gl_int_of_map_smul_projectivization_eq {G : Type*} [Group G]
    {ψ : G →* GL (Fin 2) ℤ} (hψ : Function.Injective ψ)
    {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ g : G,
      Measure.map (Matrix.GeneralLinearGroup.map (Int.castRingHom 𝕜) (ψ g) • ·) μ = μ) :
    HasFoelnerSets G := by
  let φ : G →* GL (Fin 2) 𝕜 := (Matrix.GeneralLinearGroup.map (Int.castRingHom 𝕜)).comp ψ
  have hφ : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.map_injective Int.cast_injective).comp hψ
  have hdet (g : G) : ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜).det‖ = 1 := by
    have hmap : (φ g : Matrix (Fin 2) (Fin 2) 𝕜) =
        (Int.castRingHom 𝕜).mapMatrix (ψ g : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [hmap, ← RingHom.map_det, Int.coe_castRingHom]
    rcases Int.units_eq_one_or (Matrix.GeneralLinearGroup.det (ψ g)) with hu | hu <;>
    · have hval : (ψ g : Matrix (Fin 2) (Fin 2) ℤ).det =
          ((Matrix.GeneralLinearGroup.det (ψ g) : ℤˣ) : ℤ) := rfl
      rw [hval, hu]
      simp
  have hproper : Tendsto (fun g : G => (φ g : Matrix (Fin 2) (Fin 2) 𝕜)) cofinite
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)) := by
    have hce_int : IsClosedEmbedding ((↑) : ℤ → 𝕜) := by
      have heq : ((↑) : ℤ → 𝕜) = (RCLike.ofRealLI (K := 𝕜)) ∘ ((↑) : ℤ → ℝ) := by
        ext z
        simp
      rw [heq]
      exact (RCLike.ofRealLI (K := 𝕜)).isometry.isClosedEmbedding.comp
        Int.isClosedEmbedding_coe_real
    have hce : IsClosedEmbedding
        ((Int.castRingHom 𝕜).mapMatrix : Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) 𝕜) :=
      IsClosedEmbedding.piMap fun _ => IsClosedEmbedding.piMap fun _ => hce_int
    have hco : Tendsto ((Int.castRingHom 𝕜).mapMatrix :
        Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) 𝕜)
        cofinite (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)) := by
      rw [← Filter.cocompact_eq_cofinite (Matrix (Fin 2) (Fin 2) ℤ)]
      exact hce.tendsto_cocompact
    have hinj_val : Function.Injective (fun g : G => (ψ g : Matrix (Fin 2) (Fin 2) ℤ)) :=
      Units.val_injective.comp hψ
    exact hco.comp hinj_val.tendsto_cofinite
  exact hasFoelnerSets_of_map_smul_projectivization_eq hφ hdet hproper hμ

/-- Topological-group version of
`hasFoelnerSets_of_injective_gl_int_of_map_smul_projectivization_eq`. -/
theorem amenable_of_injective_gl_int_of_map_smul_projectivization_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {ψ : G →* GL (Fin 2) ℤ} (hψ : Function.Injective ψ)
    {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ g : G,
      Measure.map (Matrix.GeneralLinearGroup.map (Int.castRingHom 𝕜) (ψ g) • ·) μ = μ) :
    Amenable G :=
  .of_hasFoelnerSets (hasFoelnerSets_of_injective_gl_int_of_map_smul_projectivization_eq hψ hμ)

end Furstenberg

end TauCeti

namespace Subgroup

open Filter Matrix MeasureTheory Topology
open scoped LinearAlgebra.Projectivization MatrixGroups

variable {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))]
  [BorelSpace (ℙ 𝕜 (Fin 2 → 𝕜))]

/-- A discrete subgroup of `SL(2, 𝕜)` (`𝕜 = ℝ` or `ℂ`) preserving a Borel probability measure on
`ℙ 𝕜 (Fin 2 → 𝕜)` has Følner sets. -/
theorem hasFoelnerSets_of_map_smul_projectivization_eq (H : Subgroup SL(2, 𝕜))
    [DiscreteTopology H] {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ h : H, Measure.map ((h : SL(2, 𝕜)) • ·) μ = μ) :
    TauCeti.HasFoelnerSets H := by
  let φ : H →* GL (Fin 2) 𝕜 := Matrix.SpecialLinearGroup.toGL.comp H.subtype
  have hφ : Function.Injective φ :=
    Matrix.SpecialLinearGroup.toGL_injective.comp H.subtype_injective
  have hdet (h : H) : ‖(φ h : Matrix (Fin 2) (Fin 2) 𝕜).det‖ = 1 := by
    simp [φ]
  have hclosed : IsClosed (H : Set SL(2, 𝕜)) := Subgroup.isClosed_of_discreteTopology
  have hce : IsClosedEmbedding (fun h : H => (φ h : Matrix (Fin 2) (Fin 2) 𝕜)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.comp hclosed.isClosedEmbedding_subtypeVal
  have hproper : Tendsto (fun h : H => (φ h : Matrix (Fin 2) (Fin 2) 𝕜)) cofinite
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)) := by
    rw [← Filter.cocompact_eq_cofinite H]
    exact hce.tendsto_cocompact
  -- Both actions multiply representatives on `ℙ 𝕜 (Fin 2 → 𝕜)` by the underlying matrix.
  have hsmul (g : SL(2, 𝕜)) (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
      Matrix.SpecialLinearGroup.toGL g • x = g • x := rfl
  exact TauCeti.hasFoelnerSets_of_map_smul_projectivization_eq hφ hdet hproper fun h => by
    simpa [φ, funext (hsmul h)] using hμ h

/-- A discrete subgroup of `SL(2, 𝕜)` (`𝕜 = ℝ` or `ℂ`) preserving a Borel probability measure on
`ℙ 𝕜 (Fin 2 → 𝕜)` is amenable. -/
theorem amenable_of_map_smul_projectivization_eq (H : Subgroup SL(2, 𝕜))
    [DiscreteTopology H] {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ h : H, Measure.map ((h : SL(2, 𝕜)) • ·) μ = μ) :
    TauCeti.Amenable H :=
  .of_hasFoelnerSets (H.hasFoelnerSets_of_map_smul_projectivization_eq hμ)

end Subgroup
