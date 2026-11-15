/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.GroupTheory.Amenable.Foelner
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.Topology.Algebra.Projectivization.Action

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import TauCeti.GroupTheory.Amenable.DiscreteFoelner
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.Finite
import TauCeti.GroupTheory.Amenable.Index
import TauCeti.GroupTheory.Amenable.Subgroup
import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.Cocompact
import TauCeti.Topology.Compactification.OnePoint.Amenable

/-!
# Furstenberg's lemma and amenable stabilizers on the projective line

Point stabilizers of `GL(2, K)` and `PSL(2, K)` acting on `ℙ K (Fin 2 → K)` are amenable for every
group topology, transported from `OnePoint.amenable_gl_stabilizer` and
`OnePoint.amenable_pgl_stabilizer` along `OnePoint.equivProjectivization`.

Over a proper normed field `𝕜`, **Furstenberg's lemma** shows that any nonzero finite measure `ν`
on `ℙ 𝕜 (Fin 2 → 𝕜)` (with opens measurable) preserved by a sequence `g : ℕ → PSL(2, 𝕜)` escaping
every compact subset of `PSL(2, 𝕜)` has an atom: rescaled matrix lifts subconverge to a nonzero
singular `2 × 2` matrix `B`, so along that subsequence `g (φ k) • z` converges to the range line
`b` of `B` for every `z` outside the kernel line `a`; if `ν {a} = 0`, dominated convergence on
every open set disjoint from `b` forces `ν {b}ᶜ = 0`, hence `ν {b} ≠ 0`.

Consequently, every discrete subgroup `Γ ≤ PSL(2, 𝕜)` preserving a nonzero finite measure on
`ℙ 𝕜 (Fin 2 → 𝕜)` has Følner sets (and is amenable): either `Γ` is finite, or an injection `ℕ ↪ Γ`
escapes every compact subset of `PSL(2, 𝕜)` (since `Γ` is closed and discrete), producing an atom
whose stabilizer in `Γ` is amenable and has finite index by
`TauCeti.Amenable.of_measure_singleton_ne_zero`. More generally, if `φ : G →* PSL(2, 𝕜)` is a
homomorphism from a discrete group `G` with amenable kernel and a subgroup `H ≤ G` has discrete
image `H.map φ` preserving `ν`, then `H` is amenable; this applies in particular to subgroups of
`SL(2, ℤ)` via `sl2zToPSL2R`.

## Main results

* `Projectivization.amenable_gl_stabilizer`, `Projectivization.amenable_psl_stabilizer`, and
  `MonoidHom.amenable_comap_psl_stabilizer`: point stabilizers of `GL(2, K)` and `PSL(2, K)` on
  `ℙ K (Fin 2 → K)` (and their pullbacks along injective homomorphisms) are amenable.
* `Projectivization.exists_measure_singleton_ne_zero_of_tendsto_cocompact`: Furstenberg's lemma for
  escaping sequences in `PSL(2, 𝕜)` over a proper normed field.
* `Subgroup.hasFoelnerSets_of_discreteTopology_of_forall_map_smul_eq`: discrete subgroups of
  `PSL(2, 𝕜)` fixing a nonzero finite measure on `ℙ 𝕜 (Fin 2 → 𝕜)` have Følner sets.
* `Subgroup.amenable_of_discreteTopology_map_of_forall_map_smul_eq`: subgroups of a discrete group
  mapping with amenable kernel and discrete image into `PSL(2, 𝕜)` and fixing a nonzero finite
  measure on `ℙ 𝕜 (Fin 2 → 𝕜)` are amenable.

## References

* H. Furstenberg, *Boundary theory and stochastic processes on homogeneous spaces*, Proc. Sympos.
  Pure Math. 26 (1973), 193–229.
* M. Burger, *Kazhdan constants for `SL(3, ℤ)`*, J. Reine Angew. Math. 413 (1991), 36–67.
* R. J. Zimmer, *Ergodic Theory and Semisimple Groups*, Birkhäuser (1984), Lemma 3.2.1 and
  Theorem 3.2.4.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

open Filter Matrix MeasureTheory MulAction Topology
open scoped LinearAlgebra.Projectivization MatrixGroups ENNReal

namespace Projectivization

section Stabilizer

variable {K : Type*} [Field K]

/-- Every general-linear point stabilizer on `ℙ K (Fin 2 → K)` is amenable for every group
topology. -/
theorem amenable_gl_stabilizer [TopologicalSpace (GL (Fin 2) K)]
    [IsTopologicalGroup (GL (Fin 2) K)] (x : ℙ K (Fin 2 → K)) :
    TauCeti.Amenable (stabilizer (GL (Fin 2) K) x) := by
  classical
  let e := OnePoint.equivProjectivization K
  have hstab : stabilizer (GL (Fin 2) K) x = stabilizer (GL (Fin 2) K) (e.symm x) := by
    ext g
    rw [mem_stabilizer_iff, mem_stabilizer_iff, ← e.injective.eq_iff,
      OnePoint.equivProjectivization_smul, e.apply_symm_apply]
  exact hstab ▸ OnePoint.amenable_gl_stabilizer (e.symm x)

/-- Every projective-special-linear point stabilizer on `ℙ K (Fin 2 → K)` is amenable for every
group topology. -/
theorem amenable_psl_stabilizer [TopologicalSpace PSL(2, K)] [IsTopologicalGroup PSL(2, K)]
    (x : ℙ K (Fin 2 → K)) : TauCeti.Amenable (stabilizer PSL(2, K) x) := by
  classical
  apply TauCeti.Amenable.of_discrete
  let _ : TopologicalSpace (stabilizer PSL(2, K) x) := ⊥
  let _ : DiscreteTopology (stabilizer PSL(2, K) x) := ⟨rfl⟩
  let _ : TopologicalSpace PGL(2, K) := ⊥
  let _ : DiscreteTopology PGL(2, K) := ⟨rfl⟩
  let e := OnePoint.equivProjectivization K
  have := OnePoint.amenable_pgl_stabilizer (e.symm x)
  have hinj : Function.Injective
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) :=
    fun g₁ g₂ h ↦ eq_of_smul_eq_smul fun c : OnePoint K ↦ by
      simpa only [ProjectiveSpecialLinearGroup.toPGL_smul] using congrArg (· • c) h
  let φ : stabilizer PSL(2, K) x →* stabilizer PGL(2, K) (e.symm x) :=
    ((ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).comp
      (stabilizer PSL(2, K) x).subtype).codRestrict
      (stabilizer PGL(2, K) (e.symm x)) fun g ↦ by
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, mem_stabilizer_iff,
          ProjectiveSpecialLinearGroup.toPGL_smul, ← e.injective.eq_iff,
          OnePoint.equivProjectivization_psl_smul, e.apply_symm_apply]
        exact g.2
  refine TauCeti.Amenable.of_injective φ ?_
  rw [MonoidHom.injective_codRestrict]
  exact hinj.comp (stabilizer PSL(2, K) x).subtype_injective

end Stabilizer

end Projectivization

namespace MonoidHom

/-- The pullback of a projective-special-linear point stabilizer on `ℙ K (Fin 2 → K)` along an
injective group homomorphism is amenable for every group topology on the source. -/
theorem amenable_comap_psl_stabilizer {K G : Type*} [Field K] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* PSL(2, K))
    (hφ : Function.Injective φ) (x : ℙ K (Fin 2 → K)) :
    TauCeti.Amenable ((stabilizer PSL(2, K) x).comap φ) := by
  let _ : TopologicalSpace PSL(2, K) := ⊥
  let _ : DiscreteTopology PSL(2, K) := ⟨rfl⟩
  have := Projectivization.amenable_psl_stabilizer x
  exact TauCeti.Amenable.of_injective (φ.subgroupComap _) (φ.subgroupComap_injective _ hφ)

end MonoidHom

namespace Projectivization

section Furstenberg

/-- If a sequence of maps `T : ℕ → X → X` on a second-countable Hausdorff space preserves a nonzero
finite measure `ν` (with opens measurable) and contracts `X \ {a}` pointwise to `b`, then `ν` has
an atom. -/
private theorem exists_measure_singleton_ne_zero_of_tendsto_off_point {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    {T : ℕ → X → X} (hinv : ∀ k, Measure.map (T k) ν = ν) {a b : X}
    (hlim : ∀ z, z ≠ a → Tendsto (fun k ↦ T k z) atTop (𝓝 b)) :
    ∃ x : X, ν {x} ≠ 0 := by
  have : Nonempty X := ⟨a⟩
  by_cases hae_all : ∀ k, AEMeasurable (T k) ν
  · by_cases hνa : ν {a} = 0
    · refine ⟨b, fun hνb ↦ hν ?_⟩
      choose V U hVo hUo hyV hbU hVU using fun y : ({b}ᶜ : Set X) ↦ t2_separation y.2
      have hνV (y : ({b}ᶜ : Set X)) : ν (V y) = 0 := by
        have hmV : Measurable ((V y).indicator (1 : X → ℝ≥0∞)) :=
          measurable_const.indicator (hVo y).measurableSet
        have hae : ∀ᵐ z ∂ν, Tendsto (fun k ↦ (V y).indicator (1 : X → ℝ≥0∞) (T k z))
            atTop (𝓝 0) := by
          filter_upwards [compl_mem_ae_iff.mpr hνa] with z hz
          exact tendsto_const_nhds.congr' <|
            ((hlim z hz).eventually ((hUo y).mem_nhds (hbU y))).mono fun k hk ↦
              (Set.indicator_of_notMem ((hVU y).symm.notMem_of_mem_left hk) _).symm
        have hdom := tendsto_lintegral_of_dominated_convergence' (fun _ : X ↦ (1 : ℝ≥0∞))
          (fun k ↦ hmV.comp_aemeasurable (hae_all k))
          (fun k ↦ .of_forall fun z ↦ Set.indicator_le_self' (fun _ _ ↦ zero_le_one) (T k z))
          (by simp [measure_ne_top]) hae
        rw [lintegral_zero] at hdom
        have heq (k : ℕ) : ∫⁻ z, (V y).indicator (1 : X → ℝ≥0∞) (T k z) ∂ν = ν (V y) := by
          rw [← lintegral_map' hmV.aemeasurable (hae_all k), hinv k,
            lintegral_indicator_one (hVo y).measurableSet]
        exact tendsto_nhds_unique (tendsto_const_nhds.congr fun k ↦ (heq k).symm) hdom
      obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
      have hcompl : ({b}ᶜ : Set X) ⊆ ⋃ y ∈ S, V y := fun x hx ↦
        hSU ▸ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hyV ⟨x, hx⟩⟩
      have hνbc : ν {b}ᶜ = 0 :=
        measure_mono_null hcompl ((measure_biUnion_null_iff hSc).mpr fun y _ ↦ hνV y)
      exact Measure.measure_univ_eq_zero.mp <| nonpos_iff_eq_zero.mp <|
        (Set.union_compl_self {b} ▸ measure_union_le {b} {b}ᶜ).trans_eq (by simp [hνb, hνbc])
    · exact ⟨a, hνa⟩
  · have ⟨k, hk⟩ : ∃ k, ¬ AEMeasurable (T k) ν := not_forall.mp hae_all
    let x₀ : X := Classical.ofNonempty
    have hdirac : ν = Measure.dirac x₀ := by
      rw [← hinv k, Measure.map_of_not_aemeasurable_of_ne_zero hk hν]
    exact ⟨x₀, by simp [hdirac]⟩

variable {𝕜 : Type*} [NormedField 𝕜] [ProperSpace 𝕜]
  [MeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))] [OpensMeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))]

/-- **Furstenberg's lemma on `ℙ¹(𝕜)`.** Let `𝕜` be a proper normed field and `ν` a nonzero finite
measure on `ℙ 𝕜 (Fin 2 → 𝕜)` with opens measurable. If a sequence `g : ℕ → PSL(2, 𝕜)` escapes every
compact subset of `PSL(2, 𝕜)` and preserves `ν`, then `ν` has an atom. -/
theorem exists_measure_singleton_ne_zero_of_tendsto_cocompact
    {ν : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    {g : ℕ → PSL(2, 𝕜)} (hg : Tendsto g atTop (cocompact PSL(2, 𝕜)))
    (hinv : ∀ n, Measure.map (g n • ·) ν = ν) :
    ∃ x : ℙ 𝕜 (Fin 2 → 𝕜), ν {x} ≠ 0 := by
  have : SeparatingDual 𝕜 (Fin 2 → 𝕜) :=
    ⟨fun v hv ↦ have ⟨i, hi⟩ := Function.ne_iff.mp hv; ⟨ContinuousLinearMap.proj i, hi⟩⟩
  choose A hA using fun n ↦ QuotientGroup.mk_surjective (g n)
  obtain ⟨m, φ, B, -, hB, hdet, hCB⟩ :=
    ProjectiveSpecialLinearGroup.exists_tendsto_inv_smul_of_tendsto_cocompact hg hA
  obtain ⟨a, b, ha, hb⟩ := exists_mk_eq_and_mk_mulVec_eq_of_det_eq_zero hB hdet
  refine exists_measure_singleton_ne_zero_of_tendsto_off_point hν (fun k ↦ hinv (φ k))
    (a := a) (b := b) fun z hz ↦ ?_
  have hBz : B *ᵥ z.rep ≠ 0 := fun h ↦ hz <| by rw [← (ha _ z.rep_ne_zero).1 h, mk_rep]
  have ht := tendsto_smul_of_tendsto_smul_coe (C := fun k ↦ (A (φ k) : GL (Fin 2) 𝕜))
    (c := fun k ↦ (m (φ k))⁻¹) hCB tendsto_const_nhds ((mem_linearProjectionDomain_iff _).2 hBz)
  have hlp : linearProjection B.mulVecLin z = b := by
    rw [← mk_rep z, linearProjection_mk _ _ hBz]
    exact hb _ hBz
  exact (hlp ▸ ht).congr fun k ↦ by
    rw [← hA (φ k), ProjectiveSpecialLinearGroup.smul_proj_mk]
    rfl

end Furstenberg

end Projectivization

namespace Subgroup

/-- **Furstenberg's invariant-measure theorem for discrete subgroups of `PSL(2, 𝕜)`.** Over a
proper normed field `𝕜`, every discrete subgroup of `PSL(2, 𝕜)` preserving a nonzero finite measure
on `ℙ 𝕜 (Fin 2 → 𝕜)` (with opens measurable) has Følner sets (and hence is amenable). -/
theorem hasFoelnerSets_of_discreteTopology_of_forall_map_smul_eq {𝕜 : Type*} [NormedField 𝕜]
    [ProperSpace 𝕜] [MeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))] [OpensMeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))]
    (Γ : Subgroup PSL(2, 𝕜)) [DiscreteTopology Γ]
    {ν : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hinv : ∀ γ : Γ, Measure.map ((γ : PSL(2, 𝕜)) • ·) ν = ν) :
    TauCeti.HasFoelnerSets Γ := by
  rw [← TauCeti.amenable_iff_hasFoelnerSets]
  have : SeparatingDual 𝕜 (Fin 2 → 𝕜) :=
    ⟨fun v hv ↦ have ⟨i, hi⟩ := Function.ne_iff.mp hv; ⟨ContinuousLinearMap.proj i, hi⟩⟩
  by_cases hfin : Finite Γ
  · exact TauCeti.Amenable.of_finite
  have : Infinite Γ := not_finite_iff_infinite.mp hfin
  have hclosed : IsClosed (Γ : Set PSL(2, 𝕜)) := Γ.isClosed_of_discreteTopology
  let e : ℕ ↪ Γ := Infinite.natEmbedding Γ
  have hesc : Tendsto (fun n ↦ (e n : PSL(2, 𝕜))) atTop (cocompact PSL(2, 𝕜)) :=
    hclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact.comp
      (Filter.cocompact_eq_cofinite Γ ▸ Nat.cofinite_eq_atTop ▸ e.injective.tendsto_cofinite)
  obtain ⟨x, hx⟩ := Projectivization.exists_measure_singleton_ne_zero_of_tendsto_cocompact hν hesc
    fun n ↦ hinv (e n)
  have : TauCeti.Amenable (stabilizer Γ x) :=
    Γ.subtype.amenable_comap_psl_stabilizer Γ.subtype_injective x
  exact TauCeti.Amenable.of_measure_singleton_ne_zero hinv hx

/-- Let `G` be a discrete group and `φ : G →* PSL(2, 𝕜)` a homomorphism into `PSL(2, 𝕜)` over a
proper normed field `𝕜` with amenable kernel. Every subgroup `H ≤ G` with discrete image `H.map φ`
that preserves a nonzero finite measure on `ℙ 𝕜 (Fin 2 → 𝕜)` (with opens measurable) is amenable.
In particular, this applies to subgroups of `SL(2, ℤ)` via `sl2zToPSL2R`. -/
theorem amenable_of_discreteTopology_map_of_forall_map_smul_eq
    {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [NormedField 𝕜] [ProperSpace 𝕜]
    [MeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))] [OpensMeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))]
    (H : Subgroup G) {φ : G →* PSL(2, 𝕜)} [TauCeti.Amenable φ.ker]
    [DiscreteTopology (H.map φ)]
    {ν : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hinv : ∀ h : H, Measure.map (φ (h : G) • ·) ν = ν) :
    TauCeti.Amenable H := by
  have : TauCeti.Amenable (H.map φ) := by
    rw [TauCeti.amenable_iff_hasFoelnerSets]
    refine (H.map φ).hasFoelnerSets_of_discreteTopology_of_forall_map_smul_eq hν ?_
    rintro ⟨_, h, hh, rfl⟩
    exact hinv ⟨h, hh⟩
  let ψ : H →* H.map φ := φ.subgroupMap H
  have : TauCeti.Amenable ψ.ker := by
    let κ : ψ.ker →* φ.ker :=
      (H.subtype.comp ψ.ker.subtype).codRestrict φ.ker fun x ↦
        congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    exact TauCeti.Amenable.of_injective κ <| (MonoidHom.injective_codRestrict _ _ _).mpr <|
      H.subtype_injective.comp ψ.ker.subtype_injective
  exact TauCeti.Amenable.of_ker_le_range ψ.ker.subtype ψ (by simp)

end Subgroup
