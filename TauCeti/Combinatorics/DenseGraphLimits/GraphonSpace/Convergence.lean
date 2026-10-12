/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Compact
public import TauCeti.Combinatorics.DenseGraphLimits.Separation.Inverse
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic
import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Coordinates

/-!
# Convergence of graphons through homomorphism densities

A sequence in the cut-distance quotient of graphons on a fixed probability carrier converges
exactly when the homomorphism density of every finite simple graph converges to that of the limit
(`tendsto_graphonSpace_iff_forall_homDensity`), and it is Cauchy exactly when every homomorphism
density is Cauchy (`cauchySeq_graphonSpace_iff_forall_homDensity_cauchySeq`). Thus finite-graph
densities give all the coordinates needed to test convergence of dense graph limits. Whenever the
graphon space is complete -- on the unit interval, or on any atomless standard Borel carrier -- a
sequence has a limit in graphon space as soon as all its homomorphism densities converge
(`exists_tendsto_graphonSpace_iff_forall_homDensity_cauchySeq`).

The carriers need not be fixed. For graphons `Wₙ` on arbitrary, possibly different, probability
carriers, `δ□(Wₙ, W) → 0` exactly when `t(F, Wₙ) → t(F, W)` for every `F`
(`tendsto_cutDist_iff_forall_homDensity_tendsto`), and `δ□(Wⱼ, Wₖ) → 0` as `j, k → ∞` exactly
when every `t(F, Wₖ)` is Cauchy (`tendsto_cutDist_prod_iff_forall_homDensity_cauchySeq`). The
sequence converges in cut distance to some graphon on a given atomless standard Borel carrier,
such as the unit interval, exactly when all its homomorphism densities converge
(`exists_graphon_tendsto_cutDist_iff_forall_homDensity_cauchySeq`), that is, exactly when it is
Cauchy in cut distance (`exists_graphon_tendsto_cutDist_iff_tendsto_cutDist_prod`). Read on the
step graphons of finite graphs, this is the theory of convergent graph sequences: a sequence of
finite graphs converges to a graphon `W` in the cut distance of step graphons exactly when all its
finite homomorphism densities converge to those of `W`
(`tendsto_cutDist_finiteGraphGraphon_iff_forall_homDensityFin_tendsto`), it is Cauchy in cut
distance exactly when all its finite homomorphism densities are Cauchy
(`tendsto_cutDist_finiteGraphGraphon_prod_iff_forall_homDensityFin_cauchySeq`), and it has a
limit graphon on any given atomless standard Borel carrier exactly when all its finite
homomorphism densities converge
(`exists_graphon_tendsto_cutDist_finiteGraphGraphon_iff_forall_homDensityFin_cauchySeq`).

The compactness argument runs on the canonical carrier `(I, volume)`, where the joint
homomorphism-density map `homDensityCoords` is a closed embedding of the compact space
`GraphonSpaceI` into a product of lines (`isClosedEmbedding_homDensityCoords`). The isometric
embedding of every fixed-carrier graphon space into the unit-interval one (`toGraphonSpaceI`) and
the unit-interval representative of every graphon (`Graphon.unitIntervalRepr`) carry the
equivalences to arbitrary carriers, and the representation of every graphon on an atomless
standard Borel carrier (`exists_graphon_cutDist_eq_zero`) places the limits there.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Theorem 11.5 and Chapter 11.
* L. Lovász and B. Szegedy, *Limits of dense graph sequences*, J. Combin. Theory Ser. B 96
  (2006), 933–957: every convergent graph sequence has a limit graphon.
* C. Borgs, J. Chayes, L. Lovász, V. Sós, K. Vesztergombi, *Convergent sequences of dense graphs
  I: Subgraph frequencies, metric properties and testing*, Adv. Math. 219 (2008), 1801–1851,
  Theorem 3.8.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology unitInterval

namespace TauCeti

namespace DenseGraphLimits

section FixedCarrier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Convergence in graphon space is convergence of all homomorphism densities.** A sequence in
the graphon space over any probability carrier converges in cut distance if and only if the
homomorphism density of every finite simple graph converges to that of the limit. -/
theorem tendsto_graphonSpace_iff_forall_homDensity
    (Ws : ℕ → GraphonSpace Ω μ) (W : GraphonSpace Ω μ) :
    Tendsto Ws atTop (𝓝 W) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        Tendsto (fun k => homDensityOnSpace F (Ws k)) atTop
          (𝓝 (homDensityOnSpace F W)) := by
  rw [isInducing_homDensityCoords.tendsto_nhds_iff, tendsto_pi_nhds]
  refine ⟨fun h n F _ => ?_, fun h ⟨n, F, _⟩ => ?_⟩
  · simpa only [Function.comp_def, homDensityCoords_apply] using h ⟨n, F, ‹_›⟩
  · simpa only [Function.comp_def, homDensityCoords_apply] using h n F

/-- The unit-interval case of `exists_tendsto_graphonSpace_iff_forall_homDensity_cauchySeq`:
by compactness a sequence in `GraphonSpaceI` has a convergent subsequence, and once every
homomorphism density converges the whole sequence converges to the subsequential limit. -/
private theorem exists_tendsto_graphonSpaceI_of_forall_homDensity_tendsto
    (Ws : ℕ → GraphonSpaceI)
    (h : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      ∃ l, Tendsto (fun k => homDensityOnSpace F (Ws k)) atTop (𝓝 l)) :
    ∃ W, Tendsto Ws atTop (𝓝 W) := by
  obtain ⟨W, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq Ws
  refine ⟨W, (tendsto_graphonSpace_iff_forall_homDensity Ws W).2 fun n F _ => ?_⟩
  obtain ⟨l, hl⟩ := h n F
  have hsub : Tendsto (fun k => homDensityOnSpace F (Ws (φ k))) atTop
      (𝓝 (homDensityOnSpace F W)) :=
    ((continuous_homDensityOnSpace F).tendsto W).comp hlim
  rwa [tendsto_nhds_unique (hl.comp hφ.tendsto_atTop) hsub] at hl

/-- **Cauchy sequences in graphon space are those with Cauchy homomorphism densities.** A sequence
in the graphon space over any probability carrier is Cauchy in cut distance if and only if the
homomorphism density of every finite simple graph is a Cauchy sequence. -/
theorem cauchySeq_graphonSpace_iff_forall_homDensity_cauchySeq (Ws : ℕ → GraphonSpace Ω μ) :
    CauchySeq Ws ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        CauchySeq (fun k => homDensityOnSpace F (Ws k)) := by
  -- transport along the isometric embedding into the complete space `GraphonSpaceI`
  have key : CauchySeq Ws ↔ ∃ X, Tendsto (toGraphonSpaceI ∘ Ws) atTop (𝓝 X) := by
    rw [CauchySeq, ← isometry_toGraphonSpaceI.isUniformInducing.cauchy_map_iff, Filter.map_map,
      cauchy_map_iff_exists_tendsto]
  rw [key]
  constructor
  · rintro ⟨X, hX⟩ n F _
    simpa only [Function.comp_def, homDensityOnSpace_toGraphonSpaceI] using
      ((tendsto_graphonSpace_iff_forall_homDensity _ X).1 hX n F).cauchySeq
  · intro h
    refine exists_tendsto_graphonSpaceI_of_forall_homDensity_tendsto _ fun n F _ => ?_
    simpa only [Function.comp_def, homDensityOnSpace_toGraphonSpaceI] using
      cauchySeq_tendsto_of_complete (h n F)

/-- **A sequence of graphons with convergent homomorphism densities converges.** Over a carrier
whose graphon space is complete -- the unit interval, or any atomless standard Borel carrier -- a
sequence in graphon space has a limit if and only if the homomorphism density of every finite
simple graph is a Cauchy, hence convergent, sequence. -/
theorem exists_tendsto_graphonSpace_iff_forall_homDensity_cauchySeq
    [CompleteSpace (GraphonSpace Ω μ)] (Ws : ℕ → GraphonSpace Ω μ) :
    (∃ W, Tendsto Ws atTop (𝓝 W)) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        CauchySeq (fun k => homDensityOnSpace F (Ws k)) :=
  ⟨fun ⟨_, hW⟩ => (cauchySeq_graphonSpace_iff_forall_homDensity_cauchySeq Ws).1 hW.cauchySeq,
    fun h => cauchySeq_tendsto_of_complete
      ((cauchySeq_graphonSpace_iff_forall_homDensity_cauchySeq Ws).2 h)⟩

end FixedCarrier

section CrossCarrier

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
variable {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)] {μs : ∀ n, Measure (Ωs n)}
  [∀ n, IsProbabilityMeasure (μs n)]

/-- **Cut-distance convergence is convergence of all homomorphism densities**, for graphons on
arbitrary, possibly different, probability carriers: `δ□(Wₙ, W) → 0` if and only if
`t(F, Wₙ) → t(F, W)` for every finite simple graph `F`. -/
theorem tendsto_cutDist_iff_forall_homDensity_tendsto (Ws : ∀ n, Graphon (Ωs n) (μs n))
    (W : Graphon Ω' μ') :
    Tendsto (fun n => cutDist (Ws n) W) atTop (𝓝 0) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        Tendsto (fun k => homDensity F (Ws k)) atTop (𝓝 (homDensity F W)) := by
  have hd : (fun n => cutDist (Ws n) W) = fun n =>
      dist (SeparationQuotient.mk (Ws n).unitIntervalRepr : GraphonSpaceI)
        (SeparationQuotient.mk W.unitIntervalRepr) := by
    funext n
    simp [dist_graphonSpace_mk_mk]
  rw [hd, ← tendsto_iff_dist_tendsto_zero, tendsto_graphonSpace_iff_forall_homDensity]
  simp only [homDensityOnSpace_mk, Graphon.homDensity_unitIntervalRepr]

/-- **Cut-distance Cauchy sequences are those with Cauchy homomorphism densities**, for graphons
on arbitrary, possibly different, probability carriers: `δ□(Wⱼ, Wₖ) → 0` as `j, k → ∞` if and
only if the homomorphism density `t(F, Wₖ)` of every finite simple graph `F` is a Cauchy
sequence. -/
theorem tendsto_cutDist_prod_iff_forall_homDensity_cauchySeq (Ws : ∀ n, Graphon (Ωs n) (μs n)) :
    Tendsto (fun p : ℕ × ℕ => cutDist (Ws p.1) (Ws p.2)) atTop (𝓝 0) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        CauchySeq (fun k => homDensity F (Ws k)) := by
  -- transport along the unit-interval representatives into `GraphonSpaceI`
  have key := (cauchySeq_iff_tendsto_dist_atTop_0 (u := fun n =>
    (SeparationQuotient.mk (Ws n).unitIntervalRepr : GraphonSpaceI))).symm.trans
    (cauchySeq_graphonSpace_iff_forall_homDensity_cauchySeq _)
  simpa only [dist_graphonSpace_mk_mk, Graphon.cutDist_unitIntervalRepr_left,
    Graphon.cutDist_unitIntervalRepr_right, homDensityOnSpace_mk,
    Graphon.homDensity_unitIntervalRepr] using key

variable (μ')

/-- **A sequence of graphons with convergent homomorphism densities has a limit graphon**, on every
atomless standard Borel carrier `(Ω', μ')`, such as the unit interval: a sequence of graphons on
arbitrary, possibly different, probability carriers converges in cut distance to some graphon on
`(Ω', μ')` if and only if the homomorphism density of every finite simple graph is a Cauchy, hence
convergent, sequence. -/
theorem exists_graphon_tendsto_cutDist_iff_forall_homDensity_cauchySeq [StandardBorelSpace Ω']
    [NullSingletonClass μ'] (Ws : ∀ n, Graphon (Ωs n) (μs n)) :
    (∃ W : Graphon Ω' μ', Tendsto (fun n => cutDist (Ws n) W) atTop (𝓝 0)) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        CauchySeq (fun k => homDensity F (Ws k)) := by
  refine ⟨fun ⟨W, hW⟩ n F _ =>
    ((tendsto_cutDist_iff_forall_homDensity_tendsto Ws W).1 hW n F).cauchySeq, fun h => ?_⟩
  -- the unit-interval representatives form a Cauchy sequence in the complete space `GraphonSpaceI`
  have hX : CauchySeq fun n =>
      (SeparationQuotient.mk (Ws n).unitIntervalRepr : GraphonSpaceI) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    simpa [dist_graphonSpace_mk_mk] using
      (tendsto_cutDist_prod_iff_forall_homDensity_cauchySeq Ws).2 h
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete hX
  obtain ⟨V, rfl⟩ := SeparationQuotient.surjective_mk Y
  -- move the unit-interval limit to the carrier `(Ω', μ')`
  obtain ⟨W, hW⟩ := exists_graphon_cutDist_eq_zero μ' V
  refine ⟨W, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero] at hY
  simpa [dist_graphonSpace_mk_mk, cutDist_congr_right hW] using hY

/-- **Cut distance is complete across carriers.** A sequence of graphons on arbitrary, possibly
different, probability carriers converges in cut distance to some graphon on a given atomless
standard Borel carrier `(Ω', μ')` if and only if it is Cauchy in cut distance. -/
theorem exists_graphon_tendsto_cutDist_iff_tendsto_cutDist_prod [StandardBorelSpace Ω']
    [NullSingletonClass μ'] (Ws : ∀ n, Graphon (Ωs n) (μs n)) :
    (∃ W : Graphon Ω' μ', Tendsto (fun n => cutDist (Ws n) W) atTop (𝓝 0)) ↔
      Tendsto (fun p : ℕ × ℕ => cutDist (Ws p.1) (Ws p.2)) atTop (𝓝 0) := by
  rw [exists_graphon_tendsto_cutDist_iff_forall_homDensity_cauchySeq μ',
    tendsto_cutDist_prod_iff_forall_homDensity_cauchySeq]

end CrossCarrier

section GraphSequence

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ → ℕ}

/-- **Convergence of a graph sequence to a graphon.** A sequence of finite graphs `Gₙ` on nonempty
vertex sets converges to a graphon `W`, on any probability carrier, in the cut distance of their
step graphons if and only if every finite homomorphism density `t(F, Gₙ)` converges to
`t(F, W)`. -/
theorem tendsto_cutDist_finiteGraphGraphon_iff_forall_homDensityFin_tendsto (hm : ∀ n, 0 < m n)
    (G : ∀ n, SimpleGraph (Fin (m n))) (W : Graphon Ω μ) :
    Tendsto (fun n => cutDist (finiteGraphGraphon (G n)) W) atTop (𝓝 0) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        Tendsto (fun k => homDensityFin F (G k)) atTop (𝓝 (homDensity F W)) := by
  simp only [tendsto_cutDist_iff_forall_homDensity_tendsto, homDensity_finiteGraphGraphon, hm]

/-- **Cut-distance Cauchy graph sequences are those with Cauchy homomorphism densities.** A
sequence of finite graphs `Gₙ` on nonempty vertex sets is Cauchy in the cut distance of their step
graphons if and only if every finite homomorphism density `t(F, Gₙ)` is a Cauchy sequence. -/
theorem tendsto_cutDist_finiteGraphGraphon_prod_iff_forall_homDensityFin_cauchySeq
    (hm : ∀ n, 0 < m n) (G : ∀ n, SimpleGraph (Fin (m n))) :
    Tendsto (fun p : ℕ × ℕ => cutDist (finiteGraphGraphon (G p.1)) (finiteGraphGraphon (G p.2)))
        atTop (𝓝 0) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        CauchySeq (fun k => homDensityFin F (G k)) := by
  rw [tendsto_cutDist_prod_iff_forall_homDensity_cauchySeq fun n => finiteGraphGraphon (G n)]
  simp only [homDensity_finiteGraphGraphon, hm]

variable (μ) in
/-- **Every convergent graph sequence has a limit graphon** (Lovász--Szegedy), on every atomless
standard Borel carrier `(Ω, μ)`, such as the unit interval. A sequence of finite graphs on nonempty
vertex sets converges in the cut distance of step graphons to some graphon on `(Ω, μ)` if and only
if every finite homomorphism density `t(F, Gₙ)` is a Cauchy, hence convergent, sequence. -/
theorem exists_graphon_tendsto_cutDist_finiteGraphGraphon_iff_forall_homDensityFin_cauchySeq
    [StandardBorelSpace Ω] [NullSingletonClass μ] (hm : ∀ n, 0 < m n)
    (G : ∀ n, SimpleGraph (Fin (m n))) :
    (∃ W : Graphon Ω μ, Tendsto (fun n => cutDist (finiteGraphGraphon (G n)) W) atTop (𝓝 0)) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        CauchySeq (fun k => homDensityFin F (G k)) := by
  rw [exists_graphon_tendsto_cutDist_iff_forall_homDensity_cauchySeq μ
    fun n => finiteGraphGraphon (G n)]
  simp only [homDensity_finiteGraphGraphon, hm]

end GraphSequence

end DenseGraphLimits

end TauCeti
