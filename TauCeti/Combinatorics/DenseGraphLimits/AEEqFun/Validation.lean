/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: √2
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.AEEqFun.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Basic
import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic

/-!
# Adversarial checks of strict graphon representatives

The passage from a measurable function to an almost-everywhere class must discard null-set
values, but must not discard values on atoms. These examples exercise both requirements.

On the unit interval, corrupt a graphon's zero row and zero column with the asymmetric values
`4` and `-6`. The resulting measurable function represents the same class, although it is neither
symmetric nor range-bounded everywhere. Averaging and clamping repairs it: the origin becomes
`1`, and the rest of the zero row and column become `0`. The repair preserves the class, every
homomorphism density, and the graphon-space point. In particular, a repaired constant graphon
need not be the same strict graphon. The representative bridge recovers the corrupted class and
its graphon-space point. On the uniform two-point atomic carrier, its returned representative
recovers the finite adjacency graphon pointwise; all four adjacency entries are also checked.

On a uniform two-point space, an asymmetric function cannot be represented by a graphon;
neither can the constant function `2` on a point mass. These checks distinguish almost-everywhere
constraints from constraints that could accidentally ignore positive-mass exceptional sets.

The examples use the strict-representative construction `Graphon.clampSymm` and the bridges
`exists_graphon_repr` and `exists_graphon_repr_iff`. The auxiliary functions are private; the
exported theorem `Graphon.toAEEqFun_not_injective_unitInterval` records why strict equality cannot
be recovered.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §6, for almost-everywhere identification of graphons.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace TauCeti.DenseGraphLimits

/-- A representative corrupted on two null coordinate lines. -/
private def corrupted (W : Graphon I (volume : Measure I)) (x y : I) : ℝ :=
  if x = 0 then 4 else if y = 0 then -6 else W x y

private theorem measurable_corrupted (W : Graphon I (volume : Measure I)) :
    Measurable (Function.uncurry (corrupted W)) := by
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
      W.measurable)

private theorem corrupted_ae (W : Graphon I (volume : Measure I)) :
    (fun p : I × I ↦ corrupted W p.1 p.2) =ᵐ[volume.prod volume]
      fun p ↦ W p.1 p.2 := by
  have hfst := (measurePreserving_fst (μ := (volume : Measure I))
    (ν := (volume : Measure I))).quasiMeasurePreserving.ae (volume.ae_ne (0 : I))
  have hsnd := (measurePreserving_snd (μ := (volume : Measure I))
    (ν := (volume : Measure I))).quasiMeasurePreserving.ae (volume.ae_ne (0 : I))
  filter_upwards [hfst, hsnd] with p hx hy
  simp [corrupted, hx, hy]

/-- The repaired strict graphon, retaining the nontrivial exceptional values. -/
private def repaired (W : Graphon I (volume : Measure I)) : Graphon I (volume : Measure I) :=
  Graphon.clampSymm volume (corrupted W) (measurable_corrupted W)

private theorem repaired_ae (W : Graphon I (volume : Measure I)) :
    (fun p : I × I ↦ repaired W p.1 p.2) =ᵐ[volume.prod volume]
      fun p ↦ W p.1 p.2 := by
  have hswap := (Measure.measurePreserving_swap (μ := (volume : Measure I))
    (ν := (volume : Measure I))).quasiMeasurePreserving.ae (corrupted_ae W)
  filter_upwards [corrupted_ae W, hswap] with p hp hps
  simp only [Prod.swap] at hps
  rw [repaired, Graphon.clampSymm_apply_of_symm_of_mem volume (corrupted W)
    (measurable_corrupted W) (hp.trans ((W.symm _ _).trans hps.symm))
    (hp ▸ W.mem_Icc _ _)]
  exact hp

-- Both range corrections are necessary. The uncorrected symmetrization is 4 at the origin
-- and -1 at (0, 1); retaining either value would not give a graphon.
example (W : Graphon I (volume : Measure I)) :
    corrupted W 0 1 = 4 ∧ corrupted W 1 0 = -6 := by
  norm_num [corrupted]

example (W : Graphon I (volume : Measure I)) :
    repaired W 0 0 = 1 ∧ repaired W 0 1 = 0 ∧ repaired W 1 0 = 0 := by
  norm_num [repaired, Graphon.clampSymm_apply, corrupted]

-- Checking the class of the original, invalid representative avoids silently replacing
-- the contract with one that only accepts functions satisfying the constraints everywhere.
example (W : Graphon I (volume : Measure I)) :
    ∃ V : Graphon I (volume : Measure I),
      Graphon.toAEEqFun V = AEEqFun.mk (Function.uncurry (corrupted W))
        (measurable_corrupted W).aestronglyMeasurable ∧
      (⟦V⟧ : GraphonSpaceI) = ⟦W⟧ := by
  let f : (I × I) →ₘ[volume.prod volume] ℝ := AEEqFun.mk (Function.uncurry (corrupted W))
    (measurable_corrupted W).aestronglyMeasurable
  have hclass : Graphon.toAEEqFun W = f := by
    apply Graphon.toAEEqFun_eq_of_ae
    exact (corrupted_ae W).symm.trans (AEEqFun.coeFn_mk _ _).symm
  obtain ⟨V, hV⟩ := exists_graphon_repr f
    (hclass ▸ Graphon.toAEEqFun_mem_Icc_ae W) (hclass ▸ Graphon.toAEEqFun_symm_ae W)
  refine ⟨V, hV, (graphonSpace_mk_eq_mk_iff _ _).2 ?_⟩
  exact cutDist_eq_zero_of_aeEq (Graphon.toAEEqFun_eq_iff.1 (hV.trans hclass.symm))

example (W : Graphon I (volume : Measure I)) :
    Graphon.toAEEqFun (repaired W) = Graphon.toAEEqFun W :=
  Graphon.toAEEqFun_eq_iff.2 (repaired_ae W)

example (W : Graphon I (volume : Measure I)) :
    (⟦repaired W⟧ : GraphonSpaceI) = ⟦W⟧ := by
  exact (graphonSpace_mk_eq_mk_iff _ _).2 (cutDist_eq_zero_of_aeEq (repaired_ae W))

/-- Passing to the almost-everywhere class loses strict equality, already on the unit interval.
A null-set modification of the constant graphon `1/2` gives a different strict graphon with the
same class. -/
theorem Graphon.toAEEqFun_not_injective_unitInterval :
    ¬ Function.Injective (Graphon.toAEEqFun (Ω := I) (μ := (volume : Measure I))) := by
  intro hinj
  let W := Graphon.const (volume : Measure I) ⟨1 / 2, by norm_num, by norm_num⟩
  have h := hinj (Graphon.toAEEqFun_eq_iff.2 (repaired_ae W))
  have hval := congrArg (fun V : Graphon I (volume : Measure I) ↦ V 0 0) h
  norm_num [repaired, Graphon.clampSymm_apply, corrupted, W] at hval

-- The nontrivial density is retained despite that strict inequality.
example : homDensity (⊤ : SimpleGraph (Fin 3))
    (repaired (Graphon.const (volume : Measure I) ⟨1 / 2, by norm_num, by norm_num⟩)) = 1 / 8 := by
  rw [homDensity_congr_ae _ (repaired_ae _), homDensity_const,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num

-- A nonconstant finite-graph example on an atomic carrier checks all four entries
-- of the two-point adjacency matrix, not just the off-diagonal ones.
example :
    (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2))) 0 0 = 0 ∧
    (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2))) 0 1 = 1 ∧
    (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2))) 1 0 = 1 ∧
    (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2))) 1 1 = 0 := by
  simp [finiteGraphGraphonOnFin_apply]

-- The bridge's returned representative agrees at every positive-mass atom.
example : ∃ W : Graphon (Fin 2) (uniformOn Set.univ),
    Graphon.toAEEqFun W = Graphon.toAEEqFun (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2))) ∧
    W = finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)) := by
  let G := finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2))
  obtain ⟨W, hW⟩ := exists_graphon_repr (Graphon.toAEEqFun G)
    (Graphon.toAEEqFun_mem_Icc_ae G) (Graphon.toAEEqFun_symm_ae G)
  refine ⟨W, hW, ?_⟩
  ext i j
  apply ae_iff_of_countable.1 (Graphon.toAEEqFun_eq_iff.1 hW) (i, j)
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [uniformOn_univ]

-- Range violations at an atom cannot be removed by changing representatives.
example : ¬ ∃ W : Graphon I (Measure.dirac 0),
    Graphon.toAEEqFun W = AEEqFun.mk (fun _ : I × I ↦ (2 : ℝ))
      measurable_const.aestronglyMeasurable := by
  rw [exists_graphon_repr_iff]
  rintro ⟨hbdd, _⟩
  have hmk := AEEqFun.coeFn_mk
    (μ := (Measure.dirac (0 : I)).prod (Measure.dirac 0)) (fun _ : I × I ↦ (2 : ℝ))
    measurable_const.aestronglyMeasurable
  rw [Measure.dirac_prod_dirac, ae_dirac_eq] at hbdd hmk
  have hval := Filter.eventually_pure.1 hbdd
  rw [Filter.eventually_pure.1 hmk] at hval
  norm_num at hval

/-- A range-bounded but asymmetric function on two positive-mass atoms. -/
private def asymmetric (p : Fin 2 × Fin 2) : ℝ := if p.1 = 0 then 0 else 1

-- The range constraint alone is not sufficient, even on the smallest nontrivial carrier.
example : ¬ ∃ W : Graphon (Fin 2) (uniformOn Set.univ),
    Graphon.toAEEqFun W = AEEqFun.mk asymmetric
      (measurable_of_finite asymmetric).aestronglyMeasurable := by
  rw [exists_graphon_repr_iff]
  rintro ⟨_, hsymm⟩
  have hmk := AEEqFun.coeFn_mk
    (μ := (uniformOn (Set.univ : Set (Fin 2))).prod (uniformOn Set.univ)) asymmetric
    (measurable_of_finite asymmetric).aestronglyMeasurable
  have hswap := (Measure.measurePreserving_swap (μ := uniformOn (Set.univ : Set (Fin 2)))
    (ν := uniformOn Set.univ)).quasiMeasurePreserving.ae hmk
  have h : ∀ᵐ p ∂(uniformOn (Set.univ : Set (Fin 2))).prod (uniformOn Set.univ),
      asymmetric p = asymmetric p.swap := by
    filter_upwards [hsymm, hmk, hswap] with p hp hmp hmps
    rwa [hmp, hmps] at hp
  have hval : asymmetric (0, 1) = asymmetric (1, 0) := by
    apply ae_iff_of_countable.1 h (0, 1)
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
    simp [uniformOn_univ]
  norm_num [asymmetric] at hval

end TauCeti.DenseGraphLimits
