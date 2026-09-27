/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
import TauCeti.Probability.Independence.InfinitePi
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Conditional independence of disjoint parts of an i.i.d. family

Conditionally on its directing measure, a conditionally i.i.d. sequence has independent
restrictions to disjoint sets of coordinates.  The joint-law statement retains the directing
measure and allows both sets to be infinite; it is the form used when hidden and visible strips
of an exchangeable array are separated.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- The joint law of the directing measure and two disjoint restrictions is the mixture of the
products of their conditional laws. Both restrictions may be infinite. -/
theorem ConditionallyIIDWith.jointLaw_pair_domRestrict [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) {S T : Set ℕ} (hST : Disjoint S T) :
    μ.map (fun ω => (ν ω,
      (S.domRestrict (fun i => X i ω), T.domRestrict (fun i => X i ω)))) =
      (μ.map ν).bind fun P => (Measure.dirac P).prod
        ((Measure.infinitePi fun _ : S => (P : Measure α)).prod
          (Measure.infinitePi fun _ : T => (P : Measure α))) := by
  let F : ProbabilityMeasure α × (ℕ → α) →
      ProbabilityMeasure α × ((S → α) × (T → α)) :=
    fun p => (p.1, (S.domRestrict p.2, T.domRestrict p.2))
  have hF : Measurable F :=
    measurable_fst.prodMk
      (((Set.measurable_restrict S).comp measurable_snd).prodMk
        ((Set.measurable_restrict T).comp measurable_snd))
  have hF_eq : F = Prod.map id (fun x => (S.domRestrict x, T.domRestrict x)) := by
    funext p
    cases p
    rfl
  calc
    μ.map (fun ω => (ν ω,
        (S.domRestrict (fun i => X i ω), T.domRestrict (fun i => X i ω)))) =
        (jointPathLaw μ X ν).map F := by
          rw [jointPathLaw_def]
          have hpath : AEMeasurable (fun ω => (ν ω, fun i => X i ω)) μ :=
            h.measurable_directing.aemeasurable.prodMk
              (AEMeasurable.of_eval h.aemeasurable)
          simpa only [F, Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hpath).symm
    _ = (iidMixtureLaw (μ.map ν) id).map F := by rw [h.jointPathLaw_eq_iidMixtureLaw]
    _ = (μ.map ν).bind fun P => (Measure.dirac P).prod
          ((Measure.infinitePi fun _ : S => (P : Measure α)).prod
            (Measure.infinitePi fun _ : T => (P : Measure α))) := by
          rw [iidMixtureLaw_def, TauCeti.MeasureTheory.map_bind
            (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const
              (ι' := ℕ) (id : ProbabilityMeasure α → ProbabilityMeasure α)
              measurable_id).aemeasurable hF]
          congr 1
          funext P
          calc
            ((Measure.dirac P).prod (Measure.infinitePi fun _ : ℕ => (P : Measure α))).map F =
                ((Measure.dirac P).map id).prod
                  ((Measure.infinitePi fun _ : ℕ => (P : Measure α)).map
                    (fun x => (S.domRestrict x, T.domRestrict x))) := by
                  rw [hF_eq]
                  exact (Measure.map_prod_map (Measure.dirac P)
                    (Measure.infinitePi fun _ : ℕ => (P : Measure α)) measurable_id
                    ((Set.measurable_restrict S).prodMk (Set.measurable_restrict T))).symm
            _ = _ := by
              rw [Measure.map_id,
                TauCeti.Probability.infinitePi_map_pair_domRestrict
                  (fun _ : ℕ => (P : Measure α)) hST]

end TauCeti.Probability
