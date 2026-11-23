/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Independence of an almost sure limit

Independence from a fixed sigma-algebra is preserved under almost sure limits along a countably
generated nontrivial filter, both for stochastic processes
(`ProbabilityTheory.indep_comap_process_of_ae_tendsto`) and for single random variables
(`ProbabilityTheory.indep_comap_of_ae_tendsto`). Using product bounded continuous test functions
makes the process-level limit work for an arbitrary index type without moment assumptions, without
second countability of the target spaces, and without `HasOuterApproxClosed` on product spaces. In
particular, it allows future increments of a right-continuous process to remain independent after
right-continuation of its filtration.
-/

public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction

namespace ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsZeroOrProbabilityMeasure P]

/-- An almost sure coordinatewise limit along a countably generated nontrivial filter of
stochastic processes eventually independent of a fixed sigma-algebra `m ≤ mΩ` under a zero or
probability measure, taking values in Borel spaces with outer closed approximation, is independent
of `m` provided the coordinates of the approximating processes are eventually a.e. measurable and
those of the limit are a.e. measurable. Neither moments of the random variables nor second
countability of the target spaces are required. -/
theorem indep_comap_process_of_ae_tendsto {ι S : Type*} {E : S → Type*}
    [∀ s, TopologicalSpace (E s)] [∀ s, MeasurableSpace (E s)] [∀ s, BorelSpace (E s)]
    [∀ s, HasOuterApproxClosed (E s)] {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {X : ι → (s : S) → Ω → E s} {Y : (s : S) → Ω → E s} (hm : m ≤ mΩ)
    (hX : ∀ s, ∀ᶠ i in l, AEMeasurable (X i s) P) (hY : ∀ s, AEMeasurable (Y s) P)
    (hind : ∀ᶠ i in l, Indep m (MeasurableSpace.pi.comap (fun ω s => X i s ω)) P)
    (hlim : ∀ s, ∀ᵐ ω ∂P, Tendsto (fun i => X i s ω) l (nhds (Y s ω))) :
    Indep m (MeasurableSpace.pi.comap (fun ω s => Y s ω)) P := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP
  · simp [Indep_iff]
  refine indep_comap_process_of_prod_bcf hm hY fun A hA I f => ?_
  have hg : Measurable fun z : (s : I) → E s => ∏ s, f s (z s) :=
    Finset.measurable_prod _ fun s _ => (f s).continuous.measurable.comp (measurable_pi_apply s)
  have hXpi : ∀ᶠ i in l, AEMeasurable (fun ω (s : I) => X i s ω) P :=
    (Filter.eventually_all.2 fun s : I => hX s).mono fun _ hi => aemeasurable_pi_iff.2 hi
  have hindI : ∀ᶠ i in l, Indep m (MeasurableSpace.pi.comap (fun ω (s : I) => X i s ω)) P :=
    hind.mono fun i hi => indep_of_indep_of_le_right hi (by
      have hcomp : (fun ω (s : I) => X i s ω) =
          (fun (z : (s : S) → E s) (s : I) => z s) ∘ fun ω s => X i s ω := rfl
      rw [hcomp, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono
        (measurable_pi_iff.2 fun s => measurable_pi_apply s.val).comap_le)
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun ω => ∏ s : I, f s (X i s ω)) P :=
    hXpi.mono fun _ hi => (hg.comp_aemeasurable hi).aestronglyMeasurable
  have hbound :
      ∀ᶠ i in l, ∀ᵐ ω ∂P, ‖∏ s : I, f s (X i s ω)‖ ≤ ∏ s : I, ‖f s‖ :=
    .of_forall fun _ => .of_forall fun ω => by
      rw [norm_prod]
      gcongr with s
      exact (f s).norm_coe_le_norm _
  have hconv :
      ∀ᵐ ω ∂P, Tendsto (fun i => ∏ s : I, f s (X i s ω)) l (nhds (∏ s : I, f s (Y s ω))) :=
    (ae_all_iff.2 fun s : I => hlim s).mono fun ω hω => tendsto_finsetProd _ fun s _ =>
      (f s).continuous.continuousAt.tendsto.comp (hω s)
  have hall := tendsto_integral_filter_of_dominated_convergence (fun _ => ∏ s : I, ‖f s‖)
    hmeas hbound (integrable_const _) hconv
  have hset := tendsto_integral_filter_of_dominated_convergence (μ := P.restrict A)
    (fun _ => ∏ s : I, ‖f s‖) (hmeas.mono fun _ h => h.restrict)
    (hbound.mono fun _ h => ae_restrict_of_ae h) (integrable_const _) (ae_restrict_of_ae hconv)
  have heq : ∀ᶠ i in l, ∫ ω in A, ∏ s : I, f s (X i s ω) ∂P =
      P.real A * ∫ ω, ∏ s : I, f s (X i s ω) ∂P :=
    (hindI.and hXpi).mono fun _ ⟨hi, hXi⟩ =>
      hi.setIntegral_eq_mul hm hXi hA hg.aestronglyMeasurable
  exact tendsto_nhds_unique hset ((tendsto_const_nhds.mul hall).congr' (heq.mono fun _ h => h.symm))

/-- An almost sure limit of random variables independent of a fixed sigma-algebra is
independent of that sigma-algebra. No moments of the random variables are required. -/
theorem indep_comap_of_ae_tendsto {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E] {X : ℕ → Ω → E} {Y : Ω → E} (hm : m ≤ mΩ)
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hind : ∀ n, Indep m (.comap (X n) inferInstance) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (nhds (Y ω))) :
    Indep m (.comap Y inferInstance) P := by
  have hpi := indep_comap_process_of_ae_tendsto (S := Unit) (E := fun _ => E)
    (X := fun n _ => X n) (Y := fun _ => Y) hm
    (fun _ => .of_forall hX) (fun _ => hY)
    (.of_forall fun n => indep_of_indep_of_le_right (hind n) (by
      have hcomp : (fun ω (_ : Unit) => X n ω) = (fun x (_ : Unit) => x) ∘ X n := rfl
      rw [hcomp, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_pi_iff.2 fun _ => measurable_id).comap_le))
    (fun _ => hlim)
  have hcomp : Y = (fun f : Unit → E => f ()) ∘ fun ω (_ : Unit) => Y ω := rfl
  rw [hcomp, ← MeasurableSpace.comap_comp]
  exact indep_of_indep_of_le_right hpi
    (MeasurableSpace.comap_mono (measurable_pi_apply ()).comap_le)

end ProbabilityTheory
