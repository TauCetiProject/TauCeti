/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure
public import TauCeti.InformationTheory.Hellinger.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.InformationTheory.Hellinger.DataProcessing
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.Probability.ProductMeasure

/-!
# Tensorization of Hellinger affinity and distance for product measures

The Hellinger affinity of product measures factorizes as the product of the marginal affinities
(Tsybakov, Definition 2.3, property (iv), p. 83):

* Binary products of finite measures (`TauCeti.hellingerAffinity_prod`):
  `hellingerAffinity (P.prod P') (Q.prod Q') = hellingerAffinity P Q * hellingerAffinity P' Q'`.
* Finite products of finite measures (`TauCeti.hellingerAffinity_pi`):
  `hellingerAffinity (Measure.pi P) (Measure.pi Q) = ∏ i, hellingerAffinity (P i) (Q i)`.
* Independent identically distributed products (`TauCeti.sqHellinger_pi_const`):
  `sqHellinger (Measure.pi fun _ : ι => P) (Measure.pi fun _ : ι => Q) =`
  `2 * (1 - (1 - sqHellinger P Q / 2) ^ Fintype.card ι)`.
* Infinite products of probability measures differing on a finite index set `s`
  (`TauCeti.hellingerAffinity_infinitePi`):
  `hellingerAffinity (Measure.infinitePi P) (Measure.infinitePi Q) =`
  `∏ i ∈ s, hellingerAffinity (P i) (Q i)`.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Definition 2.3,
  property (iv), p. 83.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- **Multiplicativity of Hellinger affinity** under binary products of finite measures. -/
theorem hellingerAffinity_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (P Q : Measure α) (P' Q' : Measure β)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsFiniteMeasure P'] [IsFiniteMeasure Q'] :
    hellingerAffinity (P.prod P') (Q.prod Q') =
      hellingerAffinity P Q * hellingerAffinity P' Q' := by
  let ν := P + Q
  let ν' := P' + Q'
  have hP : ν.withDensity (P.rnDeriv ν) = P :=
    Measure.withDensity_rnDeriv_eq P ν (Measure.AbsolutelyContinuous.rfl.add_right Q)
  have hQ : ν.withDensity (Q.rnDeriv ν) = Q :=
    Measure.withDensity_rnDeriv_eq Q ν (Measure.AbsolutelyContinuous.rfl.add_right' P)
  have hP' : ν'.withDensity (P'.rnDeriv ν') = P' :=
    Measure.withDensity_rnDeriv_eq P' ν' (Measure.AbsolutelyContinuous.rfl.add_right Q')
  have hQ' : ν'.withDensity (Q'.rnDeriv ν') = Q' :=
    Measure.withDensity_rnDeriv_eq Q' ν' (Measure.AbsolutelyContinuous.rfl.add_right' P')
  have hPP' : P.prod P' =
      (ν.prod ν').withDensity (fun z => P.rnDeriv ν z.1 * P'.rnDeriv ν' z.2) := by
    nth_rw 1 [← hP, ← hP']
    exact prod_withDensity (P.measurable_rnDeriv ν) (P'.measurable_rnDeriv ν')
  have hQQ' : Q.prod Q' =
      (ν.prod ν').withDensity (fun z => Q.rnDeriv ν z.1 * Q'.rnDeriv ν' z.2) := by
    nth_rw 1 [← hQ, ← hQ']
    exact prod_withDensity (Q.measurable_rnDeriv ν) (Q'.measurable_rnDeriv ν')
  have hfinP : IsFiniteMeasure
      ((ν.prod ν').withDensity fun z => P.rnDeriv ν z.1 * P'.rnDeriv ν' z.2) := by
    rw [← hPP']; infer_instance
  have hfinQ : IsFiniteMeasure
      ((ν.prod ν').withDensity fun z => Q.rnDeriv ν z.1 * Q'.rnDeriv ν' z.2) := by
    rw [← hQQ']; infer_instance
  have hmP : Measurable fun z : α × β => P.rnDeriv ν z.1 * P'.rnDeriv ν' z.2 :=
    ((P.measurable_rnDeriv ν).comp measurable_fst).mul
      ((P'.measurable_rnDeriv ν').comp measurable_snd)
  have hmQ : Measurable fun z : α × β => Q.rnDeriv ν z.1 * Q'.rnDeriv ν' z.2 :=
    ((Q.measurable_rnDeriv ν).comp measurable_fst).mul
      ((Q'.measurable_rnDeriv ν').comp measurable_snd)
  rw [hPP', hQQ', hellingerAffinity_eq_integral_of_withDensity hmP.aemeasurable hmQ.aemeasurable]
  have hsplit : ∀ z : α × β,
      √((P.rnDeriv ν z.1 * P'.rnDeriv ν' z.2).toReal *
          (Q.rnDeriv ν z.1 * Q'.rnDeriv ν' z.2).toReal) =
        √((P.rnDeriv ν z.1).toReal * (Q.rnDeriv ν z.1).toReal) *
          √((P'.rnDeriv ν' z.2).toReal * (Q'.rnDeriv ν' z.2).toReal) := fun z => by
    have hrearr :
        (P.rnDeriv ν z.1).toReal * (P'.rnDeriv ν' z.2).toReal *
          ((Q.rnDeriv ν z.1).toReal * (Q'.rnDeriv ν' z.2).toReal) =
        ((P.rnDeriv ν z.1).toReal * (Q.rnDeriv ν z.1).toReal) *
          ((P'.rnDeriv ν' z.2).toReal * (Q'.rnDeriv ν' z.2).toReal) := by ring
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hrearr,
      Real.sqrt_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  simp_rw [hsplit]
  rw [integral_prod_mul
      (f := fun x => √((P.rnDeriv ν x).toReal * (Q.rnDeriv ν x).toReal))
      (g := fun y => √((P'.rnDeriv ν' y).toReal * (Q'.rnDeriv ν' y).toReal)),
    hellingerAffinity_def, hellingerAffinity_def]

/-- **Tensorization of Hellinger affinity** under finite products of finite measures. -/
theorem hellingerAffinity_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    {mα : ∀ i, MeasurableSpace (α i)} (P Q : ∀ i, Measure (α i))
    [∀ i, IsFiniteMeasure (P i)] [∀ i, IsFiniteMeasure (Q i)] :
    hellingerAffinity (Measure.pi P) (Measure.pi Q) =
      ∏ i, hellingerAffinity (P i) (Q i) := by
  let ν : ∀ i, Measure (α i) := fun i => P i + Q i
  have hP (i : ι) : (ν i).withDensity ((P i).rnDeriv (ν i)) = P i :=
    Measure.withDensity_rnDeriv_eq (P i) (ν i) (Measure.AbsolutelyContinuous.rfl.add_right (Q i))
  have hQ (i : ι) : (ν i).withDensity ((Q i).rnDeriv (ν i)) = Q i :=
    Measure.withDensity_rnDeriv_eq (Q i) (ν i) (Measure.AbsolutelyContinuous.rfl.add_right' (P i))
  have hsfP (i : ι) : SigmaFinite ((ν i).withDensity ((P i).rnDeriv (ν i))) := by
    rw [hP i]; infer_instance
  have hsfQ (i : ι) : SigmaFinite ((ν i).withDensity ((Q i).rnDeriv (ν i))) := by
    rw [hQ i]; infer_instance
  have hpiP : Measure.pi P =
      (Measure.pi ν).withDensity fun x => ∏ i, (P i).rnDeriv (ν i) (x i) := by
    nth_rw 1 [← funext hP]
    exact pi_withDensity ν fun i => (P i).measurable_rnDeriv (ν i)
  have hpiQ : Measure.pi Q =
      (Measure.pi ν).withDensity fun x => ∏ i, (Q i).rnDeriv (ν i) (x i) := by
    nth_rw 1 [← funext hQ]
    exact pi_withDensity ν fun i => (Q i).measurable_rnDeriv (ν i)
  have hfinP : IsFiniteMeasure
      ((Measure.pi ν).withDensity fun x => ∏ i, (P i).rnDeriv (ν i) (x i)) := by
    rw [← hpiP]; infer_instance
  have hfinQ : IsFiniteMeasure
      ((Measure.pi ν).withDensity fun x => ∏ i, (Q i).rnDeriv (ν i) (x i)) := by
    rw [← hpiQ]; infer_instance
  have hmP : Measurable fun x : ∀ i, α i => ∏ i, (P i).rnDeriv (ν i) (x i) :=
    Finset.measurable_prod Finset.univ fun i _ =>
      ((P i).measurable_rnDeriv (ν i)).comp (measurable_pi_apply i)
  have hmQ : Measurable fun x : ∀ i, α i => ∏ i, (Q i).rnDeriv (ν i) (x i) :=
    Finset.measurable_prod Finset.univ fun i _ =>
      ((Q i).measurable_rnDeriv (ν i)).comp (measurable_pi_apply i)
  rw [hpiP, hpiQ, hellingerAffinity_eq_integral_of_withDensity hmP.aemeasurable hmQ.aemeasurable]
  have hsplit : ∀ x : ∀ i, α i,
      √((∏ i, (P i).rnDeriv (ν i) (x i)).toReal * (∏ i, (Q i).rnDeriv (ν i) (x i)).toReal) =
        ∏ i, √(((P i).rnDeriv (ν i) (x i)).toReal * ((Q i).rnDeriv (ν i) (x i)).toReal) := by
    intro x
    rw [ENNReal.toReal_prod, ENNReal.toReal_prod, ← Finset.prod_mul_distrib,
      Real.sqrt_prod Finset.univ fun i _ =>
        mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  simp_rw [hsplit]
  rw [integral_fintype_prod_eq_prod
    (f := fun i y => √(((P i).rnDeriv (ν i) y).toReal * ((Q i).rnDeriv (ν i) y).toReal))]
  exact Finset.prod_congr rfl fun i _ => (hellingerAffinity_def (P i) (Q i)).symm

/-- **Tensorization of squared Hellinger distance** for finite i.i.d. products. -/
theorem sqHellinger_pi_const {ι α : Type*} [Fintype ι] {mα : MeasurableSpace α}
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    sqHellinger (Measure.pi fun _ : ι => P) (Measure.pi fun _ : ι => Q) =
      2 * (1 - (1 - sqHellinger P Q / 2) ^ Fintype.card ι) := by
  have haff : 1 - sqHellinger P Q / 2 = hellingerAffinity P Q := by
    rw [sqHellinger_def]; ring
  rw [sqHellinger_def, hellingerAffinity_pi, Finset.prod_const, Finset.card_univ, haff]

/-- **Tensorization of Hellinger affinity for infinite product measures.** If two families of
probability measures agree outside a finite set `s` of coordinates, the Hellinger affinity of their
infinite products is the finite product of the marginal affinities over `s`. -/
theorem hellingerAffinity_infinitePi {ι : Type*} {α : ι → Type*}
    {mα : ∀ i, MeasurableSpace (α i)} (P Q : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    {s : Finset ι} (hPQ : ∀ i, i ∉ s → P i = Q i) :
    hellingerAffinity (Measure.infinitePi P) (Measure.infinitePi Q) =
      ∏ i ∈ s, hellingerAffinity (P i) (Q i) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s)
  have hP := (measurePreserving_infinitePi_piEquivPiSubtypeProd P (· ∈ s)).map_eq
  have hQ := (measurePreserving_infinitePi_piEquivPiSubtypeProd Q (· ∈ s)).map_eq
  rw [← e.hellingerAffinity_map (Measure.infinitePi P) (Measure.infinitePi Q), hP, hQ,
    hellingerAffinity_prod]
  have htail : (fun i : {i // i ∉ s} => P i) = fun i : {i // i ∉ s} => Q i :=
    funext fun i => hPQ i.1 i.2
  rw [htail, hellingerAffinity_self, probReal_univ, mul_one,
    Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi, hellingerAffinity_pi,
    Finset.prod_coe_sort (f := fun i => hellingerAffinity (P i) (Q i))]

end TauCeti
