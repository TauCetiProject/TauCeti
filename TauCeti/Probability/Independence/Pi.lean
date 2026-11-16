/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic

/-!
# Independence and product laws on finite products

This file collects two general facts relating independence to finite product measures `Measure.pi`:

1. If `(Xᵢ, Yᵢ)` is an independent family of pairs of random variables and `Xᵢ` is independent of
   `Yᵢ` for each `i`, then the whole family `(Xᵢ)ᵢ` is independent of `(Yᵢ)ᵢ`. For a finite family
   the proof compares laws via `MeasureTheory.measurePreserving_arrowProdEquivProdArrow`, and
   `ProbabilityTheory.IndepFun.process_indepFun_process₀` reduces an arbitrary family to finite
   ones.
2. Under a measurable equivalence `e : E ≃ᵐ ((i : ι) → 𝓧 i)` pushing a measure `μ` forward to a
   finite product of probability measures `Measure.pi ν`, a random variable `H` has law `μ` if and
   only if its coordinates `i ↦ e (H ·) i` are independent with marginal laws `ν i`.

## Main results

* `ProbabilityTheory.iIndepFun.indepFun_pi_of_indepFun`
* `MeasurableEquiv.hasLaw_iff_iIndepFun_and_hasLaw`
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω ι α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {P : Measure Ω}

/-- The case of a finite family, where the laws of the two halves are finite products. -/
private theorem iIndepFun.indepFun_pi_of_indepFun_of_finite [Finite ι] {X : ι → Ω → α}
    {Y : ι → Ω → β} (hX : ∀ i, AEMeasurable (X i) P) (hY : ∀ i, AEMeasurable (Y i) P)
    (h : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) P) (hXY : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P := by
  have := Fintype.ofFinite ι
  have := h.isProbabilityMeasure
  have hZ i : AEMeasurable (fun ω ↦ (X i ω, Y i ω)) P := (hX i).prodMk (hY i)
  have hpair : P.map (fun ω i ↦ (X i ω, Y i ω)) =
      Measure.pi fun i ↦ (P.map (X i)).prod (P.map (Y i)) := by
    rw [h.map_fun_eq_pi_map hZ]
    exact congrArg Measure.pi
      (funext fun i ↦ (indepFun_iff_map_prod_eq_prod_map_map (hX i) (hY i)).1 (hXY i))
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    (h.comp (fun _ ↦ Prod.fst) fun _ ↦ measurable_fst).map_fun_eq_pi_map hX,
    (h.comp (fun _ ↦ Prod.snd) fun _ ↦ measurable_snd).map_fun_eq_pi_map hY,
    ← (measurePreserving_arrowProdEquivProdArrow α β ι _ _).map_eq, ← hpair,
    AEMeasurable.map_map_of_aemeasurable (MeasurableEquiv.measurable _).aemeasurable
      (AEMeasurable.of_eval hZ)]
  -- `arrowProdEquivProdArrow` sends a family of pairs to its two coordinate families
  rfl

/-- If the pairs `(X i, Y i)` form an independent family and `X i` is independent of `Y i` for
every `i`, then the family `(X i)ᵢ` is independent of the family `(Y i)ᵢ`. -/
theorem iIndepFun.indepFun_pi_of_indepFun {X : ι → Ω → α} {Y : ι → Ω → β}
    (hX : ∀ i, AEMeasurable (X i) P) (hY : ∀ i, AEMeasurable (Y i) P)
    (h : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) P) (hXY : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P := by
  classical
  have := h.isProbabilityMeasure
  -- it suffices to treat the coordinates in finite sets `I` and `J`, and both lie in `I ∪ J`
  refine IndepFun.process_indepFun_process₀ hX hY fun I J ↦ ?_
  have hK := iIndepFun.indepFun_pi_of_indepFun_of_finite (ι := ↥(I ∪ J)) (fun i ↦ hX i)
    (fun i ↦ hY i) (h.precomp Subtype.val_injective) fun i ↦ hXY i
  exact hK.comp (φ := fun x (i : I) ↦ x ⟨i, Finset.mem_union_left J i.2⟩)
    (ψ := fun y (j : J) ↦ y ⟨j, Finset.mem_union_right I j.2⟩) (by fun_prop) (by fun_prop)

end ProbabilityTheory

namespace MeasurableEquiv

open ProbabilityTheory

/-- A random variable `H` has law `μ` if and only if its coordinates under a measurable
equivalence `e` pushing `μ` forward to a finite product of probability measures `Measure.pi ν`
are independent with marginal laws `ν i`. -/
theorem hasLaw_iff_iIndepFun_and_hasLaw {Ω E ι : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [MeasurableSpace E] {μ : Measure E} {𝓧 : ι → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] {ν : (i : ι) → Measure (𝓧 i)}
    [∀ i, IsProbabilityMeasure (ν i)] (e : E ≃ᵐ ((i : ι) → 𝓧 i))
    (hmap : μ.map e = Measure.pi ν) {H : Ω → E} :
    HasLaw H μ P ↔
      iIndepFun (fun i ω ↦ e (H ω) i) P ∧ ∀ i, HasLaw (fun ω ↦ e (H ω) i) (ν i) P := by
  have : IsProbabilityMeasure μ := ⟨by
    have h := congrArg (fun m ↦ m _root_.Set.univ) hmap
    simpa [Measure.map_apply e.measurable .univ] using h⟩
  constructor
  · intro hH
    have : IsProbabilityMeasure P := hH.isProbabilityMeasure
    have hcoord : HasLaw (fun ω ↦ e (H ω)) (Measure.pi ν) P :=
      (⟨e.measurable.aemeasurable, hmap⟩ : HasLaw e (Measure.pi ν) μ).fun_comp hH
    have hmarg : ∀ i, HasLaw (fun ω ↦ e (H ω) i) (ν i) P := fun i ↦ by
      have heval : HasLaw (Function.eval i) (ν i) (Measure.pi ν) :=
        ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval ν i).map_eq⟩
      simpa only [Function.comp_def, Function.eval] using heval.fun_comp hcoord
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi hmarg).2 hcoord, hmarg⟩
  · rintro ⟨hindep, hmarg⟩
    have hcoord : HasLaw (fun ω ↦ e (H ω)) (Measure.pi ν) P := hindep.hasLaw_pi hmarg
    have hback : HasLaw e.symm μ (Measure.pi ν) := by
      refine ⟨e.symm.measurable.aemeasurable, ?_⟩
      rw [← hmap, Measure.map_map e.symm.measurable e.measurable]
      simp
    simpa only [MeasurableEquiv.symm_apply_apply] using hback.fun_comp hcoord

end MeasurableEquiv
