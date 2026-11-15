/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic

/-!
# Independence of the two halves of an independent family of pairs

Let `(Xᵢ, Yᵢ)` be an independent family of pairs of random variables, and suppose that
within each pair `Xᵢ` and `Yᵢ` are independent. Then the whole family `(Xᵢ)ᵢ` is independent of
the whole family `(Yᵢ)ᵢ`. This is how the past and the future increments of a process with several
independent coordinates, each with independent increments, are seen to be independent.

For a finite family the proof compares laws: the joint law of the pairs is the product of the laws
of the `Xᵢ` and the `Yᵢ`, and Mathlib's `MeasureTheory.measurePreserving_arrowProdEquivProdArrow`
rearranges it into the product of the two coordinate laws. Mathlib's
`ProbabilityTheory.IndepFun.process_indepFun_process₀` reduces an arbitrary family to finite ones.

## Main results

* `ProbabilityTheory.iIndepFun.indepFun_pi_of_indepFun`
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
