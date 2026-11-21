/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic

/-!
# Independence of coordinate families, independent arrays, and product laws

Let `(Xᵢ, Yᵢ)` be an independent family of pairs of random variables, and suppose that
within each pair `Xᵢ` and `Yᵢ` are independent. Then the whole family `(Xᵢ)ᵢ` is independent of
the whole family `(Yᵢ)ᵢ`. This is how the past and the future increments of a process with several
independent coordinates, each with independent increments, are seen to be independent.

For a finite family the proof compares laws: the joint law of the pairs is the product of the laws
of the `Xᵢ` and the `Yᵢ`, and Mathlib's `MeasureTheory.measurePreserving_arrowProdEquivProdArrow`
rearranges it into the product of the two coordinate laws. Mathlib's
`ProbabilityTheory.IndepFun.process_indepFun_process₀` reduces an arbitrary family to finite ones.

Similarly, if a two-parameter array `(X a b)` has mutually independent rows and mutually
independent entries within each row, then its columns `b ↦ (a ↦ X a b)` are mutually independent
(`ProbabilityTheory.iIndepFun.swap`).

Conversely, whenever a measurable equivalence `e : E ≃ᵐ (∀ i, α i)` over a finite index type
pushes a measure `μ` forward to a product of probability measures `Measure.pi ν`, having law `μ`
is equivalent to the `e`-coordinates being mutually independent with marginal laws `ν i`.

## Main results

* `ProbabilityTheory.iIndepFun.indepFun_pi_of_indepFun`
* `ProbabilityTheory.iIndepFun.swap`
* `TauCeti.Probability.hasLaw_iff_iIndepFun_of_map_eq_pi`
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
  exact hK.comp (φ := fun x (i : I) ↦ x ⟨i, Finset.mem_union_left J i.property⟩)
    (ψ := fun y (j : J) ↦ y ⟨j, Finset.mem_union_right I j.property⟩) (by fun_prop) (by fun_prop)

/-- If a two-parameter array `(X a b)` has mutually independent rows `a ↦ (b ↦ X a b)` and
mutually independent entries `b ↦ X a b` within each row, then its columns `b ↦ (a ↦ X a b)` are
mutually independent. -/
theorem iIndepFun.swap {α' β' : Type*} {E : α' → β' → Type*}
    [∀ a b, MeasurableSpace (E a b)] {X : ∀ a b, Ω → E a b}
    (h1 : iIndepFun (fun a ω b ↦ X a b ω) P) (h2 : ∀ a, iIndepFun (X a) P)
    (hX : ∀ a b, AEMeasurable (X a b) P) :
    iIndepFun (fun b ω a ↦ X a b ω) P := by
  have := h1.isProbabilityMeasure
  -- Replace each a.e.-measurable entry by its measurable version, then regroup via `piCurry`.
  let Y (a : α') (b : β') : Ω → E a b := (hX a b).mk (X a b)
  have mY (a : α') (b : β') : Measurable (Y a b) := (hX a b).measurable_mk
  have hsig : iIndepFun (fun (p : Sigma fun _ : β' ↦ α') ω ↦ Y p.2 p.1 ω) P :=
    (iIndepFun_uncurry' mY (h1.process_congr fun a b ↦ (hX a b).ae_eq_mk)
      (fun a ↦ (h2 a).congr fun b ↦ (hX a b).ae_eq_mk)).precomp
      (g := fun (p : Sigma fun _ : β' ↦ α') ↦ (p.2, p.1))
      fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by simp only [Prod.mk.injEq] at h; cases h.1; cases h.2; rfl
  have hYswap : iIndepFun (fun b ω a ↦ Y a b ω) P := by
    have hcurry : (fun ω b a ↦ Y a b ω) = (MeasurableEquiv.piCurry (fun b a ↦ E a b)) ∘
        (fun ω (p : Sigma fun _ : β' ↦ α') ↦ Y p.2 p.1 ω) := by
      ext; simp [Sigma.curry]
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), hcurry,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 hsig,
      Measure.infinitePi_map_piCurry (fun b a ↦ P.map (Y a b))]
    congrm Measure.infinitePi fun b ↦ ?_
    exact ((iIndepFun_iff_map_fun_eq_infinitePi_map (fun a ↦ mY a b)).1
      (hsig.precomp (g := fun a ↦ ⟨b, a⟩) fun _ _ h ↦ by simpa using h)).symm
  exact hYswap.process_congr fun b a ↦ (hX a b).ae_eq_mk.symm

end ProbabilityTheory

namespace TauCeti.Probability

open ProbabilityTheory

/-- **Product-law equivalence through a measurable coordinate equivalence.** If a measurable
equivalence `e : E ≃ᵐ (∀ i, α i)` over a finite index type `ι` pushes a measure `μ` forward to a
product of probability measures `Measure.pi ν`, then a random variable `H` on a probability space
has law `μ` if and only if its coordinates `i ↦ e (H ·) i` are mutually independent with marginal
laws `ν i`. -/
theorem hasLaw_iff_iIndepFun_of_map_eq_pi {Ω E ι : Type*} {α : ι → Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [Fintype ι] [∀ i, MeasurableSpace (α i)]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure E} {ν : ∀ i, Measure (α i)}
    [∀ i, IsProbabilityMeasure (ν i)] (e : E ≃ᵐ (∀ i, α i)) (hμ : μ.map e = Measure.pi ν)
    {H : Ω → E} :
    HasLaw H μ P ↔
      iIndepFun (fun i ω ↦ e (H ω) i) P ∧ ∀ i, HasLaw (fun ω ↦ e (H ω) i) (ν i) P := by
  have he : HasLaw H μ P ↔ HasLaw (fun ω ↦ e (H ω)) (Measure.pi ν) P := by
    rw [← hμ]
    refine ⟨fun h ↦ HasLaw.comp ⟨e.measurable.aemeasurable, rfl⟩ h, fun h ↦ ?_⟩
    have hinv : HasLaw e.symm μ (μ.map e) := ⟨e.symm.measurable.aemeasurable, by
      rw [Measure.map_map e.symm.measurable e.measurable]; simp⟩
    simpa [Function.comp_def] using hinv.comp h
  rw [he]
  refine ⟨fun h ↦ ?_, fun ⟨hind, hc⟩ ↦ hind.hasLaw_pi hc⟩
  have hc : ∀ i, HasLaw (fun ω ↦ e (H ω) i) (ν i) P := fun i ↦
    HasLaw.comp ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval ν i).map_eq⟩ h
  exact ⟨(iIndepFun_iff_hasLaw_pi_pi hc).2 h, hc⟩

end TauCeti.Probability
