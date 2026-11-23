/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.MeasureTheory.MeasurableSpace.CountablyGenerated
import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Almost-everywhere equality of random measures from set evaluations

Two random measures that agree almost surely on each fixed measurable set need not agree almost
surely as measures when the ground σ-algebra is uncountably generated or when realizations take
infinite mass on every generating family. On a countably generated measurable space, however, a
countable measurable cover on which one of the random measures is almost surely finite reduces
equality of measures to countably many intersections with a countable generating π-system
(`MeasureTheory.Measure.ae_eq_of_forall_ae_eq_of_cover`), including when comparing a random measure
on a composition-product `P ⊗ₘ η` against a base random measure pulled back along `Prod.fst`
(`MeasureTheory.Measure.ae_eq_compProd_of_forall_ae_eq_of_cover`).

Unlike `MeasureTheory.Measure.map_eq_iff_forall_finset_map_eval_eq`, which identifies laws on the
Giry space, the criterion here upgrades individual setwise almost-everywhere equalities to a single
event of full measure on which the two realizations coincide on all measurable sets simultaneously.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- On a countably generated measurable space, setwise almost-everywhere equality of two random
measures upgrades to almost-everywhere equality of measures whenever one of them is almost surely
finite on each piece of a countable measurable cover. Neither measurability of the random measures
nor finite total mass is required. -/
theorem ae_eq_of_forall_ae_eq_of_cover {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] [Countable ι] {P : Measure Ω} {M₁ M₂ : Ω → Measure X}
    {s : ι → Set X} (hs : ∀ i, MeasurableSet (s i)) (hcover : ⋃ i, s i = univ)
    (hfin : ∀ i, ∀ᵐ ω ∂P, M₁ ω (s i) ≠ ∞)
    (heq : ∀ A, MeasurableSet A → ∀ᵐ ω ∂P, M₁ ω A = M₂ ω A) : M₁ =ᵐ[P] M₂ := by
  obtain ⟨C, hcount, hpi, huniv, hgen⟩ :=
    MeasurableSpace.exists_countable_isPiSystem_generateFrom (α := X)
  have hC : ∀ A ∈ C, MeasurableSet A :=
    fun A hA ↦ hgen ▸ MeasurableSpace.measurableSet_generateFrom hA
  have hcounts : ∀ᵐ ω ∂P, ∀ i, ∀ A ∈ C, M₁ ω (A ∩ s i) = M₂ ω (A ∩ s i) :=
    ae_all_iff.2 fun i ↦ (ae_ball_iff hcount).2 fun A hA ↦ heq _ ((hC A hA).inter (hs i))
  filter_upwards [ae_all_iff.2 hfin, hcounts] with ω hωfin hωeq
  exact ext_of_generateFrom_of_cover hgen (countable_range s) hpi ((sUnion_range s).trans hcover)
    (forall_mem_range.2 hωfin) (forall_mem_range.2 hωeq)
    (forall_mem_range.2 fun i ↦ by simpa using hωeq i univ huniv)

/-- On a countably generated measurable space, setwise almost-everywhere equality on a
composition-product `P ⊗ₘ η` against a base random measure `N` upgrades to almost-everywhere
equality of measures whenever `N` is `P`-almost surely finite on each piece of a countable
measurable cover. Neither s-finiteness of `P`, any typeclass on `η`, nor measurability of the
random measures is required. -/
theorem ae_eq_compProd_of_forall_ae_eq_of_cover {Ω β X ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] [Countable ι]
    {P : Measure Ω} {η : Kernel Ω β} {N : Ω → Measure X} {M : Ω × β → Measure X}
    {s : ι → Set X} (hs : ∀ i, MeasurableSet (s i)) (hcover : ⋃ i, s i = univ)
    (hfin : ∀ i, ∀ᵐ ω ∂P, N ω (s i) ≠ ∞)
    (heq : ∀ A, MeasurableSet A → ∀ᵐ z ∂(P ⊗ₘ η), M z A = N z.1 A) :
    ∀ᵐ z ∂(P ⊗ₘ η), M z = N z.1 :=
  (ae_eq_of_forall_ae_eq_of_cover hs hcover
    (fun i ↦ (quasiMeasurePreserving_fst_compProd P η).ae (hfin i))
    fun A hA ↦ (heq A hA).mono fun _ h ↦ h.symm).symm

end MeasureTheory.Measure
