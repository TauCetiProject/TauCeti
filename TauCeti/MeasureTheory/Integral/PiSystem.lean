/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# A Dynkin (π-λ) step for Bochner integrals

If a function's integral vanishes on the whole space and on every member of a π-system generating
a sub-σ-algebra, then it vanishes on every set measurable for that sub-σ-algebra; in particular,
for a π-system generating the ambient σ-algebra, it vanishes on every measurable set.

This is the Bochner counterpart of Mathlib's `ℝ≥0∞`-valued
`MeasureTheory.lintegral_eq_lintegral_of_isPiSystem`. Stating it for an arbitrary π-system rather
than for a specific one (rectangles, boxes) lets a single theorem serve every product-measure
arity.

For a countably spanning generating π-system, testing set integrals determines a function
integrable on each generating set.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

/-- **The Dynkin (π-λ) step for Bochner integrals.** A function whose integral vanishes on the
whole space and on every member of a π-system generating a sub-σ-algebra `m` has vanishing
integral on every `m`-measurable set. Taking `m = m0` gives vanishing on every measurable set. -/
theorem setIntegral_eq_zero_of_isPiSystem {X E : Type*} {m m0 : MeasurableSpace X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ρ : Measure X} {S : Set (Set X)} (hm : m ≤ m0)
    (hgen : m = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) {f : X → E}
    (hf : Integrable f ρ) (huniv : ∫ x, f x ∂ρ = 0) (hS : ∀ s ∈ S, ∫ x in s, f x ∂ρ = 0) :
    ∀ u, MeasurableSet[m] u → ∫ x in u, f x ∂ρ = 0 := by
  intro u hu
  induction u, hu using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic s hs => exact hS s hs
  | compl u hu ih => rw [setIntegral_compl (hm u hu) hf, huniv, ih, sub_zero]
  | iUnion u hd hu ih => simp [integral_iUnion (fun i => hm _ (hu i)) hd hf.integrableOn, ih]

/-- Testing set integrals on a countably spanning generating π-system determines a
Banach-valued function integrable on each generating set. -/
theorem ae_eq_zero_of_setIntegral_eq_zero_of_isPiSystem
    {X E : Type*} {m : MeasurableSpace X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {S : Set (Set X)}
    (hgen : m = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S)
    (hcover : IsCountablySpanning S) {f : X → E} (hf : ∀ s ∈ S, IntegrableOn f s μ)
    (hS : ∀ s ∈ S, ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hmeas {s : Set X} (hs : s ∈ S) : MeasurableSet s :=
    hgen ▸ MeasurableSpace.measurableSet_generateFrom hs
  obtain ⟨v, hv, hcover⟩ := hcover
  have hlocal (n : ℕ) : f =ᵐ[μ.restrict (v n)] 0 := by
    apply (hf _ (hv n)).ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs _
    apply setIntegral_eq_zero_of_isPiSystem le_rfl hgen hpi (hf _ (hv n)) (hS _ (hv n))
      (fun t ht => ?_) s hs
    rw [Measure.restrict_restrict (hmeas ht)]
    by_cases hempty : t ∩ v n = ∅
    · rw [hempty, setIntegral_empty]
    · exact hS _ (hpi t ht (v n) (hv n) (Set.nonempty_iff_ne_empty.mpr hempty))
  have h := (ae_eq_restrict_iUnion_iff v f 0).mpr hlocal
  rwa [hcover, Measure.restrict_univ] at h

end TauCeti
