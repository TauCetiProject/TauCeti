/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Mixture.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Independent categorical selection

An independent categorical selector and a source of random noise realize a finite mixture:
conditional on selecting `i`, apply the `i`th measurable transformation to the common noise.
The component law is the pushforward of the noise law by that transformation.

This gives the random-variable construction corresponding to `finiteMixtureMeasure_eq_bind`.
It allows the transformations to share one noise variable; no independence between the potential
component values is needed.

## Main results

* `MeasureTheory.Measure.map_uncurry_prod_eq_bind_map` identifies the pushforward of a product
  measure by an almost-everywhere measurable indexed family with a measure bind.
* `ProbabilityTheory.IndepFun.hasLaw_apply_bind` gives the corresponding law for an independent
  selector and noise variable.
* `TauCeti.Probability.map_uncurry_prod_eq_finiteMixtureMeasure` identifies the pushforward of a
  categorical product law by an indexed family with the corresponding finite mixture.
* `ProbabilityTheory.IndepFun.hasLaw_apply_finiteMixtureMeasure` gives the resulting law for an
  independent categorical selector and noise variable.
* `ProbabilityTheory.IndepFun.hasLaw_eval_finiteMixtureMeasure` selects directly from a finite
  family of potential random variables.
-/

public section

noncomputable section

open Convexity MeasureTheory

namespace MeasureTheory.Measure

variable {I A B : Type*} [MeasurableSpace I] [MeasurableSpace A] [MeasurableSpace B]

/-- Mapping a product measure by an almost-everywhere measurable indexed family gives the bind of
the component pushforwards. -/
theorem map_uncurry_prod_eq_bind_map (mu : Measure I) (rho : Measure A) [SFinite rho]
    {f : I → A → B} (hf : AEMeasurable (Function.uncurry f) (mu.prod rho)) :
    (mu.prod rho).map (Function.uncurry f) = mu.bind (fun i ↦ rho.map (f i)) := by
  rw [Measure.prod_eq_of_sfinite] at hf ⊢
  rw [Measure.map_bind Measurable.map_prodMk_left.aemeasurable hf]
  apply Measure.bind_congr_right
  filter_upwards [Measurable.map_prodMk_left.aemeasurable.ae_of_bind hf] with i hi
  have hmap := hi.map_map_of_aemeasurable measurable_prodMk_left.aemeasurable
  rw [show Function.uncurry f ∘ Prod.mk i = f i by rfl] at hmap
  exact hmap

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {I A B : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace A] [MeasurableSpace B]

/-- An indexed family is almost-everywhere measurable for a categorical product law when every
positive-weight component is almost-everywhere measurable. -/
private theorem aemeasurable_uncurry_categoricalMeasure_prod (p : StdSimplex NNReal I)
    (rho : Measure A) [SFinite rho] {f : I → A → B}
    (hf : ∀ i, 0 < p.weights i → AEMeasurable (f i) rho) :
    AEMeasurable (Function.uncurry f) ((categoricalMeasure p).prod rho) := by
  rw [categoricalMeasure_def, ← Measure.sum_fintype, Measure.prod_sum_left]
  apply AEMeasurable.sum_measure
  intro i
  rw [Measure.prod_smul_left]
  by_cases hi : p.weights i = 0
  · simp [hi]
  · apply AEMeasurable.smul_measure
    rw [Measure.dirac_prod, (measurableEmbedding_prodMk_left i).aemeasurable_map_iff]
    change AEMeasurable (f i) rho
    exact hf i (pos_iff_ne_zero.mpr hi)

/-- Mapping a categorical law times a noise law by an indexed family that is almost-everywhere
measurable on the positive-weight components gives their finite mixture. -/
theorem map_uncurry_prod_eq_finiteMixtureMeasure (p : StdSimplex NNReal I) (ρ : Measure A)
    [SFinite ρ] {f : I → A → B} (hf : ∀ i, 0 < p.weights i → AEMeasurable (f i) ρ) :
    ((categoricalMeasure p).prod ρ).map (Function.uncurry f) =
      finiteMixtureMeasure p (fun i ↦ ρ.map (f i)) := by
  rw [Measure.map_uncurry_prod_eq_bind_map _ _
    (aemeasurable_uncurry_categoricalMeasure_prod p ρ hf), finiteMixtureMeasure_eq_bind]

/-- Mapping a categorical law times a function-valued law by evaluation gives the finite mixture
of its coordinate pushforwards. -/
theorem map_eval_prod_eq_finiteMixtureMeasure_map (p : StdSimplex NNReal I)
    (rho : Measure (I → B)) [SFinite rho] :
    ((categoricalMeasure p).prod rho).map (fun z ↦ z.2 z.1) =
      finiteMixtureMeasure p (fun i ↦ rho.map (Function.eval i)) := by
  change ((categoricalMeasure p).prod rho).map
      (Function.uncurry fun i (y : I → B) ↦ y i) =
    finiteMixtureMeasure p (fun i ↦ rho.map (fun y ↦ y i))
  exact map_uncurry_prod_eq_finiteMixtureMeasure p rho
    (fun i _ ↦ (measurable_pi_apply i).aemeasurable)

/-- Evaluation under a categorical law times a product probability law gives the corresponding
finite mixture. -/
@[simp]
theorem map_eval_prod_pi_eq_finiteMixtureMeasure (p : StdSimplex NNReal I)
    (K : I → Measure B) [∀ i, IsProbabilityMeasure (K i)] :
    ((categoricalMeasure p).prod (Measure.pi K)).map (fun z ↦ z.2 z.1) =
      finiteMixtureMeasure p K := by
  rw [map_eval_prod_eq_finiteMixtureMeasure_map]
  apply finiteMixtureMeasure_congr
  intro i _
  exact (measurePreserving_eval K i).map_eq

end TauCeti.Probability

namespace ProbabilityTheory

variable {Omega J C D : Type*} [MeasurableSpace Omega] [MeasurableSpace J]
  [MeasurableSpace C] [MeasurableSpace D] {Q : Measure Omega} {V : Omega → J}
  {W : Omega → C} {mu : Measure J} {rho : Measure C} {L : J → Measure D}
  {g : J → C → D}

/-- Applying an indexed family to an independent selector and noise variable gives the bind of the
component pushforwards. -/
theorem IndepFun.hasLaw_apply_bind_map [IsFiniteMeasure mu] (hVW : IndepFun V W Q)
    (hV : HasLaw V mu Q) (hW : HasLaw W rho Q)
    (hg : AEMeasurable (Function.uncurry g) (mu.prod rho)) :
    HasLaw (fun omega ↦ g (V omega) (W omega)) (mu.bind fun j ↦ rho.map (g j)) Q := by
  let _ : IsFiniteMeasure Q := hV.isFiniteMeasure
  let _ : IsFiniteMeasure rho := hW.isFiniteMeasure_iff.mp inferInstance
  exact (HasLaw.mk hg (Measure.map_uncurry_prod_eq_bind_map mu rho hg)).fun_comp
    (hVW.hasLaw_prod hV hW)

/-- Applying an indexed family to an independent selector and noise variable gives any component
kernel that agrees almost everywhere with the component pushforwards. -/
theorem IndepFun.hasLaw_apply_bind [IsFiniteMeasure mu] (hVW : IndepFun V W Q)
    (hV : HasLaw V mu Q) (hW : HasLaw W rho Q)
    (hg : AEMeasurable (Function.uncurry g) (mu.prod rho))
    (hL : (fun j ↦ rho.map (g j)) =ᵐ[mu] L) :
    HasLaw (fun omega ↦ g (V omega) (W omega)) (mu.bind L) Q := by
  have h := hVW.hasLaw_apply_bind_map hV hW hg
  rw [Measure.bind_congr_right hL] at h
  exact h

variable {Ω I A B : Type*} [MeasurableSpace Ω] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableSpace A] [MeasurableSpace B]
  {P : Measure Ω} {Z : Ω → I} {U : Ω → A} {p : StdSimplex NNReal I} {ρ : Measure A}
  {K : I → Measure B} {f : I → A → B}

/-- An independent categorical selector chooses the corresponding component pushforward of a
common noise law. No independence between the potential values `f i (U ω)` is required.

The conclusion is stated directly as a `HasLaw` theorem on the native carrier `B`. -/
theorem IndepFun.hasLaw_apply_finiteMixtureMeasure_map (hZU : IndepFun Z U P)
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P) (hU : HasLaw U ρ P)
    (hf : ∀ i, 0 < p.weights i → AEMeasurable (f i) ρ) :
    HasLaw (fun ω ↦ f (Z ω) (U ω))
      (TauCeti.Probability.finiteMixtureMeasure p (fun i ↦ ρ.map (f i))) P := by
  let _ : IsFiniteMeasure P := hZ.isFiniteMeasure
  let _ : IsFiniteMeasure ρ := hU.isFiniteMeasure_iff.mp inferInstance
  have h := hZU.hasLaw_apply_bind_map hZ hU
    (TauCeti.Probability.aemeasurable_uncurry_categoricalMeasure_prod p ρ hf)
  rw [← TauCeti.Probability.finiteMixtureMeasure_eq_bind] at h
  exact h

/-- An independent categorical selector chooses the corresponding component law when every
positive-weight component is realized as a measurable transformation of the common noise.
No condition is imposed on zero-weight components. -/
theorem IndepFun.hasLaw_apply_finiteMixtureMeasure (hZU : IndepFun Z U P)
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P) (hU : HasLaw U ρ P)
    (hf : ∀ i, 0 < p.weights i → AEMeasurable (f i) ρ)
    (hK : ∀ i, 0 < p.weights i → ρ.map (f i) = K i) :
    HasLaw (fun ω ↦ f (Z ω) (U ω)) (TauCeti.Probability.finiteMixtureMeasure p K) P := by
  have h := hZU.hasLaw_apply_finiteMixtureMeasure_map hZ hU hf
  rw [TauCeti.Probability.finiteMixtureMeasure_congr hK] at h
  exact h

/-- The selected value is almost-everywhere measurable when every component that the categorical
selector can choose has a law. -/
private theorem aemeasurable_eval_of_hasLaw {Y : I → Ω → B}
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P)
    (hY : ∀ i, 0 < p.weights i → HasLaw (Y i) (K i) P) :
    AEMeasurable (fun ω ↦ Y (Z ω) ω) P := by
  obtain ⟨i₀, hi₀⟩ := p.support_weights_nonempty
  have hi₀' : 0 < p.weights i₀ := pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi₀)
  let g : I → Ω → B := fun i ↦ if hi : 0 < p.weights i then
    (hY i hi).aemeasurable.mk (Y i) else (hY i₀ hi₀').aemeasurable.mk (Y i₀)
  have hg : Measurable (Function.uncurry g) :=
    measurable_from_prod_countable_right fun i ↦ by
      change Measurable (g i)
      dsimp only [g]
      split_ifs with hi
      · exact (hY i hi).aemeasurable.measurable_mk
      · exact (hY i₀ hi₀').aemeasurable.measurable_mk
  have hcat := Convexity.StdSimplex.ae_mem_image_support_map_categoricalMeasure p id
  rw [Measure.map_id] at hcat
  have hcat' : ∀ᵐ i ∂TauCeti.Probability.categoricalMeasure p, 0 < p.weights i := by
    filter_upwards [hcat] with i hi
    have hi' : i ∈ p.weights.support := by simpa using hi
    exact pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi')
  have hpos : ∀ᵐ ω ∂P, 0 < p.weights (Z ω) :=
    hZ.ae_iff Measurable.of_discrete |>.2 hcat'
  have hYg : ∀ᵐ ω ∂P, ∀ i, 0 < p.weights i → Y i ω = g i ω :=
    ae_all_iff.2 fun i ↦ by
      by_cases hi : 0 < p.weights i
      · filter_upwards [(hY i hi).aemeasurable.ae_eq_mk] with ω hω
        intro
        simpa only [g, dite_eq_left hi] using hω
      · exact ae_of_all _ fun _ hi' ↦ (hi hi').elim
  exact (hg.comp_aemeasurable (hZ.aemeasurable.prodMk aemeasurable_id)).congr <| by
    filter_upwards [hpos, hYg] with ω hω hω' using (hω' (Z ω) hω).symm

/-- Evaluating a finite family of potential random variables at a categorical selector gives the
finite mixture of their laws when the selector is independent of every positive-weight component.
Dependence between the potential variables themselves is allowed. -/
theorem IndepFun.hasLaw_eval_finiteMixtureMeasure {Y : I → Ω → B}
    (hZY : ∀ i, 0 < p.weights i → IndepFun Z (Y i) P)
    (hZ : HasLaw Z (TauCeti.Probability.categoricalMeasure p) P)
    (hY : ∀ i, 0 < p.weights i → HasLaw (Y i) (K i) P) :
    HasLaw (fun ω ↦ Y (Z ω) ω) (TauCeti.Probability.finiteMixtureMeasure p K) P := by
  let _ : IsFiniteMeasure P := hZ.isFiniteMeasure
  have hsel := aemeasurable_eval_of_hasLaw hZ hY
  refine ⟨hsel, ?_⟩
  ext s hs
  rw [Measure.map_apply_of_aemeasurable hsel hs,
    TauCeti.Probability.finiteMixtureMeasure_def, _root_.sum_apply]
  have hpre : (fun ω ↦ Y (Z ω) ω) ⁻¹' s =
      ⋃ i ∈ Finset.univ, Z ⁻¹' {i} ∩ Y i ⁻¹' s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_univ, exists_const,
      Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h ↦ ⟨Z ω, rfl, h⟩, fun ⟨_i, hi, h⟩ ↦ hi ▸ h⟩
  rw [hpre, measure_biUnion_finset₀]
  · simp only [smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hZi : P (Z ⁻¹' {i}) = p.weights i := by
      calc
        P (Z ⁻¹' {i}) = TauCeti.Probability.categoricalMeasure p {i} :=
          hZ.measure_eq (measurableSet_singleton i)
        _ = p.weights i := TauCeti.Probability.categoricalMeasure_singleton p i
    by_cases hi : 0 < p.weights i
    · have hYi : P (Y i ⁻¹' s) = K i s := (hY i hi).measure_eq hs
      rw [(hZY i hi).measure_inter_preimage_eq_mul {i} s (measurableSet_singleton i) hs,
        hZi, hYi]
    · have hi' : p.weights i = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hi)
      rw [measure_mono_null Set.inter_subset_left]
      · simp [hi']
      · rw [hZi, hi', ENNReal.coe_zero]
  · intro i _ j _ hij
    apply Disjoint.aedisjoint
    refine Set.disjoint_left.2 ?_
    intro ω (hωi : ω ∈ Z ⁻¹' {i} ∩ Y i ⁻¹' s)
      (hωj : ω ∈ Z ⁻¹' {j} ∩ Y j ⁻¹' s)
    exact hij (hωi.1.symm.trans hωj.1)
  · intro i _
    by_cases hi : 0 < p.weights i
    · exact (hZ.aemeasurable.nullMeasurableSet_preimage (measurableSet_singleton i)).inter
        ((hY i hi).aemeasurable.nullMeasurableSet_preimage hs)
    · apply NullMeasurableSet.of_null
      apply measure_mono_null Set.inter_subset_left
      calc
        P (Z ⁻¹' {i}) = TauCeti.Probability.categoricalMeasure p {i} :=
          hZ.measure_eq (measurableSet_singleton i)
        _ = p.weights i := TauCeti.Probability.categoricalMeasure_singleton p i
        _ = 0 := by rw [nonpos_iff_eq_zero.mp (not_lt.mp hi), ENNReal.coe_zero]

end ProbabilityTheory
