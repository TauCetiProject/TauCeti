/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.W1p.Translation
public import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.Analysis.Sobolev.Translation
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation

/-!
# Translation of arbitrary-order Sobolev functions

Translation on the whole space preserves every weak derivative. Thus translating an element of
`W^{k,p}` translates its value and each field in its iterated weak-gradient chain. The resulting
operator is a linear isometry. This is the whole-space symmetry needed to average translated
Sobolev functions against smooth kernels in the density argument.

The construction follows the weak-derivative graph defining `W^{k,p}`. The first stage uses
`TauCeti.Sobolev1JetLp.translateLp_mem_w1pSubmodule`; later stages use
`TauCeti.HasWeakFDerivOn.translateLp` to translate the preceding stage and its highest weak
derivative together. See Evans, *Partial Differential Equations*, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

/-- Translation of a first-order Sobolev function, obtained by translating its whole
value-gradient jet. -/
private def translateOne (h : E) (u : Wkp mu ⊤ p 1) : Wkp mu ⊤ p 1 :=
  ⟨(mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h u.1,
    Sobolev1JetLp.translateLp_mem_w1pSubmodule h u.2⟩

private theorem value_translateOne (h : E) (u : Wkp mu ⊤ p 1) :
    value 1 (translateOne h u) =
      (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (value 1 u) := by
  rw [value_one, value_one]
  apply Lp.ext
  let nu := mu.restrict ((⊤ : Opens E) : Set E)
  have hq : Filter.Tendsto (· + h) (ae nu) (ae nu) :=
    (measurePreserving_add_right nu h).quasiMeasurePreserving.tendsto_ae
  filter_upwards [W1p.value_apply_ae (translateOne h u),
    hq.eventually (W1p.value_apply_ae u), Measure.coeFn_translateLp (mu := nu) h u.1,
    Measure.coeFn_translateLp (mu := nu) h (W1p.value u)]
    with x hvT hvU hjet hval
  simpa only [Function.comp_apply] using
    hvT.trans ((congrArg WithLp.fst hjet).trans (hvU.symm.trans hval.symm))

private theorem iteratedGradient_translateOne (h : E) (u : Wkp mu ⊤ p 1) :
    iteratedGradient 0 (translateOne h u) =
      (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (iteratedGradient 0 u) := by
  rw [iteratedGradient_zero, iteratedGradient_zero]
  apply Lp.ext
  let nu := mu.restrict ((⊤ : Opens E) : Set E)
  have hq : Filter.Tendsto (· + h) (ae nu) (ae nu) :=
    (measurePreserving_add_right nu h).quasiMeasurePreserving.tendsto_ae
  filter_upwards [W1p.gradient_apply_ae (translateOne h u),
    hq.eventually (W1p.gradient_apply_ae u), Measure.coeFn_translateLp (mu := nu) h u.1,
    Measure.coeFn_translateLp (mu := nu) h (W1p.gradient u)]
    with x hgT hgU hjet hgrad
  simpa only [Function.comp_apply] using
    hgT.trans ((congrArg WithLp.snd hjet).trans (hgU.symm.trans hgrad.symm))

/-- A translated positive-order Sobolev function, with equations for its value and highest
weak derivative. These equations control the recursive construction. -/
private structure Translated (h : E) (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) where
  element : Wkp mu ⊤ p (k + 1)
  value_eq : value (k + 1) element =
    (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (value (k + 1) u)
  gradient_eq : iteratedGradient k element =
    (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (iteratedGradient k u)

private def translated (h : E) : (k : ℕ) → (u : Wkp mu ⊤ p (k + 1)) →
    Translated (mu := mu) (p := p) h k u
  | 0, u =>
      { element := translateOne h u
        value_eq := value_translateOne h u
        gradient_eq := iteratedGradient_translateOne h u }
  | k + 1, u =>
      let previous := translated h k (lowerOrder (k + 1) u)
      let hweak : HasWeakFDerivOn mu ⊤ (iteratedGradient k previous.element)
          ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h
            (iteratedGradient (k + 1) u)) := by
        rw [previous.gradient_eq]
        exact (hasWeakFDerivOn_iteratedGradient k u).translateLp h
      { element := mk k previous.element
          ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h
            (iteratedGradient (k + 1) u)) hweak
        value_eq := by
          calc
            value (k + 2) (mk k previous.element _ hweak) =
                value (k + 1) previous.element := by rw [value_succ, lowerOrder_mk]
            _ = (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h
                (value (k + 1) (lowerOrder (k + 1) u)) := previous.value_eq
            _ = (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h
                (value (k + 2) u) :=
                  congrArg _ (value_succ (k + 1) u).symm
        gradient_eq := by
          rw [iteratedGradient_mk] }

/-- Translation of a whole-space Sobolev function. At every order it translates the value
and all recorded weak derivatives by the same vector. -/
def translate (h : E) : (k : ℕ) → Wkp mu ⊤ p k → Wkp mu ⊤ p k
  | 0 => (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h
  | k + 1 => fun u => (translated h k u).element

/-- The value of a translated Sobolev function is the translated value. -/
@[simp]
theorem value_translate (h : E) : ∀ (k : ℕ) (u : Wkp mu ⊤ p k),
    value k (translate h k u) =
      (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (value k u)
  | 0, u => by simp only [translate, value_zero]
  | k + 1, u => (translated h k u).value_eq

/-- At order one, whole-space translation agrees with the existing local translation when
the source and target domains are both the whole space. -/
theorem translate_one_eq_W1p_translate (h : E) (u : Wkp mu ⊤ p 1) :
    translate h 1 u = W1p.translate (h := h) (fun _ _ => by simp) u := by
  let ht : MapsTo (· + h) (⊤ : Opens E) ⊤ := fun _ _ => by simp
  apply W1p.ext_value
  rw [← value_one (translate h 1 u), value_translate h 1 u, value_one u]
  apply Lp.ext
  exact (Measure.coeFn_translateLp (mu := mu.restrict ((⊤ : Opens E) : Set E)) h
    (W1p.value u)).trans (W1p.value_translate_ae ht u).symm

/-- The highest weak derivative of a translated Sobolev function is the translated highest
weak derivative. -/
@[simp]
theorem iteratedGradient_translate (h : E) (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) :
    iteratedGradient k (translate h (k + 1) u) =
      (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (iteratedGradient k u) :=
  (translated h k u).gradient_eq

/-- Translation commutes with forgetting the highest weak derivative. -/
@[simp]
theorem lowerOrder_translate (h : E) (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) :
    lowerOrder k (translate h (k + 1) u) = translate h k (lowerOrder k u) := by
  apply ext k
  calc
    value k (lowerOrder k (translate h (k + 1) u)) =
        value (k + 1) (translate h (k + 1) u) := (value_succ k _).symm
    _ = (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h (value (k + 1) u) :=
      value_translate h (k + 1) u
    _ = (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h
        (value k (lowerOrder k u)) := congrArg _ (value_succ k u)
    _ = value k (translate h k (lowerOrder k u)) :=
      (value_translate h k (lowerOrder k u)).symm

/-- Translation by zero fixes every whole-space Sobolev function. -/
@[simp]
theorem translate_zero (k : ℕ) (u : Wkp mu ⊤ p k) : translate (0 : E) k u = u := by
  apply ext k
  rw [value_translate, Measure.translateLp_zero]

/-- Two successive Sobolev translations compose by addition of their vectors. -/
theorem translate_add (h₁ h₂ : E) (k : ℕ) (u : Wkp mu ⊤ p k) :
    translate (h₁ + h₂) k u = translate h₂ k (translate h₁ k u) := by
  apply ext k
  calc
    value k (translate (h₁ + h₂) k u) =
        (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p (h₁ + h₂) (value k u) :=
      value_translate (h₁ + h₂) k u
    _ = (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h₂
        ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h₁ (value k u)) := by
      rw [Measure.translateLp_add, LinearIsometryEquiv.trans_apply]
    _ = value k (translate h₂ k (translate h₁ k u)) := by
      rw [value_translate, value_translate]

/-- Translation preserves the iterated graph norm at every Sobolev order. -/
@[simp]
theorem norm_translate (h : E) : ∀ (k : ℕ) (u : Wkp mu ⊤ p k),
    ‖translate h k u‖ = ‖u‖
  | 0, u => by
      exact (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h |>.norm_map u
  | 1, u => by
      exact (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h |>.norm_map u.1
  | k + 2, u => by
      have hgraph (v : Wkp mu ⊤ p (k + 2)) :
          ‖v‖ ^ 2 = ‖lowerOrder (k + 1) v‖ ^ 2 +
            ‖iteratedGradient (k + 1) v‖ ^ 2 := by
        simpa only [lowerOrder_succ, iteratedGradient_succ] using
          WeakDerivStep.norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq
            (sobolevStage (mu := mu) (Omega := ⊤) (p := p) k).iteratedGradientL v
      have hv := hgraph (translate h (k + 2) u)
      have hu := hgraph u
      rw [lowerOrder_translate, iteratedGradient_translate,
        norm_translate h (k + 1) (lowerOrder (k + 1) u),
        LinearIsometryEquiv.norm_map] at hv
      nlinarith [norm_nonneg (translate h (k + 2) u), norm_nonneg u]

/-- Whole-space translation is a linear isometry on `W^{k,p}`. It acts on the value and every
weak derivative by the corresponding `Lᵖ` translation. -/
def translateLI (h : E) (k : ℕ) : Wkp mu ⊤ p k →ₗᵢ[ℝ] Wkp mu ⊤ p k where
  toFun := translate h k
  map_add' := by
    intro u v
    apply ext k
    have hadd (x y : Wkp mu ⊤ p k) : value k (x + y) = value k x + value k y := by
      simpa only [← valueL_apply] using (valueL k).map_add x y
    rw [value_translate, hadd u v, map_add,
      hadd (translate h k u) (translate h k v),
      value_translate h k u, value_translate h k v]
  map_smul' := by
    intro c u
    apply ext k
    have hsmul (x : Wkp mu ⊤ p k) : value k (c • x) = c • value k x := by
      simpa only [← valueL_apply] using (valueL k).map_smul c x
    rw [value_translate, hsmul u, map_smul, RingHom.id_apply,
      hsmul (translate h k u), value_translate h k u]
  norm_map' := norm_translate h k

@[simp]
theorem translateLI_apply (h : E) (k : ℕ) (u : Wkp mu ⊤ p k) :
    translateLI h k u = translate h k u := (rfl)

end TauCeti.Wkp

end

end
