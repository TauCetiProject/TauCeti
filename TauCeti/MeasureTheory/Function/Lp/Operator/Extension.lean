/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Extending an operator from `L² ∩ Lᵖ` to `Lᵖ`

An operator initially defined on `L²` often admits an `Lᵖ` estimate on functions in both spaces.
For `1 < p < ∞`, the intersection is dense in `Lᵖ`: finite-measure simple functions lie in
both spaces. A uniform estimate therefore gives a unique bounded operator on all of `Lᵖ`.
This is the final density step in the Calderón–Zygmund strong-type theorem.

The construction uses Mathlib's `Lp.simpleFunc.dense` and `LinearMap.extendOfNorm`.

## Bounds from simple functions

An `Lᵖ → L^q` bound for a bounded operator `T : Lʳ → Lˢ`, `r < ∞`, `1 ≤ p < ∞`, needs only to be
checked on simple functions in `Lʳ`: it then holds for every `f ∈ Lʳ ∩ Lᵖ`
(`ContinuousLinearMap.eLpNorm_apply_le_of_forall_simpleFunc`). The simple approximants of `f`
converge to `f` in `Lʳ` and `Lᵖ` at once, and Fatou's lemma bounds `‖T f‖_q`. The operator norm
bound itself reads `‖T f‖_s ≤ M ‖f‖_r` in `eLpNorm` form
(`ContinuousLinearMap.eLpNorm_apply_le_of_norm_le`).
-/

public section

noncomputable section

namespace MeasureTheory

open scoped ENNReal NNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Finite-measure simple functions are in `L²` at every finite exponent `p ≥ 1`. -/
theorem Lp.simpleFunc.memLp_two [Fact (1 ≤ p)] (hp : p ≠ ∞) (f : Lp.simpleFunc E p μ) :
    MemLp (f : α → E) 2 μ := by
  refine Lp.simpleFunc.induction (by exact (zero_lt_one.trans_le Fact.out).ne') hp ?_ ?_ f
  · intro c s hs hμ
    have h : MemLp (s.indicator fun _ : α => c) 2 μ :=
      memLp_indicator_const 2 hs.nullMeasurableSet c (.inr hμ.ne)
    exact h.ae_eq (by simpa only [Lp.simpleFunc.coe_indicatorConst] using
      (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμ.ne) (c := c)).symm)
  · intro f g hf hg _ hmf hmg
    exact (hmf.add hmg).ae_eq (Lp.coeFn_add (f.toLp hf : Lp E p μ) (g.toLp hg)).symm

variable [NormedSpace ℝ E]

/-- The `Lᵖ` functions which also belong to `L²`. -/
def lpTwoSubmodule : Submodule ℝ (Lp E p μ) where
  carrier := {f | MemLp (f : α → E) 2 μ}
  zero_mem' := by
    -- Unfold submodule membership to the `MemLp` condition on the zero `Lp` class.
    change MemLp ((0 : Lp E p μ) : α → E) 2 μ
    exact (MemLp.zero : MemLp (0 : α → E) 2 μ).ae_eq
      (Lp.coeFn_zero E p μ).symm
  add_mem' := by
    intro f g hf hg
    exact (hf.add hg).ae_eq (Lp.coeFn_add f g).symm
  smul_mem' := by
    intro c f hf
    exact (hf.const_smul c).ae_eq (Lp.coeFn_smul c f).symm

/-- Membership in `Lᵖ ∩ L²` means that the `Lᵖ` representative also has finite `L²` norm. -/
theorem mem_lpTwoSubmodule (f : Lp E p μ) :
    f ∈ lpTwoSubmodule (E := E) (p := p) (μ := μ) ↔ MemLp (f : α → E) 2 μ :=
  Iff.rfl

/-- The `L²` membership proof carried by an element of `Lᵖ ∩ L²`. -/
theorem lpTwoSubmodule.memLp (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    MemLp (f.1 : α → E) 2 μ := f.property

/-- An `Lᵖ ∩ L²` function, read as an element of `L²`. -/
def lpTwoSubmodule.toL2 : lpTwoSubmodule (E := E) (p := p) (μ := μ) →ₗ[ℝ] Lp E 2 μ where
  toFun f := (lpTwoSubmodule.memLp f).toLp (f.1 : α → E)
  map_add' := by
    intro f g
    apply Lp.ext
    have hfg := lpTwoSubmodule.memLp (f + g)
    have hf := lpTwoSubmodule.memLp f
    have hg := lpTwoSubmodule.memLp g
    filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_add (f.1 : Lp E p μ) g.1,
      Lp.coeFn_add (hf.toLp (f.1 : α → E)) (hg.toLp (g.1 : α → E))]
      with x h₁ h₂ h₃ h₄ h₅
    calc
      _ = (f.1 : α → E) x + (g.1 : α → E) x := h₁.trans h₄
      _ = (hf.toLp (f.1 : α → E) : α → E) x +
          (hg.toLp (g.1 : α → E) : α → E) x := by rw [h₂, h₃]
      _ = _ := h₅.symm
  map_smul' := by
    intro c f
    apply Lp.ext
    have hcf := lpTwoSubmodule.memLp (c • f)
    have hf := lpTwoSubmodule.memLp f
    filter_upwards [hcf.coeFn_toLp, hf.coeFn_toLp,
      Lp.coeFn_smul c (f.1 : Lp E p μ),
      Lp.coeFn_smul c (hf.toLp (f.1 : α → E))] with x h₁ h₂ h₃ h₄
    calc
      _ = ((c • f).1 : α → E) x := h₁
      _ = c • (f.1 : α → E) x := h₃
      _ = c • (hf.toLp (f.1 : α → E) : α → E) x := by rw [h₂]
      _ = _ := h₄.symm

/-- The `L²` and `Lᵖ` views of an intersection function agree almost everywhere. -/
theorem lpTwoSubmodule.toL2_ae (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    (lpTwoSubmodule.toL2 f : α → E) =ᵐ[μ] (f.1 : α → E) := by
  have hf := lpTwoSubmodule.memLp f
  exact hf.coeFn_toLp

variable [Fact (1 ≤ p)]

/-- The intersection `Lᵖ ∩ L²` is dense in `Lᵖ` when `p < ∞`. -/
theorem dense_lpTwoSubmodule (hp : p ≠ ∞) :
    Dense (lpTwoSubmodule (E := E) (p := p) (μ := μ) : Set (Lp E p μ)) := by
  apply (Lp.simpleFunc.dense (E := E) (p := p) (μ := μ) hp).mono
  intro f hf
  exact Lp.simpleFunc.memLp_two hp ⟨f, hf⟩

end MeasureTheory

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal NNReal

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞}

/-- A strong-type estimate on `L²` makes the operator's value an `Lᵖ` function whenever its
argument lies in `L² ∩ Lᵖ`. -/
theorem memLp_apply_of_eLpNorm_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ)
    (f : Lp E 2 μ) (hf : MemLp f p μ) : MemLp (T f) p μ := by
  exact (hT f hf).trans_lt (ENNReal.mul_lt_top (by finiteness) hf)

/-- The strong-type operator on the dense intersection, with values read in `Lᵖ`. -/
def strongTypeOnIntersection (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) :
    lpTwoSubmodule (E := E) (p := p) (μ := μ) →ₗ[ℝ] Lp F p μ where
  toFun f := (memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f)
    (by
      have hf := lpTwoSubmodule.memLp f
      exact (Lp.memLp f.1).ae_eq hf.coeFn_toLp.symm)).toLp (T (lpTwoSubmodule.toL2 f))
  map_add' := by
    intro f g
    apply Lp.ext
    let hfg := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 (f + g))
      (by
        have h := lpTwoSubmodule.memLp (f + g)
        exact (Lp.memLp (f + g).1).ae_eq h.coeFn_toLp.symm)
    let hf := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f)
      (by
        have h := lpTwoSubmodule.memLp f
        exact (Lp.memLp f.1).ae_eq h.coeFn_toLp.symm)
    let hg := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 g)
      (by
        have h := lpTwoSubmodule.memLp g
        exact (Lp.memLp g.1).ae_eq h.coeFn_toLp.symm)
    filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_add (T (lpTwoSubmodule.toL2 f)) (T (lpTwoSubmodule.toL2 g)),
      Lp.coeFn_add (hf.toLp _) (hg.toLp _)] with x h₁ h₂ h₃ h₄ h₅
    calc
      _ = (T (lpTwoSubmodule.toL2 (f + g)) : α → F) x := h₁
      _ = ((T (lpTwoSubmodule.toL2 f) + T (lpTwoSubmodule.toL2 g) : Lp F 2 μ) : α → F) x :=
        by rw [map_add, map_add]
      _ = (T (lpTwoSubmodule.toL2 f) : α → F) x +
          (T (lpTwoSubmodule.toL2 g) : α → F) x := h₄
      _ = (hf.toLp _ : α → F) x + (hg.toLp _ : α → F) x := by rw [h₂, h₃]
      _ = _ := h₅.symm
  map_smul' := by
    intro c f
    apply Lp.ext
    let hcf := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 (c • f))
      (by
        have h := lpTwoSubmodule.memLp (c • f)
        exact (Lp.memLp (c • f).1).ae_eq h.coeFn_toLp.symm)
    let hf := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f)
      (by
        have h := lpTwoSubmodule.memLp f
        exact (Lp.memLp f.1).ae_eq h.coeFn_toLp.symm)
    filter_upwards [hcf.coeFn_toLp, hf.coeFn_toLp,
      Lp.coeFn_smul c (T (lpTwoSubmodule.toL2 f)), Lp.coeFn_smul c (hf.toLp _)]
      with x h₁ h₂ h₃ h₄
    calc
      _ = (T (lpTwoSubmodule.toL2 (c • f)) : α → F) x := h₁
      _ = (c • T (lpTwoSubmodule.toL2 f) : Lp F 2 μ) x := by rw [map_smul, map_smul]
      _ = c • (T (lpTwoSubmodule.toL2 f) : α → F) x := h₃
      _ = c • (hf.toLp _ : α → F) x := by rw [h₂]
      _ = _ := h₄.symm

/-- On the intersection, the strong-type map has the same pointwise values almost everywhere
as the given `L²` operator. -/
theorem strongTypeOnIntersection_ae (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ)
    (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    (strongTypeOnIntersection T C hT f : α → F) =ᵐ[μ] T (lpTwoSubmodule.toL2 f) := by
  have hf : MemLp (lpTwoSubmodule.toL2 f : α → E) p μ :=
    (Lp.memLp f.1).ae_eq (lpTwoSubmodule.toL2_ae f).symm
  exact (memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f) hf).coeFn_toLp

variable [Fact (1 ≤ p)]

/-- The `Lᵖ` bound on `L² ∩ Lᵖ`, expressed in ordinary operator norms. -/
theorem norm_strongTypeOnIntersection_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ)
    (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    ‖strongTypeOnIntersection T C hT f‖ ≤ C * ‖f‖ := by
  have hf := lpTwoSubmodule.memLp f
  have hfp : MemLp (lpTwoSubmodule.toL2 f : α → E) p μ :=
    (Lp.memLp f.1).ae_eq hf.coeFn_toLp.symm
  have hTp := memLp_apply_of_eLpNorm_le T C hT (lpTwoSubmodule.toL2 f) hfp
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfp.ne)
    (hT (lpTwoSubmodule.toL2 f) hfp)
  have heq : eLpNorm (lpTwoSubmodule.toL2 f : α → E) p μ = eLpNorm (f.1 : α → E) p μ :=
    eLpNorm_congr_ae hf.coeFn_toLp
  -- The bundled map applies by turning its `L²` value into the corresponding `Lᵖ` class.
  change ‖hTp.toLp (T (lpTwoSubmodule.toL2 f))‖ ≤ (C : ℝ) * ‖(f : Lp E p μ)‖
  rw [Lp.norm_toLp, Lp.norm_def]
  simpa [heq, ENNReal.toReal_mul] using h

variable [CompleteSpace F]

/-- The unique continuous `Lᵖ` extension of an `L²` operator satisfying a strong-type
estimate. It agrees with the original operator on `L² ∩ Lᵖ`. -/
def strongTypeExtension (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (_hp : p ≠ ∞) :
    Lp E p μ →L[ℝ] Lp F p μ :=
  (strongTypeOnIntersection T C hT).extendOfNorm (lpTwoSubmodule (E := E) (p := p) (μ := μ)).subtype

/-- On the dense intersection the extension equals the original `L²` operator, interpreted in
`Lᵖ`. -/
theorem strongTypeExtension_apply (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞)
    (f : lpTwoSubmodule (E := E) (p := p) (μ := μ)) :
    strongTypeExtension T C hT hp f.1 = strongTypeOnIntersection T C hT f := by
  apply LinearMap.extendOfNorm_eq
  · exact (denseRange_subtype_val).2 (dense_lpTwoSubmodule (E := E) (p := p) (μ := μ) hp)
  · exact ⟨C, norm_strongTypeOnIntersection_le T C hT⟩

/-- The operator norm of the extended map is bounded by the strong-type constant. -/
theorem norm_strongTypeExtension_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞) :
    ‖strongTypeExtension T C hT hp‖ ≤ C := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact (denseRange_subtype_val).2 (dense_lpTwoSubmodule (E := E) (p := p) (μ := μ) hp)
  · exact C.property
  · exact norm_strongTypeOnIntersection_le T C hT

/-- The `Lᵖ` extension agrees almost everywhere with the original `L²` operator on every
function in `L² ∩ Lᵖ`. -/
theorem strongTypeExtension_apply_of_memLp (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞)
    (f : Lp E 2 μ) (hf : MemLp f p μ) :
    (strongTypeExtension T C hT hp (hf.toLp f) : α → F) =ᵐ[μ] T f := by
  have h2 : MemLp (hf.toLp f : α → E) 2 μ :=
    (Lp.memLp f).ae_eq hf.coeFn_toLp.symm
  let g : lpTwoSubmodule (E := E) (p := p) (μ := μ) := ⟨hf.toLp f, h2⟩
  have hg : lpTwoSubmodule.toL2 g = f :=
    Lp.ext (h2.coeFn_toLp.trans hf.coeFn_toLp)
  rw [strongTypeExtension_apply T C hT hp ⟨hf.toLp f, h2⟩]
  simpa only [hg] using strongTypeOnIntersection_ae T C hT g

/-- A bounded operator on `Lᵖ` agreeing with the strong-type estimate on the dense intersection
is the extension constructed above. -/
theorem strongTypeExtension_unique (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞)
    (S : Lp E p μ →L[ℝ] Lp F p μ)
    (hS : ∀ f : lpTwoSubmodule (E := E) (p := p) (μ := μ),
      S f.1 = strongTypeOnIntersection T C hT f) :
    S = strongTypeExtension T C hT hp := by
  symm
  apply LinearMap.extendOfNorm_unique
    ((denseRange_subtype_val).2 (dense_lpTwoSubmodule (E := E) (p := p) (μ := μ) hp))
    C (norm_strongTypeOnIntersection_le T C hT)
  apply LinearMap.ext
  intro f
  exact hS f

/-- Agreement almost everywhere on every `L² ∩ Lᵖ` function characterizes the `Lᵖ` extension. -/
theorem strongTypeExtension_unique_of_ae (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (C : ℝ≥0)
    (hT : ∀ f : Lp E 2 μ, MemLp f p μ →
      eLpNorm (T f) p μ ≤ C * eLpNorm f p μ) (hp : p ≠ ∞)
    (S : Lp E p μ →L[ℝ] Lp F p μ)
    (hS : ∀ (f : Lp E 2 μ) (hf : MemLp f p μ),
      (S (hf.toLp f) : α → F) =ᵐ[μ] T f) :
    S = strongTypeExtension T C hT hp := by
  apply strongTypeExtension_unique T C hT hp S
  intro g
  have h₂ := lpTwoSubmodule.memLp g
  have hp' : MemLp (lpTwoSubmodule.toL2 g : α → E) p μ :=
    (Lp.memLp g.1).ae_eq h₂.coeFn_toLp.symm
  have heq : hp'.toLp (lpTwoSubmodule.toL2 g : α → E) = g.1 :=
    Lp.ext (hp'.coeFn_toLp.trans h₂.coeFn_toLp)
  have hSg := hS (lpTwoSubmodule.toL2 g) hp'
  rw [heq] at hSg
  have hEg := strongTypeExtension_apply_of_memLp T C hT hp (lpTwoSubmodule.toL2 g) hp'
  rw [heq, strongTypeExtension_apply T C hT hp g] at hEg
  exact Lp.ext (hSg.trans hEg.symm)

end ContinuousLinearMap

/-! ### Bounds from simple functions -/

namespace ContinuousLinearMap

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {α β 𝕜 E F : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {ν : Measure β} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p q r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]

/-- An operator norm bound `‖T‖ ≤ M` for `T : Lʳ → Lˢ` is the bound `‖T f‖_s ≤ M ‖f‖_r` in
`eLpNorm` form. -/
theorem eLpNorm_apply_le_of_norm_le (T : Lp E r μ →L[𝕜] Lp F s ν) {M : ℝ≥0} (hT : ‖T‖ ≤ M)
    (f : Lp E r μ) : eLpNorm (T f) s ν ≤ M * eLpNorm f r μ := by
  rw [← Lp.enorm_def, ← Lp.enorm_def]
  refine T.le_of_opENorm_le ?_ f
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hT

/-- A bound for `T : Lʳ → Lˢ`, `r < ∞`, from `Lᵖ` to `L^q`, `1 ≤ p < ∞`, on simple functions in
`Lʳ` passes to every `f ∈ Lʳ ∩ Lᵖ`, for any finite constant `C`. -/
theorem eLpNorm_apply_le_of_forall_simpleFunc [MeasurableSpace E] [BorelSpace E] (hr : r ≠ ∞)
    (T : Lp E r μ →L[𝕜] Lp F s ν) (hp1 : 1 ≤ p) (hp : p ≠ ∞) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ (g : SimpleFunc α E) (hg : MemLp g r μ), eLpNorm (T (hg.toLp g)) q ν ≤
      C * eLpNorm g p μ)
    (f : Lp E r μ) (hf : MemLp f p μ) : eLpNorm (T f) q ν ≤ C * eLpNorm f p μ := by
  have hfm := Lp.aestronglyMeasurable f
  set φ := hfm.mk f
  have hφ : Measurable φ := hfm.stronglyMeasurable_mk.measurable
  have := hfm.stronglyMeasurable_mk.separableSpace_range_union_singleton (b := 0)
  have hfφ : (f : α → E) =ᵐ[μ] φ := hfm.ae_eq_mk
  have hφr : MemLp φ r μ := (Lp.memLp f).ae_eq hfφ
  have hφp : MemLp φ p μ := hf.ae_eq hfφ
  set g : ℕ → SimpleFunc α E := fun n ↦ SimpleFunc.approxOn φ hφ (Set.range φ ∪ {0}) 0
    (by simp) n
  have hgr : ∀ n, MemLp (g n) r μ := SimpleFunc.memLp_approxOn_range hφ hφr
  -- The approximants converge to `f` in `Lʳ`, so their images converge to `T f` in `Lˢ`.
  have hφf : hφr.toLp φ = f := by
    rw [← Lp.toLp_coeFn f (Lp.memLp f), MemLp.toLp_eq_toLp_iff]
    exact hfφ.symm
  have hT : Tendsto (fun n ↦ T ((hgr n).toLp (g n))) atTop (𝓝 (T f)) := by
    have := SimpleFunc.tendsto_approxOn_range_Lp hr hφ hφr
    rw [hφf] at this
    exact (T.continuous.tendsto f).comp this
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hT).exists_seq_tendsto_ae
  -- The approximants also converge to `f` in `Lᵖ`.
  have hgp : Tendsto (fun k ↦ C * (eLpNorm f p μ + eLpNorm (⇑(g (ns k)) - φ) p μ)) atTop
      (𝓝 (C * (eLpNorm f p μ + 0))) :=
    ENNReal.Tendsto.const_mul (tendsto_const_nhds.add
      ((SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm hp hφ hφp.eLpNorm_lt_top).comp
        hns.tendsto_atTop)) (Or.inr hC)
  calc eLpNorm (T f) q ν
      ≤ atTop.liminf fun k ↦ eLpNorm (T ((hgr (ns k)).toLp (g (ns k)))) q ν :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun _ ↦ Lp.aestronglyMeasurable _) _
          (Lp.aestronglyMeasurable _) hae
    _ ≤ atTop.liminf fun k ↦ C * (eLpNorm f p μ + eLpNorm (⇑(g (ns k)) - φ) p μ) := by
        refine liminf_le_liminf (Eventually.of_forall fun k ↦ (h _ _).trans ?_)
        gcongr
        calc eLpNorm (g (ns k)) p μ = eLpNorm (φ + (⇑(g (ns k)) - φ)) p μ := by
              rw [add_sub_cancel]
          _ ≤ eLpNorm φ p μ + eLpNorm (⇑(g (ns k)) - φ) p μ :=
              eLpNorm_add_le hp1
          _ = eLpNorm f p μ + eLpNorm (⇑(g (ns k)) - φ) p μ := by rw [eLpNorm_congr_ae hfφ]
    _ = C * eLpNorm f p μ := by rw [hgp.liminf_eq, add_zero]

end ContinuousLinearMap
