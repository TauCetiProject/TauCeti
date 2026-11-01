/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation

/-!
# `L∞` along absolutely continuous measures

Let `ν ≪ μ`. A function essentially bounded for `μ` is essentially bounded for `ν`, with no
larger essential supremum, and functions equal `μ`-almost everywhere are equal `ν`-almost
everywhere. Taking `ν`-classes of `μ`-classes is therefore a well-defined linear map
`MeasureTheory.Lp.linftyOfAbsolutelyContinuous 𝕜 h : Lp E ∞ μ →L[𝕜] Lp E ∞ ν` of norm at most
one. At the exponent `∞` this extends Mathlib's `MeasureTheory.Lp.LpToLpOfMeasureLeSMul`, which
needs `ν ≤ c • μ` for a finite constant `c`, to every absolutely continuous `ν`: `L∞` only sees
a measure through its null sets.

When `μ` and `ν` have the same null sets the maps in both directions are inverse to each other,
giving the linear isometry equivalence `MeasureTheory.Lp.linftyCongr`. This applies to `μ` and
`c • μ` for every `c ≠ 0`, and to any two regular left Haar measures on a locally compact group.

For real-valued functions the map is monotone and sends the constant class one to the constant
class one. It sends the class of a bounded continuous function to the class of the same function,
and on a group it commutes with left translation when both measures are left invariant. These are
the properties needed to move invariant means on `L∞` from one measure to another.

## Main definitions

* `MeasureTheory.Lp.linftyOfAbsolutelyContinuous 𝕜 h`: for `h : ν ≪ μ`, the map
  `Lp E ∞ μ →L[𝕜] Lp E ∞ ν` sending a `μ`-class to the `ν`-class of the same function.
* `MeasureTheory.Lp.linftyCongr 𝕜 hμν hνμ`: for measures with the same null sets, the resulting
  linear isometry equivalence `Lp E ∞ μ ≃ₗᵢ[𝕜] Lp E ∞ ν`.

## Main results

* `MeasureTheory.Lp.coeFn_linftyOfAbsolutelyContinuous`: the new class is `ν`-almost everywhere
  the old representative.
* `MeasureTheory.Lp.norm_linftyOfAbsolutelyContinuous_le`: the map does not increase norms, and
  `MeasureTheory.Lp.norm_linftyOfAbsolutelyContinuous` preserves them when `μ ≪ ν` as well.
* `MeasureTheory.Lp.linftyOfAbsolutelyContinuous_linftyOfAbsolutelyContinuous`: the maps compose
  along `ρ ≪ ν ≪ μ`.
* `MeasureTheory.Lp.leftTranslation_linftyOfAbsolutelyContinuous`: the map commutes with left
  translation.
-/

public section

noncomputable section

open Filter
open scoped ENNReal BoundedContinuousFunction

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ ν ρ : Measure α}

/-- The essential supremum norm does not increase when passing to an absolutely continuous
measure. -/
theorem eLpNorm_top_mono_ac (f : α → E) (h : ν ≪ μ) : eLpNorm f ∞ ν ≤ eLpNorm f ∞ μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [eLpNorm_exponent_top hf, eLpNorm_exponent_top (hf.mono_ac h)]
    exact eLpNormEssSup_mono_measure f h
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]

/-- An essentially bounded function for `μ` is essentially bounded for every `ν ≪ μ`. -/
theorem MemLp.mono_ac_top {f : α → E} (hf : MemLp f ∞ μ) (h : ν ≪ μ) : MemLp f ∞ ν :=
  memLp_iff.2 <| (eLpNorm_top_mono_ac f h).trans_lt (memLp_iff.1 hf)

namespace Lp

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- For `ν ≪ μ`, the map `Lp E ∞ μ →L[𝕜] Lp E ∞ ν` sending the `μ`-class of an essentially
bounded function to its `ν`-class. -/
def linftyOfAbsolutelyContinuous (h : ν ≪ μ) : Lp E ∞ μ →L[𝕜] Lp E ∞ ν :=
  LinearMap.mkContinuous
    { toFun f := ((Lp.memLp f).mono_ac_top h).toLp f
      map_add' f g := by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (h.ae_eq (Lp.coeFn_add f g))
      map_smul' c f := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (h.ae_eq (Lp.coeFn_smul c f)) }
    1 fun f => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_top_mono_ac _ h)

variable {𝕜}

/-- The `ν`-class obtained from a `μ`-class is `ν`-almost everywhere its representative. -/
theorem coeFn_linftyOfAbsolutelyContinuous (h : ν ≪ μ) (f : Lp E ∞ μ) :
    linftyOfAbsolutelyContinuous 𝕜 h f =ᵐ[ν] f := by
  rw [linftyOfAbsolutelyContinuous, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

/-- The class of an essentially bounded function for `μ` goes to its class for `ν`. -/
@[simp]
theorem linftyOfAbsolutelyContinuous_toLp (h : ν ≪ μ) {f : α → E} (hf : MemLp f ∞ μ) :
    linftyOfAbsolutelyContinuous 𝕜 h (hf.toLp f) = (hf.mono_ac_top h).toLp f :=
  Lp.ext <| (coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) h _).trans <|
    (h.ae_eq (MemLp.coeFn_toLp hf)).trans (MemLp.coeFn_toLp _).symm

/-- Passing to the class for an absolutely continuous measure does not increase the norm. -/
theorem norm_linftyOfAbsolutelyContinuous_le (h : ν ≪ μ) (f : Lp E ∞ μ) :
    ‖linftyOfAbsolutelyContinuous 𝕜 h f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) h f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_top_mono_ac _ h)

/-- For `ν = μ`, the map is the identity. -/
@[simp]
theorem linftyOfAbsolutelyContinuous_self (h : μ ≪ μ) (f : Lp E ∞ μ) :
    linftyOfAbsolutelyContinuous 𝕜 h f = f :=
  Lp.ext (coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) h f)

/-- The maps compose along `ρ ≪ ν ≪ μ`. -/
@[simp]
theorem linftyOfAbsolutelyContinuous_linftyOfAbsolutelyContinuous (hνμ : ν ≪ μ) (hρν : ρ ≪ ν)
    (f : Lp E ∞ μ) :
    linftyOfAbsolutelyContinuous 𝕜 hρν (linftyOfAbsolutelyContinuous 𝕜 hνμ f) =
      linftyOfAbsolutelyContinuous 𝕜 (hρν.trans hνμ) f :=
  Lp.ext <| (coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) hρν _).trans <|
    (hρν.ae_eq (coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) hνμ f)).trans
      (coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) _ f).symm

/-- For measures `μ` and `ν` with the same null sets, passing from `μ`-classes to `ν`-classes
preserves the norm. -/
theorem norm_linftyOfAbsolutelyContinuous (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E ∞ μ) :
    ‖linftyOfAbsolutelyContinuous 𝕜 hνμ f‖ = ‖f‖ :=
  le_antisymm (norm_linftyOfAbsolutelyContinuous_le hνμ f) <| by
    simpa only [linftyOfAbsolutelyContinuous_linftyOfAbsolutelyContinuous,
      linftyOfAbsolutelyContinuous_self] using
      norm_linftyOfAbsolutelyContinuous_le (𝕜 := 𝕜) hμν (linftyOfAbsolutelyContinuous 𝕜 hνμ f)

variable (𝕜) in
/-- For measures `μ` and `ν` with the same null sets, `Lp E ∞ μ` and `Lp E ∞ ν` are identified
by sending the class of a function for one measure to its class for the other. -/
def linftyCongr (hμν : μ ≪ ν) (hνμ : ν ≪ μ) : Lp E ∞ μ ≃ₗᵢ[𝕜] Lp E ∞ ν where
  toFun := linftyOfAbsolutelyContinuous 𝕜 hνμ
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := linftyOfAbsolutelyContinuous 𝕜 hμν
  left_inv f := by
    rw [linftyOfAbsolutelyContinuous_linftyOfAbsolutelyContinuous,
      linftyOfAbsolutelyContinuous_self]
  right_inv f := by
    rw [linftyOfAbsolutelyContinuous_linftyOfAbsolutelyContinuous,
      linftyOfAbsolutelyContinuous_self]
  norm_map' := norm_linftyOfAbsolutelyContinuous hμν hνμ

/-- The identification sends a `μ`-class to the `ν`-class of the same function. -/
@[simp]
theorem linftyCongr_apply (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E ∞ μ) :
    linftyCongr 𝕜 hμν hνμ f = linftyOfAbsolutelyContinuous 𝕜 hνμ f :=
  (rfl)

/-- The inverse identification sends a `ν`-class to the `μ`-class of the same function. -/
@[simp]
theorem linftyCongr_symm (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (linftyCongr 𝕜 hμν hνμ).symm = linftyCongr (E := E) 𝕜 hνμ hμν :=
  (rfl)

/-! ### Real-valued functions -/

/-- Passing to the class for an absolutely continuous measure is monotone on real `L∞`. -/
theorem linftyOfAbsolutelyContinuous_mono (h : ν ≪ μ) {f g : Lp ℝ ∞ μ} (hfg : f ≤ g) :
    linftyOfAbsolutelyContinuous ℝ h f ≤ linftyOfAbsolutelyContinuous ℝ h g := by
  rw [← Lp.coeFn_le] at hfg ⊢
  filter_upwards [coeFn_linftyOfAbsolutelyContinuous (𝕜 := ℝ) h f,
    coeFn_linftyOfAbsolutelyContinuous (𝕜 := ℝ) h g, h.ae_le hfg] with x hf hg hle
  exact hf ▸ hg ▸ hle

/-- The constant class one goes to the constant class one. -/
@[simp]
theorem linftyOfAbsolutelyContinuous_linftyOne (h : ν ≪ μ) :
    linftyOfAbsolutelyContinuous ℝ h TauCeti.linftyOne = TauCeti.linftyOne :=
  Lp.ext <| (coeFn_linftyOfAbsolutelyContinuous (𝕜 := ℝ) h _).trans <|
    (h.ae_eq TauCeti.coeFn_linftyOne).trans TauCeti.coeFn_linftyOne.symm

/-- The class of a bounded continuous function for `μ` goes to its class for `ν`. -/
@[simp]
theorem linftyOfAbsolutelyContinuous_toLpTop [TopologicalSpace α] [BorelSpace α]
    [SecondCountableTopologyEither α E] (h : ν ≪ μ) (f : α →ᵇ E) :
    linftyOfAbsolutelyContinuous 𝕜 h (BoundedContinuousFunction.toLpTop μ 𝕜 f) =
      BoundedContinuousFunction.toLpTop ν 𝕜 f :=
  Lp.ext <| (coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) h _).trans <|
    (h.ae_eq (BoundedContinuousFunction.coeFn_toLpTop μ f)).trans
      (BoundedContinuousFunction.coeFn_toLpTop ν f).symm

/-! ### Left translation -/

/-- For left-invariant measures `ν ≪ μ` on a group, passing from `μ`-classes to `ν`-classes
commutes with left translation. -/
theorem leftTranslation_linftyOfAbsolutelyContinuous {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {μ ν : Measure G} [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (h : ν ≪ μ) (g : G) (f : Lp E ∞ μ) :
    leftTranslation ν ∞ 𝕜 g (linftyOfAbsolutelyContinuous 𝕜 h f) =
      linftyOfAbsolutelyContinuous 𝕜 h (leftTranslation μ ∞ 𝕜 g f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_leftTranslation (𝕜 := 𝕜) g (linftyOfAbsolutelyContinuous 𝕜 h f),
    coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) h (leftTranslation μ ∞ 𝕜 g f),
    h.ae_le (coeFn_leftTranslation (𝕜 := 𝕜) g f),
    (measurePreserving_mul_left ν g⁻¹).quasiMeasurePreserving.ae
      (coeFn_linftyOfAbsolutelyContinuous (𝕜 := 𝕜) h f)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

end Lp

end MeasureTheory
