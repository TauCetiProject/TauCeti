/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CalderonVaillancourt
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping

/-!
# The bounded extension of uniform symbols of order zero to `L²`

Let `a` be a symbol of order `0` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(-|β|)` hold with constants independent of the position `x`
(`TauCeti.Symbol.IsUniform`). By the Calderón–Vaillancourt theorem
(`TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`,
`TauCeti.Symbol.exists_quantizeUniformOrderZero`) its Kohn–Nirenberg quantization `Op(a)`
extends to a bounded operator on `L²` when the coefficient spaces are complex Hilbert spaces or
finite-dimensional. This file records the resulting `L²` estimate on Schwartz functions and names
the extension, as an operator on the Bessel-potential space `H^0 = L²`, so that it can be compared
across symbols. The extension is defined for normed coefficient spaces; its API assumes the `L²`
estimate on Schwartz functions.

## Main declarations

* `TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le`,
  `TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional`: there is
  a constant `C` with `‖Op(a) u‖_{L²} ≤ C ‖u‖_{L²}` for every Schwartz function `u`.
* `TauCeti.Symbol.quantizeUniformOrderZero`: the bounded extension `H^0(ℝⁿ; V) → H^0(ℝⁿ; W)`,
  with `TauCeti.Symbol.toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply`
  identifying its values on Schwartz functions, its norm bound
  `TauCeti.Symbol.norm_quantizeUniformOrderZero_le` and its linearity in the symbol.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace Symbol

section InnerProductSpace

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W 0}

/-- **`L²` boundedness of uniform symbols of order zero.** For a symbol `a` of order `0` between
complex Hilbert spaces whose estimates are uniform in the position, there is a constant `C` with
`‖Op(a) u‖_{L²} ≤ C ‖u‖_{L²}` for every Schwartz function `u`. -/
theorem IsUniform.exists_eLpNorm_quantizeSchwartzValue_le (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  obtain ⟨T, hT⟩ := a.exists_quantizeUniformOrderZeroLp ha
  refine ⟨‖T‖, norm_nonneg T, fun u ↦ ?_⟩
  have hTu : eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume = ‖T (u.toLp 2)‖ₑ := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (hT u).symm
  have hu : ‖u.toLp 2‖ₑ = eLpNorm u 2 volume := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (u.coeFn_toLp 2 volume)
  rw [hTu, ← hu, ofReal_norm T]
  exact T.le_opENorm _

end InnerProductSpace

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {a : Symbol n V W 0}

/-- **`L²` boundedness of uniform symbols of order zero** for finite-dimensional coefficient
spaces: there is a constant `C` with `‖Op(a) u‖_{L²} ≤ C ‖u‖_{L²}` for every Schwartz
function `u`. -/
theorem IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  obtain ⟨T, hT⟩ := a.exists_quantizeUniformOrderZero ha
  refine ⟨‖T‖, norm_nonneg T, fun u ↦ ?_⟩
  have hTu : T (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u) := by
    ext φ
    rw [hT, SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply,
      coe_quantizeUniformCLM]
  have hle := T.le_opNorm (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u)
  rw [hTu, SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, coe_quantizeUniformCLM] at hle
  have hfin := ((quantizeUniformCLM a ha u).memLp 2).eLpNorm_ne_top
  rw [coe_quantizeUniformCLM] at hfin
  rw [← ENNReal.ofReal_toReal hfin]
  refine (ENNReal.ofReal_le_ofReal hle).trans ?_
  rw [ENNReal.ofReal_mul (norm_nonneg T)]
  gcongr
  exact ENNReal.ofReal_toReal_le

/-- An `L²` estimate for `Op(a)` on Schwartz functions, in `H^0` norms. -/
private theorem norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le (ha : a.IsUniform) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(CoordinateSpace n, V), eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
      ENNReal.ofReal C * eLpNorm u 2 volume) (u : 𝓢(CoordinateSpace n, V)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u)‖ ≤
      C * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ := by
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, coe_quantizeUniformCLM,
    ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (u.memLp 2).eLpNorm_ne_top) (hC u)

/-- **The bounded extension of `Op(a)` to `L²`**, for a uniform symbol `a` of order `0`, as an
operator on the Bessel-potential space `H^0 = L²`. When `Op(a)` satisfies an `L²` estimate on
Schwartz functions (for instance for complex Hilbert spaces,
`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le`, or finite-dimensional ones,
`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional`), it
extends the quantization of Schwartz functions
(`TauCeti.Symbol.toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply`), and it is the
unique continuous linear map with this property (`BesselPotentialSpace.continuousLinearMap_ext`).
Without such an estimate it is `0`. -/
def quantizeUniformOrderZero (a : Symbol n V W 0) (ha : a.IsUniform) :
    H^{0}(CoordinateSpace n, V) →L[ℂ] H^{0}(CoordinateSpace n, W) :=
  ((SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) 0 2).comp
      (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) 0 2).toLinearMap

/-- On Schwartz functions, the bounded extension of `Op(a)` is `Op(a)`, given an `H^0` bound. -/
private theorem quantizeUniformOrderZero_toBesselPotentialSpaceCLM_of_norm_le (ha : a.IsUniform)
    (hC : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformOrderZero ha (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u) :=
  LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) 0 ENNReal.ofNat_ne_top) hC u

/-- An `L²` estimate for `Op(a)` on Schwartz functions gives one in `H^0` norms. -/
private theorem exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le (ha : a.IsUniform)
    (hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume) :
    ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ :=
  let ⟨C, hC0, hC⟩ := hC
  ⟨C, norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hC0 hC⟩

/-- On Schwartz functions, the bounded extension of `Op(a)` is `Op(a)`, provided `Op(a)` satisfies
an `L²` estimate on Schwartz functions. -/
@[simp]
theorem quantizeUniformOrderZero_toBesselPotentialSpaceCLM (ha : a.IsUniform)
    (hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformOrderZero ha (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u) :=
  quantizeUniformOrderZero_toBesselPotentialSpaceCLM_of_norm_le ha
    (exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hC) u

/-- On a Schwartz function `u`, the bounded extension of `Op(a)` to `H^0` gives the tempered
distribution of the function `Op(a) u = quantizeSchwartzValue a.coefficient u`, provided `Op(a)`
satisfies an `L²` estimate on Schwartz functions. -/
theorem toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply (ha : a.IsUniform)
    (hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume)
    (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniformOrderZero ha (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeUniformOrderZero_toBesselPotentialSpaceCLM ha hC,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply, coe_quantizeUniformCLM]

/-- The operator norm of the bounded extension of `Op(a)` is at most any constant of the `L²`
estimate on Schwartz functions. -/
theorem norm_quantizeUniformOrderZero_le (ha : a.IsUniform) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(CoordinateSpace n, V), eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
      ENNReal.ofReal C * eLpNorm u 2 volume) :
    ‖a.quantizeUniformOrderZero ha‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) 0 ENNReal.ofNat_ne_top) hC0
    (norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hC0 hC)

/-- The bounded extension of `Op(a)` is additive in the symbol, for symbols satisfying `L²`
estimates on Schwartz functions. -/
theorem quantizeUniformOrderZero_add {b : Symbol n V W 0} (ha : a.IsUniform) (hb : b.IsUniform)
    (hCa : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume)
    (hCb : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue b.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume) :
    (a + b).quantizeUniformOrderZero (ha.add hb) =
      a.quantizeUniformOrderZero ha + b.quantizeUniformOrderZero hb := by
  obtain ⟨Ca, hCa⟩ := exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hCa
  obtain ⟨Cb, hCb⟩ := exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le hb hCb
  have hCab : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM (a + b) (ha.add hb) u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ := by
    refine ⟨Ca + Cb, fun u ↦ ?_⟩
    rw [quantizeUniformCLM_add ha hb, add_apply, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hCa u) (hCb u))
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [add_apply, quantizeUniformOrderZero_toBesselPotentialSpaceCLM_of_norm_le (ha.add hb) hCab,
    quantizeUniformOrderZero_toBesselPotentialSpaceCLM_of_norm_le ha ⟨Ca, hCa⟩,
    quantizeUniformOrderZero_toBesselPotentialSpaceCLM_of_norm_le hb ⟨Cb, hCb⟩,
    quantizeUniformCLM_add ha hb, add_apply, map_add]

/-- The bounded extension of `Op(a)` is homogeneous in the symbol, for a symbol satisfying an `L²`
estimate on Schwartz functions. -/
theorem quantizeUniformOrderZero_smul (ha : a.IsUniform)
    (hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume) (c : ℂ) :
    (c • a).quantizeUniformOrderZero (ha.smul c) = c • a.quantizeUniformOrderZero ha := by
  obtain ⟨C, hC⟩ := exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hC
  have hCc : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM (c • a) (ha.smul c) u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ := by
    refine ⟨‖c‖ * C, fun u ↦ ?_⟩
    rw [quantizeUniformCLM_smul ha c, smul_apply, map_smul, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg c)
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [smul_apply, quantizeUniformOrderZero_toBesselPotentialSpaceCLM_of_norm_le (ha.smul c) hCc,
    quantizeUniformOrderZero_toBesselPotentialSpaceCLM_of_norm_le ha ⟨C, hC⟩,
    quantizeUniformCLM_smul ha c, smul_apply, map_smul]

end Symbol

end TauCeti
