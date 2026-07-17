module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.MeasureTheory.Function.WeightL2Isometry
import TauCeti.Analysis.InnerProductSpace.HilbertBasisMap

/-!
# From an orthogonality relation to a Hilbert basis of a weighted measure

Given a family of real polynomials `p : ℕ → ℝ[X]`, an almost-everywhere-positive weight
`w : ℝ → ℝ`, and positive normalization constants `c : ℕ → ℝ` satisfying the orthogonality
relation
`∫ (p m).eval x * (p n).eval x * w x ∂μ = if m = n then c n else 0`,
the normalized polynomials `pₙ/√cₙ`, viewed as elements of the weighted `L²` space
`L²(w·μ)` (with `w·μ := μ.withDensity (ENNReal.ofReal ∘ w)`), form an orthonormal family; if in
addition their span has trivial orthogonal complement, they form a `HilbertBasis`.

This is the family-agnostic assembly step of Part B2 of the `OrthogonalL2Bases` roadmap: the
orthogonality relation and the completeness hypothesis enter as arguments, so the bridge is
grounded by construction and reusable across families (Hermite, Chebyshev, ...). The scalars are
generic over `[RCLike 𝕜]`: the real polynomial values are cast through `algebraMap ℝ 𝕜`, so a single
construction serves both the real and complex `L²` spaces.

Two normalizations come out of one construction. The bare normalized polynomials are natively an
orthonormal basis of the **weighted measure** `L²(w·μ)` (`hilbertBasisOfWeightedMeasure`); pushing
that basis across the `weightL2Isometry` (multiplication by `√w`) yields the `√w`-envelope basis of
the **reference measure** `L²(μ)` (`hilbertBasisOfOrthogonalSystem`), with no separate proof. Each
basis exports its element-level `coe_*` lemma, so downstream family instances specialize rather than
re-derive.

## Main definitions

* `TauCeti.barePolyLp` — the normalized polynomial `pₙ/√cₙ` as a vector of `L²(w·μ; 𝕜)`.
* `TauCeti.hilbertBasisOfWeightedMeasure` — the bare polynomials as a `HilbertBasis` of `L²(w·μ)`.
* `TauCeti.hilbertBasisOfOrthogonalSystem` — the `√w`-envelope basis of `L²(μ)`, the
  `weightL2Isometry`-image of the weighted-measure basis.

## Main statements

* `TauCeti.orthonormal_barePolyLp` — orthonormality from the orthogonality relation.
* `TauCeti.coe_hilbertBasisOfWeightedMeasure`, `TauCeti.coe_hilbertBasisOfOrthogonalSystem` — the
  element-level characterizations (anti-vacuity pins).
-/

public section

namespace TauCeti

open MeasureTheory

open scoped ENNReal NNReal

variable {𝕜 : Type*} [RCLike 𝕜] (p : ℕ → Polynomial ℝ) (w : ℝ → ℝ) (c : ℕ → ℝ)

/-- The bare normalized polynomial `pₙ/√cₙ` as an element of `L²(w·μ; 𝕜)`, where
`w·μ = μ.withDensity (ENNReal.ofReal ∘ w)` and the real value is cast through `algebraMap ℝ 𝕜`. -/
noncomputable def barePolyLp {μ : Measure ℝ}
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun x => ENNReal.ofReal (w x)))) (n : ℕ) :
    Lp 𝕜 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))) :=
  (hmem n).toLp _

/-- The `Lp` representative of `barePolyLp` is the expected scalar-cast normalized polynomial. -/
theorem coeFn_barePolyLp {μ : Measure ℝ}
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun x => ENNReal.ofReal (w x)))) (n : ℕ) :
    ⇑(barePolyLp (𝕜 := 𝕜) p w c hmem n)
      =ᵐ[μ.withDensity (fun x => ENNReal.ofReal (w x))]
        fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n)) :=
  MemLp.coeFn_toLp _

/-- Changing the weighted measure back to `μ`: the `w·μ`-integral of a real product of polynomial
evaluations equals the `μ`-integral of that product times the weight `w`. -/
private theorem integral_eval_mul_withDensity {μ : Measure ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) (m n : ℕ) :
    (∫ x, (p m).eval x * (p n).eval x ∂(μ.withDensity (fun x => ENNReal.ofReal (w x))))
      = ∫ x, (p m).eval x * (p n).eval x * w x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hwm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hwpos] with x hx
  rw [ENNReal.toReal_ofReal hx.le, smul_eq_mul]
  ring

/-- The `w·μ`-integral of the product of two normalized real polynomials is the Kronecker delta. -/
private theorem integral_barePoly_real {μ : Measure ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) (hc : ∀ n, 0 < c n)
    (horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * w x ∂μ) = if m = n then c n else 0)
    (m n : ℕ) :
    (∫ x, ((p m).eval x / Real.sqrt (c m)) * ((p n).eval x / Real.sqrt (c n))
        ∂(μ.withDensity (fun x => ENNReal.ofReal (w x))))
      = if m = n then 1 else 0 := by
  have hcm := hc m
  have hcn := hc n
  calc
    (∫ x, ((p m).eval x / Real.sqrt (c m)) * ((p n).eval x / Real.sqrt (c n))
        ∂(μ.withDensity (fun x => ENNReal.ofReal (w x))))
        = (Real.sqrt (c m) * Real.sqrt (c n))⁻¹ *
            ∫ x, (p m).eval x * (p n).eval x
              ∂(μ.withDensity (fun x => ENNReal.ofReal (w x))) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          field_simp [Real.sqrt_ne_zero'.mpr hcm, Real.sqrt_ne_zero'.mpr hcn]
    _ = (Real.sqrt (c m) * Real.sqrt (c n))⁻¹ *
            ∫ x, (p m).eval x * (p n).eval x * w x ∂μ := by
          rw [integral_eval_mul_withDensity p w hwpos hwm m n]
    _ = if m = n then 1 else 0 := by
          rw [horth]
          by_cases hmn : m = n
          · subst hmn
            rw [if_pos rfl, if_pos rfl, Real.mul_self_sqrt hcn.le, inv_mul_cancel₀ hcn.ne']
          · rw [if_neg hmn, if_neg hmn, mul_zero]

/-- The normalized bare polynomials have Kronecker-delta inner products in `L²(w·μ)`. -/
theorem inner_barePolyLp {μ : Measure ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) (hc : ∀ n, 0 < c n)
    (horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * w x ∂μ) = if m = n then c n else 0)
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun x => ENNReal.ofReal (w x)))) (m n : ℕ) :
    inner 𝕜 (barePolyLp (𝕜 := 𝕜) p w c hmem m) (barePolyLp (𝕜 := 𝕜) p w c hmem n)
      = if m = n then 1 else 0 := by
  have hinner : ∀ a b : ℝ,
      inner 𝕜 ((algebraMap ℝ 𝕜) a) ((algebraMap ℝ 𝕜) b) = (algebraMap ℝ 𝕜) (a * b) := by
    intro a b
    simp [RCLike.inner_apply, RCLike.conj_ofReal, map_mul, mul_comm]
  calc
    inner 𝕜 (barePolyLp (𝕜 := 𝕜) p w c hmem m) (barePolyLp (𝕜 := 𝕜) p w c hmem n)
        = ∫ x, (algebraMap ℝ 𝕜)
              (((p m).eval x / Real.sqrt (c m)) * ((p n).eval x / Real.sqrt (c n)))
            ∂(μ.withDensity (fun x => ENNReal.ofReal (w x))) := by
          rw [MeasureTheory.L2.inner_def]
          refine integral_congr_ae ?_
          filter_upwards [coeFn_barePolyLp (𝕜 := 𝕜) p w c hmem m,
            coeFn_barePolyLp (𝕜 := 𝕜) p w c hmem n] with x hxm hxn
          rw [hxm, hxn]
          exact hinner _ _
    _ = if m = n then 1 else 0 := by
          rw [integral_ofReal, integral_barePoly_real p w c hwpos hwm hc horth m n]
          by_cases hmn : m = n <;> simp [hmn]

/-- **Orthonormality from the orthogonality relation.** The normalized bare polynomials
`pₙ/√cₙ` form an orthonormal family in `L²(w·μ)`. -/
theorem orthonormal_barePolyLp {μ : Measure ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) (hc : ∀ n, 0 < c n)
    (horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * w x ∂μ) = if m = n then c n else 0)
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    Orthonormal 𝕜 (barePolyLp (𝕜 := 𝕜) p w c hmem) := by
  rw [orthonormal_iff_ite]
  exact inner_barePolyLp p w c hwpos hwm hc horth hmem

/-- **The weighted-measure basis.** The normalized bare polynomials, orthonormal by the
orthogonality relation and complete by hypothesis, form a Hilbert basis of `L²(w·μ)` — the textbook
statement that a family of orthogonal polynomials is an orthonormal basis of its own weighted `L²`
space. -/
noncomputable def hilbertBasisOfWeightedMeasure {μ : Measure ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) (hc : ∀ n, 0 < c n)
    (horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * w x ∂μ) = if m = n then c n else 0)
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun x => ENNReal.ofReal (w x))))
    (hcomplete :
      (Submodule.span 𝕜 (Set.range (barePolyLp (𝕜 := 𝕜) p w c hmem)))ᗮ = ⊥) :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (orthonormal_barePolyLp p w c hwpos hwm hc horth hmem) hcomplete

/-- Element-level characterization of the weighted-measure basis. -/
theorem coe_hilbertBasisOfWeightedMeasure {μ : Measure ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) (hc : ∀ n, 0 < c n)
    (horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * w x ∂μ) = if m = n then c n else 0)
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun x => ENNReal.ofReal (w x))))
    (hcomplete :
      (Submodule.span 𝕜 (Set.range (barePolyLp (𝕜 := 𝕜) p w c hmem)))ᗮ = ⊥) :
    ⇑(hilbertBasisOfWeightedMeasure p w c hwpos hwm hc horth hmem hcomplete)
      = barePolyLp (𝕜 := 𝕜) p w c hmem :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **The `√w`-envelope basis of `L²(μ)`.** The `weightL2Isometry`-image (multiplication by `√w`) of
the weighted-measure basis; the `√w`-normalized functions `pₙ·√w/√cₙ` form a Hilbert basis of the
reference measure `L²(μ)`, obtained with no separate proof. -/
noncomputable def hilbertBasisOfOrthogonalSystem {μ : Measure ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) (hc : ∀ n, 0 < c n)
    (horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * w x ∂μ) = if m = n then c n else 0)
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun x => ENNReal.ofReal (w x))))
    (hcomplete :
      (Submodule.span 𝕜 (Set.range (barePolyLp (𝕜 := 𝕜) p w c hmem)))ᗮ = ⊥) :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 μ) :=
  (hilbertBasisOfWeightedMeasure p w c hwpos hwm hc horth hmem hcomplete).mapₗᵢ
    (weightL2Isometry μ w hwpos hwm)

/-- Element-level characterization of the `√w`-envelope basis: the `weightL2Isometry`-image of the
weighted-measure basis vector. -/
theorem coe_hilbertBasisOfOrthogonalSystem {μ : Measure ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) (hc : ∀ n, 0 < c n)
    (horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * w x ∂μ) = if m = n then c n else 0)
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun x => ENNReal.ofReal (w x))))
    (hcomplete :
      (Submodule.span 𝕜 (Set.range (barePolyLp (𝕜 := 𝕜) p w c hmem)))ᗮ = ⊥) (n : ℕ) :
    hilbertBasisOfOrthogonalSystem p w c hwpos hwm hc horth hmem hcomplete n
      = weightL2Isometry μ w hwpos hwm (barePolyLp (𝕜 := 𝕜) p w c hmem n) := by
  rw [hilbertBasisOfOrthogonalSystem, HilbertBasis.mapₗᵢ_apply,
    coe_hilbertBasisOfWeightedMeasure p w c hwpos hwm hc horth hmem hcomplete]

end TauCeti
