/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct
public import TauCeti.Analysis.Complex.CanonicalProduct.RankBound
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.DivisorFactorization

/-!
# Canonical products over sets of finite rank

For a set `Λ ⊆ ℂ` and a genus `p`, the canonical product
`Λ.canonicalProduct p z = z ^ δ * ∏' w ∈ Λ \ {0}, E_p (z / w)` has one factor `z` exactly when
`0 ∈ Λ` (`δ = 1`) and one primary factor `E_p = Complex.weierstrassFactor p` for each nonzero point
of `Λ`. Its finite partial products `Λ.partialCanonicalProduct p s` restrict the primary factors
to a finite set `s` of nonzero points.

When `Λ` has rank bound `p` (`Set.HasRankBound`), the partial products converge locally uniformly
to the canonical product, which is entire, vanishes exactly on `Λ`, and has a simple zero at
every point of `Λ`: its analytic order is `1` there, its divisor is the indicator of `Λ`, and its
derivative does not vanish there. It has finite order at most `p + 1`, with the explicit bound
`‖Λ.canonicalProduct p z‖ ≤ exp (C * (1 + ‖z‖) ^ (p + 1))` for
`C = 1 + (p + 1) * ∑' w ∈ Λ \ {0}, ‖w‖ ^ -(p + 1)`.

Since `Λ` is a set, each point is a simple zero; the product is independent of any enumeration of
`Λ`, and the origin contributes its factor once.

## Main results

* `Set.HasRankBound.tendstoLocallyUniformly_partialCanonicalProduct`: locally uniform convergence
  of the partial products along the directed family of finite sets of nonzero points.
* `Set.HasRankBound.differentiable_canonicalProduct`: the canonical product is entire.
* `Set.HasRankBound.canonicalProduct_eq_zero_iff`: its zeros are exactly the points of `Λ`.
* `Set.HasRankBound.analyticOrderAt_canonicalProduct`,
  `Set.HasRankBound.divisor_canonicalProduct`, `Set.HasRankBound.deriv_canonicalProduct_ne_zero`:
  every zero is simple.
* `Set.HasRankBound.norm_canonicalProduct_le_exp`: the growth bound of order `p + 1`.

## References

* R. Beuzart-Plessis, Y. Liu, W. Zhang, X. Zhu, *Isolation of cuspidal spectrum, with application
  to the Gan–Gross–Prasad conjecture*, Ann. of Math. (2) **194** (2021), §2.1, Lemma 2.2.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Theorem 15.9.
-/

public section

open Complex Filter Topology

namespace Set

open Classical in
/-- The canonical product of genus `p` over `Λ ⊆ ℂ`: the factor `z` if `0 ∈ Λ`, times the
unordered product of the primary factors `Complex.weierstrassFactor p (z / w)` over the nonzero
points `w` of `Λ`. -/
noncomputable def canonicalProduct (Λ : Set ℂ) (p : ℕ) (z : ℂ) : ℂ :=
  (if (0 : ℂ) ∈ Λ then z else 1) * ∏' w : ↥(Λ \ {0}), weierstrassFactor p (z / w)

open Classical in
/-- The partial canonical product of genus `p` over `Λ ⊆ ℂ` indexed by a finite set `s` of
nonzero points of `Λ`: the factor `z` if `0 ∈ Λ`, times the primary factors over `s`. -/
noncomputable def partialCanonicalProduct (Λ : Set ℂ) (p : ℕ) (s : Finset ↥(Λ \ {0})) (z : ℂ) :
    ℂ :=
  (if (0 : ℂ) ∈ Λ then z else 1) * ∏ w ∈ s, weierstrassFactor p (z / w)

variable {Λ : Set ℂ} {p : ℕ} {z : ℂ}

/-- The defining formula of the canonical product, for any decidability instance. -/
theorem canonicalProduct_def [Decidable ((0 : ℂ) ∈ Λ)] (z : ℂ) :
    Λ.canonicalProduct p z =
      (if (0 : ℂ) ∈ Λ then z else 1) * ∏' w : ↥(Λ \ {0}), weierstrassFactor p (z / w) := by
  rw [canonicalProduct]
  congr

/-- The defining formula of the partial canonical product, for any decidability instance. -/
theorem partialCanonicalProduct_def [Decidable ((0 : ℂ) ∈ Λ)] (s : Finset ↥(Λ \ {0})) (z : ℂ) :
    Λ.partialCanonicalProduct p s z =
      (if (0 : ℂ) ∈ Λ then z else 1) * ∏ w ∈ s, weierstrassFactor p (z / w) := by
  rw [partialCanonicalProduct]
  congr

/-- The canonical product over the empty set is the constant `1`, including at the origin. -/
@[simp]
theorem canonicalProduct_empty : (∅ : Set ℂ).canonicalProduct p = 1 := by
  ext z
  classical
  simp [canonicalProduct_def]

/-- The partial canonical product with no primary factors is the origin factor. -/
@[simp]
theorem partialCanonicalProduct_empty [Decidable ((0 : ℂ) ∈ Λ)] (z : ℂ) :
    Λ.partialCanonicalProduct p ∅ z = if (0 : ℂ) ∈ Λ then z else 1 := by
  simp [partialCanonicalProduct_def]

/-- Inserting a nonzero point `w` into the index multiplies the partial canonical product by
`E_p (z / w)`. -/
theorem partialCanonicalProduct_insert [DecidableEq ↥(Λ \ {0})] {s : Finset ↥(Λ \ {0})}
    {w : ↥(Λ \ {0})} (hw : w ∉ s) (z : ℂ) :
    Λ.partialCanonicalProduct p (insert w s) z =
      weierstrassFactor p (z / w) * Λ.partialCanonicalProduct p s z := by
  classical
  rw [partialCanonicalProduct_def, partialCanonicalProduct_def, Finset.prod_insert hw]
  ring

namespace HasRankBound

variable (h : Λ.HasRankBound p)
include h

/-- The partial canonical products converge locally uniformly to the canonical product. -/
theorem tendstoLocallyUniformly_partialCanonicalProduct :
    TendstoLocallyUniformly (Λ.partialCanonicalProduct p) (Λ.canonicalProduct p) atTop := by
  classical
  have hP := hasProdLocallyUniformlyOn_weierstrassFactor_div (p := fun _ ↦ p)
    fun R _ ↦ h.summable_div_pow R
  rw [HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_univ] at hP
  -- The origin factor does not depend on the finite index.
  have hO : TendstoLocallyUniformly (fun (_ : Finset ↥(Λ \ {0})) (z : ℂ) ↦
      if (0 : ℂ) ∈ Λ then z else 1) (fun z ↦ if (0 : ℂ) ∈ Λ then z else 1) atTop :=
    fun u hu _ ↦ ⟨univ, univ_mem, .of_forall fun _ _ _ ↦ refl_mem_uniformity hu⟩
  have hOc : Continuous fun z : ℂ ↦ if (0 : ℂ) ∈ Λ then z else 1 := by
    split_ifs <;> fun_prop
  have hlim := hO.fun_mul₀ hP hOc (differentiable_tprod_weierstrassFactor_div (p := fun _ ↦ p)
    fun R _ ↦ h.summable_div_pow R).continuous
  have hpart : Λ.partialCanonicalProduct p = fun (s : Finset ↥(Λ \ {0})) z ↦
      (if (0 : ℂ) ∈ Λ then z else 1) * ∏ w ∈ s, weierstrassFactor p (z / w) := by
    ext s z
    exact partialCanonicalProduct_def s z
  have hcan : Λ.canonicalProduct p = fun z ↦
      (if (0 : ℂ) ∈ Λ then z else 1) * ∏' w : ↥(Λ \ {0}), weierstrassFactor p (z / w) := by
    ext z
    exact canonicalProduct_def z
  rw [hpart, hcan]
  exact hlim

/-- The canonical product over a rank-bounded set is entire. -/
theorem differentiable_canonicalProduct : Differentiable ℂ (Λ.canonicalProduct p) := by
  classical
  have hP := differentiable_tprod_weierstrassFactor_div (p := fun _ ↦ p)
    fun R _ ↦ h.summable_div_pow R
  have hO : Differentiable ℂ fun z : ℂ ↦ if (0 : ℂ) ∈ Λ then z else 1 := by
    split_ifs <;> fun_prop
  intro z
  have hz := (hO z).mul (hP z)
  rwa [show Λ.canonicalProduct p = _ from funext canonicalProduct_def]

/-- The zeros of the canonical product over a rank-bounded set are exactly its points. -/
theorem canonicalProduct_eq_zero_iff : Λ.canonicalProduct p z = 0 ↔ z ∈ Λ := by
  classical
  rw [canonicalProduct_def, mul_eq_zero,
    tprod_weierstrassFactor_div_eq_zero_iff (p := fun _ ↦ p)
    fun R _ ↦ h.summable_div_pow R]
  by_cases hz : z = 0
  · subst hz
    by_cases h0 : (0 : ℂ) ∈ Λ <;> simp [h0]
  · constructor
    · rintro (hO | ⟨w, -, rfl⟩)
      · split_ifs at hO with h0
        · exact absurd hO hz
        · exact absurd hO one_ne_zero
      · exact w.property.1
    · exact fun hzΛ ↦ Or.inr ⟨⟨z, hzΛ, hz⟩, hz, rfl⟩

/-- **Simple zeros of canonical products.** The analytic order of the canonical product over a
rank-bounded set is `1` at its points and `0` elsewhere. -/
theorem analyticOrderAt_canonicalProduct [Decidable (z ∈ Λ)] :
    analyticOrderAt (Λ.canonicalProduct p) z = if z ∈ Λ then 1 else 0 := by
  classical
  have hΨ := Differentiable.analyticAt h.differentiable_canonicalProduct z
  split_ifs with hzΛ
  swap
  · exact hΨ.analyticOrderAt_eq_zero.mpr (mt h.canonicalProduct_eq_zero_iff.mp hzΛ)
  have hP := differentiable_tprod_weierstrassFactor_div (p := fun _ ↦ p)
    fun R _ ↦ h.summable_div_pow R
  have hPord := analyticOrderAt_tprod_weierstrassFactor_div (p := fun _ ↦ p)
    (fun R _ ↦ h.summable_div_pow R) z
  rw [show Λ.canonicalProduct p = _ from funext canonicalProduct_def]
  by_cases hz : z = 0
  · -- At the origin, the factor `z` has a simple zero and the primary product equals `1`.
    subst hz
    have hP0 : ∏' w : ↥(Λ \ {0}), weierstrassFactor p ((0 : ℂ) / w) ≠ 0 := by simp
    simp only [hzΛ, ite_true]
    rw [analyticOrderAt_fun_mul (f := fun w ↦ w) (by fun_prop) (hP.analyticAt _),
      (hP.analyticAt _).analyticOrderAt_eq_zero.mpr hP0, add_zero]
    exact analyticOrderAt_id
  · -- Away from the origin, the factor `z` or `1` does not vanish and the product has a simple
    -- zero, the fiber of `z` in `Λ \ {0}` being a single point.
    have hO : AnalyticAt ℂ (fun w : ℂ ↦ if (0 : ℂ) ∈ Λ then w else 1) z := by
      split_ifs <;> fun_prop
    have hOz : (if (0 : ℂ) ∈ Λ then z else 1) ≠ 0 := by
      split_ifs
      · exact hz
      · exact one_ne_zero
    have hfiber : {w : ↥(Λ \ {0}) | (w : ℂ) ≠ 0 ∧ (w : ℂ) = z} = {⟨z, hzΛ, hz⟩} := by
      ext w
      simp only [mem_ofPred_eq, mem_singleton_iff, Subtype.ext_iff]
      exact ⟨And.right, fun hw ↦ ⟨hw ▸ hz, hw⟩⟩
    rw [analyticOrderAt_fun_mul hO (hP.analyticAt _), hO.analyticOrderAt_eq_zero.mpr hOz, zero_add,
      hPord, hfiber, ncard_singleton, Nat.cast_one]

/-- The whole-plane divisor of the canonical product over a rank-bounded set is the indicator
function of the set. -/
theorem divisor_canonicalProduct (z : ℂ) :
    MeromorphicOn.divisor (Λ.canonicalProduct p) univ z = Λ.indicator 1 z := by
  classical
  rw [h.differentiable_canonicalProduct.divisor_univ_eq_of_analyticOrderAt_eq
    (n := if z ∈ Λ then 1 else 0) (by rw [h.analyticOrderAt_canonicalProduct]; split_ifs <;> rfl)]
  split_ifs with hz <;> simp [hz]

/-- The derivative of the canonical product over a rank-bounded set does not vanish at any of its
zeros. -/
theorem deriv_canonicalProduct_ne_zero (hz : z ∈ Λ) : deriv (Λ.canonicalProduct p) z ≠ 0 := by
  classical
  have hΨ := Differentiable.analyticAt h.differentiable_canonicalProduct z
  rw [← hΨ.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero, h.canonicalProduct_eq_zero_iff.mpr hz]
  simpa [hz] using h.analyticOrderAt_canonicalProduct (z := z)

/-- **Growth of canonical products of finite rank.** If `Λ` has rank bound `p`, its canonical
product of genus `p` has order at most `p + 1`:
`‖Λ.canonicalProduct p z‖ ≤ exp (C * (1 + ‖z‖) ^ (p + 1))` with
`C = 1 + (p + 1) * ∑' w ∈ Λ \ {0}, ‖w‖ ^ -(p + 1)`. -/
theorem norm_canonicalProduct_le_exp (z : ℂ) :
    ‖Λ.canonicalProduct p z‖ ≤
      Real.exp ((1 + (p + 1) * ∑' w : ↥(Λ \ {0}), (‖(w : ℂ)‖ ^ (p + 1))⁻¹) *
        (1 + ‖z‖) ^ (p + 1)) := by
  classical
  set S := ∑' w : ↥(Λ \ {0}), (‖(w : ℂ)‖ ^ (p + 1))⁻¹
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  -- The origin factor is at most `1 + ‖z‖ ≤ exp ((1 + ‖z‖) ^ (p + 1))`.
  have hO : ‖(if (0 : ℂ) ∈ Λ then z else 1)‖ ≤ Real.exp ((1 + ‖z‖) ^ (p + 1)) := by
    have hle : ‖(if (0 : ℂ) ∈ Λ then z else 1)‖ ≤ 1 + ‖z‖ := by
      split_ifs <;> simp
    calc
      _ ≤ 1 + ‖z‖ := hle
      _ ≤ (1 + ‖z‖) ^ (p + 1) := le_self_pow₀ (by linarith) (by omega)
      _ ≤ (1 + ‖z‖) ^ (p + 1) + 1 := by linarith
      _ ≤ _ := Real.add_one_le_exp _
  have hP := norm_tprod_weierstrassFactor_div_le_exp p (a := ((↑) : ↥(Λ \ {0}) → ℂ))
    (hasRankBound_def.mp h) z
  rw [canonicalProduct_def, norm_mul]
  calc
    _ ≤ Real.exp ((1 + ‖z‖) ^ (p + 1)) * Real.exp ((p + 1) * S * ‖z‖ ^ (p + 1)) := by
      gcongr
    _ ≤ Real.exp ((1 + ‖z‖) ^ (p + 1)) * Real.exp ((p + 1) * S * (1 + ‖z‖) ^ (p + 1)) := by
      gcongr
      linarith
    _ = _ := by
      rw [← Real.exp_add]
      ring_nf

end HasRankBound

end Set

/-! ### Examples -/

/-- At genus zero over `{0, 1}`, the partial product with no primary factor is `z` and the one with
the factor at `1` is `z * (1 - z)`; at `z = 2` they are `2` and `-2`. -/
example :
    ({0, 1} : Set ℂ).partialCanonicalProduct 0 ∅ 2 = 2 ∧
      ({0, 1} : Set ℂ).partialCanonicalProduct 0 {⟨1, by simp, by simp⟩} 2 = -2 := by
  classical
  constructor
  · simp
  · rw [Set.partialCanonicalProduct_def]
    norm_num
