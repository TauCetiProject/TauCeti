/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Sums and linear combinations in `Lᵖ`, and composition with a continuous linear map

Mathlib provides `MeasureTheory.MemLp.toLp_zero`, `MeasureTheory.MemLp.toLp_add`, and
`MeasureTheory.Lp.coeFn_finsetSum`, as well as `MeasureTheory.memLp_finsetSum` and
`MeasureTheory.memLp_finsetSum'`. This file records the companion identities identifying the `Lp`
class of a finite sum of `Lᵖ` functions with the sum of their `Lp` classes, for any `MemLp`
witness on the sum.

Mathlib describes the representatives of sums, negatives and scalar multiples in `Lᵖ` almost
everywhere (`MeasureTheory.Lp.coeFn_add` and its siblings); this file records the forms that
transport almost-everywhere descriptions `⇑u =ᵐ[μ] g` of the summands, which compute the
representatives of linear combinations.

Mathlib composes `f : Lp E p μ` with `L : E →SL[σ] F` both as an element `L.compLp f` and through
the bundled continuous semilinear map `L.compLpL p μ`; this file also records that the two agree.

## Main declarations

* `MeasureTheory.MemLp.toLp_finsetSum'`: `hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.MemLp.toLp_finsetSum`:
  `hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.Lp.coeFn_add_ae_eq_of_ae_eq`, `MeasureTheory.Lp.coeFn_sub_ae_eq_of_ae_eq`,
  `MeasureTheory.Lp.coeFn_neg_ae_eq_of_ae_eq`, `MeasureTheory.Lp.coeFn_smul_ae_eq_of_ae_eq`: if
  `⇑u =ᵐ[μ] g` and `⇑v =ᵐ[μ] h`, then `⇑(u + v) =ᵐ[μ] g + h`, and similarly for `-` and `•`.
* `ContinuousLinearMap.compLpL_apply`: the bundled composition applied to `f` is `L.compLp f`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α E ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} {s : Finset ι} {f : ι → α → E}

/-- The `Lp` class of a finite sum of `Lᵖ` functions is the sum of their `Lp` classes. -/
theorem toLp_finsetSum' (hsum : MemLp (∑ i ∈ s, f i) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i) :=
  Lp.ext_iff.2 <| hsum.coeFn_toLp.trans <|
    (eventuallyEq_sum fun i _ ↦ (hf i).coeFn_toLp.symm).trans
      (Lp.coeFn_finsetSum s fun i ↦ (hf i).toLp (f i)).symm

/-- The `Lp` class of a pointwise finite sum `fun x ↦ ∑ i ∈ s, f i x` of `Lᵖ` functions is the
sum of their `Lp` classes. -/
theorem toLp_finsetSum (hsum : MemLp (fun x ↦ ∑ i ∈ s, f i x) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i) := by
  convert (memLp_finsetSum' s fun i _ ↦ hf i).toLp_finsetSum' hf using 1
  exact toLp_congr _ _ (.of_forall fun x ↦ (Finset.sum_apply x s f).symm)

end MeasureTheory.MemLp

namespace MeasureTheory.Lp

variable {α E 𝕜 : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup E] {u v : Lp E p μ} {g h : α → E}

/-- If `u` and `v` are almost everywhere `g` and `h`, then `u + v` is almost everywhere `g + h`. -/
theorem coeFn_add_ae_eq_of_ae_eq (hu : ⇑u =ᵐ[μ] g) (hv : ⇑v =ᵐ[μ] h) : ⇑(u + v) =ᵐ[μ] g + h :=
  (coeFn_add u v).trans (hu.add hv)

/-- If `u` and `v` are almost everywhere `g` and `h`, then `u - v` is almost everywhere `g - h`. -/
theorem coeFn_sub_ae_eq_of_ae_eq (hu : ⇑u =ᵐ[μ] g) (hv : ⇑v =ᵐ[μ] h) : ⇑(u - v) =ᵐ[μ] g - h :=
  (coeFn_sub u v).trans (hu.sub hv)

/-- If `u` is almost everywhere `g`, then `-u` is almost everywhere `-g`. -/
theorem coeFn_neg_ae_eq_of_ae_eq (hu : ⇑u =ᵐ[μ] g) : ⇑(-u) =ᵐ[μ] -g :=
  (coeFn_neg u).trans hu.neg

/-- If `u` is almost everywhere `g`, then `c • u` is almost everywhere `c • g`. -/
theorem coeFn_smul_ae_eq_of_ae_eq [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (c : 𝕜)
    (hu : ⇑u =ᵐ[μ] g) : ⇑(c • u) =ᵐ[μ] c • g :=
  (coeFn_smul c u).trans (hu.const_smul c)

end MeasureTheory.Lp

namespace ContinuousLinearMap

open MeasureTheory

variable {α E F 𝕜 𝕜' : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜' F]

/-- The bundled composition `L.compLpL p μ` applied to `f` is the composition `L.compLp f`. -/
@[simp]
theorem compLpL_apply [Fact (1 ≤ p)] (L : E →SL[σ] F) (f : Lp E p μ) :
    L.compLpL p μ f = L.compLp f :=
  rfl

end ContinuousLinearMap
