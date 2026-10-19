/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Weak
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Absolutely summing operators

Let `1 ≤ p ≤ ∞`. A bounded operator `T : E →L[𝕜] F` is *absolutely `p`-summing* if there is a
constant `C` such that the `Lᵖ` norm of `(T xᵢ)ᵢ`, which is `(∑ ‖T xᵢ‖ᵖ)^(1/p)` for finite `p`,
is at most `C * weakLpNorm p x` for every finite family `x` in `E`; the least such constant is
the `p`-summing norm `πₚ(T)`. We record `πₚ(T)` as the extended gauge
`ContinuousLinearMap.summingENorm p T ∈ [0, ∞]`, the supremum over finite families of the ratio
of the two sides. It is finite exactly on the absolutely `p`-summing operators, which form the
submodule `TauCeti.absolutelySummingOperators 𝕜 p E F` of `E →L[𝕜] F`.

The gauge is absolutely homogeneous and subadditive, and satisfies the two-sided ideal inequality
`πₚ(A ∘ T ∘ B) ≤ ‖A‖ πₚ(T) ‖B‖`. Over real or complex scalars it dominates the operator norm,
takes the value `‖f‖ ‖y‖` on the rank-one operator `x ↦ f x • y`, and is lower semicontinuous for
the operator-norm topology, which is the input for completeness of the summing-norm ideal.
At exponent `∞` it is the operator norm, and it decreases as the exponent grows:
`π_q(T) ≤ π_p(T)` for `p ≤ q`, so absolutely `p`-summing operators are absolutely `q`-summing.

## Main declarations

* `ContinuousLinearMap.summingENorm`: the extended `p`-summing gauge `πₚ(T)`.
* `ContinuousLinearMap.summingENorm_le_ofReal_iff`: `πₚ(T) ≤ C` iff the defining inequality
  holds with constant `C`.
* `ContinuousLinearMap.enorm_toLp_le_summingENorm_mul`: the defining inequality with the
  constant `πₚ(T)`, for families indexed by any finite type.
* `ContinuousLinearMap.summingENorm_comp_comp_le`: the ideal inequality.
* `ContinuousLinearMap.enorm_le_summingENorm`: `‖T‖ ≤ πₚ(T)`.
* `ContinuousLinearMap.summingENorm_smulRight`: the rank-one value.
* `ContinuousLinearMap.lowerSemicontinuous_summingENorm`: lower semicontinuity.
* `ContinuousLinearMap.summingENorm_top`: `π_∞(T) = ‖T‖`.
* `ContinuousLinearMap.summingENorm_le_summingENorm_of_exponent_le`: `π_q(T) ≤ π_p(T)` for
  `p ≤ q`.
* `TauCeti.absolutelySummingOperators`: the submodule of absolutely `p`-summing operators.
* `TauCeti.absolutelySummingOperators_le_of_exponent_le`: the inclusion of these submodules.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.2.
* J. Diestel, H. Jarchow and A. Tonge, *Absolutely Summing Operators*, Chapter 2.
-/

public section

noncomputable section

open TauCeti
open scoped ENNReal

namespace ContinuousLinearMap

section NormedField

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The extended absolutely `p`-summing gauge `πₚ(T) ∈ [0, ∞]`: the supremum over finite families
`x` of the `Lᵖ` norm of `(T xᵢ)ᵢ` divided by the weak `Lᵖ` norm of `x`. A family of zero weak norm
whose image is not null contributes `∞`. It is the least constant in the defining inequality of
absolutely `p`-summing operators (`summingENorm_le_ofReal_iff`). -/
def summingENorm (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (x : Fin n → E),
    ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ / ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x)

/-- The `p`-summing gauge as a supremum of ratios over families indexed by `Fin n`. -/
theorem summingENorm_def (T : E →L[𝕜] F) :
    T.summingENorm p = ⨆ (n : ℕ) (x : Fin n → E),
      ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ / ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x) := (rfl)

variable {p}

/-- Each finite family bounds the gauge from below by the ratio of its two norms. -/
theorem enorm_toLp_div_le_summingENorm (T : E →L[𝕜] F) {n : ℕ} (x : Fin n → E) :
    ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ / ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x) ≤
      T.summingENorm p :=
  le_iSup₂ (f := fun (n : ℕ) (x : Fin n → E) ↦
    ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ / ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x)) n x

/-- A finite upper bound on the gauge is a bound in the defining inequality, in extended form. -/
theorem summingENorm_le_iff {T : E →L[𝕜] F} {C : ℝ≥0∞} (hC : C ≠ ∞) :
    T.summingENorm p ≤ C ↔ ∀ (n : ℕ) (x : Fin n → E),
      ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ ≤ C * ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x) := by
  simp only [summingENorm_def, iSup_le_iff]
  exact forall₂_congr fun n x ↦
    ENNReal.div_le_iff_le_mul (Or.inr hC) (Or.inl ENNReal.ofReal_ne_top)

/-- The gauge is at most `C` exactly when the `Lᵖ` norm of `(T xᵢ)ᵢ` is at most
`C * weakLpNorm p x` for every finite family `x`. -/
theorem summingENorm_le_ofReal_iff {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C) :
    T.summingENorm p ≤ ENNReal.ofReal C ↔ ∀ (n : ℕ) (x : Fin n → E),
      ‖WithLp.toLp p (fun i ↦ T (x i))‖ ≤ C * weakLpNorm (𝕜 := 𝕜) p x := by
  rw [summingENorm_le_iff ENNReal.ofReal_ne_top]
  refine forall₂_congr fun n x ↦ ?_
  rw [← ENNReal.ofReal_mul hC, ← ofReal_norm,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (apply_nonneg _ _))]

/-- A finite gauge bounds the image of every finite family, whatever its index type. -/
theorem enorm_toLp_le_summingENorm_mul_of_ne_top {T : E →L[𝕜] F}
    (hT : T.summingENorm p ≠ ∞) {ι : Type*} [Fintype ι] (x : ι → E) :
    ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ ≤
      T.summingENorm p * ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x) := by
  let e := Fintype.equivFin ι
  have h := (summingENorm_le_iff hT).1 le_rfl _ (x ∘ e.symm)
  have hn : ‖WithLp.toLp p (fun i ↦ T ((x ∘ e.symm) i))‖ₑ =
      ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg _ (PiLp.norm_toLp_comp_equiv e.symm fun i ↦ T (x i))
  rwa [weakLpNorm_comp_equiv, hn] at h

/-- The real form of the defining inequality with constant `πₚ(T)`, for an operator of finite
gauge. -/
theorem norm_toLp_le_toReal_summingENorm_mul {T : E →L[𝕜] F}
    (hT : T.summingENorm p ≠ ∞) {ι : Type*} [Fintype ι] (x : ι → E) :
    ‖WithLp.toLp p (fun i ↦ T (x i))‖ ≤
      (T.summingENorm p).toReal * weakLpNorm (𝕜 := 𝕜) p x := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hT ENNReal.ofReal_ne_top)
    (enorm_toLp_le_summingENorm_mul_of_ne_top hT x)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (apply_nonneg _ _), toReal_enorm] at h

/-- An operator of zero operator norm has zero gauge. -/
theorem summingENorm_eq_zero_of_norm_eq_zero {T : E →L[𝕜] F} (hT : ‖T‖ = 0) :
    T.summingENorm p = 0 := by
  refine le_antisymm ?_ bot_le
  rw [← ENNReal.ofReal_zero, summingENorm_le_ofReal_iff le_rfl]
  intro n x
  simpa [hT] using PiLp.norm_toLp_comp_le (p := p) (norm_nonneg T) T.le_opNorm x

/-- The zero operator has zero gauge. -/
@[simp]
theorem summingENorm_zero : (0 : E →L[𝕜] F).summingENorm p = 0 :=
  summingENorm_eq_zero_of_norm_eq_zero norm_zero

/-- Absolute homogeneity of the gauge, including its infinite values. -/
@[simp]
theorem summingENorm_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).summingENorm p = ‖c‖ₑ * T.summingENorm p := by
  have h (n : ℕ) (x : Fin n → E) :
      ‖WithLp.toLp p (fun i ↦ (c • T) (x i))‖ₑ = ‖c‖ₑ * ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ := by
    simp only [smul_apply, ← Pi.smul_def, WithLp.toLp_smul, enorm_smul]
  simp only [summingENorm_def, h, mul_div_assoc, ENNReal.mul_iSup]

/-- Negation preserves the gauge. -/
@[simp]
theorem summingENorm_neg (T : E →L[𝕜] F) : (-T).summingENorm p = T.summingENorm p := by
  simpa using summingENorm_smul (-1 : 𝕜) T

/-- The gauge is subadditive. -/
theorem summingENorm_add_le (S T : E →L[𝕜] F) :
    (S + T).summingENorm p ≤ S.summingENorm p + T.summingENorm p := by
  refine iSup₂_le fun n x ↦ ?_
  have hle : ‖WithLp.toLp p (fun i ↦ (S + T) (x i))‖ₑ ≤
      ‖WithLp.toLp p (fun i ↦ S (x i))‖ₑ + ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ := by
    have hadd : WithLp.toLp p (fun i ↦ (S + T) (x i)) =
        WithLp.toLp p (fun i ↦ S (x i)) + WithLp.toLp p (fun i ↦ T (x i)) := by
      ext i
      simp
    rw [hadd]
    exact enorm_add_le _ _
  calc
    _ ≤ (‖WithLp.toLp p (fun i ↦ S (x i))‖ₑ + ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ) /
        ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x) := by gcongr
    _ = _ := ENNReal.add_div
    _ ≤ S.summingENorm p + T.summingENorm p :=
      add_le_add (S.enorm_toLp_div_le_summingENorm x) (T.enorm_toLp_div_le_summingENorm x)

/-- Composing on the left with a bounded operator multiplies the gauge by at most its norm. -/
theorem summingENorm_comp_left_le (A : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (A ∘L T).summingENorm p ≤ ‖A‖ₑ * T.summingENorm p := by
  refine iSup₂_le fun n x ↦ ?_
  have hle : ‖WithLp.toLp p (fun i ↦ (A ∘L T) (x i))‖ₑ ≤
      ‖A‖ₑ * ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (PiLp.norm_toLp_comp_le (norm_nonneg A) A.le_opNorm fun i ↦ T (x i))
  calc
    _ ≤ ‖A‖ₑ * ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ /
        ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x) := by gcongr
    _ ≤ ‖A‖ₑ * T.summingENorm p := by
      rw [mul_div_assoc]
      gcongr
      exact T.enorm_toLp_div_le_summingENorm x

/-- Composing on the right with a bounded operator multiplies the gauge by at most its norm. -/
theorem summingENorm_comp_right_le (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (T ∘L B).summingENorm p ≤ T.summingENorm p * ‖B‖ₑ := by
  rcases eq_or_ne (T.summingENorm p) ∞ with hT | hT
  · rcases eq_or_ne ‖B‖ₑ 0 with hB | hB
    · -- A null right factor makes the composite null, whatever the gauge of `T`.
      have hB' : ‖B‖ = 0 := by simpa using congrArg ENNReal.toReal hB
      have hTB : ‖T ∘L B‖ = 0 :=
        le_antisymm ((opNorm_comp_le T B).trans (by simp [hB'])) (norm_nonneg _)
      simp [summingENorm_eq_zero_of_norm_eq_zero hTB]
    · simp [hT, ENNReal.top_mul hB]
  · rw [summingENorm_le_iff (ENNReal.mul_ne_top hT enorm_ne_top)]
    intro n x
    calc
      _ ≤ T.summingENorm p * ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p (B ∘ x)) :=
        enorm_toLp_le_summingENorm_mul_of_ne_top hT (B ∘ x)
      _ ≤ T.summingENorm p * (‖B‖ₑ * ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x)) := by
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        gcongr
        exact weakLpNorm_comp_le p B x
      _ = _ := (mul_assoc _ _ _).symm

/-- The two-sided ideal inequality `πₚ(A ∘ T ∘ B) ≤ ‖A‖ πₚ(T) ‖B‖`. -/
theorem summingENorm_comp_comp_le (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (A ∘L T ∘L B).summingENorm p ≤ ‖A‖ₑ * T.summingENorm p * ‖B‖ₑ :=
  calc
    _ ≤ ‖A‖ₑ * (T ∘L B).summingENorm p := summingENorm_comp_left_le A (T ∘L B)
    _ ≤ ‖A‖ₑ * (T.summingENorm p * ‖B‖ₑ) := by gcongr; exact summingENorm_comp_right_le T B
    _ = _ := (mul_assoc _ _ _).symm

/-- The rank-one operator `x ↦ f x • y` has gauge at most `‖f‖ ‖y‖`. -/
theorem summingENorm_smulRight_le (f : StrongDual 𝕜 E) (y : F) :
    (f.smulRight y).summingENorm p ≤ ‖f‖ₑ * ‖y‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    summingENorm_le_ofReal_iff (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  intro n x
  simp only [smulRight_apply]
  rw [PiLp.norm_toLp_smul_const]
  calc
    _ ≤ weakLpNorm (𝕜 := 𝕜) p x * ‖f‖ * ‖y‖ := by
      gcongr
      exact norm_eval_le_weakLpNorm p x f
    _ = _ := by ring

end NormedField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded operator maps a family of zero weak norm to a family of zero `Lᵖ` norm. -/
theorem norm_toLp_eq_zero_of_weakLpNorm_eq_zero (T : E →L[𝕜] F) {ι : Type*} [Fintype ι]
    {x : ι → E} (hx : weakLpNorm (𝕜 := 𝕜) p x = 0) :
    ‖WithLp.toLp p (fun i ↦ T (x i))‖ = 0 := by
  refine le_antisymm ((PiLp.norm_mono (y := (0 : PiLp p fun _ : ι ↦ ℝ)) fun i ↦ ?_).trans
    (by simp)) (norm_nonneg _)
  have hxi : ‖x i‖ = 0 := le_antisymm (hx ▸ norm_le_weakLpNorm p x i) (norm_nonneg _)
  simpa [hxi] using T.le_opNorm (x i)

/-- The defining inequality with the constant `πₚ(T)`, for families indexed by any finite type.
Over real or complex scalars no finiteness assumption is needed. -/
theorem enorm_toLp_le_summingENorm_mul (T : E →L[𝕜] F) {ι : Type*} [Fintype ι] (x : ι → E) :
    ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ ≤
      T.summingENorm p * ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x) := by
  rcases eq_or_ne (T.summingENorm p) ∞ with hT | hT
  · rcases eq_or_ne (weakLpNorm (𝕜 := 𝕜) p x) 0 with hx | hx
    · simp [← ofReal_norm, norm_toLp_eq_zero_of_weakLpNorm_eq_zero T hx]
    · rw [hT, ENNReal.top_mul (ENNReal.ofReal_pos.2 ((apply_nonneg _ _).lt_of_ne' hx)).ne']
      exact le_top
  · exact enorm_toLp_le_summingENorm_mul_of_ne_top hT x

/-- The `p`-summing gauge dominates the operator norm. -/
theorem enorm_le_summingENorm (T : E →L[𝕜] F) : ‖T‖ₑ ≤ T.summingENorm p := by
  refine T.opENorm_le_bound fun v ↦ ?_
  have hT : (fun i ↦ T ((Pi.single 0 v : Fin 1 → E) i)) = Pi.single 0 (T v) :=
    funext fun i ↦ Pi.apply_single (fun _ ↦ ⇑T) (fun _ ↦ map_zero T) 0 v i
  have h := enorm_toLp_le_summingENorm_mul (p := p) T (Pi.single (0 : Fin 1) v)
  rwa [hT, weakLpNorm_single, ofReal_norm, PiLp.toLp_single, ← ofReal_norm,
    PiLp.norm_single, ofReal_norm] at h

/-- The gauge vanishes exactly at zero for maps into a separated normed space. -/
@[simp]
theorem summingENorm_eq_zero_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T : E →L[𝕜] F} : T.summingENorm p = 0 ↔ T = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ summingENorm_zero⟩
  have hn : ‖T‖ = 0 := by
    have h0 := congrArg ENNReal.toReal (le_antisymm (h ▸ enorm_le_summingENorm T) bot_le)
    rw [toReal_enorm] at h0
    simpa using h0
  -- Mathlib's `opNorm_zero_iff` requires a normed source; here the source is only seminormed.
  ext v
  exact norm_le_zero_iff.mp (by simpa [hn] using T.le_opNorm v)

/-- The rank-one operator `x ↦ f x • y` has gauge `‖f‖ ‖y‖`. -/
@[simp]
theorem summingENorm_smulRight (f : StrongDual 𝕜 E) (y : F) :
    (f.smulRight y).summingENorm p = ‖f‖ₑ * ‖y‖ₑ := by
  refine le_antisymm (summingENorm_smulRight_le f y) ?_
  calc
    ‖f‖ₑ * ‖y‖ₑ = ‖f.smulRight y‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, norm_smulRight_apply,
        ENNReal.ofReal_mul (norm_nonneg _)]
    _ ≤ _ := enorm_le_summingENorm _

/-- At exponent `∞` the summing gauge is the operator norm. -/
@[simp]
theorem summingENorm_top (T : E →L[𝕜] F) : T.summingENorm ∞ = ‖T‖ₑ := by
  refine le_antisymm ?_ (enorm_le_summingENorm T)
  rw [← ofReal_norm, summingENorm_le_ofReal_iff (norm_nonneg T)]
  intro n x
  rw [weakLpNorm_top]
  exact PiLp.norm_toLp_comp_le (norm_nonneg T) T.le_opNorm x

/-- **Inclusion of summing operators.** The summing gauge decreases as the exponent grows:
`π_q(T) ≤ π_p(T)` for `p ≤ q`. -/
theorem summingENorm_le_summingENorm_of_exponent_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (T : E →L[𝕜] F) : T.summingENorm q ≤ T.summingENorm p := by
  rcases eq_or_ne q ∞ with rfl | hq
  · simpa using enorm_le_summingENorm (p := p) T
  rcases hpq.eq_or_lt with rfl | hpq
  · exact le_rfl
  rcases eq_or_ne (T.summingENorm p) ∞ with hT | hT
  · simp [hT]
  -- Write `P < Q` for the real exponents and `s = P Q / (Q - P)`, so `1 / P = 1 / s + 1 / Q`.
  set P := p.toReal with hPdef
  set Q := q.toReal with hQdef
  have hP : 0 < P := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hpq.ne_top
  have hPQ : P < Q := ENNReal.toReal_strict_mono hq hpq
  have hQ : 0 < Q := hP.trans hPQ
  have hQP : 0 < Q - P := sub_pos.2 hPQ
  have hs : (P * Q / (Q - P)).HolderTriple Q P :=
    ⟨by field_simp; ring, div_pos (mul_pos hP hQ) hQP, hQ⟩
  rw [← ENNReal.ofReal_toReal hT, summingENorm_le_ofReal_iff ENNReal.toReal_nonneg]
  intro n x
  rw [PiLp.norm_eq_sum hQ, ← hQdef]
  set S := ∑ i, ‖T (x i)‖ ^ Q
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ by positivity
  rcases hS0.eq_or_lt with hS | hS
  · rw [← hS, Real.zero_rpow (one_div_pos.2 hQ).ne']
    positivity
  -- Apply the `p`-summing inequality to `cᵢ • xᵢ` with weights `cᵢ = ‖T xᵢ‖ ^ ((Q - P) / P)`.
  let c : Fin n → 𝕜 := fun i ↦ ((‖T (x i)‖ ^ ((Q - P) / P) : ℝ) : 𝕜)
  have hc (i : Fin n) : ‖c i‖ = ‖T (x i)‖ ^ ((Q - P) / P) := by
    simp [c, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hcs : ∑ i, ‖c i‖ ^ (P * Q / (Q - P)) = S := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hc, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  have hTc : ‖WithLp.toLp p (fun i ↦ T (c i • x i))‖ = S ^ (1 / P) := by
    rw [PiLp.norm_eq_sum hP, ← hPdef]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PiLp.toLp_apply, map_smul, norm_smul, hc,
      ← Real.rpow_add_one' (norm_nonneg _) (by positivity),
      ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
    ring
  have key := (norm_toLp_le_toReal_summingENorm_mul hT fun i ↦ c i • x i).trans
    (mul_le_mul_of_nonneg_left (weakLpNorm_smul_le p hs c x) ENNReal.toReal_nonneg)
  rw [hTc, hcs, hs.one_div_eq, Real.rpow_add hS, mul_left_comm] at key
  exact le_of_mul_le_mul_left key (Real.rpow_pos_of_pos hS _)

/-- The `p`-summing gauge is lower semicontinuous for the operator-norm topology. -/
theorem lowerSemicontinuous_summingENorm :
    LowerSemicontinuous (summingENorm p : (E →L[𝕜] F) → ℝ≥0∞) := by
  refine lowerSemicontinuous_iSup fun n ↦ lowerSemicontinuous_iSup fun x ↦ ?_
  rcases eq_or_ne (weakLpNorm (𝕜 := 𝕜) p x) 0 with hx | hx
  · -- Every image of a family of zero weak norm is null, so its ratio vanishes identically.
    have h0 : (fun T : E →L[𝕜] F ↦ ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ /
        ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x)) = fun _ ↦ 0 := by
      funext T
      simp [← ofReal_norm, norm_toLp_eq_zero_of_weakLpNorm_eq_zero T hx]
    rw [h0]
    exact lowerSemicontinuous_const
  · refine Continuous.lowerSemicontinuous ?_
    refine (ENNReal.continuous_div_const _
      (ENNReal.ofReal_pos.2 ((apply_nonneg _ _).lt_of_ne' hx)).ne').comp
      (continuous_enorm.comp ((PiLp.continuous_toLp p _).comp ?_))
    exact continuous_pi fun i ↦ continuous_eval_const (x i)

end RCLike

end ContinuousLinearMap

namespace TauCeti

section NormedField

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  {E F G : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (E F) in
/-- The absolutely `p`-summing operators from `E` to `F`: the bounded operators of finite
`p`-summing gauge. -/
def absolutelySummingOperators : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {T | T.summingENorm p < ∞}
  add_mem' {S T} hS hT :=
    (S.summingENorm_add_le T).trans_lt (ENNReal.add_lt_top.2 ⟨hS, hT⟩)
  zero_mem' := by simp
  smul_mem' c T hT := by
    simpa [ContinuousLinearMap.summingENorm_smul] using ENNReal.mul_lt_top enorm_lt_top hT

variable {𝕜 p}

/-- Membership in the submodule means finite gauge. -/
@[simp]
theorem mem_absolutelySummingOperators {T : E →L[𝕜] F} :
    T ∈ absolutelySummingOperators 𝕜 p E F ↔ T.summingENorm p < ∞ := Iff.rfl

/-- An operator is absolutely `p`-summing iff for some constant `C` the `Lᵖ` norm of `(T xᵢ)ᵢ` is
at most `C * weakLpNorm p x` for every finite family `x`. -/
theorem mem_absolutelySummingOperators_iff {T : E →L[𝕜] F} :
    T ∈ absolutelySummingOperators 𝕜 p E F ↔ ∃ C, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
      ‖WithLp.toLp p (fun i ↦ T (x i))‖ ≤ C * weakLpNorm (𝕜 := 𝕜) p x := by
  rw [mem_absolutelySummingOperators]
  constructor
  · intro hT
    refine ⟨(T.summingENorm p).toReal, ENNReal.toReal_nonneg, ?_⟩
    rw [← ContinuousLinearMap.summingENorm_le_ofReal_iff ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hT.ne]
  · rintro ⟨C, hC, h⟩
    exact ((ContinuousLinearMap.summingENorm_le_ofReal_iff hC).2 h).trans_lt
      ENNReal.ofReal_lt_top

/-- Absolutely summing operators are stable under composition on the left. -/
theorem comp_left_mem_absolutelySummingOperators (A : F →L[𝕜] G) {T : E →L[𝕜] F}
    (hT : T ∈ absolutelySummingOperators 𝕜 p E F) :
    A ∘L T ∈ absolutelySummingOperators 𝕜 p E G :=
  (A.summingENorm_comp_left_le T).trans_lt (ENNReal.mul_lt_top enorm_lt_top hT)

/-- Absolutely summing operators are stable under composition on the right. -/
theorem comp_right_mem_absolutelySummingOperators {T : F →L[𝕜] G}
    (hT : T ∈ absolutelySummingOperators 𝕜 p F G) (B : E →L[𝕜] F) :
    T ∘L B ∈ absolutelySummingOperators 𝕜 p E G :=
  (T.summingENorm_comp_right_le B).trans_lt (ENNReal.mul_lt_top hT enorm_lt_top)

/-- Rank-one operators are absolutely summing. -/
theorem smulRight_mem_absolutelySummingOperators (f : StrongDual 𝕜 E) (y : F) :
    f.smulRight y ∈ absolutelySummingOperators 𝕜 p E F :=
  (ContinuousLinearMap.summingENorm_smulRight_le f y).trans_lt
    (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top)

end NormedField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Absolutely `p`-summing operators are absolutely `q`-summing for `p ≤ q`. -/
theorem absolutelySummingOperators_le_of_exponent_le {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (hpq : p ≤ q) :
    absolutelySummingOperators 𝕜 p E F ≤ absolutelySummingOperators 𝕜 q E F :=
  fun T hT ↦ (T.summingENorm_le_summingENorm_of_exponent_le hpq).trans_lt hT

end RCLike

end TauCeti
