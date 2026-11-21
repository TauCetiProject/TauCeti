/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The `W^{k,p}` size of a function

`TauCeti.eLpNormWkp p U k f μ` is the extended `W^{k,p}(U)` norm of `f : E → F`, for real normed
spaces `E` and `F` and a measure `μ` on `E` (defaulting to `volume`): the `Lᵖ(U)` norm of `f` plus,
recursively, the `W^{k-1,p}(U)` size of its weak derivative on `interior U`, minimized over all
weak derivatives. It is `∞` when no weak derivative exists, or when one of the norms is infinite.
Its derivatives are taken on the interior and its norms on `U` itself, matching
`TauCeti.MemWkpLoc`. On an open set of a finite-dimensional space weak derivatives are unique
almost everywhere, so the minimum is attained by every weak derivative.

This is the quantity in which interior estimates of elliptic equations are stated. The file
supplies its unfolding, its value through a given weak derivative on an open set, the `Lᵖ` and
`W^{k,p}_loc` membership of a function of finite norm and, conversely, the finiteness of the
norm of a `W^{k,p}_loc` function on relatively compact subsets, the extraction of a weak
derivative from a finite successor-order norm, the almost-everywhere vanishing of a function of
zero norm, monotonicity in the set and in the derivative order, invariance under
almost-everywhere change, the triangle inequality (also over finite sums) and the operator-norm
bound under a continuous linear map of the codomain. An upper bound of the form
`a + c ‖f‖_{W^{k+1,p}(U)}` (for finite `c`, with `‖f‖_{W^{k+1,p}(U)}` finite when `c = 0`) may be
checked through each weak derivative of `f` separately.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

universe u v w

/-- Auxiliary recursion for `TauCeti.eLpNormWkp` whose codomain lies in `Type max u v`, so iterated
operator spaces `E →L[ℝ] F` stay in the same universe. -/
private def eLpNormWkpAux {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (p : ℝ≥0∞) (U : Set E) :
    (k : ℕ) → {F : Type max u v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (E → F) → ℝ≥0∞
  | 0, _, _, _, f => eLpNorm f p (μ.restrict U)
  | k + 1, F, _, _, f => eLpNorm f p (μ.restrict U) +
      ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn μ (Opens.interior U) f D),
        eLpNormWkpAux μ p U k D

private theorem eLpNormWkpAux_univ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {k : ℕ}
    {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} :
    eLpNormWkpAux.{u, v} μ p U k f = eLpNormWkpAux.{u, max u v} μ p U k f := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    simp only [eLpNormWkpAux]
    congr 1
    exact iInf_congr fun D => iInf_congr fun _ => ih (F := E →L[ℝ] F) (f := D)

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure E} {p : ℝ≥0∞} {U V : Set E} {k : ℕ} {f g : E → F}

/-- The extended `W^{k,p}(U)` norm: the `Lᵖ(U)` norm of `f` plus the smallest `W^{k-1,p}(U)` norm
of a weak derivative of `f` on `interior U`. It is `∞` when no weak derivative exists. -/
def eLpNormWkp (p : ℝ≥0∞) (U : Set E) (k : ℕ) (f : E → F)
    (μ : Measure E := by volume_tac) : ℝ≥0∞ :=
  match k with
  | 0 => eLpNorm f p (μ.restrict U)
  | k + 1 => eLpNorm f p (μ.restrict U) +
      ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn μ (Opens.interior U) f D),
        eLpNormWkpAux.{u, v} μ p U k D

private theorem eLpNormWkp_eq_aux {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} :
    eLpNormWkp.{u, max u v} p U k f μ = eLpNormWkpAux.{u, v} μ p U k f := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [eLpNormWkp, eLpNormWkpAux]
    congr 1
    exact iInf_congr fun _ => iInf_congr fun _ => (eLpNormWkpAux_univ.{u, v}).symm

/-- At order zero the `W^{k,p}` norm is the `Lᵖ` norm. -/
@[simp]
theorem eLpNormWkp_zero : eLpNormWkp p U 0 f μ = eLpNorm f p (μ.restrict U) := by rfl

/-- The successor-order unfolding of the `W^{k,p}` norm. -/
theorem eLpNormWkp_succ : eLpNormWkp p U (k + 1) f μ = eLpNorm f p (μ.restrict U) +
    ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn μ (Opens.interior U) f D),
      eLpNormWkp p U k D μ := by
  simp only [eLpNormWkp]
  congr 1
  exact iInf_congr fun _ => iInf_congr fun _ => (eLpNormWkp_eq_aux.{u, v}).symm

/-- The `Lᵖ` norm is bounded by every `W^{k,p}` norm. -/
theorem eLpNorm_le_eLpNormWkp : eLpNorm f p (μ.restrict U) ≤ eLpNormWkp p U k f μ := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_self_add

/-- A function of finite `W^{k,p}` norm is `Lᵖ` on the set. -/
theorem memLp_of_eLpNormWkp_ne_top (hf : eLpNormWkp p U k f μ ≠ ∞) :
    MemLp f p (μ.restrict U) :=
  memLp_iff.2 (eLpNorm_le_eLpNormWkp.trans_lt (lt_top_iff_ne_top.2 hf))

/-- A function of zero `W^{k,p}` norm vanishes almost everywhere on the set. -/
theorem ae_eq_zero_of_eLpNormWkp_eq_zero (hp : p ≠ 0) (hf : eLpNormWkp p U k f μ = 0) :
    f =ᵐ[μ.restrict U] 0 :=
  (eLpNorm_eq_zero_iff hp).1 (le_antisymm (hf ▸ eLpNorm_le_eLpNormWkp) zero_le)

/-- Any weak derivative bounds the successor-order norm. -/
theorem eLpNormWkp_succ_le {D : E → E →L[ℝ] F}
    (hD : HasWeakFDerivOn μ (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f μ ≤ eLpNorm f p (μ.restrict U) + eLpNormWkp p U k D μ := by
  rw [eLpNormWkp_succ]
  gcongr
  exact iInf₂_le D hD

private theorem eLpNormWkp_mono_set_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hVU : V ⊆ U) :
    eLpNormWkp p V k f μ ≤ eLpNormWkp p U k f μ := by
  induction k generalizing F with
  | zero => exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr ?_ + ?_
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
    · exact le_iInf₂ fun D hD => iInf₂_le_of_le D (hD.mono (interior_mono hVU)) ih

/-- The `W^{k,p}` norm increases with the set. -/
theorem eLpNormWkp_mono_set (hVU : V ⊆ U) : eLpNormWkp p V k f μ ≤ eLpNormWkp p U k f μ := by
  cases k with
  | zero => exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  | succ k =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr ?_ + ?_
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
    · exact le_iInf₂ fun D hD =>
        iInf₂_le_of_le D (hD.mono (interior_mono hVU)) (eLpNormWkp_mono_set_max hVU)

private theorem eLpNormWkp_mono_order_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {l : ℕ} (hlk : l ≤ k) :
    eLpNormWkp p U l f μ ≤ eLpNormWkp p U k f μ := by
  induction l generalizing k F with
  | zero => exact eLpNorm_le_eLpNormWkp.trans_eq' eLpNormWkp_zero.symm
  | succ l ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr
    exact ih (by omega)

/-- The `W^{k,p}(U)` norm increases with the derivative order. -/
theorem eLpNormWkp_mono_order {l : ℕ} (hlk : l ≤ k) :
    eLpNormWkp p U l f μ ≤ eLpNormWkp p U k f μ := by
  cases l with
  | zero => exact eLpNorm_le_eLpNormWkp.trans_eq' eLpNormWkp_zero.symm
  | succ l =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr
    exact eLpNormWkp_mono_order_max (by omega)

/-- Almost-everywhere equality on `U` preserves the `W^{k,p}(U)` norm. -/
theorem eLpNormWkp_congr_ae (hfg : f =ᵐ[μ.restrict U] g) :
    eLpNormWkp p U k f μ = eLpNormWkp p U k g μ := by
  cases k with
  | zero => exact eLpNorm_congr_ae hfg
  | succ k =>
    have hint : f =ᵐ[μ.restrict (Opens.interior U)] g :=
      ae_mono (Measure.restrict_mono_set μ interior_subset) hfg
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNorm_congr_ae hfg]
    congr 1
    refine le_antisymm (le_iInf₂ fun D hD => iInf₂_le_of_le D ?_ le_rfl)
      (le_iInf₂ fun D hD => iInf₂_le_of_le D ?_ le_rfl)
    · exact hD.congr_ae (Filter.EventuallyEq.symm hint)
    · exact hD.congr_ae hint

/-- On an open set of a finite-dimensional space, every weak derivative realizes the
successor-order norm. -/
theorem eLpNormWkp_succ_eq_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    {Ω : Opens E} {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω f D) :
    eLpNormWkp p Ω (k + 1) f μ = eLpNorm f p (μ.restrict Ω) + eLpNormWkp p Ω k D μ := by
  refine le_antisymm (eLpNormWkp_succ_le (by rwa [Opens.interior_coe])) ?_
  rw [eLpNormWkp_succ, Opens.interior_coe]
  gcongr
  exact le_iInf₂ fun D' hD' => (eLpNormWkp_congr_ae (hD.ae_eq hD')).le

/-- A finite successor-order norm provides a weak derivative on the interior of finite norm of
the previous order. -/
theorem exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top (hf : eLpNormWkp p U (k + 1) f μ ≠ ∞) :
    ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn μ (Opens.interior U) f D ∧ eLpNormWkp p U k D μ ≠ ∞ := by
  rw [eLpNormWkp_succ, ENNReal.add_ne_top] at hf
  obtain ⟨D, hD, hlt⟩ : ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn μ (Opens.interior U) f D ∧ eLpNormWkp p U k D μ < ∞ := by
    simpa [iInf_lt_iff, lt_top_iff_ne_top] using hf.2
  exact ⟨D, hD, hlt.ne⟩

/-- Let `c ≠ ∞`, and if `c = 0` let `f` have finite `W^{k+1,p}(U)` norm. To bound `b` by
`a + c ‖f‖_{W^{k+1,p}(U)}` it suffices to bound it by `a + c (‖f‖_{Lᵖ(U)} + ‖D‖_{W^{k,p}(U)})`
for every weak derivative `D` of `f` on `interior U` of finite `W^{k,p}(U)` norm. -/
theorem le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn {a b c : ℝ≥0∞}
    (hc : c ≠ ∞) (hf : c = 0 → eLpNormWkp p U (k + 1) f μ ≠ ∞)
    (H : ∀ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D →
      eLpNormWkp p U k D μ ≠ ∞ →
        b ≤ a + c * (eLpNorm f p (μ.restrict U) + eLpNormWkp p U k D μ)) :
    b ≤ a + c * eLpNormWkp p U (k + 1) f μ := by
  rcases eq_or_ne c 0 with rfl | hc0
  · obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top (hf rfl)
    simpa using H D hD hDk
  calc b
      ≤ ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn μ (Opens.interior U) f D),
          a + c * (eLpNorm f p (μ.restrict U) + eLpNormWkp p U k D μ) :=
        le_iInf₂ fun D hD => by
          by_cases hDk : eLpNormWkp p U k D μ = ∞
          · rw [hDk, add_top, ENNReal.mul_top hc0, add_top]
            exact le_top
          · exact H D hD hDk
    _ = a + c * eLpNormWkp p U (k + 1) f μ := by
        rw [eLpNormWkp_succ]
        simp only [ENNReal.add_iInf, ENNReal.mul_iInf_of_ne hc0 hc]

private theorem memWkpLoc_of_eLpNormWkp_ne_top_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : eLpNormWkp p U k f μ ≠ ∞) : MemWkpLoc p U k f μ := by
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 (memLp_of_eLpNormWkp_ne_top hf).memLpLoc
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
    exact memWkpLoc_succ_iff.2 ⟨(memLp_of_eLpNormWkp_ne_top hf).memLpLoc, D, hD, ih hDk⟩

/-- A function of finite `W^{k,p}` norm lies in the local Sobolev class `W^{k,p}_loc`. -/
theorem memWkpLoc_of_eLpNormWkp_ne_top (hf : eLpNormWkp p U k f μ ≠ ∞) : MemWkpLoc p U k f μ := by
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 (memLp_of_eLpNormWkp_ne_top hf).memLpLoc
  | succ k =>
    obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
    exact memWkpLoc_succ_iff.2
      ⟨(memLp_of_eLpNormWkp_ne_top hf).memLpLoc, D, hD, memWkpLoc_of_eLpNormWkp_ne_top_max hDk⟩

/-- On an open set of a finite-dimensional space, a finite successor-order norm is realized by a
weak derivative of finite norm of the previous order. -/
theorem exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top [FiniteDimensional ℝ E] [BorelSpace E]
    {Ω : Opens E} (hf : eLpNormWkp p Ω (k + 1) f μ ≠ ∞) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ eLpNormWkp p Ω k D μ ≠ ∞ ∧
      eLpNormWkp p Ω (k + 1) f μ = eLpNorm f p (μ.restrict Ω) + eLpNormWkp p Ω k D μ := by
  obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
  rw [Opens.interior_coe] at hD
  exact ⟨D, hD, hDk, eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD⟩

private theorem eLpNormWkp_ne_top_of_isCompact_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : MemWkpLoc p U k f μ) {K : Set E}
    (hKU : K ⊆ U) (hK : IsCompact K) : eLpNormWkp p K k f μ ≠ ∞ := by
  induction k generalizing F with
  | zero => exact (memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := hf.exists_weakFDeriv
    refine ne_top_of_le_ne_top ?_ (eLpNormWkp_succ_le (hD.mono (interior_mono hKU)))
    exact ENNReal.add_ne_top.2 ⟨(memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top, ih hDk⟩

/-- A local Sobolev function has finite `W^{k,p}` norm on every compact subset of its domain. -/
theorem MemWkpLoc.eLpNormWkp_ne_top_of_isCompact (hf : MemWkpLoc p U k f μ) {K : Set E}
    (hKU : K ⊆ U) (hK : IsCompact K) : eLpNormWkp p K k f μ ≠ ∞ := by
  cases k with
  | zero => exact (memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top
  | succ k =>
    obtain ⟨D, hD, hDk⟩ := hf.exists_weakFDeriv
    refine ne_top_of_le_ne_top ?_ (eLpNormWkp_succ_le (hD.mono (interior_mono hKU)))
    exact ENNReal.add_ne_top.2 ⟨(memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top,
      eLpNormWkp_ne_top_of_isCompact_max hDk hKU hK⟩

/-- A local Sobolev function has finite `W^{k,p}` norm on every set whose closure is compact and
contained in its domain. -/
theorem MemWkpLoc.eLpNormWkp_ne_top_of_closure_subset (hf : MemWkpLoc p U k f μ)
    (hV : IsCompact (closure V)) (hVU : closure V ⊆ U) : eLpNormWkp p V k f μ ≠ ∞ :=
  ne_top_of_le_ne_top (hf.eLpNormWkp_ne_top_of_isCompact hVU hV)
    (eLpNormWkp_mono_set subset_closure)

private theorem eLpNormWkp_zero_fun_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] : eLpNormWkp p U k (0 : E → F) μ = 0 := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    refine le_antisymm ((eLpNormWkp_succ_le hasWeakFDerivOn_zero).trans ?_) zero_le
    simp [ih]

/-- The zero function has zero `W^{k,p}` norm. -/
@[simp]
theorem eLpNormWkp_zero_fun [CompleteSpace F] : eLpNormWkp p U k (0 : E → F) μ = 0 := by
  cases k with
  | zero => simp
  | succ k =>
    refine le_antisymm ((eLpNormWkp_succ_le hasWeakFDerivOn_zero).trans ?_) zero_le
    rw [eLpNormWkp_zero_fun_max (F := E →L[ℝ] F)]
    simp

private theorem eLpNormWkp_add_le_max [OpensMeasurableSpace E] {F : Type max u v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} (hp : 1 ≤ p) :
    eLpNormWkp p U k (f + g) μ ≤ eLpNormWkp p U k f μ + eLpNormWkp p U k g μ := by
  induction k generalizing F with
  | zero => exact eLpNorm_add_le hp
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNormWkp_succ, add_add_add_comm]
    gcongr ?_ + ?_
    · exact eLpNorm_add_le hp
    · exact ENNReal.le_iInf_add_iInf fun D D' => ENNReal.le_iInf_add_iInf fun hD hD' =>
        iInf₂_le_of_le (D + D') (hD.add hD') ih

/-- The triangle inequality for the `W^{k,p}` norm. -/
theorem eLpNormWkp_add_le [OpensMeasurableSpace E] (hp : 1 ≤ p) :
    eLpNormWkp p U k (f + g) μ ≤ eLpNormWkp p U k f μ + eLpNormWkp p U k g μ := by
  cases k with
  | zero => exact eLpNorm_add_le hp
  | succ k =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNormWkp_succ, add_add_add_comm]
    gcongr ?_ + ?_
    · exact eLpNorm_add_le hp
    · exact ENNReal.le_iInf_add_iInf fun D D' => ENNReal.le_iInf_add_iInf fun hD hD' =>
        iInf₂_le_of_le (D + D') (hD.add hD') (eLpNormWkp_add_le_max hp)

/-- The triangle inequality for the `W^{k,p}` norm over a finite sum. -/
theorem eLpNormWkp_sum_le [OpensMeasurableSpace E] [CompleteSpace F] {ι : Type*}
    {s : Finset ι} {u : ι → E → F} (hp : 1 ≤ p) :
    eLpNormWkp p U k (∑ i ∈ s, u i) μ ≤ ∑ i ∈ s, eLpNormWkp p U k (u i) μ :=
  Finset.le_sum_of_subadditive (fun u : E → F ↦ eLpNormWkp p U k u μ) eLpNormWkp_zero_fun.le
    (fun _ _ ↦ eLpNormWkp_add_le hp) s u

private theorem eLpNormWkp_clm_comp_le_max [OpensMeasurableSpace E] {F : Type max u v}
    {G : Type max u w} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {f : E → F} (A : F →L[ℝ] G) :
    eLpNormWkp p U k (fun z => A (f z)) μ ≤ ‖A‖ₑ * eLpNormWkp p U k f μ := by
  induction k generalizing F G with
  | zero => exact MeasureTheory.eLpNorm_clm_comp_le A
  | succ k ih =>
    by_cases hA : A = 0
    · subst hA
      have h0 : (fun z => (0 : F →L[ℝ] G) (f z)) = (0 : E → G) := rfl
      rw [h0, eLpNormWkp_zero_fun]
      exact zero_le
    have hA₀ : ‖A‖ₑ ≠ 0 := by
      rw [eNorm_eq_nnNorm]; exact ENNReal.coe_ne_zero.2 (nnNorm_ne_zero_iff.2 hA)
    have hA_top : ‖A‖ₑ ≠ ⊤ := eNorm_ne_top
    rw [eLpNormWkp_succ, eLpNormWkp_succ, mul_add]
    gcongr ?_ + ?_
    · exact MeasureTheory.eLpNorm_clm_comp_le A
    · rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
      refine le_iInf fun D => ?_
      rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
      refine le_iInf fun hD => iInf₂_le_of_le _ (hD.clm_comp A) ?_
      refine (ih (ContinuousLinearMap.compL ℝ E F G A)).trans ?_
      gcongr
      have hle : ‖ContinuousLinearMap.compL ℝ E F G A‖ ≤ ‖A‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun B => A.opNorm_comp_le B
      exact eNorm_le_iff_norm_le.2 hle

/-- A continuous linear map of the codomain scales the `W^{k,p}` norm by at most its operator
norm. -/
theorem eLpNormWkp_clm_comp_le [OpensMeasurableSpace E] [CompleteSpace G] (A : F →L[ℝ] G) :
    eLpNormWkp p U k (fun z => A (f z)) μ ≤ ‖A‖ₑ * eLpNormWkp p U k f μ := by
  cases k with
  | zero => exact MeasureTheory.eLpNorm_clm_comp_le A
  | succ k =>
    by_cases hA : A = 0
    · subst hA
      have h0 : (fun z => (0 : F →L[ℝ] G) (f z)) = (0 : E → G) := rfl
      rw [h0, eLpNormWkp_zero_fun]
      exact zero_le
    have hA₀ : ‖A‖ₑ ≠ 0 := by
      rw [eNorm_eq_nnNorm]; exact ENNReal.coe_ne_zero.2 (nnNorm_ne_zero_iff.2 hA)
    have hA_top : ‖A‖ₑ ≠ ⊤ := eNorm_ne_top
    rw [eLpNormWkp_succ, eLpNormWkp_succ, mul_add]
    gcongr ?_ + ?_
    · exact MeasureTheory.eLpNorm_clm_comp_le A
    · rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
      refine le_iInf fun D => ?_
      rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
      refine le_iInf fun hD => iInf₂_le_of_le _ (hD.clm_comp A) ?_
      refine (eLpNormWkp_clm_comp_le_max (ContinuousLinearMap.compL ℝ E F G A)).trans ?_
      gcongr
      have hle : ‖ContinuousLinearMap.compL ℝ E F G A‖ ≤ ‖A‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun B => A.opNorm_comp_le B
      exact eNorm_le_iff_norm_le.2 hle

end TauCeti
