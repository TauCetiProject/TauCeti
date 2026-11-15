/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The `W^{k,p}` size of a function on a subset of a normed space

`TauCeti.eLpNormWkp p U k f` is the extended `W^{k,p}(U)` norm of `f : E → F`, for real normed
spaces `E` and `F`: the `Lᵖ(U)` norm of `f` plus, recursively, the `W^{k-1,p}(U)` size of its weak
derivative on `interior U`, minimized over all weak derivatives. It is `∞` when no weak
derivative exists, or when one of the norms is infinite. Its derivatives are taken on the
interior and its norms on `U` itself, matching `TauCeti.MemWkpLoc`. On an open subset of a
finite-dimensional `E` with Borel measure, weak derivatives are unique almost everywhere, so the
minimum is attained by every weak derivative.

This is the quantity in which interior estimates of elliptic equations are stated. The file
supplies its unfolding, its value through a given weak derivative on an open set, the `Lᵖ` and
`W^{k,p}_loc` membership of a function of finite norm and, conversely, the finiteness of the
norm of a `W^{k,p}_loc` function on relatively compact subsets, the extraction of a weak
derivative from a finite successor-order norm, the almost-everywhere vanishing of a function of
zero norm, monotonicity in the set and in the derivative order, invariance under
almost-everywhere change, the triangle inequality and the operator-norm bound under a continuous
linear map of the codomain. An upper bound of the form `a + c ‖f‖_{W^{k+1,p}(U)}` (for finite
`c`, with `‖f‖_{W^{k+1,p}(U)}` finite when `c = 0`) may be checked through each weak derivative
of `f` separately.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

private def eLpNormWkpAux.{u, w} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] (p : ℝ≥0∞) (U : Set E) :
    (k : ℕ) → {F : Type (max u w)} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (E → F) → ℝ≥0∞
  | 0, _, _, _, f => eLpNorm f p (volume.restrict U)
  | k + 1, F, _, _, f => eLpNorm f p (volume.restrict U) +
      ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
        eLpNormWkpAux p U k D

/-- The extended `W^{k,p}(U)` norm: the `Lᵖ(U)` norm of `f` plus the smallest `W^{k-1,p}(U)` norm
of a weak derivative of `f` on `interior U`. It is `∞` when no weak derivative exists. -/
def eLpNormWkp.{u, v} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    (p : ℝ≥0∞) (U : Set E) :
    (k : ℕ) → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (E → F) → ℝ≥0∞
  | 0, _, _, _, f => eLpNorm f p (volume.restrict U)
  | k + 1, F, _, _, f => eLpNorm f p (volume.restrict U) +
      ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
        eLpNormWkpAux.{u, max u v} p U k D

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p : ℝ≥0∞} {U V : Set E} {k : ℕ} {f g : E → F}

/-- At order zero the `W^{k,p}` norm is the `Lᵖ` norm. -/
@[simp]
theorem eLpNormWkp_zero : eLpNormWkp p U 0 f = eLpNorm f p (volume.restrict U) := by
  unfold eLpNormWkp; rfl

/-- The successor-order unfolding of the `W^{k,p}` norm. -/
theorem eLpNormWkp_succ : eLpNormWkp p U (k + 1) f = eLpNorm f p (volume.restrict U) +
    ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
      eLpNormWkp p U k D := by
  cases k <;> rfl

/-- The `Lᵖ` norm is bounded by every `W^{k,p}` norm. -/
theorem eLpNorm_le_eLpNormWkp : eLpNorm f p (volume.restrict U) ≤ eLpNormWkp p U k f := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_self_add

/-- A function of finite `W^{k,p}` norm is `Lᵖ` on the set. -/
theorem memLp_of_eLpNormWkp_ne_top (hf : eLpNormWkp p U k f ≠ ∞) :
    MemLp f p (volume.restrict U) :=
  memLp_iff.2 (eLpNorm_le_eLpNormWkp.trans_lt (lt_top_iff_ne_top.2 hf))

/-- A function of zero `W^{k,p}` norm vanishes almost everywhere on the set. -/
theorem ae_eq_zero_of_eLpNormWkp_eq_zero (hp : p ≠ 0) (hf : eLpNormWkp p U k f = 0) :
    f =ᵐ[volume.restrict U] 0 :=
  (eLpNorm_eq_zero_iff hp).1 (le_antisymm (hf ▸ eLpNorm_le_eLpNormWkp) zero_le)

/-- Any weak derivative bounds the successor-order norm. -/
theorem eLpNormWkp_succ_le {D : E → E →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f ≤ eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D := by
  rw [eLpNormWkp_succ]
  gcongr
  exact iInf₂_le D hD

private theorem eLpNormWkp_mono_set_aux.{u, w} {E : Type u} {F : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U V : Set E} {k : ℕ} {f : E → F}
    (hVU : V ⊆ U) : eLpNormWkp p V k f ≤ eLpNormWkp p U k f := by
  induction k generalizing F with
  | zero => exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr ?_ + ?_
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
    · exact le_iInf₂ fun D hD => iInf₂_le_of_le D (hD.mono (interior_mono hVU)) ih

/-- The `W^{k,p}` norm increases with the set. -/
theorem eLpNormWkp_mono_set (hVU : V ⊆ U) : eLpNormWkp p V k f ≤ eLpNormWkp p U k f := by
  cases k with
  | zero => exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  | succ k =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr ?_ + ?_
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
    · exact le_iInf₂ fun D hD =>
        iInf₂_le_of_le D (hD.mono (interior_mono hVU)) (eLpNormWkp_mono_set_aux hVU)

private theorem eLpNormWkp_mono_order_aux.{u, w} {E : Type u} {F : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {l k : ℕ} {f : E → F}
    (hlk : l ≤ k) : eLpNormWkp p U l f ≤ eLpNormWkp p U k f := by
  induction l generalizing k F with
  | zero => exact eLpNorm_le_eLpNormWkp.trans_eq' eLpNormWkp_zero.symm
  | succ l ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr
    exact ih (by omega)

/-- The `W^{k,p}(U)` norm increases with the derivative order. -/
theorem eLpNormWkp_mono_order {l : ℕ} (hlk : l ≤ k) :
    eLpNormWkp p U l f ≤ eLpNormWkp p U k f := by
  cases l with
  | zero => exact eLpNorm_le_eLpNormWkp.trans_eq' eLpNormWkp_zero.symm
  | succ l =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr
    exact eLpNormWkp_mono_order_aux (by omega)

/-- Almost-everywhere equality on `U` preserves the `W^{k,p}(U)` norm. -/
theorem eLpNormWkp_congr_ae (hfg : f =ᵐ[volume.restrict U] g) :
    eLpNormWkp p U k f = eLpNormWkp p U k g := by
  cases k with
  | zero => exact eLpNorm_congr_ae hfg
  | succ k =>
    have hint : f =ᵐ[volume.restrict (Opens.interior U)] g :=
      ae_mono (Measure.restrict_mono_set volume interior_subset) hfg
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNorm_congr_ae hfg]
    congr 1
    refine le_antisymm (le_iInf₂ fun D hD => iInf₂_le_of_le D ?_ le_rfl)
      (le_iInf₂ fun D hD => iInf₂_le_of_le D ?_ le_rfl)
    · exact hD.congr_ae (Filter.EventuallyEq.symm hint)
    · exact hD.congr_ae hint

/-- On an open set, every weak derivative realizes the successor-order norm. -/
theorem eLpNormWkp_succ_eq_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    {Ω : Opens E} {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) :
    eLpNormWkp p Ω (k + 1) f = eLpNorm f p (volume.restrict Ω) + eLpNormWkp p Ω k D := by
  refine le_antisymm (eLpNormWkp_succ_le (by rwa [Opens.interior_coe])) ?_
  rw [eLpNormWkp_succ, Opens.interior_coe]
  gcongr
  exact le_iInf₂ fun D' hD' => (eLpNormWkp_congr_ae (hD.ae_eq hD')).le

/-- A finite successor-order norm provides a weak derivative on the interior of finite norm of
the previous order. -/
theorem exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top (hf : eLpNormWkp p U (k + 1) f ≠ ∞) :
    ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn volume (Opens.interior U) f D ∧ eLpNormWkp p U k D ≠ ∞ := by
  rw [eLpNormWkp_succ, ENNReal.add_ne_top] at hf
  obtain ⟨D, hD, hlt⟩ : ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn volume (Opens.interior U) f D ∧ eLpNormWkp p U k D < ∞ := by
    simpa [iInf_lt_iff, lt_top_iff_ne_top] using hf.2
  exact ⟨D, hD, hlt.ne⟩

/-- Let `c ≠ ∞`, and if `c = 0` let `f` have finite `W^{k+1,p}(U)` norm. To bound `b` by
`a + c ‖f‖_{W^{k+1,p}(U)}` it suffices to bound it by `a + c (‖f‖_{Lᵖ(U)} + ‖D‖_{W^{k,p}(U)})`
for every weak derivative `D` of `f` on `interior U` of finite `W^{k,p}(U)` norm. -/
theorem le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn {a b c : ℝ≥0∞}
    (hc : c ≠ ∞) (hf : c = 0 → eLpNormWkp p U (k + 1) f ≠ ∞)
    (H : ∀ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D →
      eLpNormWkp p U k D ≠ ∞ →
        b ≤ a + c * (eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D)) :
    b ≤ a + c * eLpNormWkp p U (k + 1) f := by
  rcases eq_or_ne c 0 with rfl | hc0
  · obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top (hf rfl)
    simpa using H D hD hDk
  calc b
      ≤ ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
          a + c * (eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D) :=
        le_iInf₂ fun D hD => by
          by_cases hDk : eLpNormWkp p U k D = ∞
          · rw [hDk, add_top, ENNReal.mul_top hc0, add_top]
            exact le_top
          · exact H D hD hDk
    _ = a + c * eLpNormWkp p U (k + 1) f := by
        rw [eLpNormWkp_succ]
        simp only [ENNReal.add_iInf, ENNReal.mul_iInf_of_ne hc0 hc]

private theorem memWkpLoc_of_eLpNormWkp_ne_top_aux.{u, w} {E : Type u} {F : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F}
    (hf : eLpNormWkp p U k f ≠ ∞) : MemWkpLoc p U k f := by
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 (memLp_of_eLpNormWkp_ne_top hf).memLpLoc
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
    exact memWkpLoc_succ_iff.2 ⟨(memLp_of_eLpNormWkp_ne_top hf).memLpLoc, D, hD, ih hDk⟩

/-- A function of finite `W^{k,p}` norm lies in the local Sobolev class `W^{k,p}_loc`. -/
theorem memWkpLoc_of_eLpNormWkp_ne_top (hf : eLpNormWkp p U k f ≠ ∞) : MemWkpLoc p U k f := by
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 (memLp_of_eLpNormWkp_ne_top hf).memLpLoc
  | succ k =>
    obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
    exact memWkpLoc_succ_iff.2 ⟨(memLp_of_eLpNormWkp_ne_top hf).memLpLoc, D, hD,
      memWkpLoc_of_eLpNormWkp_ne_top_aux hDk⟩

/-- On an open set, a finite successor-order norm is realized by a weak derivative of finite norm
of the previous order. -/
theorem exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top [FiniteDimensional ℝ E] [BorelSpace E]
    {Ω : Opens E} (hf : eLpNormWkp p Ω (k + 1) f ≠ ∞) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ eLpNormWkp p Ω k D ≠ ∞ ∧
      eLpNormWkp p Ω (k + 1) f = eLpNorm f p (volume.restrict Ω) + eLpNormWkp p Ω k D := by
  obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
  rw [Opens.interior_coe] at hD
  exact ⟨D, hD, hDk, eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD⟩

private theorem eLpNormWkp_ne_top_of_isCompact_aux.{u, w} {E : Type u} {F : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U K : Set E} {k : ℕ} {f : E → F}
    (hf : MemWkpLoc p U k f) (hKU : K ⊆ U) (hK : IsCompact K) : eLpNormWkp p K k f ≠ ∞ := by
  induction k generalizing F with
  | zero => exact (memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := hf.exists_weakFDeriv
    refine ne_top_of_le_ne_top ?_ (eLpNormWkp_succ_le (hD.mono (interior_mono hKU)))
    exact ENNReal.add_ne_top.2 ⟨(memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top, ih hDk⟩

/-- A local Sobolev function has finite `W^{k,p}` norm on every compact subset of its domain. -/
theorem MemWkpLoc.eLpNormWkp_ne_top_of_isCompact (hf : MemWkpLoc p U k f) {K : Set E}
    (hKU : K ⊆ U) (hK : IsCompact K) : eLpNormWkp p K k f ≠ ∞ := by
  cases k with
  | zero => exact (memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top
  | succ k =>
    obtain ⟨D, hD, hDk⟩ := hf.exists_weakFDeriv
    refine ne_top_of_le_ne_top ?_ (eLpNormWkp_succ_le (hD.mono (interior_mono hKU)))
    exact ENNReal.add_ne_top.2 ⟨(memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top,
      eLpNormWkp_ne_top_of_isCompact_aux hDk hKU hK⟩

/-- A local Sobolev function has finite `W^{k,p}` norm on every set whose closure is compact and
contained in its domain. -/
theorem MemWkpLoc.eLpNormWkp_ne_top_of_closure_subset (hf : MemWkpLoc p U k f)
    (hV : IsCompact (closure V)) (hVU : closure V ⊆ U) : eLpNormWkp p V k f ≠ ∞ :=
  ne_top_of_le_ne_top (hf.eLpNormWkp_ne_top_of_isCompact hVU hV)
    (eLpNormWkp_mono_set subset_closure)

private theorem eLpNormWkp_zero_fun_aux.{u, w} {E : Type u} {F : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ℝ≥0∞} {U : Set E} {k : ℕ} : eLpNormWkp p U k (0 : E → F) = 0 := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    refine le_antisymm ((eLpNormWkp_succ_le hasWeakFDerivOn_zero).trans ?_) zero_le
    simp [ih]

/-- The zero function has zero `W^{k,p}` norm. -/
@[simp]
theorem eLpNormWkp_zero_fun.{u, v} {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ℝ≥0∞} {U : Set E} {k : ℕ} : eLpNormWkp p U k (0 : E → F) = 0 := by
  cases k with
  | zero => simp
  | succ k =>
    refine le_antisymm ((eLpNormWkp_succ_le (f := (0 : E → F)) hasWeakFDerivOn_zero).trans ?_)
      zero_le
    rw [eLpNorm_zero, zero_add]
    exact (eLpNormWkp_zero_fun_aux.{u, v} (E := E) (F := E →L[ℝ] F)).le

private theorem eLpNormWkp_add_le_aux.{u, w} {E : Type u} {F : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f g : E → F}
    (hp : 1 ≤ p) : eLpNormWkp p U k (f + g) ≤ eLpNormWkp p U k f + eLpNormWkp p U k g := by
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
    eLpNormWkp p U k (f + g) ≤ eLpNormWkp p U k f + eLpNormWkp p U k g := by
  cases k with
  | zero => exact eLpNorm_add_le hp
  | succ k =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNormWkp_succ, add_add_add_comm]
    gcongr ?_ + ?_
    · exact eLpNorm_add_le hp
    · exact ENNReal.le_iInf_add_iInf fun D D' => ENNReal.le_iInf_add_iInf fun hD hD' =>
        iInf₂_le_of_le (D + D') (hD.add hD') (eLpNormWkp_add_le_aux hp)

private theorem eLpNormWkp_clm_comp_le_aux.{u, w} {E : Type u} {F G : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} (A : F →L[ℝ] G) :
    eLpNormWkp p U k (fun z => A (f z)) ≤ ‖A‖ₑ * eLpNormWkp p U k f := by
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

private theorem eLpNorm_linearIsometryEquiv_le {α F' G' : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {μ : Measure α} {p : ℝ≥0∞} {f : α → F'} (e : F' ≃ₗᵢ[ℝ] G') :
    eLpNorm (fun x => e (f x)) p μ ≤ eLpNorm f p μ := by
  refine (MeasureTheory.eLpNorm_clm_comp_le e.toLinearIsometry.toContinuousLinearMap).trans
    (mul_le_of_le_one_left' ?_)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 e.toLinearIsometry.norm_toContinuousLinearMap_le

private theorem eLpNorm_linearIsometryEquiv {α F' G' : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {μ : Measure α} {p : ℝ≥0∞} {f : α → F'} (e : F' ≃ₗᵢ[ℝ] G') :
    eLpNorm (fun x => e (f x)) p μ = eLpNorm f p μ := by
  refine le_antisymm (eLpNorm_linearIsometryEquiv_le e) ?_
  simpa using eLpNorm_linearIsometryEquiv_le (f := fun x => e (f x)) e.symm

private theorem eLpNormWkp_linearIsometryEquiv_aux.{u, w} {E : Type u} {F G : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} (e : F ≃ₗᵢ[ℝ] G) :
    eLpNormWkp p U k (fun z => e (f z)) = eLpNormWkp p U k f := by
  cases k with
  | zero => exact eLpNorm_linearIsometryEquiv e
  | succ k =>
    by_cases hF : CompleteSpace F
    · have : CompleteSpace G :=
        (e.toContinuousLinearEquiv.isUniformEmbedding.isUniformInducing.completeSpace_congr
          e.surjective).mp hF
      let eL : F →L[ℝ] G := e.toLinearIsometry.toContinuousLinearMap
      let eSymmL : G →L[ℝ] F := e.symm.toLinearIsometry.toContinuousLinearMap
      have heL : ‖eL‖ₑ ≤ 1 := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_one.2 e.toLinearIsometry.norm_toContinuousLinearMap_le
      have heSymmL : ‖eSymmL‖ₑ ≤ 1 := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_one.2 e.symm.toLinearIsometry.norm_toContinuousLinearMap_le
      refine le_antisymm ((eLpNormWkp_clm_comp_le_aux eL).trans (mul_le_of_le_one_left' heL)) ?_
      have heq : f = fun z => eSymmL (e (f z)) := by ext z; simp [eSymmL]
      exact (le_of_eq (congrArg (eLpNormWkp p U (k + 1)) heq)).trans
        ((eLpNormWkp_clm_comp_le_aux eSymmL).trans (mul_le_of_le_one_left' heSymmL))
    · have hG : ¬ CompleteSpace G := fun hGc => hF <|
        (e.toContinuousLinearEquiv.isUniformEmbedding.isUniformInducing.completeSpace_congr
          e.surjective).mpr hGc
      have htopF : ∀ D : E → E →L[ℝ] F, ¬ HasWeakFDerivOn volume (Opens.interior U) f D :=
        fun _ hD => hF hD.completeSpace
      have htopG : ∀ D : E → E →L[ℝ] G,
          ¬ HasWeakFDerivOn volume (Opens.interior U) (fun z => e (f z)) D :=
        fun _ hD => hG hD.completeSpace
      simp [eLpNormWkp_succ, htopF, htopG]

private def uliftCLMLIE.{u, v, w} (E : Type u) (F : Type v) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (E →L[ℝ] ULift.{w, v} F) ≃ₗᵢ[ℝ] ULift.{w, max u v} (E →L[ℝ] F) :=
  let eF : ULift.{w, v} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  let eFL := eF.toLinearIsometry.toContinuousLinearMap
  let eOut : ULift.{w, max u v} (E →L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] F) :=
    LinearIsometryEquiv.ulift ℝ (E →L[ℝ] F)
  { ((ContinuousLinearEquiv.refl ℝ E).arrowCongr eF.toContinuousLinearEquiv).trans
      eOut.toContinuousLinearEquiv.symm with
    norm_map' := fun T => by
      refine (eOut.symm.norm_map (((ContinuousLinearEquiv.refl ℝ E).arrowCongr
        eF.toContinuousLinearEquiv) T)).trans ?_
      change ‖eFL.comp T‖ = ‖T‖
      refine le_antisymm
        (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => by
          simpa [eFL] using T.le_opNorm x)
        (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
          simpa [eFL] using (eFL.comp T).le_opNorm x) }

private theorem eLpNormWkp_ulift_aux.{u, v, w} {E : Type u} {F : Type (max u v)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} :
    eLpNormWkp p U k
      (fun z => (LinearIsometryEquiv.ulift ℝ F : ULift.{w, max u v} F ≃ₗᵢ[ℝ] F).symm (f z)) =
      eLpNormWkp p U k f := by
  induction k generalizing F with
  | zero =>
    let eF : ULift.{w, max u v} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
    exact eLpNorm_linearIsometryEquiv eF.symm
  | succ k ih =>
    let eF : ULift.{w, max u v} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
    let eFL := eF.toLinearIsometry.toContinuousLinearMap
    let eFSymmL := eF.symm.toLinearIsometry.toContinuousLinearMap
    let eCLM := uliftCLMLIE.{u, max u v, w} E F
    let eOut : ULift.{w, max u v} (E →L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] F) :=
      LinearIsometryEquiv.ulift ℝ (E →L[ℝ] F)
    rw [eLpNormWkp_succ, eLpNormWkp_succ,
      show eLpNorm (fun z => eF.symm (f z)) p (volume.restrict U) =
        eLpNorm f p (volume.restrict U) from eLpNorm_linearIsometryEquiv eF.symm]
    congr 1
    refine le_antisymm ?_ ?_
    · refine le_iInf₂ fun D hD => ?_
      have : CompleteSpace F := hD.completeSpace
      refine (iInf₂_le (fun z => eFSymmL.comp (D z)) (hD.clm_comp eFSymmL)).trans ?_
      have heq : (fun z => eCLM (eFSymmL.comp (D z))) = fun z => eOut.symm (D z) := by
        ext1 z
        change eOut.symm (((ContinuousLinearEquiv.refl ℝ E).arrowCongr eF.toContinuousLinearEquiv)
          (eFSymmL.comp (D z))) = eOut.symm (D z)
        congr 1
      rw [← eLpNormWkp_linearIsometryEquiv_aux.{u, max v w} eCLM, heq, ih]
    · refine le_iInf₂ fun D' hD' => ?_
      have : CompleteSpace (ULift.{w, max u v} F) := hD'.completeSpace
      have : CompleteSpace F :=
        (eF.toContinuousLinearEquiv.isUniformEmbedding.isUniformInducing.completeSpace_congr
          eF.surjective).mp inferInstance
      refine (iInf₂_le (fun z => eFL.comp (D' z)) (hD'.clm_comp eFL)).trans ?_
      have heq' : (fun z => eOut.symm (eFL.comp (D' z))) = fun z => eCLM (D' z) := by
        ext1 z
        change eOut.symm (eFL.comp (D' z)) =
          eOut.symm (((ContinuousLinearEquiv.refl ℝ E).arrowCongr eF.toContinuousLinearEquiv)
            (D' z))
        congr 1
      rw [← ih, heq']
      exact (eLpNormWkp_linearIsometryEquiv_aux.{u, max v w} (f := D') eCLM).le

private theorem eLpNormWkp_ulift.{u, v, w} {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} :
    eLpNormWkp p U k
      (fun z => (LinearIsometryEquiv.ulift ℝ F : ULift.{w, v} F ≃ₗᵢ[ℝ] F).symm (f z)) =
      eLpNormWkp p U k f := by
  let eF : ULift.{w, v} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  cases k with
  | zero => exact eLpNorm_linearIsometryEquiv eF.symm
  | succ k =>
    let eFL := eF.toLinearIsometry.toContinuousLinearMap
    let eFSymmL := eF.symm.toLinearIsometry.toContinuousLinearMap
    let eCLM := uliftCLMLIE.{u, v, w} E F
    let eOut : ULift.{w, max u v} (E →L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] F) :=
      LinearIsometryEquiv.ulift ℝ (E →L[ℝ] F)
    rw [eLpNormWkp_succ, eLpNormWkp_succ,
      show eLpNorm (fun z => eF.symm (f z)) p (volume.restrict U) =
        eLpNorm f p (volume.restrict U) from eLpNorm_linearIsometryEquiv eF.symm]
    congr 1
    refine le_antisymm ?_ ?_
    · refine le_iInf₂ fun D hD => ?_
      have : CompleteSpace F := hD.completeSpace
      refine (iInf₂_le (fun z => eFSymmL.comp (D z)) (hD.clm_comp eFSymmL)).trans ?_
      have heq : (fun z => eCLM (eFSymmL.comp (D z))) = fun z => eOut.symm (D z) := by
        ext1 z
        change eOut.symm (((ContinuousLinearEquiv.refl ℝ E).arrowCongr eF.toContinuousLinearEquiv)
          (eFSymmL.comp (D z))) = eOut.symm (D z)
        congr 1
      rw [← eLpNormWkp_linearIsometryEquiv_aux.{u, max v w} eCLM, heq, eLpNormWkp_ulift_aux]
    · refine le_iInf₂ fun D' hD' => ?_
      have : CompleteSpace (ULift.{w, v} F) := hD'.completeSpace
      have : CompleteSpace F :=
        (eF.toContinuousLinearEquiv.isUniformEmbedding.isUniformInducing.completeSpace_congr
          eF.surjective).mp inferInstance
      refine (iInf₂_le (fun z => eFL.comp (D' z)) (hD'.clm_comp eFL)).trans ?_
      have heq' : (fun z => eOut.symm (eFL.comp (D' z))) = fun z => eCLM (D' z) := by
        ext1 z
        change eOut.symm (eFL.comp (D' z)) =
          eOut.symm (((ContinuousLinearEquiv.refl ℝ E).arrowCongr eF.toContinuousLinearEquiv)
            (D' z))
        congr 1
      rw [← eLpNormWkp_ulift_aux.{u, v, w}, heq']
      exact (eLpNormWkp_linearIsometryEquiv_aux.{u, max v w} (f := D') eCLM).le

/-- A continuous linear map of the codomain scales the `W^{k,p}` norm by at most its operator
norm. -/
theorem eLpNormWkp_clm_comp_le.{u, v₁, v₂} {E : Type u} {F : Type v₁} {G : Type v₂}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} (A : F →L[ℝ] G) :
    eLpNormWkp p U k (fun z => A (f z)) ≤ ‖A‖ₑ * eLpNormWkp p U k f := by
  let eFLift : ULift.{max u v₂, v₁} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  let eGLift : ULift.{max u v₁, v₂} G ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  let A' : ULift.{max u v₂, v₁} F →L[ℝ] ULift.{max u v₁, v₂} G :=
    eGLift.symm.toLinearIsometry.toContinuousLinearMap.comp
      (A.comp eFLift.toLinearIsometry.toContinuousLinearMap)
  have hA' : (fun z => eGLift.symm (A (f z))) = fun z => A' (eFLift.symm (f z)) := by
    ext1 z; simp [A']
  rw [← eLpNormWkp_ulift.{u, v₂, max u v₁}, ← eLpNormWkp_ulift.{u, v₁, max u v₂}, hA']
  refine (eLpNormWkp_clm_comp_le_aux.{u, max v₁ v₂} A').trans ?_
  gcongr
  exact eNorm_le_iff_norm_le.2
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => by
      simpa [A'] using A.le_opNorm (eFLift x))

end TauCeti
