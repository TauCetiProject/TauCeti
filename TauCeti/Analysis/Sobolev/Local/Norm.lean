/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.Analysis.Complex.OperatorNorm

/-!
# The `W^{k,p}` size of a function on a planar set

`TauCeti.eLpNormWkp p U k f` is the extended `W^{k,p}(U)` norm of `f : ℂ → F`, for a real normed
space `F`: the `Lᵖ(U)` norm of `f` plus, recursively, the `W^{k-1,p}(U)` size of its weak
derivative on `interior U`, minimized over all weak derivatives. It is `∞` when no weak
derivative exists, or when one of the norms is infinite. Its derivatives are taken on the
interior and its norms on `U` itself, matching `TauCeti.MemWkpLoc`. On an open set weak
derivatives are unique almost everywhere, so the minimum is attained by every weak derivative.

This is the quantity in which interior estimates of elliptic equations are stated. The file
supplies its unfolding, its value through a given weak derivative on an open set or on a set
that agrees almost everywhere with its interior, such as a half-disc, the `Lᵖ` and
`W^{k,p}_loc` membership of a function of finite norm and, conversely, the finiteness of the
norm of a `W^{k,p}_loc` function on relatively compact subsets, the extraction of a weak
derivative from a finite successor-order norm, the almost-everywhere vanishing of a function of
zero norm, monotonicity in the set and in the derivative order, invariance under
almost-everywhere change, the triangle inequality (also over finite sums and for pairs) and the
operator-norm bound under a continuous linear map of the codomain. An upper bound of the form
`a + c ‖f‖_{W^{k+1,p}(U)}` (for finite `c`, with `‖f‖_{W^{k+1,p}(U)}` finite when `c = 0`) may be
checked through each weak derivative of `f` separately. A chain bound
`TauCeti.WeakDerivChainLe p S T C m f g` between the iterated weak derivatives of `f` and `g`,
with a finite nonzero constant `C`, gives the norm bound `‖f‖_{W^{m,p}(S)} ≤ C ‖g‖_{W^{m,p}(T)}`
when `f` has the iterated weak derivatives, for instance when `MemWkpLoc q S m f`
(`TauCeti.WeakDerivChainLe.eLpNormWkp_le`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p : ℝ≥0∞} {U V : Set ℂ} {k : ℕ} {f g : ℂ → F}

/-- The extended `W^{k,p}(U)` norm: the `Lᵖ(U)` norm of `f` plus the smallest `W^{k-1,p}(U)` norm
of a weak derivative of `f` on `interior U`. It is `∞` when no weak derivative exists. -/
def eLpNormWkp (p : ℝ≥0∞) (U : Set ℂ) :
    (k : ℕ) → {F : Type*} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℂ → F) → ℝ≥0∞
  | 0, _, _, _, f => eLpNorm f p (volume.restrict U)
  | k + 1, F, _, _, f => eLpNorm f p (volume.restrict U) +
      ⨅ (D : ℂ → ℂ →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
        eLpNormWkp p U k D

/-- At order zero the `W^{k,p}` norm is the `Lᵖ` norm. -/
@[simp]
theorem eLpNormWkp_zero : eLpNormWkp p U 0 f = eLpNorm f p (volume.restrict U) := by
  rw [eLpNormWkp]

/-- The successor-order unfolding of the `W^{k,p}` norm. -/
theorem eLpNormWkp_succ : eLpNormWkp p U (k + 1) f = eLpNorm f p (volume.restrict U) +
    ⨅ (D : ℂ → ℂ →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
      eLpNormWkp p U k D := by
  rw [eLpNormWkp]

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
theorem eLpNormWkp_succ_le {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f ≤ eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D := by
  rw [eLpNormWkp_succ]
  gcongr
  exact iInf₂_le D hD

/-- The `W^{k,p}` norm increases with the set. -/
theorem eLpNormWkp_mono_set (hVU : V ⊆ U) : eLpNormWkp p V k f ≤ eLpNormWkp p U k f := by
  induction k generalizing F with
  | zero => exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr ?_ + ?_
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
    · exact le_iInf₂ fun D hD => iInf₂_le_of_le D (hD.mono (interior_mono hVU)) ih

/-- The `W^{k,p}(U)` norm increases with the derivative order. -/
theorem eLpNormWkp_mono_order {l : ℕ} (hlk : l ≤ k) :
    eLpNormWkp p U l f ≤ eLpNormWkp p U k f := by
  induction l generalizing k F with
  | zero => exact eLpNorm_le_eLpNormWkp.trans_eq' eLpNormWkp_zero.symm
  | succ l ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr
    exact ih (by omega)

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

/-- On a set that agrees almost everywhere with its interior, every weak derivative on the
interior realizes the successor-order norm. This applies to open sets and to the half-discs
`Ω ∩ {0 ≤ im}` (`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). -/
theorem eLpNormWkp_succ_eq_of_hasWeakFDerivOn_interior
    (hU : U =ᵐ[volume] (Opens.interior U : Set ℂ)) {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f = eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D := by
  refine le_antisymm (eLpNormWkp_succ_le hD) ?_
  rw [eLpNormWkp_succ]
  gcongr
  refine le_iInf₂ fun D' hD' => (eLpNormWkp_congr_ae ?_).le
  rw [Measure.restrict_congr_set hU]
  exact hD.ae_eq hD'

/-- On an open set, every weak derivative realizes the successor-order norm. -/
theorem eLpNormWkp_succ_eq_of_hasWeakFDerivOn {Ω : Opens ℂ} {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume Ω f D) :
    eLpNormWkp p Ω (k + 1) f = eLpNorm f p (volume.restrict Ω) + eLpNormWkp p Ω k D :=
  eLpNormWkp_succ_eq_of_hasWeakFDerivOn_interior (by rw [Opens.interior_coe])
    (by rwa [Opens.interior_coe])

/-- On an open set, the order-`k` norm of a weak derivative is at most the order-`k + 1` norm of
the function. At `k = 0` this bounds `‖D‖_{Lᵖ(Ω)}` by `‖f‖_{W^{1,p}(Ω)}`. -/
theorem eLpNormWkp_le_eLpNormWkp_succ_of_hasWeakFDerivOn {Ω : Opens ℂ} {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume Ω f D) : eLpNormWkp p Ω k D ≤ eLpNormWkp p Ω (k + 1) f := by
  rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD]
  exact le_add_self

/-- A finite successor-order norm provides a weak derivative on the interior of finite norm of
the previous order. -/
theorem exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top (hf : eLpNormWkp p U (k + 1) f ≠ ∞) :
    ∃ D : ℂ → ℂ →L[ℝ] F,
      HasWeakFDerivOn volume (Opens.interior U) f D ∧ eLpNormWkp p U k D ≠ ∞ := by
  rw [eLpNormWkp_succ, ENNReal.add_ne_top] at hf
  obtain ⟨D, hD, hlt⟩ : ∃ D : ℂ → ℂ →L[ℝ] F,
      HasWeakFDerivOn volume (Opens.interior U) f D ∧ eLpNormWkp p U k D < ∞ := by
    simpa [iInf_lt_iff, lt_top_iff_ne_top] using hf.2
  exact ⟨D, hD, hlt.ne⟩

/-- Let `c ≠ ∞`, and if `c = 0` let `f` have finite `W^{k+1,p}(U)` norm. To bound `b` by
`a + c ‖f‖_{W^{k+1,p}(U)}` it suffices to bound it by `a + c (‖f‖_{Lᵖ(U)} + ‖D‖_{W^{k,p}(U)})`
for every weak derivative `D` of `f` on `interior U` of finite `W^{k,p}(U)` norm. -/
theorem le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn {a b c : ℝ≥0∞}
    (hc : c ≠ ∞) (hf : c = 0 → eLpNormWkp p U (k + 1) f ≠ ∞)
    (H : ∀ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D →
      eLpNormWkp p U k D ≠ ∞ →
        b ≤ a + c * (eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D)) :
    b ≤ a + c * eLpNormWkp p U (k + 1) f := by
  rcases eq_or_ne c 0 with rfl | hc0
  · obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top (hf rfl)
    simpa using H D hD hDk
  calc b
      ≤ ⨅ (D : ℂ → ℂ →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
          a + c * (eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D) :=
        le_iInf₂ fun D hD => by
          by_cases hDk : eLpNormWkp p U k D = ∞
          · rw [hDk, add_top, ENNReal.mul_top hc0, add_top]
            exact le_top
          · exact H D hD hDk
    _ = a + c * eLpNormWkp p U (k + 1) f := by
        rw [eLpNormWkp_succ]
        simp only [ENNReal.add_iInf, ENNReal.mul_iInf_of_ne hc0 hc]

/-- A function of finite `W^{k,p}` norm lies in the local Sobolev class `W^{k,p}_loc`. -/
theorem memWkpLoc_of_eLpNormWkp_ne_top (hf : eLpNormWkp p U k f ≠ ∞) : MemWkpLoc p U k f := by
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 (memLp_of_eLpNormWkp_ne_top hf).memLpLoc
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
    exact memWkpLoc_succ_iff.2 ⟨(memLp_of_eLpNormWkp_ne_top hf).memLpLoc, D, hD, ih hDk⟩

/-- On an open set, a finite successor-order norm is realized by a weak derivative of finite norm
of the previous order. -/
theorem exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top {Ω : Opens ℂ}
    (hf : eLpNormWkp p Ω (k + 1) f ≠ ∞) :
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ eLpNormWkp p Ω k D ≠ ∞ ∧
      eLpNormWkp p Ω (k + 1) f = eLpNorm f p (volume.restrict Ω) + eLpNormWkp p Ω k D := by
  obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
  rw [Opens.interior_coe] at hD
  exact ⟨D, hD, hDk, eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD⟩

/-- On a set that agrees almost everywhere with its interior, for instance a half-disc
`Ω ∩ {0 ≤ im}`, a finite successor-order norm is realized by a weak derivative on the interior of
finite norm of the previous order. -/
theorem exists_hasWeakFDerivOn_interior_eLpNormWkp_succ_eq_of_ne_top
    (hU : U =ᵐ[volume] (Opens.interior U : Set ℂ)) (hf : eLpNormWkp p U (k + 1) f ≠ ∞) :
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      eLpNormWkp p U k D ≠ ∞ ∧
      eLpNormWkp p U (k + 1) f = eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D := by
  obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
  exact ⟨D, hD, hDk, eLpNormWkp_succ_eq_of_hasWeakFDerivOn_interior hU hD⟩

/-- A local Sobolev function has finite `W^{k,p}` norm on every compact subset of its domain. -/
theorem MemWkpLoc.eLpNormWkp_ne_top_of_isCompact (hf : MemWkpLoc p U k f) {K : Set ℂ}
    (hKU : K ⊆ U) (hK : IsCompact K) : eLpNormWkp p K k f ≠ ∞ := by
  induction k generalizing F with
  | zero => exact (memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := hf.exists_weakFDeriv
    refine ne_top_of_le_ne_top ?_ (eLpNormWkp_succ_le (hD.mono (interior_mono hKU)))
    exact ENNReal.add_ne_top.2 ⟨(memLpLoc_iff.1 hf.memLpLoc K hKU hK).eLpNorm_ne_top, ih hDk⟩

/-- A local Sobolev function has finite `W^{k,p}` norm on every set whose closure is compact and
contained in its domain. -/
theorem MemWkpLoc.eLpNormWkp_ne_top_of_closure_subset (hf : MemWkpLoc p U k f)
    (hV : IsCompact (closure V)) (hVU : closure V ⊆ U) : eLpNormWkp p V k f ≠ ∞ :=
  ne_top_of_le_ne_top (hf.eLpNormWkp_ne_top_of_isCompact hVU hV)
    (eLpNormWkp_mono_set subset_closure)

/-- A local estimate `‖v‖_{Lᵗ(V)} ≤ C ‖v‖_{W^{k,r}(W)}` on every `V` with compact closure in an
open `W` makes every `u ∈ W^{k,r}_loc(Ω, F)` locally `Lᵗ`. -/
theorem MemWkpLoc.memLpLoc_of_forall_exists_eLpNorm_le {Ω : Opens ℂ} {r t : ℝ≥0∞}
    (hf : MemWkpLoc r Ω k f)
    (hest : ∀ {V : Set ℂ} {W : Opens ℂ}, IsCompact (closure V) → closure V ⊆ W →
      ∃ C : ℝ≥0, ∀ v : ℂ → F, eLpNorm v t (volume.restrict V) ≤ C * eLpNormWkp r W k v) :
    MemLpLoc t Ω f := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  have hKc : closure K = K := hK.isClosed.closure_eq
  obtain ⟨C, hC⟩ := hest (W := W) (by rwa [hKc]) (by rwa [hKc])
  exact memLp_iff.2 ((hC f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_top_iff_ne_top.2 (hf.eLpNormWkp_ne_top_of_closure_subset hWc hWΩ))))

/-- The zero function has zero `W^{k,p}` norm. -/
@[simp]
theorem eLpNormWkp_zero_fun [CompleteSpace F] : eLpNormWkp p U k (0 : ℂ → F) = 0 := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    refine le_antisymm ((eLpNormWkp_succ_le hasWeakFDerivOn_zero).trans ?_) zero_le
    simp [ih]

/-- The triangle inequality for the `W^{k,p}` norm. -/
theorem eLpNormWkp_add_le (hp : 1 ≤ p) :
    eLpNormWkp p U k (f + g) ≤ eLpNormWkp p U k f + eLpNormWkp p U k g := by
  induction k generalizing F with
  | zero => exact eLpNorm_add_le hp
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNormWkp_succ, add_add_add_comm]
    gcongr ?_ + ?_
    · exact eLpNorm_add_le hp
    · exact ENNReal.le_iInf_add_iInf fun D D' => ENNReal.le_iInf_add_iInf fun hD hD' =>
        iInf₂_le_of_le (D + D') (hD.add hD') ih

/-- The triangle inequality for the `W^{k,p}` norm over a finite sum. -/
theorem eLpNormWkp_sum_le [CompleteSpace F] {ι : Type*} {s : Finset ι} {u : ι → ℂ → F}
    (hp : 1 ≤ p) : eLpNormWkp p U k (∑ i ∈ s, u i) ≤ ∑ i ∈ s, eLpNormWkp p U k (u i) :=
  Finset.le_sum_of_subadditive (fun u : ℂ → F ↦ eLpNormWkp p U k u) eLpNormWkp_zero_fun.le
    (fun _ _ ↦ eLpNormWkp_add_le hp) s u

/-- A continuous linear map of the codomain scales the `W^{k,p}` norm by at most its operator
norm. -/
theorem eLpNormWkp_clm_comp_le [CompleteSpace G] (A : F →L[ℝ] G) :
    eLpNormWkp p U k (fun z => A (f z)) ≤ ‖A‖ₑ * eLpNormWkp p U k f := by
  induction k generalizing F G with
  | zero => exact A.eLpNorm_comp_le
  | succ k ih =>
    by_cases hA : A = 0
    · subst hA
      have h0 : (fun z => (0 : F →L[ℝ] G) (f z)) = (0 : ℂ → G) := rfl
      rw [h0, eLpNormWkp_zero_fun]
      exact zero_le
    have hA₀ : ‖A‖ₑ ≠ 0 := by
      rw [eNorm_eq_nnNorm]; exact ENNReal.coe_ne_zero.2 (nnNorm_ne_zero_iff.2 hA)
    have hA_top : ‖A‖ₑ ≠ ⊤ := eNorm_ne_top
    rw [eLpNormWkp_succ, eLpNormWkp_succ, mul_add]
    gcongr ?_ + ?_
    · exact A.eLpNorm_comp_le
    · rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
      refine le_iInf fun D => ?_
      rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
      refine le_iInf fun hD => iInf₂_le_of_le _ (hD.clm_comp A) ?_
      refine (ih (ContinuousLinearMap.compL ℝ ℂ F G A)).trans ?_
      gcongr
      have hle : ‖ContinuousLinearMap.compL ℝ ℂ F G A‖ ≤ ‖A‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun B => A.opNorm_comp_le B
      exact eNorm_le_iff_norm_le.2 hle

/-- A linear isometric equivalence does not increase the `W^{k,p}` size. -/
private theorem eLpNormWkp_linearIsometryEquiv_comp_le [CompleteSpace G] (e : F ≃ₗᵢ[ℝ] G)
    (f : ℂ → F) : eLpNormWkp p U k (fun z => e (f z)) ≤ eLpNormWkp p U k f := by
  have hn : ‖(e.toContinuousLinearEquiv : F →L[ℝ] G)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  have he : ‖(e.toContinuousLinearEquiv : F →L[ℝ] G)‖ₑ ≤ 1 :=
    (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_one.2 hn)
  calc
    _ ≤ ‖(e.toContinuousLinearEquiv : F →L[ℝ] G)‖ₑ * eLpNormWkp p U k f :=
      eLpNormWkp_clm_comp_le (e.toContinuousLinearEquiv : F →L[ℝ] G)
    _ ≤ 1 * eLpNormWkp p U k f := by gcongr
    _ = _ := one_mul _

/-- **Linear isometric equivalences preserve the `W^{k,p}` size.** For a linear isometric
equivalence `e : F ≃ₗᵢ[ℝ] G` between complete spaces, `‖e ∘ f‖_{W^{k,p}(U)} = ‖f‖_{W^{k,p}(U)}`. -/
@[simp]
theorem eLpNormWkp_linearIsometryEquiv_comp [CompleteSpace F] [CompleteSpace G]
    (e : F ≃ₗᵢ[ℝ] G) (f : ℂ → F) :
    eLpNormWkp p U k (fun z => e (f z)) = eLpNormWkp p U k f := by
  refine le_antisymm (eLpNormWkp_linearIsometryEquiv_comp_le e f) ?_
  calc
    _ = eLpNormWkp p U k (fun z => e.symm (e (f z))) := by simp
    _ ≤ _ := eLpNormWkp_linearIsometryEquiv_comp_le e.symm _


/-- A continuous linear map of norm at most one does not increase the `W^{k,p}` norm. -/
theorem eLpNormWkp_clm_comp_le_of_norm_le_one [CompleteSpace G] (A : F →L[ℝ] G) (hA : ‖A‖ ≤ 1) :
    eLpNormWkp p U k (fun z => A (f z)) ≤ eLpNormWkp p U k f :=
  (eLpNormWkp_clm_comp_le A).trans (mul_le_of_le_one_left zero_le (by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 hA))

/-- The `W^{k,p}` norm of a pair of functions is at most the sum of the norms of its
components. -/
theorem eLpNormWkp_prodMk_le [CompleteSpace F] [CompleteSpace G] (hp : 1 ≤ p) {v : ℂ → G} :
    eLpNormWkp p U k (fun z => (f z, v z)) ≤ eLpNormWkp p U k f + eLpNormWkp p U k v := by
  have h : (fun z => (f z, v z)) = (fun z => ContinuousLinearMap.inl ℝ F G (f z)) +
      fun z => ContinuousLinearMap.inr ℝ F G (v z) := by
    ext1 z
    simp
  rw [h]
  exact (eLpNormWkp_add_le hp).trans (add_le_add
    (eLpNormWkp_clm_comp_le_of_norm_le_one _ (ContinuousLinearMap.norm_inl_le_one ℝ F G))
    (eLpNormWkp_clm_comp_le_of_norm_le_one _ (ContinuousLinearMap.norm_inr_le_one ℝ F G)))

/-- Evaluating a field of linear maps at a vector `v` with `‖v‖ ≤ 1` does not increase the
`W^{k,p}` norm. -/
theorem eLpNormWkp_apply_le_of_norm_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace F] (f : ℂ → E →L[ℝ] F) {v : E} (hv : ‖v‖ ≤ 1) :
    eLpNormWkp p U k (fun z => f z v) ≤ eLpNormWkp p U k f :=
  eLpNormWkp_clm_comp_le_of_norm_le_one (ContinuousLinearMap.apply ℝ F v)
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => by
      simpa using (A.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg A) hv))

/-- On an open set, a partial derivative `z ↦ D z v`, `‖v‖ ≤ 1`, of a weak derivative `D` of `f`
has `W^{k,p}` norm at most the `W^{k+1,p}` norm of `f`. -/
theorem eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn [CompleteSpace F] {Ω : Opens ℂ}
    {D : ℂ → ℂ →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    eLpNormWkp p Ω k (fun z => D z v) ≤ eLpNormWkp p Ω (k + 1) f :=
  (eLpNormWkp_apply_le_of_norm_le_one D hv).trans
    (eLpNormWkp_le_eLpNormWkp_succ_of_hasWeakFDerivOn hD)

/-- On a set `U` almost everywhere equal to its interior, a partial derivative `z ↦ D z v`,
`‖v‖ ≤ 1`, of a weak derivative `D` of `f` on the interior has `W^{k,p}(U)` norm at most the
`W^{k+1,p}(U)` norm of `f`. -/
theorem eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn_interior [CompleteSpace F]
    (hU : U =ᵐ[volume] (Opens.interior U : Set ℂ)) {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior U) f D) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    eLpNormWkp p U k (fun z => D z v) ≤ eLpNormWkp p U (k + 1) f := by
  rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn_interior hU hD]
  exact (eLpNormWkp_apply_le_of_norm_le_one D hv).trans le_add_self

/-- Negation preserves the `W^{k,p}` norm. -/
@[simp]
theorem eLpNormWkp_neg : eLpNormWkp p U k (-f) = eLpNormWkp p U k f := by
  induction k generalizing F with
  | zero => exact eLpNorm_neg f p _
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNorm_neg]
    congr 1
    refine le_antisymm (le_iInf₂ fun D hD => iInf₂_le_of_le (-D) hD.neg ?_)
      (le_iInf₂ fun D hD => iInf₂_le_of_le (-D) (by simpa using hD.neg) ?_)
    all_goals exact (ih (f := D)).le

/-- The triangle inequality for the `W^{k,p}` norm of a difference. -/
theorem eLpNormWkp_sub_le (hp : 1 ≤ p) :
    eLpNormWkp p U k (f - g) ≤ eLpNormWkp p U k f + eLpNormWkp p U k g := by
  rw [sub_eq_add_neg]
  exact (eLpNormWkp_add_le hp).trans_eq (by rw [eLpNormWkp_neg])

/-- **A chain bound bounds the `W^{m,p}` norm.** Let `C` be finite and nonzero. If the iterated
weak derivatives of `f` on the interior of `S` are bounded in `Lᵖ(S)` by `C` times those of `g` on
the interior of `T` in `Lᵖ(T)`, in the sense of `TauCeti.WeakDerivChainLe`, then
`‖f‖_{W^{m,p}(S)} ≤ C ‖g‖_{W^{m,p}(T)}`. The
derivatives of `f` must exist, which `MemWkpLoc q S m f` provides for any exponent `q`; those of
`g` need not, the right side being `∞` otherwise. -/
theorem WeakDerivChainLe.eLpNormWkp_le {S T : Set ℂ} {C : ℝ≥0∞} (hC : C ≠ ∞) (hC0 : C ≠ 0)
    {m : ℕ} (h : WeakDerivChainLe p S T C m f g) {q : ℝ≥0∞} (hf : MemWkpLoc q S m f) :
    eLpNormWkp p S m f ≤ C * eLpNormWkp p T m g := by
  induction m generalizing F with
  | zero => simpa using h.eLpNorm_le
  | succ m ih =>
    obtain ⟨-, Df, hDf, hDfm⟩ := memWkpLoc_succ_iff.1 hf
    simpa using le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn (a := 0) hC
      (fun h0 => absurd h0 hC0) fun Dg hDg _ => by
        rw [zero_add, mul_add]
        exact (eLpNormWkp_succ_le hDf).trans
          (add_le_add h.eLpNorm_le (ih (h.weakFDeriv hDf hDg) hDfm))

/-- **The `W^{k+1,p}` norm through partial derivatives.** If `D` is a weak derivative of `f` on the
interior of `U`, the `W^{k+1,p}(U)` norm of `f` is at most its `Lᵖ(U)` norm plus the
`W^{k,p}(U)` norms of the partial derivatives `z ↦ D z 1` and `z ↦ D z I`, weighted by the norms
of the maps `L₁`, `L₂` that reassemble `D` from them
(`ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM`). This is the norm form of
`TauCeti.memWkpLoc_succ_iff_apply_one_apply_I`. -/
theorem eLpNormWkp_succ_le_eLpNorm_add_apply_one_add_apply_I [CompleteSpace F] (hp : 1 ≤ p)
    {D : ℂ → ℂ →L[ℝ] F} (hD : HasWeakFDerivOn volume (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f ≤ eLpNorm f p (volume.restrict U) +
      (‖ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℂ F Complex.reCLM‖ₑ *
          eLpNormWkp p U k (fun z => D z 1) +
        ‖ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℂ F Complex.imCLM‖ₑ *
          eLpNormWkp p U k (fun z => D z Complex.I)) := by
  refine (eLpNormWkp_succ_le hD).trans ?_
  gcongr
  conv_lhs => rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM D]
  exact (eLpNormWkp_add_le hp).trans (add_le_add (eLpNormWkp_clm_comp_le _)
    (eLpNormWkp_clm_comp_le _))

end TauCeti
