/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Multiplication
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Data.ENNReal.Mul
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Local bounds for mixed-exponent products on planar domains

Let `p > 2`, `1 ≤ q ≤ p` and let `Ω` be an open planar domain. Fix real normed spaces `F`, `G`
and `H` with `G` finite-dimensional. This file proves the local bounds that accompany the
order-zero and order-one mixed-exponent products of `TauCeti.Analysis.Sobolev.Local.Multiplication`,
stated with the `W^{k,p}` size `TauCeti.eLpNormWkp`. There is a constant `C` such that for every
continuous bilinear map `B : F × G → H`:

* order zero, on a compact `K ⊆ Ω`: `‖B(f, g)‖_{L^q(K)} ≤ C ‖B‖ ‖f‖_{Lᵖ(K)} ‖g‖_{W^{1,q}(Ω)}`;
* order one, for `1 < q`, finite-dimensional `F` and complete `H`, on a set `U` whose closure is
  compact and contained in `Ω`:
  `‖B(f, g)‖_{W^{1,q}(U)} ≤ C ‖B‖ ‖f‖_{W^{1,p}(Ω)} ‖g‖_{W^{1,q}(Ω)}`. Taking `U` open controls
  the weak derivative of the product on all of `U`.

The constant depends on the spaces, the exponents and the sets, and is uniform in `B`, `f` and
`g`. No membership hypothesis is needed: the bounds hold trivially when a norm on the right is
infinite.

## Main declarations

* `TauCeti.exists_eLpNorm_bilin_le_eLpNormWkp_one`: the order-zero bound.
* `TauCeti.exists_eLpNormWkp_one_bilin_le`: the order-one bound. At `q = p` this is the local
  bound for the algebra property of `W^{1,p}_loc`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Module
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

/-- **Local bound for order-zero mixed products.** Fix real normed spaces `F`, `G` and `H` with
`G` finite-dimensional. For `p > 2`, `1 ≤ q ≤ p` and a compact `K ⊆ Ω`, there is a constant `C`
such that `‖B(f, g)‖_{L^q(K)} ≤ C ‖B‖ ‖f‖_{Lᵖ(K)} ‖g‖_{W^{1,q}(Ω)}` for every continuous bilinear
map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. -/
theorem exists_eLpNorm_bilin_le_eLpNormWkp_one (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNorm (fun z => B (f z) (g z)) q (volume.restrict K) ≤
        C * ‖B‖ₑ * eLpNorm f p (volume.restrict K) * eLpNormWkp q Ω 1 g := by
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_bilin_le (μ := volume) (Ω := Ω) (F := F) (G := G)
    (H := H) (by simpa using hp) hqp hK hKΩ
  refine ⟨C + 1, fun B f g => ?_⟩
  have hq0 : (q : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  -- If `B = 0` or either factor vanishes almost everywhere on `K`, so does the product.
  have hvanish (h : (fun z => B (f z) (g z)) =ᵐ[volume.restrict K] 0) :
      eLpNorm (fun z => B (f z) (g z)) q (volume.restrict K) = 0 := by
    rw [eLpNorm_congr_ae h, eLpNorm_zero]
  refine ENNReal.le_mul_mul_of_ne_top_imp_le (fun hCB => hvanish (.of_forall fun z => ?_))
    (fun hf0 => hvanish ?_) (fun hg0 => hvanish ?_) fun _ hf hg => ?_
  · -- `enorm_eq_zero` does not elaborate on this iterated operator space, so go through `‖B‖`.
    simp [B.opNorm_zero_iff.1 <| (norm_nonneg B).antisymm' <| by simpa [← ofReal_norm] using hCB]
  · filter_upwards [(eLpNorm_eq_zero_iff (by simpa using (zero_lt_two.trans hp).ne')).1 hf0]
      with z hz
    simp [hz]
  · filter_upwards [ae_mono (Measure.restrict_mono hKΩ le_rfl)
      (ae_eq_zero_of_eLpNormWkp_eq_zero hq0 hg0)] with z hz
    simp [hz]
  obtain ⟨Dg, hDg, hgq, hDgq, hgΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hg
  rw [eLpNormWkp_zero] at hDgq hgΩ
  have hf : AEStronglyMeasurable f (volume.restrict K) :=
    (memLp_iff.2 (lt_top_iff_ne_top.2 hf)).aestronglyMeasurable
  calc
    _ ≤ C * ‖B‖ₑ * eLpNorm f p (volume.restrict K) *
        (eLpNorm g q (volume.restrict Ω) + eLpNorm Dg q (volume.restrict Ω)) :=
      hC B f g Dg hf hDg hgq (memLp_iff.2 (lt_top_iff_ne_top.2 hDgq))
    _ ≤ _ := by
      rw [← hgΩ]
      gcongr
      exact_mod_cast le_self_add

/-- **Local bound for order-one mixed products.** Fix real normed spaces `F`, `G` and `H` with
`F` and `G` finite-dimensional and `H` complete. For `p > 2`, `1 < q ≤ p` and a set `U` whose
closure is compact and contained in `Ω`, there is a constant `C` such that
`‖B(f, g)‖_{W^{1,q}(U)} ≤ C ‖B‖ ‖f‖_{W^{1,p}(Ω)} ‖g‖_{W^{1,q}(Ω)}` for every continuous bilinear
map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. Taking `U` open controls the
weak derivative of the product on all of `U`. At `q = p` this is the local bound for the algebra
property of `W^{1,p}_loc`. -/
theorem exists_eLpNormWkp_one_bilin_le [FiniteDimensional ℝ F] [CompleteSpace H] (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp q U 1 (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω 1 f * eLpNormWkp q Ω 1 g := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  let _ : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨hq1⟩
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨hq1.trans (by exact_mod_cast hqp)⟩
  have hp' : (finrank ℝ ℂ : ℝ≥0) < p := by simpa using hp
  obtain ⟨C₁, hC₁⟩ := W1p.exists_eLpNorm_bilin_add_eLpNorm_deriv_le (μ := volume) (Ω := Ω)
    (F := F) (G := G) (H := H) hp' hqp hU hUΩ
  obtain ⟨C₂, hC₂⟩ := W1p.exists_eLpNorm_le_of_holderTriple (μ := volume) (Ω := Ω) (G := F)
    (r := ∞) hp' le_rfl hU hUΩ
  refine ⟨C₁ * (C₂ + 1) + 1, fun B f g => (eLpNormWkp_mono_set subset_closure).trans ?_⟩
  set K := closure U
  have hq0 : (q : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hKm : volume.restrict K ≤ volume.restrict Ω := Measure.restrict_mono hUΩ le_rfl
  -- If `B = 0` or either factor vanishes almost everywhere on `Ω`, so does the product on `K`.
  have hvanish (h : (fun z => B (f z) (g z)) =ᵐ[volume.restrict Ω] 0) :
      eLpNormWkp q K 1 (fun z => B (f z) (g z)) = 0 := by
    rw [eLpNormWkp_congr_ae (ae_mono hKm h), eLpNormWkp_zero_fun]
  refine ENNReal.le_mul_mul_of_ne_top_imp_le (fun hCB => hvanish (.of_forall fun z => ?_))
    (fun hf0 => hvanish ?_) (fun hg0 => hvanish ?_) fun _ hf hg => ?_
  · -- `enorm_eq_zero` does not elaborate on this iterated operator space, so go through `‖B‖`.
    simp [B.opNorm_zero_iff.1 <| (norm_nonneg B).antisymm' <| by simpa [← ofReal_norm] using hCB]
  · filter_upwards [ae_eq_zero_of_eLpNormWkp_eq_zero hp0 hf0] with z hz
    simp [hz]
  · filter_upwards [ae_eq_zero_of_eLpNormWkp_eq_zero hq0 hg0] with z hz
    simp [hz]
  obtain ⟨Df, hDf, hfp, hDfp, hfΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hf
  obtain ⟨Dg, hDg, hgq, hDgq, hgΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hg
  rw [eLpNormWkp_zero] at hDfp hfΩ hDgq hgΩ
  replace hDfp : MemLp Df p (volume.restrict Ω) := memLp_iff.2 (lt_top_iff_ne_top.2 hDfp)
  replace hDgq : MemLp Dg q (volume.restrict Ω) := memLp_iff.2 (lt_top_iff_ne_top.2 hDgq)
  -- `f` is locally bounded on `Ω`, so the weak Leibniz rule applies there.
  have hfloc : MemWkpLoc p Ω 1 f :=
    memWkpLoc_succ_iff_of_isOpen.2
      ⟨hfp.memLpLoc, Df, hDf, memWkpLoc_zero_iff.2 hDfp.memLpLoc⟩
  have hLeib := hDf.bilin_of_memLpLoc B hp hq hqp
    ((hfloc.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top) hDfp.memLpLoc
    hDg hgq.memLpLoc hDgq.memLpLoc
  have hint : Opens.interior K ≤ Ω := fun z hz => hUΩ (interior_subset hz)
  set Xf := eLpNorm f p (volume.restrict Ω) + eLpNorm Df p (volume.restrict Ω)
  set Xg := eLpNorm g q (volume.restrict Ω) + eLpNorm Dg q (volume.restrict Ω)
  have hfK : eLpNorm f ∞ (volume.restrict K) ≤ C₂ * Xf := hC₂ f Df hDf hfp hDfp
  have hDfK : eLpNorm Df p (volume.restrict K) ≤ Xf :=
    (eLpNorm_mono_measure Df hKm).trans le_add_self
  calc
    _ ≤ eLpNorm (fun z => B (f z) (g z)) q (volume.restrict K) +
        eLpNormWkp q K 0
          (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) :=
      eLpNormWkp_succ_le (hLeib.mono hint)
    _ ≤ C₁ * ‖B‖ₑ * (eLpNorm f ∞ (volume.restrict K) + eLpNorm Df p (volume.restrict K)) * Xg := by
      rw [eLpNormWkp_zero]
      exact hC₁ B f Df g Dg (hfp.aestronglyMeasurable.mono_measure hKm)
        (hDfp.aestronglyMeasurable.mono_measure hKm) hDg hgq hDgq
    _ ≤ C₁ * ‖B‖ₑ * ((C₂ + 1) * Xf) * Xg := by
      gcongr
      calc
        eLpNorm f ∞ (volume.restrict K) + eLpNorm Df p (volume.restrict K) ≤ C₂ * Xf + Xf :=
          add_le_add hfK hDfK
        _ = (C₂ + 1) * Xf := by ring
    _ = ↑(C₁ * (C₂ + 1)) * ‖B‖ₑ * eLpNormWkp p Ω 1 f * eLpNormWkp q Ω 1 g := by
      rw [hfΩ, hgΩ]
      push_cast
      ring
    _ ≤ _ := by
      gcongr
      exact_mod_cast le_self_add

end TauCeti
