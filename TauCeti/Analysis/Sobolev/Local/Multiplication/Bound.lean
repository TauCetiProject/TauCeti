/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Multiplication
public import TauCeti.Analysis.Sobolev.Local.Norm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Local bounds for mixed-exponent products on planar domains

Let `p > 2`, `1 ≤ q ≤ p`, let `Ω` be an open planar domain and let `K ⊆ Ω` be compact. This file
proves the local bounds that accompany the order-zero and order-one mixed-exponent products of
`TauCeti.Analysis.Sobolev.Local.Multiplication`, stated with the `W^{k,p}` size
`TauCeti.eLpNormWkp`. There is an open `W` between `K` and `Ω` with compact closure in `Ω`, and a
constant `C`, such that for every continuous bilinear map `B : F × G → H`:

* order zero: `‖B(f, g)‖_{L^q(K)} ≤ C ‖B‖ ‖f‖_{Lᵖ(K)} ‖g‖_{W^{1,q}(W)}`;
* order one, for `1 < q` and finite-dimensional `F`:
  `‖B(f, g)‖_{W^{1,q}(K)} ≤ C ‖B‖ ‖f‖_{W^{1,p}(W)} ‖g‖_{W^{1,q}(W)}`.

The constant is uniform in `B`, `f` and `g`. No membership hypothesis is needed: the bounds hold
trivially when a norm on the right is infinite.

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

omit [FiniteDimensional ℝ G] in
/-- To bound `L` by `C ‖B‖ a b` with `C ≠ 0`, it suffices to treat finite `a` and `b`, provided `L`
vanishes when `B`, `a` or `b` does: otherwise the right side is infinite. -/
private theorem le_mul_enorm_mul_mul_of_ne_top {L a b C : ℝ≥0∞} {B : F →L[ℝ] G →L[ℝ] H}
    (hC : C ≠ 0) (hB : B = 0 → L = 0) (ha : a = 0 → L = 0) (hb : b = 0 → L = 0)
    (hfin : a ≠ ∞ → b ≠ ∞ → L ≤ C * ‖B‖ₑ * a * b) : L ≤ C * ‖B‖ₑ * a * b := by
  by_cases hB0 : B = 0
  · exact (hB hB0).le.trans zero_le
  by_cases ha0 : a = 0
  · exact (ha ha0).le.trans zero_le
  by_cases hb0 : b = 0
  · exact (hb hb0).le.trans zero_le
  -- `enorm_ne_zero` does not elaborate on this iterated operator space, so go through `‖B‖`.
  have hCB : C * ‖B‖ₑ ≠ 0 := mul_ne_zero hC (ofReal_norm B ▸
    (ENNReal.ofReal_pos.2 ((norm_nonneg B).lt_of_ne' (mt B.opNorm_zero_iff.1 hB0))).ne')
  by_cases hat : a = ∞
  · rw [hat, ENNReal.mul_top hCB, ENNReal.top_mul hb0]
    exact le_top
  by_cases hbt : b = ∞
  · rw [hbt, ENNReal.mul_top (mul_ne_zero hCB ha0)]
    exact le_top
  exact hfin hat hbt

/-- **Local bound for order-zero mixed products.** For `p > 2`, `1 ≤ q ≤ p` and a compact
`K ⊆ Ω`, there are an open `W` between `K` and `Ω` with compact closure in `Ω` and a constant `C`
such that `‖B(f, g)‖_{L^q(K)} ≤ C ‖B‖ ‖f‖_{Lᵖ(K)} ‖g‖_{W^{1,q}(W)}` for every continuous bilinear
map `B`, every `f` and every `g` with finite-dimensional values. -/
theorem exists_eLpNorm_bilin_le_eLpNormWkp_one (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ closure W ⊆ Ω ∧
      ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
        eLpNorm (fun z => B (f z) (g z)) q (volume.restrict K) ≤
          C * ‖B‖ₑ * eLpNorm f p (volume.restrict K) * eLpNormWkp q W 1 g := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_bilin_le (μ := volume) (Ω := ⟨W, hWo⟩) (F := F) (G := G)
    (H := H) (by simpa using hp) hqp hK hKW
  refine ⟨W, hWo, hKW, hWc, hWΩ, C + 1, fun B f g => ?_⟩
  have hq0 : (q : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  -- If `B = 0` or either factor vanishes almost everywhere on `K`, so does the product.
  have hvanish (h : (fun z => B (f z) (g z)) =ᵐ[volume.restrict K] 0) :
      eLpNorm (fun z => B (f z) (g z)) q (volume.restrict K) = 0 := by
    rw [eLpNorm_congr_ae h, eLpNorm_zero]
  refine le_mul_enorm_mul_mul_of_ne_top (by simp)
    (fun hB => hvanish (.of_forall fun z => by simp [hB])) (fun hf0 => hvanish ?_)
    (fun hg0 => hvanish ?_) fun hf hg => ?_
  · filter_upwards [(eLpNorm_eq_zero_iff (by simpa using (zero_lt_two.trans hp).ne')).1 hf0]
      with z hz
    simp [hz]
  · filter_upwards [ae_mono (Measure.restrict_mono hKW le_rfl)
      (ae_eq_zero_of_eLpNormWkp_eq_zero hq0 hg0)] with z hz
    simp [hz]
  obtain ⟨Dg, hDg, hgq, hDgq, hgW⟩ := exists_weakFDeriv_memLp_of_eLpNormWkp_one_ne_top hWo hg
  have hf : AEStronglyMeasurable f (volume.restrict K) :=
    (memLp_iff.2 (lt_top_iff_ne_top.2 hf)).aestronglyMeasurable
  calc
    _ ≤ C * ‖B‖ₑ * eLpNorm f p (volume.restrict K) *
        (eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)) :=
      hC B f g Dg hf hDg hgq hDgq
    _ ≤ _ := by
      rw [← hgW]
      gcongr
      exact_mod_cast le_self_add

/-- **Local bound for order-one mixed products.** For `p > 2`, `1 < q ≤ p` and a compact `K ⊆ Ω`,
there are an open `W` between `K` and `Ω` with compact closure in `Ω` and a constant `C` such that
`‖B(f, g)‖_{W^{1,q}(K)} ≤ C ‖B‖ ‖f‖_{W^{1,p}(W)} ‖g‖_{W^{1,q}(W)}` for every continuous bilinear map
`B` and all `f`, `g` with finite-dimensional values. At `q = p` this is the local bound for the
algebra property of `W^{1,p}_loc`. -/
theorem exists_eLpNormWkp_one_bilin_le [FiniteDimensional ℝ F] [CompleteSpace H] (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ closure W ⊆ Ω ∧
      ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
        eLpNormWkp q K 1 (fun z => B (f z) (g z)) ≤
          C * ‖B‖ₑ * eLpNormWkp p W 1 f * eLpNormWkp q W 1 g := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  let _ : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨hq1⟩
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨hq1.trans (by exact_mod_cast hqp)⟩
  have hp' : (finrank ℝ ℂ : ℝ≥0) < p := by simpa using hp
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  let W' : Opens ℂ := ⟨W, hWo⟩
  obtain ⟨C₁, hC₁⟩ := W1p.exists_eLpNorm_bilin_add_eLpNorm_deriv_le (μ := volume) (Ω := W')
    (F := F) (G := G) (H := H) hp' hqp hK hKW
  obtain ⟨C₂, hC₂⟩ := W1p.exists_eLpNorm_le_of_holderTriple (μ := volume) (Ω := W') (G := F)
    (r := ∞) hp' le_rfl hK hKW
  refine ⟨W, hWo, hKW, hWc, hWΩ, C₁ * (C₂ + 1) + 1, fun B f g => ?_⟩
  have hq0 : (q : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hKm : volume.restrict K ≤ volume.restrict W := Measure.restrict_mono hKW le_rfl
  -- If `B = 0` or either factor vanishes almost everywhere on `W`, so does the product on `K`.
  have hvanish (h : (fun z => B (f z) (g z)) =ᵐ[volume.restrict W] 0) :
      eLpNormWkp q K 1 (fun z => B (f z) (g z)) = 0 := by
    rw [eLpNormWkp_congr_ae (ae_mono hKm h), eLpNormWkp_zero_fun]
  refine le_mul_enorm_mul_mul_of_ne_top (by simp)
    (fun hB => hvanish (.of_forall fun z => by simp [hB])) (fun hf0 => hvanish ?_)
    (fun hg0 => hvanish ?_) fun hf hg => ?_
  · filter_upwards [ae_eq_zero_of_eLpNormWkp_eq_zero hp0 hf0] with z hz
    simp [hz]
  · filter_upwards [ae_eq_zero_of_eLpNormWkp_eq_zero hq0 hg0] with z hz
    simp [hz]
  obtain ⟨Df, hDf, hfp, hDfp, hfW⟩ := exists_weakFDeriv_memLp_of_eLpNormWkp_one_ne_top hWo hf
  obtain ⟨Dg, hDg, hgq, hDgq, hgW⟩ := exists_weakFDeriv_memLp_of_eLpNormWkp_one_ne_top hWo hg
  -- `f` is locally bounded on `W`, so the weak Leibniz rule applies there.
  have hfloc : MemWkpLoc p W' 1 f :=
    memWkpLoc_succ_iff_of_isOpen.2
      ⟨hfp.memLpLoc, Df, hDf, memWkpLoc_zero_iff.2 hDfp.memLpLoc⟩
  have hLeib := hDf.bilin_of_memLpLoc B hp hq hqp
    ((hfloc.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top) hDfp.memLpLoc
    hDg hgq.memLpLoc hDgq.memLpLoc
  have hint : Opens.interior K ≤ W' := fun z hz => hKW (interior_subset hz)
  set Xf := eLpNorm f p (volume.restrict W) + eLpNorm Df p (volume.restrict W)
  set Xg := eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)
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
    _ = ↑(C₁ * (C₂ + 1)) * ‖B‖ₑ * eLpNormWkp p W 1 f * eLpNormWkp q W 1 g := by
      rw [hfW, hgW]
      push_cast
      ring
    _ ≤ _ := by
      gcongr
      exact_mod_cast le_self_add

end TauCeti
