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

/-- A finite first-order size on an open set is realized by a weak derivative, and then the
function and that derivative are `Lᵖ` there. -/
private theorem exists_weakFDeriv_memLp_of_eLpNormWkp_one_ne_top {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ≥0∞} {W : Set ℂ} (hW : IsOpen W) {u : ℂ → E}
    (hu : eLpNormWkp r W 1 u ≠ ∞) :
    ∃ Du : ℂ → ℂ →L[ℝ] E, HasWeakFDerivOn volume ⟨W, hW⟩ u Du ∧
      MemLp u r (volume.restrict W) ∧ MemLp Du r (volume.restrict W) ∧
      eLpNormWkp r W 1 u = eLpNorm u r (volume.restrict W) + eLpNorm Du r (volume.restrict W) := by
  have hW' : interior W = ((⟨W, hW⟩ : Opens ℂ) : Set ℂ) := hW.interior_eq
  rw [eLpNormWkp_succ, ENNReal.add_ne_top] at hu
  obtain ⟨Du, hDu, hlt⟩ : ∃ Du : ℂ → ℂ →L[ℝ] E,
      HasWeakFDerivOn volume (Opens.interior W) u Du ∧ eLpNorm Du r (volume.restrict W) < ∞ := by
    simpa [iInf_lt_iff, lt_top_iff_ne_top] using hu.2
  have hDu' : HasWeakFDerivOn volume ⟨W, hW⟩ u Du := hDu.mono (le_of_eq (SetLike.ext' hW'.symm))
  refine ⟨Du, hDu', memLp_iff.2 (lt_top_iff_ne_top.2 hu.1), memLp_iff.2 hlt, ?_⟩
  exact (eLpNormWkp_succ_eq_of_hasWeakFDerivOn hDu').trans (by rw [eLpNormWkp_zero]; rfl)

/-- A function that is `Lᵖ` on a set is locally `Lᵖ` there. -/
private theorem memLpLoc_of_memLp {E : Type*} [NormedAddCommGroup E] {r : ℝ≥0∞} {W : Set ℂ}
    {u : ℂ → E} (hu : MemLp u r (volume.restrict W)) : MemLpLoc r W u :=
  memLpLoc_iff.2 fun _ hLW _ => hu.mono_measure (Measure.restrict_mono hLW le_rfl)

omit [FiniteDimensional ℝ G] in
/-- A nonzero continuous bilinear map has nonzero extended operator norm. -/
private theorem enorm_ne_zero_of_ne_zero (B : F →L[ℝ] G →L[ℝ] H) (hB : B ≠ 0) : ‖B‖ₑ ≠ 0 := by
  rw [← ofReal_norm, Ne, ENNReal.ofReal_eq_zero, not_le]
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (mt B.opNorm_zero_iff.1 hB))

/-- A function of zero first-order size on a set vanishes almost everywhere there. -/
private theorem ae_eq_zero_of_eLpNormWkp_one_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ≥0∞} (hr : r ≠ 0) {W : Set ℂ} {u : ℂ → E}
    (hu : eLpNormWkp r W 1 u = 0) : u =ᵐ[volume.restrict W] 0 :=
  (eLpNorm_eq_zero_iff hr).1 (le_antisymm (hu ▸ eLpNorm_le_eLpNormWkp) zero_le)

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
  by_cases hB : B = 0
  · exact (hvanish (.of_forall fun z => by simp [hB])).le.trans zero_le
  by_cases hf0 : eLpNorm f p (volume.restrict K) = 0
  · refine (hvanish ?_).le.trans zero_le
    filter_upwards [(eLpNorm_eq_zero_iff (by simpa using (zero_lt_two.trans hp).ne')).1 hf0]
      with z hz
    simp [hz]
  by_cases hg0 : eLpNormWkp q W 1 g = 0
  · refine (hvanish ?_).le.trans zero_le
    filter_upwards [ae_mono (Measure.restrict_mono hKW le_rfl)
      (ae_eq_zero_of_eLpNormWkp_one_eq_zero hq0 hg0)] with z hz
    simp [hz]
  have hCB : ((C + 1 : ℝ≥0) : ℝ≥0∞) * ‖B‖ₑ ≠ 0 :=
    mul_ne_zero (by simp) (enorm_ne_zero_of_ne_zero B hB)
  by_cases hfin : eLpNorm f p (volume.restrict K) ≠ ∞ ∧ eLpNormWkp q W 1 g ≠ ∞
  · obtain ⟨Dg, hDg, hgq, hDgq, hgW⟩ := exists_weakFDeriv_memLp_of_eLpNormWkp_one_ne_top hWo hfin.2
    have hf : AEStronglyMeasurable f (volume.restrict K) :=
      (memLp_iff.2 (lt_top_iff_ne_top.2 hfin.1)).aestronglyMeasurable
    calc
      _ ≤ C * ‖B‖ₑ * eLpNorm f p (volume.restrict K) *
          (eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)) :=
        hC B f g Dg hf hDg hgq hDgq
      _ ≤ _ := by
        rw [← hgW]
        gcongr
        exact_mod_cast le_self_add
  · -- Otherwise one factor on the right is infinite and the others are nonzero.
    rw [not_and_or, not_not, not_not] at hfin
    rcases hfin with hf | hg
    · rw [hf, ENNReal.mul_top hCB, ENNReal.top_mul hg0]
      exact le_top
    · rw [hg, ENNReal.mul_top (mul_ne_zero hCB hf0)]
      exact le_top

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
  -- If either factor vanishes almost everywhere on `W`, so does the product on `K`.
  have hvanish (h : (fun z => B (f z) (g z)) =ᵐ[volume.restrict W] 0) :
      eLpNormWkp q K 1 (fun z => B (f z) (g z)) = 0 := by
    rw [eLpNormWkp_congr_ae (ae_mono hKm h), eLpNormWkp_zero_fun]
  have hC0 : ((C₁ * (C₂ + 1) + 1 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simp
  by_cases hfg : eLpNormWkp p W 1 f = ∞ ∨ eLpNormWkp q W 1 g = ∞
  · -- The right side is infinite unless `B = 0` or one factor has size zero.
    by_cases hB : B = 0
    · exact (hvanish (.of_forall fun z => by simp [hB])).le.trans zero_le
    have hBe : ‖B‖ₑ ≠ 0 := enorm_ne_zero_of_ne_zero B hB
    by_cases hf0 : eLpNormWkp p W 1 f = 0
    · refine (hvanish ?_).le.trans zero_le
      filter_upwards [ae_eq_zero_of_eLpNormWkp_one_eq_zero hp0 hf0] with z hz
      simp [hz]
    by_cases hg0 : eLpNormWkp q W 1 g = 0
    · refine (hvanish ?_).le.trans zero_le
      filter_upwards [ae_eq_zero_of_eLpNormWkp_one_eq_zero hq0 hg0] with z hz
      simp [hz]
    rcases hfg with hf | hg
    · rw [hf, ENNReal.mul_top (mul_ne_zero hC0 hBe), ENNReal.top_mul hg0]
      exact le_top
    · rw [hg, ENNReal.mul_top (mul_ne_zero (mul_ne_zero hC0 hBe) hf0)]
      exact le_top
  rw [not_or] at hfg
  obtain ⟨Df, hDf, hfp, hDfp, hfW⟩ := exists_weakFDeriv_memLp_of_eLpNormWkp_one_ne_top hWo
    hfg.1
  obtain ⟨Dg, hDg, hgq, hDgq, hgW⟩ := exists_weakFDeriv_memLp_of_eLpNormWkp_one_ne_top hWo
    hfg.2
  -- `f` is locally bounded on `W`, so the weak Leibniz rule applies there.
  have hfloc : MemWkpLoc p W' 1 f :=
    memWkpLoc_succ_iff_of_isOpen.2
      ⟨memLpLoc_of_memLp hfp, Df, hDf, memWkpLoc_zero_iff.2 (memLpLoc_of_memLp hDfp)⟩
  have hLeib := hDf.bilin_of_memLpLoc B hp hq hqp
    ((hfloc.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top) (memLpLoc_of_memLp hDfp)
    hDg (memLpLoc_of_memLp hgq) (memLpLoc_of_memLp hDgq)
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
