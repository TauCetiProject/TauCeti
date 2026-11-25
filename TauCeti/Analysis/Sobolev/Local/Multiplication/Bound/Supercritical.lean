/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Multiplication.Supercritical
public import TauCeti.Analysis.Sobolev.Local.Norm
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Higher
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding

/-!
# Local bounds for products of local Sobolev maps for `kp > 2`

Let `Ω ⊆ ℂ` be open, let `1 < p` and let `B : F × G → H` be continuous bilinear with `F` and `G`
finite-dimensional. This file proves the local bounds that accompany the membership theorems of
`TauCeti.Analysis.Sobolev.Local.Multiplication.Supercritical`, including the range `p ≤ 2`,
stated with the `W^{k,p}` size `TauCeti.eLpNormWkp`. On a set `U` whose closure is compact and
contained in `Ω`,

`‖B(f, g)‖_{W^{c,p}(U)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω)} ‖g‖_{W^{b,p}(Ω)}`

for `c ≤ a`, `c ≤ b` and `(a + b - c) p > 2`, with `C` uniform in `B`, `f` and `g`. The proof
follows the induction of the membership theorems. At order zero, Hölder's inequality is combined
with the local `L^∞` bound for a factor with `ap > 2`
(`TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul`) or, when neither factor is bounded,
with the Sobolev bounds `TauCeti.exists_eLpNorm_le_mul_eLpNormWkp_of_inv_sub_inv_le_div_two` at the
exponents of `TauCeti.exists_holderTriple_of_two_lt_add_mul`. The Leibniz step is
`TauCeti.eLpNormWkp_succ_bilin_le_of_hasWeakFDerivOn`. These bounds feed the higher-order
elliptic estimates with Sobolev coefficients.

## Main declarations

* `TauCeti.exists_eLpNorm_bilin_le_of_two_lt_add_mul` and
  `TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul`: the local bounds for products with
  `(a + b) p > 2` and `(a + b - c) p > 2`.
* `TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_mul`,
  `TauCeti.exists_eLpNormWkp_clm_apply_le_of_two_lt_mul` and
  `TauCeti.exists_eLpNormWkp_compL_le_of_two_lt_mul`: the local bounds for the algebra property
  for `kp > 2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, second edition, Theorem 4.39.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ}

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- Hölder's inequality on `U` turns bounds for the factors in `Lˢ(U)` and `Lᵗ(U)`, with
`1/s + 1/t = 1/p`, by their Sobolev norms on `Ω` into a bound for their product in `Lᵖ(U)`. -/
private theorem exists_eLpNorm_bilin_le_of_holderTriple {p : ℝ≥0} (hp : 1 ≤ p) {a b : ℕ}
    {s t : ℝ≥0∞} [ENNReal.HolderTriple s t p] {U : Set ℂ} (hUΩ : U ⊆ Ω) {Cf Cg : ℝ≥0}
    (hCf : ∀ f : ℂ → F, eLpNorm f s (volume.restrict U) ≤ Cf * eLpNormWkp p Ω a f)
    (hCg : ∀ g : ℂ → G, eLpNorm g t (volume.restrict U) ≤ Cg * eLpNormWkp p Ω b g) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNorm (fun z => B (f z) (g z)) p (volume.restrict U) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω a f * eLpNormWkp p Ω b g := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (by exact_mod_cast hp : (1 : ℝ≥0∞) ≤ p)).ne'
  have hUm : volume.restrict U ≤ volume.restrict Ω := Measure.restrict_mono hUΩ le_rfl
  refine ⟨Cf * Cg + 1, fun B f g => ?_⟩
  refine le_mul_eNorm_mul_eLpNormWkp_mul_eLpNormWkp_of_ne_top_imp_le hp0 hp0 hUΩ hUΩ
    (by positivity) (fun h => by rw [eLpNorm_congr_ae h, eLpNorm_zero]) fun hf hg => ?_
  calc
    _ ≤ ‖B‖ₑ * eLpNorm f s (volume.restrict U) * eLpNorm g t (volume.restrict U) :=
      eLpNorm_le_eNorm_mul_eLpNorm_mul_eLpNorm B
        ((memLp_of_eLpNormWkp_ne_top hf).aestronglyMeasurable.mono_measure hUm)
        ((memLp_of_eLpNormWkp_ne_top hg).aestronglyMeasurable.mono_measure hUm)
    _ ≤ ‖B‖ₑ * (Cf * eLpNormWkp p Ω a f) * (Cg * eLpNormWkp p Ω b g) := by
      gcongr
      exacts [hCf f, hCg g]
    _ = ↑(Cf * Cg) * ‖B‖ₑ * eLpNormWkp p Ω a f * eLpNormWkp p Ω b g := by
      push_cast
      ring
    _ ≤ _ := by
      gcongr
      exact_mod_cast le_self_add

omit [FiniteDimensional ℝ F] in
/-- The `Lᵖ(U)` norm is at most the `W^{m,p}(Ω)` norm, for `U ⊆ Ω`. -/
private theorem eLpNorm_le_one_mul_eLpNormWkp {p : ℝ≥0} {m : ℕ} {U : Set ℂ} (hUΩ : U ⊆ Ω)
    (u : ℂ → F) : eLpNorm u p (volume.restrict U) ≤ (1 : ℝ≥0) * eLpNormWkp p Ω m u := by
  rw [ENNReal.coe_one, one_mul]
  exact (eLpNorm_mono_measure u (Measure.restrict_mono hUΩ le_rfl)).trans eLpNorm_le_eLpNormWkp

/-- **Local bound for products in `Lᵖ`.** Let `1 ≤ p` and `(a + b) p > 2`, and let `U` have
compact closure contained in `Ω`. There is a constant `C` such that
`‖B(f, g)‖_{Lᵖ(U)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω)} ‖g‖_{W^{b,p}(Ω)}` for every continuous bilinear map
`B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This is the bound that accompanies
`TauCeti.MemWkpLoc.memLpLoc_bilin_of_two_lt_add_mul`. -/
theorem exists_eLpNorm_bilin_le_of_two_lt_add_mul {p : ℝ≥0} (hp : 1 ≤ p) {a b : ℕ}
    (hab : 2 < ((a + b : ℕ) : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNorm (fun z => B (f z) (g z)) p (volume.restrict U) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω a f * eLpNormWkp p Ω b g := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
  -- If one factor is locally bounded, Hölder's inequality with `L^∞` suffices.
  by_cases ha : 2 < (a : ℝ≥0∞) * p
  · obtain ⟨Cf, hCf⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul (F := F) hp1 ha hU hUΩ
    exact exists_eLpNorm_bilin_le_of_holderTriple hp hUΩ' hCf (eLpNorm_le_one_mul_eLpNormWkp hUΩ')
  by_cases hb : 2 < (b : ℝ≥0∞) * p
  · obtain ⟨Cg, hCg⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul (F := G) hp1 hb hU hUΩ
    exact exists_eLpNorm_bilin_le_of_holderTriple hp hUΩ' (eLpNorm_le_one_mul_eLpNormWkp hUΩ') hCg
  -- Otherwise the Sobolev embedding bounds both factors in finite Hölder exponents.
  obtain ⟨s, t, hps, hpt, hs, ht, hst⟩ := exists_holderTriple_of_two_lt_add_mul hp ha hb hab
  obtain ⟨Cf, hCf⟩ := exists_eLpNorm_le_mul_eLpNormWkp_of_inv_sub_inv_le_div_two (F := F) (k := a)
    hp hps hs hU hUΩ
  obtain ⟨Cg, hCg⟩ := exists_eLpNorm_le_mul_eLpNormWkp_of_inv_sub_inv_le_div_two (F := G) (k := b)
    hp hpt ht hU hUΩ
  exact exists_eLpNorm_bilin_le_of_holderTriple hp hUΩ' hCf hCg

/-- **Local bound for products with three orders.** Let `1 < p`, let `c ≤ a`, `c ≤ b` with
`(a + b - c) p > 2`, and let `U` have compact closure contained in `Ω`. There is a constant `C`
such that `‖B(f, g)‖_{W^{c,p}(U)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω)} ‖g‖_{W^{b,p}(Ω)}` for every
continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This is the
bound that accompanies `TauCeti.MemWkpLoc.bilin_of_two_lt_add_sub_mul`. -/
theorem exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul [CompleteSpace H] {p : ℝ≥0}
    (hp : 1 < p) {a b c : ℕ} (hca : c ≤ a) (hcb : c ≤ b)
    (habc : 2 < ((a + b - c : ℕ) : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp p U c (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω a f * eLpNormWkp p Ω b g := by
  induction c generalizing F G H a b with
  | zero =>
    obtain ⟨C, hC⟩ := exists_eLpNorm_bilin_le_of_two_lt_add_mul (F := F) (G := G) (H := H)
      hp.le (by simpa using habc) hU hUΩ
    exact ⟨C, fun B f g => by simpa only [eLpNormWkp_zero] using hC B f g⟩
  | succ c ih =>
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hle {n : ℕ} (hn : a + 1 + (b + 1) - (c + 1) ≤ n) : 2 < (n : ℝ≥0) * p :=
      habc.trans_le (mul_le_mul_left (Nat.cast_le.2 hn) _)
    -- The order-zero bound controls the `Lᵖ` part. Both terms of the Leibniz rule keep the value
    -- of `a + b - c` and lose one order, for the bilinear maps `B.precompL ℂ` and
    -- `B.precompR ℂ`.
    obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_bilin_le_of_two_lt_add_mul (F := F) (G := G) (H := H)
      hp.le (a := a + 1) (b := b + 1) (hle (by omega)) hU hUΩ
    have habc' : a + (b + 1) - c = a + 1 + (b + 1) - (c + 1) := by omega
    have habc'' : a + 1 + b - c = a + 1 + (b + 1) - (c + 1) := by omega
    obtain ⟨Cl, hCl⟩ := ih (F := ℂ →L[ℝ] F) (G := G) (H := ℂ →L[ℝ] H) (a := a) (b := b + 1)
      (by omega) (by omega) (by rwa [habc'])
    obtain ⟨Cr, hCr⟩ := ih (F := F) (G := ℂ →L[ℝ] G) (H := ℂ →L[ℝ] H) (a := a + 1) (b := b)
      (by omega) (by omega) (by rwa [habc''])
    refine ⟨C₀ + Cl + Cr + 1, fun B f g => ?_⟩
    have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
    have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hp1).ne'
    have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
    refine le_mul_eNorm_mul_eLpNormWkp_mul_eLpNormWkp_of_ne_top_imp_le hp0 hp0 hUΩ' hUΩ'
      (by positivity) (fun h => by rw [eLpNormWkp_congr_ae h, eLpNormWkp_zero_fun]) fun hf hg => ?_
    -- Weak derivatives of the factors realizing their norms on `Ω`.
    obtain ⟨Df, hDf, -, hfΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hf
    obtain ⟨Dg, hDg, -, hgΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hg
    have hLeib := hDf.bilin_of_two_lt_add_mul B hp hDg (memWkpLoc_of_eLpNormWkp_ne_top hf)
      (memWkpLoc_of_eLpNormWkp_ne_top hg) (hle (by omega))
    exact eLpNormWkp_succ_bilin_le_of_hasWeakFDerivOn B hp1
      (hLeib.mono fun z hz => hUΩ' (interior_subset hz)) (hC₀ B f g)
      ((hCl (B.precompL ℂ) Df g).trans (by
        gcongr
        exacts [eNorm_le_iff_norm_le.2 (B.norm_precompL_le ℂ), hfΩ ▸ le_add_self]))
      ((hCr (B.precompR ℂ) f Dg).trans (by
        gcongr
        exacts [eNorm_le_iff_norm_le.2 (B.norm_precompR_le ℂ), hgΩ ▸ le_add_self]))

/-- **Local bound for the algebra property for `kp > 2`.** Let `1 < p` and `k p > 2`, and let
`U` have compact closure contained in `Ω`. There is a constant `C` such that
`‖B(f, g)‖_{W^{k,p}(U)} ≤ C ‖B‖ ‖f‖_{W^{k,p}(Ω)} ‖g‖_{W^{k,p}(Ω)}` for every continuous bilinear
map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This includes `p ≤ 2` for
`k ≥ 2`, and is the bound that accompanies `TauCeti.MemWkpLoc.bilin_of_two_lt_mul`. -/
theorem exists_eLpNormWkp_bilin_le_of_two_lt_mul [CompleteSpace H] {p : ℝ≥0} (hp : 1 < p)
    {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp p U k (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω k f * eLpNormWkp p Ω k g :=
  exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul hp le_rfl le_rfl
    (by rwa [Nat.add_sub_cancel]) hU hUΩ

/-- **Local bound for coefficient fields for `kp > 2`.** Let `1 < p` and `k p > 2`, and let `U`
have compact closure contained in `Ω`. There is a constant `C` such that
`‖z ↦ A z (u z)‖_{W^{k,p}(U)} ≤ C ‖A‖_{W^{k,p}(Ω)} ‖u‖_{W^{k,p}(Ω)}` for every coefficient field
`A : ℂ → F →L[ℝ] G` and every `u : ℂ → F`. This is the bound that accompanies
`TauCeti.MemWkpLoc.clm_apply_of_two_lt_mul`. -/
theorem exists_eLpNormWkp_clm_apply_le_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → F →L[ℝ] G) (u : ℂ → F),
      eLpNormWkp p U k (fun z => A z (u z)) ≤
        C * eLpNormWkp p Ω k A * eLpNormWkp p Ω k u := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_mul (F := F →L[ℝ] G) (G := F) (H := G)
    hp hkp hU hUΩ
  exact ⟨C, fun A u => le_mul_mul_of_le_mul_eNorm_mul_mul ContinuousLinearMap.norm_id_le
    (hC (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) A u)⟩

/-- **Local bound for compositions of fields of linear maps for `kp > 2`.** Let `1 < p` and
`k p > 2`, and let `U` have compact closure contained in `Ω`. There is a constant `C` such that
`‖z ↦ A z ∘L T z‖_{W^{k,p}(U)} ≤ C ‖A‖_{W^{k,p}(Ω)} ‖T‖_{W^{k,p}(Ω)}` for all fields
`A : ℂ → G →L[ℝ] H` and `T : ℂ → F →L[ℝ] G`. This is the bound that accompanies
`TauCeti.MemWkpLoc.compL_of_two_lt_mul`. -/
theorem exists_eLpNormWkp_compL_le_of_two_lt_mul [FiniteDimensional ℝ H] {p : ℝ≥0} (hp : 1 < p)
    {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → G →L[ℝ] H) (T : ℂ → F →L[ℝ] G),
      eLpNormWkp p U k (fun z => (A z).comp (T z)) ≤
        C * eLpNormWkp p Ω k A * eLpNormWkp p Ω k T := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_mul (F := G →L[ℝ] H) (G := F →L[ℝ] G)
    (H := F →L[ℝ] H) hp hkp hU hUΩ
  exact ⟨C, fun A T => le_mul_mul_of_le_mul_eNorm_mul_mul
    (ContinuousLinearMap.norm_compL_le ℝ F G H) (hC (ContinuousLinearMap.compL ℝ F G H) A T)⟩

/-- The bound at `p = 4/3` and `k = 2`, where `kp = 8/3 > 2` while `p < 2`: on the disc of radius
`1/2`, the `W^{2,4/3}` norm of a product is controlled by the norms of the factors on the unit
disc. -/
example [CompleteSpace H] :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) (1 / 2)) 2 (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) 1) 2 f *
          eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) 1) 2 g :=
  exists_eLpNormWkp_bilin_le_of_two_lt_mul (Ω := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩)
    (by norm_num) (by norm_num)
    ((isCompact_closedBall 0 (1 / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall)
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num)))

end TauCeti
