/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey
public import TauCeti.Analysis.Sobolev.Local.Norm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Local.W1p
import TauCeti.Analysis.Sobolev.Morrey.Exponent
import TauCeti.Analysis.Sobolev.W1p.SobolevEmbedding
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# The Sobolev embedding for local Sobolev maps and Morrey for `kp > 2`

Let `Ω ⊆ ℂ` be open, let `F` be a finite-dimensional real normed space and let `1 ≤ q ≤ s < ∞`
with `1/q - 1/s ≤ 1/2`. This includes the critical exponent `1/s = 1/q - 1/2` for `q < 2`, every
finite `s ≥ q` for `q ≥ 2`, and every intermediate exponent. This file proves the embedding
`W^{1,q}_loc(Ω, F) ⊂ L^s_loc(Ω, F)` for the local classes `TauCeti.MemWkpLoc` and
`TauCeti.MemLpLoc`, with the estimate

`‖u‖_{L^s(V)} ≤ C ‖u‖_{W^{1,q}(W)}` whenever `V` has compact closure inside the open set `W`,

where `‖u‖_{W^{1,q}(W)}` is `TauCeti.eLpNormWkp q W 1 u`. Applied to the weak derivatives, it
lowers the derivative order while raising the integrability exponent:
`W^{k+1,q}_loc ⊂ W^{k,s}_loc`, with the corresponding estimate.

Iterating this, a member of `W^{k,p}_loc(Ω, F)` with `1 ≤ p` and `kp > 2` lies in
`W^{1,r}_loc(Ω, F)` for some finite `r > 2`. While `p ≤ 2`, one step lowers the order with an
exponent supplied by `TauCeti.exists_le_and_inv_sub_inv_le_and_lt_mul`. The order-one Morrey
embedding of `TauCeti.Analysis.Sobolev.Local.Morrey` then makes the precise representative of `u`
continuous on `Ω`, and the order-one `L^∞` bound gives the local estimate
`‖u‖_{L^∞(V)} ≤ C ‖u‖_{W^{k,p}(W)}`. These continuity and `L^∞` results hold for every
`1 ≤ p ≤ ∞` with `kp > 2`; Hölder and higher `C^{m,α}` regularity are not treated here.

The scalar estimate is the interior Sobolev embedding of `TauCeti.W1p`
(`TauCeti.W1p.exists_eLpNorm_value_le_of_inv_sub_inv_le`), applied on `W` through
`TauCeti.exists_w1p_enorm_le_eLpNormWkp`; for `q > 2` the `L^∞` bound uses
`TauCeti.W1p.exists_lpInftyEmbeddingL_of_isCompact_closure` in the same way. The vector-valued
estimates follow in a basis of `F`.

## Main declarations

* `TauCeti.exists_eLpNorm_le_mul_eLpNormWkp_one`: the local Sobolev inequality
  `‖u‖_{L^s(V)} ≤ C ‖u‖_{W^{1,q}(W)}`.
* `TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_one`: the order-one `L^∞` bound for `q > 2`.
* `TauCeti.MemWkpLoc.memLpLoc_top`: the local `L^∞` embedding `W^{1,q}_loc ⊂ L^∞_loc` for `q > 2`.
* `TauCeti.MemWkpLoc.memLpLoc_of_inv_sub_inv_le`: the embedding `W^{1,q}_loc ⊂ L^s_loc`.
* `TauCeti.MemWkpLoc.exists_two_lt_le_memLpLoc_of_one_lt`: for `p > 2` and `s > 1`, membership of
  `W^{1,s}_loc` in `L^r_loc` for some finite `2 < r ≤ p`.
* `TauCeti.MemWkpLoc.of_succ_of_inv_sub_inv_le`: order lowering `W^{k+1,q}_loc ⊂ W^{k,s}_loc`.
* `TauCeti.exists_eLpNormWkp_le_mul_eLpNormWkp_succ`: the estimate for order lowering.
* `TauCeti.MemWkpLoc.exists_two_lt_memWkpLoc_one_of_two_lt_mul`: for `kp > 2`, membership in
  `W^{1,r}_loc` for some finite `r > 2`.
* `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul` and
  `TauCeti.MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul`: continuous representatives for
  `kp > 2`.
* `TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul`: the local `L^∞` bound for
  `kp > 2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev embeddings for local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.3, Theorem 6.
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {q s : ℝ≥0}
  {Ω W : Opens ℂ} {V : Set ℂ} {k : ℕ} {u : ℂ → F}

/-- A bound for the values of `W1p volume W q` in `L^t(V)` passes to real functions, with their
`W^{1,q}(W)` norm on the right. -/
private theorem exists_eLpNorm_le_mul_eLpNormWkp_one_real [Fact (1 ≤ (q : ℝ≥0∞))] {t : ℝ≥0∞}
    (hVW : closure V ⊆ W) (hW1p : ∃ C : ℝ≥0, ∀ v : W1p volume W (q : ℝ≥0∞),
      eLpNorm (W1p.value v) t (volume.restrict V) ≤ C * ‖v‖ₑ) :
    ∃ C : ℝ≥0, ∀ u : ℂ → ℝ, eLpNorm u t (volume.restrict V) ≤ C * eLpNormWkp q W 1 u := by
  obtain ⟨C, hC⟩ := hW1p
  -- `C + 1` is nonzero, so that it absorbs an infinite right-hand side: `0 * ∞ = 0` in `ℝ≥0∞`.
  refine ⟨C + 1, fun u => ?_⟩
  by_cases hfin : eLpNormWkp q W 1 u = ∞
  · rw [hfin, ENNReal.mul_top (by simp)]
    exact le_top
  obtain ⟨v, hv, hnorm⟩ := exists_w1p_enorm_le_eLpNormWkp hfin
  calc eLpNorm u t (volume.restrict V)
      = eLpNorm (W1p.value v) t (volume.restrict V) :=
        eLpNorm_congr_ae (Filter.EventuallyEq.symm
          (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVW) hv))
    _ ≤ C * ‖v‖ₑ := hC v
    _ ≤ (C + 1 : ℝ≥0) * eLpNormWkp q W 1 u := by
        gcongr
        exact_mod_cast le_self_add

variable [FiniteDimensional ℝ F]

/-- A bound for the values of `W1p volume W q` in `L^t(V)`, with `1 ≤ t`, passes to functions
valued in `F` coordinatewise in a basis of `F`. -/
private theorem exists_eLpNorm_le_mul_eLpNormWkp_one_of_w1p [Fact (1 ≤ (q : ℝ≥0∞))] {t : ℝ≥0∞}
    (ht : 1 ≤ t) (hVW : closure V ⊆ W) (hW1p : ∃ C : ℝ≥0, ∀ v : W1p volume W (q : ℝ≥0∞),
      eLpNorm (W1p.value v) t (volume.restrict V) ≤ C * ‖v‖ₑ) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNorm u t (volume.restrict V) ≤ C * eLpNormWkp q W 1 u := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_mul_eLpNormWkp_one_real hVW hW1p
  set b := Module.finBasis ℝ F
  set ℓ : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  set A : Fin (finrank ℝ F) → ℝ →L[ℝ] F := fun i => (ContinuousLinearMap.id ℝ ℝ).smulRight (b i)
  refine ⟨∑ i, ‖A i‖₊ * C * ‖ℓ i‖₊, fun u => ?_⟩
  have hsum : u = ∑ i, fun z => A i (ℓ i (u z)) := by
    funext z
    simp only [Finset.sum_apply, A, ℓ, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]
    exact (b.sum_repr (u z)).symm
  calc eLpNorm u t (volume.restrict V)
      = eLpNorm (∑ i, fun z => A i (ℓ i (u z))) t (volume.restrict V) := by rw [← hsum]
    _ ≤ ∑ i, eLpNorm (fun z => A i (ℓ i (u z))) t (volume.restrict V) :=
        eLpNorm_sum_le ht
    _ ≤ ∑ i, ‖A i‖ₑ * eLpNorm (fun z => ℓ i (u z)) t (volume.restrict V) := by
        gcongr with i
        exact eLpNorm_clm_comp_le (A i)
    _ ≤ ∑ i, ‖A i‖ₑ * (C * (‖ℓ i‖ₑ * eLpNormWkp q W 1 u)) := by
        gcongr with i
        exact (hC _).trans (by gcongr; exact eLpNormWkp_clm_comp_le (ℓ i))
    _ = (∑ i, ‖A i‖₊ * C * ‖ℓ i‖₊ : ℝ≥0) * eLpNormWkp q W 1 u := by
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [eNorm_eq_nnNorm]
        ring

/-- **The local Sobolev inequality.** Let `1 ≤ q ≤ s < ∞` with `1/q - 1/s ≤ 1/2`, and let `V` have
compact closure inside the open set `W ⊆ ℂ`. There is a constant `C` such that every
`u : ℂ → F` satisfies `‖u‖_{L^s(V)} ≤ C ‖u‖_{W^{1,q}(W)}`. The case `1/s = 1/q - 1/2` is the
critical Sobolev embedding for `q < 2`; for `q ≥ 2` every finite `s ≥ q` is allowed. -/
theorem exists_eLpNorm_le_mul_eLpNormWkp_one (hq : 1 ≤ q) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNorm u s (volume.restrict V) ≤ C * eLpNormWkp q W 1 u :=
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  exists_eLpNorm_le_mul_eLpNormWkp_one_of_w1p (by exact_mod_cast hq.trans hqs) hVW
    (W1p.exists_eLpNorm_value_le_of_inv_sub_inv_le (μ := volume) hqs
      (by rwa [Complex.finrank_real_complex, Nat.cast_ofNat]) hVc hVW)

/-- **The local `L^∞` bound for `q > 2`.** Let `2 < q ≤ ∞`, and let `V` have compact closure
inside the open set `W ⊆ ℂ`. There is a constant `C` such that every `u : ℂ → F` satisfies
`‖u‖_{L^∞(V)} ≤ C ‖u‖_{W^{1,q}(W)}`. -/
theorem exists_eLpNorm_top_le_mul_eLpNormWkp_one {q : ℝ≥0∞} (hq : 2 < q)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNorm u ∞ (volume.restrict V) ≤ C * eLpNormWkp q W 1 u := by
  rcases eq_or_ne q ∞ with rfl | hqt
  · refine ⟨1, fun u => ?_⟩
    rw [ENNReal.coe_one, one_mul]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume
      (subset_closure.trans hVW))).trans eLpNorm_le_eLpNormWkp
  lift q to ℝ≥0 using hqt
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨one_le_two.trans hq.le⟩
  refine exists_eLpNorm_le_mul_eLpNormWkp_one_of_w1p le_top hVW ?_
  obtain ⟨S, hS⟩ := W1p.exists_lpInftyEmbeddingL_of_isCompact_closure (μ := volume) (Ω := W)
    (q := q) (by rw [Complex.finrank_real_complex, Nat.cast_ofNat]; exact_mod_cast hq) hVc hVW
  refine ⟨‖S‖₊, fun v => ?_⟩
  rw [← eLpNorm_congr_ae (hS v), ← Lp.eNorm_def, ← eNorm_eq_nnNorm]
  exact S.le_opENorm v

/-- **The local `L^∞` Sobolev embedding for `q > 2`.** Every `u ∈ W^{1,q}_loc(Ω, F)` with
`2 < q ≤ ∞` is locally `L^∞` on `Ω`. -/
theorem MemWkpLoc.memLpLoc_top {q : ℝ≥0∞} (hu : MemWkpLoc q Ω 1 u) (hq : 2 < q) :
    MemLpLoc ∞ Ω u := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  have hKc : closure K = K := hK.isClosed.closure_eq
  obtain ⟨C, hC⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_one (F := F) (W := W) hq
    (by rwa [hKc]) (by rwa [hKc])
  exact memLp_iff.2 ((hC u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_top_iff_ne_top.2 (hu.eLpNormWkp_ne_top_of_closure_subset hWc hWΩ))))

/-- **The local Sobolev embedding.** If `1 ≤ q ≤ s < ∞` and `1/q - 1/s ≤ 1/2`, every
`u ∈ W^{1,q}_loc(Ω, F)` is locally `L^s` on `Ω`. This includes the critical exponent
`1/s = 1/q - 1/2` for `q < 2`. -/
theorem MemWkpLoc.memLpLoc_of_inv_sub_inv_le (hu : MemWkpLoc q Ω 1 u) (hq : 1 ≤ q)
    (hqs : q ≤ s) (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) : MemLpLoc s Ω u := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  have hKc : closure K = K := hK.isClosed.closure_eq
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_mul_eLpNormWkp_one (F := F) (W := W) hq hqs hgap
    (by rwa [hKc]) (by rwa [hKc])
  exact memLp_iff.2 ((hC u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_top_iff_ne_top.2 (hu.eLpNormWkp_ne_top_of_closure_subset hWc hWΩ))))

/-- **Order-one Sobolev upgrade above `2`.** If `2 < p ≤ ∞` and `1 < s ≤ ∞`, every
`u ∈ W^{1,s}_loc(Ω, F)` belongs to `L^r_loc(Ω, F)` for some finite exponent `r` with
`2 < r ≤ p`. -/
theorem MemWkpLoc.exists_two_lt_le_memLpLoc_of_one_lt {p s : ℝ≥0∞} (hu : MemWkpLoc s Ω 1 u)
    (hp : 2 < p) (hs : 1 < s) : ∃ r : ℝ≥0, 2 < r ∧ (r : ℝ≥0∞) ≤ p ∧ MemLpLoc r Ω u := by
  let p' : ℝ≥0 := (min p 3).toNNReal
  have hp'_coe : (p' : ℝ≥0∞) = min p 3 :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right p 3))
  have hp' : 2 < p' := by
    rw [← ENNReal.coe_lt_coe, hp'_coe]
    exact lt_min hp (by exact_mod_cast (by norm_num : 2 < 3))
  have hp'p : (p' : ℝ≥0∞) ≤ p := hp'_coe.le.trans (min_le_left p 3)
  let s' : ℝ≥0 := (min s (p' : ℝ≥0∞)).toNNReal
  have hs'_coe : (s' : ℝ≥0∞) = min s p' :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right s p'))
  have hs' : 1 < s' := by
    rw [← ENNReal.coe_lt_coe, hs'_coe]
    exact lt_min hs (ENNReal.coe_lt_coe.2 (one_lt_two.trans hp'))
  have hs'p' : s' ≤ p' := ENNReal.coe_le_coe.1 (hs'_coe.le.trans (min_le_right s p'))
  have hu' : MemWkpLoc s' Ω 1 u := hu.mono_exponent (hs'_coe.le.trans (min_le_left s p'))
  have hp'R : (2 : ℝ) < p' := by exact_mod_cast hp'
  have hs'R : (1 : ℝ) < s' := by exact_mod_cast hs'
  have hs'0 : (0 : ℝ) < s' := zero_lt_one.trans hs'R
  have hp'0 : (0 : ℝ) < p' := by linarith
  rcases le_or_gt ((s' : ℝ)⁻¹ - (p' : ℝ)⁻¹) 2⁻¹ with hgap | hgap
  · exact ⟨p', hp', hp'p,
      hu'.memLpLoc_of_inv_sub_inv_le (by exact_mod_cast hs'R.le) hs'p' hgap⟩
  · set b : ℝ := (s' : ℝ)⁻¹ - 2⁻¹
    have hp'_inv_pos : 0 < (p' : ℝ)⁻¹ := inv_pos.2 hp'0
    have hb_gt_p' : (p' : ℝ)⁻¹ < b := by dsimp only [b]; linarith
    have hb_pos : 0 < b := hp'_inv_pos.trans hb_gt_p'
    have hs'_inv_lt : (s' : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs'R
    have hb_lt_half : b < 2⁻¹ := by dsimp only [b]; linarith
    let r : ℝ≥0 := ⟨b⁻¹, by positivity⟩
    have hr_coe : (r : ℝ) = b⁻¹ := NNReal.coe_mk b⁻¹ (by positivity)
    have hr_inv : (r : ℝ)⁻¹ = b := by rw [hr_coe, inv_inv]
    have hr_gt2 : 2 < r := by
      rw [← NNReal.coe_lt_coe, hr_coe]
      have h := (inv_lt_inv₀ (by positivity : (0 : ℝ) < 2⁻¹) hb_pos).2 hb_lt_half
      norm_num at h
      exact_mod_cast h
    have hr_le_p' : r ≤ p' := by
      rw [← NNReal.coe_le_coe, hr_coe]
      have h := (inv_lt_inv₀ hb_pos hp'_inv_pos).2 hb_gt_p'
      rw [inv_inv] at h
      exact h.le
    have hs'_le_r : s' ≤ r := by
      rw [← NNReal.coe_le_coe, hr_coe]
      have hb_lt_s' : b < (s' : ℝ)⁻¹ := by dsimp only [b]; linarith
      have h := (inv_lt_inv₀ (inv_pos.2 hs'0) hb_pos).2 hb_lt_s'
      rw [inv_inv] at h
      exact h.le
    exact ⟨r, hr_gt2, (ENNReal.coe_le_coe.2 hr_le_p').trans hp'p,
      hu'.memLpLoc_of_inv_sub_inv_le (by exact_mod_cast hs'R.le) hs'_le_r
        (by rw [hr_inv]; dsimp only [b]; linarith)⟩

/-- **Order lowering.** If `1 ≤ q ≤ s < ∞` and `1/q - 1/s ≤ 1/2`, then
`W^{k+1,q}_loc(Ω, F) ⊂ W^{k,s}_loc(Ω, F)`: the function and its weak derivatives through order `k`
gain integrability, and the same weak derivatives serve. -/
theorem MemWkpLoc.of_succ_of_inv_sub_inv_le (hu : MemWkpLoc q Ω (k + 1) u) (hq : 1 ≤ q)
    (hqs : q ≤ s) (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) : MemWkpLoc s Ω k u := by
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 (hu.memLpLoc_of_inv_sub_inv_le hq hqs hgap)
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv_of_isOpen
    exact memWkpLoc_succ_iff_of_isOpen.2
      ⟨(hu.of_le (by omega)).memLpLoc_of_inv_sub_inv_le hq hqs hgap, D, hD, ih hDk⟩

/-- **The estimate for order lowering.** Let `1 ≤ q ≤ s < ∞` with `1/q - 1/s ≤ 1/2`, and let `V`
have compact closure inside the open set `W ⊆ ℂ`. There is a constant `C` such that every
`u : ℂ → F` satisfies `‖u‖_{W^{k,s}(V)} ≤ C ‖u‖_{W^{k+1,q}(W)}`. -/
theorem exists_eLpNormWkp_le_mul_eLpNormWkp_succ (hq : 1 ≤ q) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNormWkp s V k u ≤ C * eLpNormWkp q W (k + 1) u := by
  induction k generalizing F with
  | zero =>
    obtain ⟨C, hC⟩ := exists_eLpNorm_le_mul_eLpNormWkp_one (F := F) hq hqs hgap hVc hVW
    exact ⟨C, fun u => by simpa only [eLpNormWkp_zero] using hC u⟩
  | succ k ih =>
    obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_le_mul_eLpNormWkp_one (F := F) hq hqs hgap hVc hVW
    obtain ⟨C₁, hC₁⟩ := ih (F := ℂ →L[ℝ] F)
    -- The `+ 1` keeps the constant nonzero, for the case of an infinite right-hand side.
    refine ⟨C₀ + C₁ + 1, fun u => ?_⟩
    by_cases hfin : eLpNormWkp q W (k + 1 + 1) u = ∞
    · rw [hfin, ENNReal.mul_top (by simp)]
      exact le_top
    obtain ⟨D, hD, -⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hfin
    rw [Opens.interior_coe] at hD
    have hDV : HasWeakFDerivOn volume (Opens.interior V) u D :=
      hD.mono (SetLike.coe_subset_coe.1 (interior_subset.trans (subset_closure.trans hVW)))
    have h1 : eLpNormWkp q W 1 u ≤ eLpNormWkp q W (k + 1 + 1) u :=
      eLpNormWkp_mono_order (by omega)
    have h2 : eLpNormWkp q W (k + 1) D ≤ eLpNormWkp q W (k + 1 + 1) u := by
      rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD (k := k + 1)]
      exact le_add_self
    calc eLpNormWkp s V (k + 1) u
        ≤ eLpNorm u s (volume.restrict V) + eLpNormWkp s V k D := eLpNormWkp_succ_le hDV
      _ ≤ C₀ * eLpNormWkp q W 1 u + C₁ * eLpNormWkp q W (k + 1) D :=
          add_le_add (hC₀ u) (hC₁ D)
      _ ≤ C₀ * eLpNormWkp q W (k + 1 + 1) u + C₁ * eLpNormWkp q W (k + 1 + 1) u := by
          gcongr
      _ = (C₀ + C₁ : ℝ≥0) * eLpNormWkp q W (k + 1 + 1) u := by
          push_cast
          ring
      _ ≤ (C₀ + C₁ + 1 : ℝ≥0) * eLpNormWkp q W (k + 1 + 1) u :=
          mul_le_mul_left (ENNReal.coe_le_coe.2 le_self_add) _

/-- **Order one with exponent above two from `kp > 2`.** If `1 ≤ p ≤ ∞` and `2 < k p`, every
`u ∈ W^{k,p}_loc(Ω, F)` lies in `W^{1,r}_loc(Ω, F)` for some finite `r > 2`. -/
theorem MemWkpLoc.exists_two_lt_memWkpLoc_one_of_two_lt_mul {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hu : MemWkpLoc p Ω k u) :
    ∃ r : ℝ≥0, 2 < r ∧ MemWkpLoc r Ω 1 u := by
  induction k generalizing p with
  | zero => simp at hkp
  | succ k ih =>
    by_cases hp2 : 2 < p
    · rcases eq_or_ne p ∞ with rfl | hpt
      · exact ⟨3, by norm_num, (hu.of_le (by omega)).mono_exponent le_top⟩
      lift p to ℝ≥0 using hpt
      exact ⟨p, by exact_mod_cast hp2, hu.of_le (by omega)⟩
    lift p to ℝ≥0 using ne_top_of_le_ne_top ENNReal.ofNat_ne_top (not_lt.1 hp2)
    obtain ⟨s, hps, hgap, hks⟩ := exists_le_and_inv_sub_inv_le_and_lt_mul (n := 2)
      (by exact_mod_cast not_lt.1 hp2) (by exact_mod_cast hkp)
    exact ih (p := s) (hp.trans (by exact_mod_cast hps)) (by exact_mod_cast hks)
      (hu.of_succ_of_inv_sub_inv_le (by exact_mod_cast hp) hps (by exact_mod_cast hgap))

/-- **Morrey for `kp > 2`: continuity.** If `1 ≤ p ≤ ∞` and `2 < k p`, the precise representative
of `u ∈ W^{k,p}_loc(Ω, F)` is continuous on `Ω`. It agrees with `u` almost everywhere on `Ω`
(`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`). -/
theorem MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hu : MemWkpLoc p Ω k u) :
    ContinuousOn (preciseRepresentative volume u) Ω := by
  obtain ⟨r, hr, hu1⟩ := hu.exists_two_lt_memWkpLoc_one_of_two_lt_mul hp hkp
  exact hu1.continuousOn_preciseRepresentative (by exact_mod_cast hr)

/-- **Morrey for `kp > 2`: continuous representatives.** If `1 ≤ p ≤ ∞` and `2 < k p`, every
`u ∈ W^{k,p}_loc(Ω, F)` agrees almost everywhere on `Ω` with a function continuous on `Ω`. -/
theorem MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hu : MemWkpLoc p Ω k u) :
    ∃ g : ℂ → F, ContinuousOn g Ω ∧ u =ᵐ[volume.restrict Ω] g :=
  ⟨_, hu.continuousOn_preciseRepresentative_of_two_lt_mul hp hkp,
    hu.memLpLoc.ae_eq_preciseRepresentative hp⟩

/-- **Morrey for `kp > 2`: the local bound.** Let `1 ≤ p ≤ ∞` with `2 < k p`, and let `V` have
compact closure inside the open set `W ⊆ ℂ`. There is a constant `C` such that every `u : ℂ → F`
satisfies `‖u‖_{L^∞(V)} ≤ C ‖u‖_{W^{k,p}(W)}`. Together with
`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul` this bounds the continuous
representative on `V`. -/
theorem exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNorm u ∞ (volume.restrict V) ≤ C * eLpNormWkp p W k u := by
  induction k generalizing p W with
  | zero => simp at hkp
  | succ k ih =>
    by_cases hp2 : 2 < p
    · obtain ⟨C, hC⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_one (F := F) hp2 hVc hVW
      exact ⟨C, fun u => (hC u).trans (by gcongr; exact eLpNormWkp_mono_order (by omega))⟩
    lift p to ℝ≥0 using ne_top_of_le_ne_top ENNReal.ofNat_ne_top (not_lt.1 hp2)
    obtain ⟨s, hps, hgap, hks⟩ := exists_le_and_inv_sub_inv_le_and_lt_mul (n := 2)
      (by exact_mod_cast not_lt.1 hp2) (by exact_mod_cast hkp)
    obtain ⟨W', hVW', hW'W, hW'c⟩ := Opens.exists_between_and_isCompact_closure hVc hVW
    obtain ⟨C₁, hC₁⟩ := exists_eLpNormWkp_le_mul_eLpNormWkp_succ (F := F) (k := k)
      (by exact_mod_cast hp) hps (by exact_mod_cast hgap) hW'c hW'W
    obtain ⟨C₂, hC₂⟩ := ih (p := s) (hp.trans (by exact_mod_cast hps)) (by exact_mod_cast hks)
      hVW'
    refine ⟨C₂ * C₁, fun u => ?_⟩
    calc eLpNorm u ∞ (volume.restrict V) ≤ C₂ * eLpNormWkp s W' k u := hC₂ u
      _ ≤ C₂ * (C₁ * eLpNormWkp p W (k + 1) u) := by gcongr; exact hC₁ u
      _ = (C₂ * C₁ : ℝ≥0) * eLpNormWkp p W (k + 1) u := by push_cast; ring

end TauCeti
