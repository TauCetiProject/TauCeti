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
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.Topology.Sets.Opens

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
`‖u‖_{L^∞(V)} ≤ C ‖u‖_{W^{k,p}(W)}`. For continuous maps the `L^∞` norm on an open set is the
supremum, so convergence of continuous maps in `W^{k,p}` on compact subsets of `Ω` is locally
uniform on `Ω`. These continuity and `L^∞` results hold for every
`1 ≤ p ≤ ∞` with `kp > 2`; Hölder and higher `C^{m,α}` regularity are not treated here.

The scalar estimate is the interior Sobolev embedding of `TauCeti.W1p`
(`TauCeti.W1p.exists_eLpNorm_value_le_of_inv_sub_inv_le`), applied on `W` through
`TauCeti.exists_w1p_enorm_le_eLpNormWkp`; for `q > 2` the `L^∞` bound uses
`TauCeti.W1p.exists_lpInftyEmbeddingL_of_isCompact_closure` in the same way. The vector-valued
estimates follow in a basis of `F`.

## Main declarations

* `TauCeti.exists_eLpNorm_le_mul_eLpNormWkp_one`: the local Sobolev inequality
  `‖u‖_{L^s(V)} ≤ C ‖u‖_{W^{1,q}(W)}`.
* `TauCeti.exists_eLpNorm_le_mul_eLpNormWkp_one_of_ne_top`: the same with exponents in `ℝ≥0∞`.
* `TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_one`: the order-one `L^∞` bound for `q > 2`.
* `TauCeti.MemWkpLoc.memLpLoc_of_inv_sub_inv_le`: the embedding `W^{1,q}_loc ⊂ L^s_loc`, and
  `TauCeti.MemWkpLoc.memLpLoc_of_inv_sub_inv_le_of_ne_top`, the same with exponents in `ℝ≥0∞`.
* `TauCeti.MemWkpLoc.of_succ_of_inv_sub_inv_le`: order lowering `W^{k+1,q}_loc ⊂ W^{k,s}_loc`.
* `TauCeti.MemWkpLoc.of_le_of_inv_sub_inv_le`: its iterate `W^{k,q}_loc ⊂ W^{m,s}_loc` for
  `m ≤ k` and `1/q - 1/s ≤ (k - m)/2`, and `TauCeti.MemWkpLoc.memLpLoc_of_inv_sub_inv_le_div_two`,
  the embedding `W^{k,q}_loc ⊂ L^s_loc` for `1/q - 1/s ≤ k/2`.
* `TauCeti.exists_eLpNormWkp_le_mul_eLpNormWkp_succ`: the estimate for order lowering, and
  `TauCeti.exists_eLpNormWkp_le_mul_eLpNormWkp_add` and
  `TauCeti.exists_eLpNorm_le_mul_eLpNormWkp_of_inv_sub_inv_le_div_two`, its iterates
  `‖u‖_{W^{m,s}(V)} ≤ C ‖u‖_{W^{k+m,q}(W)}` and `‖u‖_{L^s(V)} ≤ C ‖u‖_{W^{k,q}(W)}` for
  `1/q - 1/s ≤ k/2`.
* `TauCeti.MemWkpLoc.exists_two_lt_memWkpLoc_one_of_two_lt_mul`: for `kp > 2`, membership in
  `W^{1,r}_loc` for some finite `r > 2`.
* `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul` and
  `TauCeti.MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul`: continuous representatives for
  `kp > 2`.
* `TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul`: the local `L^∞` bound for
  `kp > 2`.
* `TauCeti.MemWkpLoc.memLpLoc_top_of_two_lt_mul`: local boundedness of `W^{k,p}_loc` for `kp > 2`.
* `TauCeti.tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul`: for `kp > 2`,
  convergence of continuous maps in `W^{k,p}` on compact sets is locally uniform.

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
        exact (A i).eLpNorm_comp_le
    _ ≤ ∑ i, ‖A i‖ₑ * (C * (‖ℓ i‖ₑ * eLpNormWkp q W 1 u)) := by
        gcongr with i
        exact (hC _).trans (by gcongr; exact (ℓ i).eLpNormWkp_comp_le)
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

/-- **The local Sobolev embedding.** If `1 ≤ q ≤ s < ∞` and `1/q - 1/s ≤ 1/2`, every
`u ∈ W^{1,q}_loc(Ω, F)` is locally `L^s` on `Ω`. This includes the critical exponent
`1/s = 1/q - 1/2` for `q < 2`. -/
theorem MemWkpLoc.memLpLoc_of_inv_sub_inv_le (hu : MemWkpLoc q Ω 1 u) (hq : 1 ≤ q)
    (hqs : q ≤ s) (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) : MemLpLoc s Ω u :=
  hu.memLpLoc_of_forall_exists_eLpNorm_le fun hVc hVW =>
    exists_eLpNorm_le_mul_eLpNormWkp_one hq hqs hgap hVc hVW

/-- The local Sobolev inequality for exponents in `ℝ≥0∞`: if `1 ≤ r ≤ t < ∞` and
`1/r - 1/t ≤ 1/2`, and `V` has compact closure inside the open set `W`, there is a constant `C`
such that every `u : ℂ → F` satisfies `‖u‖_{Lᵗ(V)} ≤ C ‖u‖_{W^{1,r}(W)}`. -/
theorem exists_eLpNorm_le_mul_eLpNormWkp_one_of_ne_top {r t : ℝ≥0∞} (hr : 1 ≤ r) (ht : t ≠ ⊤)
    (hrt : r ≤ t) (hgap : r⁻¹ - t⁻¹ ≤ 2⁻¹) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNorm u t (volume.restrict V) ≤ C * eLpNormWkp r W 1 u := by
  have hr_top : r ≠ ⊤ := ne_top_of_le_ne_top ht hrt
  have ht0 : t ≠ 0 := (zero_lt_one.trans_le (hr.trans hrt)).ne'
  rw [← ENNReal.coe_toNNReal hr_top, ← ENNReal.coe_toNNReal ht]
  refine exists_eLpNorm_le_mul_eLpNormWkp_one ?_ (ENNReal.toNNReal_mono ht hrt) ?_ hVc hVW
  · rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hr_top]
    exact_mod_cast hr
  · have h := ENNReal.toReal_mono (by finiteness) (tsub_le_iff_right.1 hgap)
    simp only [ne_eq, ENNReal.inv_eq_top, ht0, not_false_eq_true, OfNat.ofNat_ne_zero,
      ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h
    simp only [ENNReal.coe_toNNReal_eq_toReal]
    linarith

/-- The local Sobolev embedding `W^{1,r}_loc(Ω, F) ⊂ Lᵗ_loc(Ω, F)` for exponents in `ℝ≥0∞`: if
`1 ≤ r ≤ t < ∞` and `1/r - 1/t ≤ 1/2`, every `u ∈ W^{1,r}_loc(Ω, F)` is locally `Lᵗ` on `Ω`. -/
theorem MemWkpLoc.memLpLoc_of_inv_sub_inv_le_of_ne_top {r t : ℝ≥0∞} (hu : MemWkpLoc r Ω 1 u)
    (hr : 1 ≤ r) (ht : t ≠ ⊤) (hrt : r ≤ t) (hgap : r⁻¹ - t⁻¹ ≤ 2⁻¹) : MemLpLoc t Ω u :=
  hu.memLpLoc_of_forall_exists_eLpNorm_le fun hVc hVW =>
    exists_eLpNorm_le_mul_eLpNormWkp_one_of_ne_top hr ht hrt hgap hVc hVW

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

/-- With no order to spend, the Sobolev embedding does not change the exponent: for `1 ≤ q ≤ s`
and `1/q - 1/s ≤ 0`, the exponents agree. -/
private theorem eq_of_inv_sub_inv_le_zero (hq : 1 ≤ q) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 0) : s = q := by
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le (by exact_mod_cast hq)
  have hs0 : (0 : ℝ) < s := hq0.trans_le (by exact_mod_cast hqs)
  have hsq : (s : ℝ) ≤ q := (inv_le_inv₀ hq0 hs0).1 (by linarith)
  exact le_antisymm (by exact_mod_cast hsq) hqs

/-- One step of the Sobolev embedding at higher order. For `1 ≤ q ≤ s` and
`1/q - 1/s ≤ (k + 1)/2`, the exponent `q₁` with `1/q₁ = max (1/q - 1/2) (1/s)` lies between `q`
and `s`, is reached from `q` by lowering the order once, and reaches `s` by lowering it `k` more
times. -/
private theorem exists_inv_sub_inv_le_half_and_le_div_two (hq : 1 ≤ q) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ ((k + 1 : ℕ) : ℝ) / 2) :
    ∃ q₁ : ℝ≥0, q ≤ q₁ ∧ q₁ ≤ s ∧ (q : ℝ)⁻¹ - (q₁ : ℝ)⁻¹ ≤ 2⁻¹ ∧
      (q₁ : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ k / 2 := by
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le (by exact_mod_cast hq)
  have hs0 : (0 : ℝ) < s := hq0.trans_le (by exact_mod_cast hqs)
  set r : ℝ := max ((q : ℝ)⁻¹ - 2⁻¹) (s : ℝ)⁻¹ with hr
  have hr0 : 0 < r := lt_max_of_lt_right (inv_pos.2 hs0)
  have hrq : r ≤ (q : ℝ)⁻¹ :=
    max_le (by linarith) ((inv_le_inv₀ hs0 hq0).2 (by exact_mod_cast hqs))
  let q₁ : ℝ≥0 := ⟨r⁻¹, (inv_pos.2 hr0).le⟩
  have hq₁ : (q₁ : ℝ)⁻¹ = r := inv_inv r
  have hq₁0 : (0 : ℝ) < q₁ := inv_pos.2 hr0
  refine ⟨q₁, ?_, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hq₁0 hq0, hq₁]
    exact hrq
  · rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hs0 hq₁0, hq₁]
    exact le_max_right _ _
  · rw [hq₁]
    linarith [le_max_left ((q : ℝ)⁻¹ - 2⁻¹) (s : ℝ)⁻¹]
  · rw [hq₁]
    push_cast at hgap
    rcases max_cases ((q : ℝ)⁻¹ - 2⁻¹) (s : ℝ)⁻¹ with ⟨h, -⟩ | ⟨h, -⟩
    · rw [hr, h]
      linarith
    · rw [hr, h, sub_self]
      positivity

/-- The Sobolev embedding at every order, with the order of the source written as `k + m`. -/
private theorem MemWkpLoc.of_add_of_inv_sub_inv_le {m : ℕ} (hu : MemWkpLoc q Ω (k + m) u)
    (hq : 1 ≤ q) (hqs : q ≤ s) (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ k / 2) : MemWkpLoc s Ω m u := by
  -- Each step lowers the order by one and replaces `1/q` by `max (1/q - 1/2) (1/s)`.
  induction k generalizing q with
  | zero =>
    obtain rfl := eq_of_inv_sub_inv_le_zero hq hqs (by simpa using hgap)
    simpa using hu
  | succ k ih =>
    obtain ⟨q₁, hqq₁, hq₁s, hgap₁, hgap₂⟩ := exists_inv_sub_inv_le_half_and_le_div_two hq hqs hgap
    have hu' : MemWkpLoc q Ω (k + m + 1) u := by rwa [show k + m + 1 = k + 1 + m by omega]
    exact ih (hu'.of_succ_of_inv_sub_inv_le hq hqq₁ hgap₁) (hq.trans hqq₁) hq₁s hgap₂

/-- **The Sobolev embedding at every order.** If `m ≤ k`, `1 ≤ q ≤ s < ∞` and
`1/q - 1/s ≤ (k - m)/2`, then `W^{k,q}_loc(Ω, F) ⊂ W^{m,s}_loc(Ω, F)`. -/
theorem MemWkpLoc.of_le_of_inv_sub_inv_le {m : ℕ} (hu : MemWkpLoc q Ω k u) (hmk : m ≤ k)
    (hq : 1 ≤ q) (hqs : q ≤ s) (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ ((k - m : ℕ) : ℝ) / 2) :
    MemWkpLoc s Ω m u := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + m := ⟨k - m, by omega⟩
  rw [Nat.add_sub_cancel] at hgap
  exact hu.of_add_of_inv_sub_inv_le hq hqs hgap

/-- **The local Sobolev embedding at every order.** If `1 ≤ q ≤ s < ∞` and
`1/q - 1/s ≤ k/2`, every `u ∈ W^{k,q}_loc(Ω, F)` is locally `L^s` on `Ω`. -/
theorem MemWkpLoc.memLpLoc_of_inv_sub_inv_le_div_two (hu : MemWkpLoc q Ω k u) (hq : 1 ≤ q)
    (hqs : q ≤ s) (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ k / 2) : MemLpLoc s Ω u :=
  memWkpLoc_zero_iff.1 (hu.of_le_of_inv_sub_inv_le k.zero_le hq hqs (by simpa using hgap))

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

/-- **The estimate for the Sobolev embedding at every order.** Let `1 ≤ q ≤ s < ∞` with
`1/q - 1/s ≤ k/2`, and let `V` have compact closure inside the open set `W ⊆ ℂ`. There is a
constant `C` such that every `u : ℂ → F` satisfies `‖u‖_{W^{m,s}(V)} ≤ C ‖u‖_{W^{k+m,q}(W)}`.
This is the estimate for `TauCeti.MemWkpLoc.of_le_of_inv_sub_inv_le`. -/
theorem exists_eLpNormWkp_le_mul_eLpNormWkp_add {m : ℕ} (hq : 1 ≤ q) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ k / 2) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNormWkp s V m u ≤ C * eLpNormWkp q W (k + m) u := by
  -- Each step lowers the order once on an intermediate open set, as in
  -- `TauCeti.MemWkpLoc.of_le_of_inv_sub_inv_le`.
  induction k generalizing q W with
  | zero =>
    obtain rfl := eq_of_inv_sub_inv_le_zero hq hqs (by simpa using hgap)
    refine ⟨1, fun u => ?_⟩
    rw [ENNReal.coe_one, one_mul, zero_add]
    exact eLpNormWkp_mono_set (subset_closure.trans hVW)
  | succ k ih =>
    obtain ⟨q₁, hqq₁, hq₁s, hgap₁, hgap₂⟩ := exists_inv_sub_inv_le_half_and_le_div_two hq hqs hgap
    obtain ⟨W', hVW', hW'W, hW'c⟩ := Opens.exists_between_and_isCompact_closure hVc hVW
    obtain ⟨C₁, hC₁⟩ := exists_eLpNormWkp_le_mul_eLpNormWkp_succ (F := F) (k := k + m) hq hqq₁
      hgap₁ hW'c hW'W
    obtain ⟨C₂, hC₂⟩ := ih (hq.trans hqq₁) hq₁s hgap₂ hVW'
    refine ⟨C₂ * C₁, fun u => ?_⟩
    calc eLpNormWkp s V m u ≤ C₂ * eLpNormWkp q₁ W' (k + m) u := hC₂ u
      _ ≤ C₂ * (C₁ * eLpNormWkp q W (k + m + 1) u) := by gcongr; exact hC₁ u
      _ = (C₂ * C₁ : ℝ≥0) * eLpNormWkp q W (k + 1 + m) u := by
        rw [show k + 1 + m = k + m + 1 by omega]
        push_cast
        ring

/-- **The local Sobolev inequality at every order.** Let `1 ≤ q ≤ s < ∞` with
`1/q - 1/s ≤ k/2`, and let `V` have compact closure inside the open set `W ⊆ ℂ`. There is a
constant `C` such that every `u : ℂ → F` satisfies `‖u‖_{L^s(V)} ≤ C ‖u‖_{W^{k,q}(W)}`. This is
the estimate for `TauCeti.MemWkpLoc.memLpLoc_of_inv_sub_inv_le_div_two`. -/
theorem exists_eLpNorm_le_mul_eLpNormWkp_of_inv_sub_inv_le_div_two (hq : 1 ≤ q) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ k / 2) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, eLpNorm u s (volume.restrict V) ≤ C * eLpNormWkp q W k u := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_le_mul_eLpNormWkp_add (F := F) (m := 0) hq hqs hgap hVc hVW
  exact ⟨C, fun u => by simpa only [eLpNormWkp_zero, add_zero] using hC u⟩

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

/-- **Local boundedness for `kp > 2`.** If `1 ≤ p ≤ ∞` and `2 < k p`, every
`u ∈ W^{k,p}_loc(Ω, F)` is locally essentially bounded on `Ω`. -/
theorem MemWkpLoc.memLpLoc_top_of_two_lt_mul {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hu : MemWkpLoc p Ω k u) : MemLpLoc ∞ Ω u :=
  (hu.continuousOn_preciseRepresentative_of_two_lt_mul hp hkp).memLpLoc.congr_ae
    (hu.memLpLoc.ae_eq_preciseRepresentative hp).symm

/-- **Morrey for `kp > 2`: convergence in `W^{k,p}` is locally uniform.** Let `1 ≤ p ≤ ∞` with
`2 < k p`. If maps `uₙ`, eventually continuous on every compact subset of `Ω`, converge in
`W^{k,p}` on every compact subset of `Ω` to a map `u₀` continuous on `Ω`, then `uₙ → u₀` locally
uniformly on `Ω`. -/
theorem tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) {ι : Type*} {l : Filter ι} {u : ι → ℂ → F} {u₀ : ℂ → F}
    (huc : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hu₀c : ContinuousOn u₀ Ω)
    (hlim : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Filter.Tendsto (fun n => eLpNormWkp p K k (u n - u₀)) l (nhds 0)) :
    TendstoLocallyUniformlyOn u u₀ l Ω := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact Ω.isOpen).2 fun K hKΩ hK => ?_
  -- Open sets `K ⊆ V`, `closure V ⊆ W'` and `closure W' ⊆ Ω` with compact closures.
  obtain ⟨V, hKV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  obtain ⟨W', hVW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hVc hVΩ
  obtain ⟨C, hC⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul (F := F) hp hkp hVc hVW
  have hT : Filter.Tendsto (fun n => (C : ℝ≥0∞) * eLpNormWkp p (closure W') k (u n - u₀)) l
      (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (hlim _ hWΩ hWc) (Or.inr ENNReal.coe_ne_top)
  refine EMetric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [huc _ hVΩ hVc, hT.eventually (gt_mem_nhds hε)]
    with n hnc hn z hz
  -- At points of the open set `V`, the value is bounded by the `L^∞(V)` norm.
  have hcont : ContinuousWithinAt (u n - u₀) V z :=
    ((hnc.mono subset_closure).sub (hu₀c.mono fun y hy => hVΩ (subset_closure hy))) z (hKV hz)
  rw [edist_comm, eDist_eq_eNorm_sub, ← Pi.sub_apply]
  calc ‖(u n - u₀) z‖ₑ ≤ eLpNorm (u n - u₀) ∞ (volume.restrict V) :=
      hcont.eNorm_le_eLpNorm_top_restrict (V.isOpen.mem_nhds (hKV hz))
    _ ≤ C * eLpNormWkp p W' k (u n - u₀) := hC _
    _ ≤ C * eLpNormWkp p (closure W') k (u n - u₀) := by
      gcongr
      exact eLpNormWkp_mono_set subset_closure
    _ < ε := hn

end TauCeti
