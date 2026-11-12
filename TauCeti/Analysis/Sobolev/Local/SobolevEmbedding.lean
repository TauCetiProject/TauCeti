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
import TauCeti.Analysis.Sobolev.MorreyExponent
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
`W^{1,r}_loc(Ω, F)` for some `r > 2`. For `p < 2` each step uses the critical exponent
`1/s = 1/p - 1/2`, and `(k - 1) · 2p/(2 - p) > 2` is equivalent to `kp > 2`; for `p = 2` any finite
`s > 2` serves (`TauCeti.exists_sobolev_exponent_step`). The order-one Morrey embedding of
`TauCeti.Analysis.Sobolev.Local.Morrey` then makes the precise representative of `u` continuous on
`Ω`, and the order-one `L^∞` bound gives the local estimate `‖u‖_{L^∞(V)} ≤ C ‖u‖_{W^{k,p}(W)}`.
This covers the exponents `p ≤ 2` of the Morrey statement for `kp > 2`.

The scalar estimate is the interior Sobolev embedding of `TauCeti.W1p` on a relatively compact
open subset (`TauCeti.W1p.exists_eLpNorm_value_le_of_gain_le`), through
`TauCeti.MemWkpLoc.exists_w1p`; the vector-valued estimate follows in a basis of `F`.

## Main declarations

* `TauCeti.exists_eLpNorm_le_mul_eLpNormWkp_one`: the local Sobolev inequality
  `‖u‖_{L^s(V)} ≤ C ‖u‖_{W^{1,q}(W)}`.
* `TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_one`: the order-one `L^∞` bound for `q > 2`.
* `TauCeti.MemWkpLoc.memLpLoc_of_inv_sub_inv_le`: the embedding `W^{1,q}_loc ⊂ L^s_loc`.
* `TauCeti.MemWkpLoc.of_succ_of_inv_sub_inv_le`: order lowering `W^{k+1,q}_loc ⊂ W^{k,s}_loc`.
* `TauCeti.exists_eLpNormWkp_le_mul_eLpNormWkp_succ`: the estimate for order lowering.
* `TauCeti.MemWkpLoc.exists_two_lt_memWkpLoc_one_of_two_lt_mul`: for `kp > 2`, membership in
  `W^{1,r}_loc` for some `r > 2`.
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
  [Fact (1 ≤ (q : ℝ≥0∞))] {Ω W : Opens ℂ} {V : Set ℂ} {k : ℕ} {u : ℂ → F}

/-- A bound for the values of `W1p volume W q` in `L^t(V)` passes to real members of
`W^{1,q}_loc(W)`, with their `W^{1,q}(W)` norm on the right. -/
private theorem exists_eLpNorm_le_mul_eLpNormWkp_one_real {t : ℝ≥0∞} (hVW : closure V ⊆ W)
    (hW1p : ∃ C : ℝ≥0, ∀ v : W1p volume W (q : ℝ≥0∞),
      eLpNorm (W1p.value v) t (volume.restrict V) ≤ C * ‖v‖ₑ) :
    ∃ C : ℝ≥0, ∀ u : ℂ → ℝ, MemWkpLoc q W 1 u →
      eLpNorm u t (volume.restrict V) ≤ C * eLpNormWkp q W 1 u := by
  obtain ⟨C, hC⟩ := hW1p
  refine ⟨C + 1, fun u hu => ?_⟩
  obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
  rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD, eLpNormWkp_zero]
  by_cases hfin : eLpNorm u q (volume.restrict W) + eLpNorm D q (volume.restrict W) = ∞
  · rw [hfin, ENNReal.mul_top (by simp)]
    exact le_top
  have hu1 : MemLp u q (volume.restrict W) :=
    lt_of_le_of_lt le_self_add (lt_top_iff_ne_top.2 hfin)
  have hD1 : MemLp D q (volume.restrict W) :=
    lt_of_le_of_lt le_add_self (lt_top_iff_ne_top.2 hfin)
  obtain ⟨v, hv, hg⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn hu1 hD1 hD
  have hnorm : ‖v‖ₑ ≤ eLpNorm u q (volume.restrict W) + eLpNorm D q (volume.restrict W) := by
    have h1 : ‖v‖ₑ ≤ ‖W1p.value v‖ₑ + ‖W1p.gradient v‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (W1p.norm_le_norm_value_add_norm_gradient v)
    refine h1.trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
    · rw [Lp.enorm_def, eLpNorm_congr_ae hv]
    · rw [Lp.enorm_def]
      exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) hD1.aestronglyMeasurable
        (hg.mono fun z hz => by rw [hz, LinearIsometryEquiv.norm_map])
  calc eLpNorm u t (volume.restrict V)
      = eLpNorm (W1p.value v) t (volume.restrict V) :=
        eLpNorm_congr_ae (Filter.EventuallyEq.symm
          (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVW) hv))
    _ ≤ C * ‖v‖ₑ := hC v
    _ ≤ (C + 1 : ℝ≥0) * (eLpNorm u q (volume.restrict W) + eLpNorm D q (volume.restrict W)) := by
        gcongr
        · exact_mod_cast le_self_add

variable [FiniteDimensional ℝ F]

/-- A bound for the values of `W1p volume W q` in `L^t(V)`, with `1 ≤ t`, passes to members of
`W^{1,q}_loc(W, F)` coordinatewise in a basis of `F`. -/
private theorem exists_eLpNorm_le_mul_eLpNormWkp_one_of_w1p {t : ℝ≥0∞} (ht : 1 ≤ t)
    (hVW : closure V ⊆ W) (hW1p : ∃ C : ℝ≥0, ∀ v : W1p volume W (q : ℝ≥0∞),
      eLpNorm (W1p.value v) t (volume.restrict V) ≤ C * ‖v‖ₑ) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, MemWkpLoc q W 1 u →
      eLpNorm u t (volume.restrict V) ≤ C * eLpNormWkp q W 1 u := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_mul_eLpNormWkp_one_real hVW hW1p
  set b := Module.finBasis ℝ F
  set ℓ : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  set A : Fin (finrank ℝ F) → ℝ →L[ℝ] F := fun i => (ContinuousLinearMap.id ℝ ℝ).smulRight (b i)
  refine ⟨∑ i, ‖A i‖₊ * C * ‖ℓ i‖₊, fun u hu => ?_⟩
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
        exact (hC _ (hu.clm_comp (ℓ i))).trans (by gcongr; exact eLpNormWkp_clm_comp_le (ℓ i))
    _ = (∑ i, ‖A i‖₊ * C * ‖ℓ i‖₊ : ℝ≥0) * eLpNormWkp q W 1 u := by
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [enorm_eq_nnnorm]
        ring

/-- **The local Sobolev inequality.** Let `1 ≤ q ≤ s < ∞` with `1/q - 1/s ≤ 1/2`, and let `V` have
compact closure inside the open set `W ⊆ ℂ`. There is a constant `C` such that every
`u ∈ W^{1,q}_loc(W, F)` satisfies `‖u‖_{L^s(V)} ≤ C ‖u‖_{W^{1,q}(W)}`. The case
`1/s = 1/q - 1/2` is the critical Sobolev embedding for `q < 2`; for `q ≥ 2` every finite `s ≥ q`
is allowed. -/
theorem exists_eLpNorm_le_mul_eLpNormWkp_one (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, MemWkpLoc q W 1 u →
      eLpNorm u s (volume.restrict V) ≤ C * eLpNormWkp q W 1 u :=
  exists_eLpNorm_le_mul_eLpNormWkp_one_of_w1p
    ((Fact.out : (1 : ℝ≥0∞) ≤ q).trans (ENNReal.coe_le_coe.2 hqs)) hVW
    (W1p.exists_eLpNorm_value_le_of_gain_le (μ := volume) hqs
      (by rwa [Complex.finrank_real_complex, Nat.cast_ofNat]) hVc hVW)

/-- **The local `L^∞` bound for `q > 2`.** Let `2 < q < ∞`, and let `V` have compact closure
inside the open set `W ⊆ ℂ`. There is a constant `C` such that every `u ∈ W^{1,q}_loc(W, F)`
satisfies `‖u‖_{L^∞(V)} ≤ C ‖u‖_{W^{1,q}(W)}`. -/
theorem exists_eLpNorm_top_le_mul_eLpNormWkp_one (hq : 2 < q) (hVc : IsCompact (closure V))
    (hVW : closure V ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, MemWkpLoc q W 1 u →
      eLpNorm u ∞ (volume.restrict V) ≤ C * eLpNormWkp q W 1 u := by
  refine exists_eLpNorm_le_mul_eLpNormWkp_one_of_w1p le_top hVW ?_
  obtain ⟨S, hS⟩ := W1p.exists_lpInftyEmbeddingL_of_isCompact_closure (μ := volume) (Ω := W)
    (q := q) (by rwa [Complex.finrank_real_complex, Nat.cast_ofNat]) hVc hVW
  refine ⟨‖S‖₊, fun v => ?_⟩
  rw [← eLpNorm_congr_ae (hS v), ← Lp.enorm_def, ← enorm_eq_nnnorm]
  exact S.le_opENorm v

/-- **The local Sobolev embedding.** If `1 ≤ q ≤ s < ∞` and `1/q - 1/s ≤ 1/2`, every
`u ∈ W^{1,q}_loc(Ω, F)` is locally `L^s` on `Ω`. This includes the critical exponent
`1/s = 1/q - 1/2` for `q < 2`. -/
theorem MemWkpLoc.memLpLoc_of_inv_sub_inv_le (hu : MemWkpLoc q Ω 1 u) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) : MemLpLoc s Ω u := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  have hKc : closure K = K := hK.isClosed.closure_eq
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_mul_eLpNormWkp_one (F := F) (W := W) hqs hgap
    (by rwa [hKc]) (by rwa [hKc])
  refine (hC u (hu.mono (subset_closure.trans hWΩ))).trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_top_iff_ne_top.2 (hu.eLpNormWkp_ne_top hWc hWΩ))

/-- **Order lowering.** If `1 ≤ q ≤ s < ∞` and `1/q - 1/s ≤ 1/2`, then
`W^{k+1,q}_loc(Ω, F) ⊂ W^{k,s}_loc(Ω, F)`: the function and its weak derivatives through order `k`
gain integrability, and the same weak derivatives serve. -/
theorem MemWkpLoc.of_succ_of_inv_sub_inv_le (hu : MemWkpLoc q Ω (k + 1) u) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) : MemWkpLoc s Ω k u := by
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 (hu.memLpLoc_of_inv_sub_inv_le hqs hgap)
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv_of_isOpen
    exact memWkpLoc_succ_iff_of_isOpen.2
      ⟨(hu.of_le (by omega)).memLpLoc_of_inv_sub_inv_le hqs hgap, D, hD, ih hDk⟩

/-- **The estimate for order lowering.** Let `1 ≤ q ≤ s < ∞` with `1/q - 1/s ≤ 1/2`, and let the
open set `V` have compact closure inside the open set `W ⊆ ℂ`. There is a constant `C` such that
every `u ∈ W^{k+1,q}_loc(W, F)` satisfies `‖u‖_{W^{k,s}(V)} ≤ C ‖u‖_{W^{k+1,q}(W)}`. -/
theorem exists_eLpNormWkp_le_mul_eLpNormWkp_succ (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹) {V : Opens ℂ} (hVc : IsCompact (closure (V : Set ℂ)))
    (hVW : closure (V : Set ℂ) ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, MemWkpLoc q W (k + 1) u →
      eLpNormWkp s V k u ≤ C * eLpNormWkp q W (k + 1) u := by
  induction k generalizing F with
  | zero =>
    obtain ⟨C, hC⟩ := exists_eLpNorm_le_mul_eLpNormWkp_one (F := F) hqs hgap hVc hVW
    exact ⟨C, fun u hu => by simpa only [eLpNormWkp_zero] using hC u hu⟩
  | succ k ih =>
    obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_le_mul_eLpNormWkp_one (F := F) hqs hgap hVc hVW
    obtain ⟨C₁, hC₁⟩ := ih (F := ℂ →L[ℝ] F)
    refine ⟨C₀ + C₁, fun u hu => ?_⟩
    obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv_of_isOpen
    have hDV : HasWeakFDerivOn volume (Opens.interior (V : Set ℂ)) u D := by
      rw [Opens.interior_coe]
      exact hD.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hVW))
    have h1 : eLpNormWkp q W 1 u ≤ eLpNormWkp q W (k + 1 + 1) u :=
      eLpNormWkp_mono_order (by omega)
    have h2 : eLpNormWkp q W (k + 1) D ≤ eLpNormWkp q W (k + 1 + 1) u := by
      rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD (k := k + 1)]
      exact le_add_self
    calc eLpNormWkp s V (k + 1) u
        ≤ eLpNorm u s (volume.restrict V) + eLpNormWkp s V k D := eLpNormWkp_succ_le hDV
      _ ≤ C₀ * eLpNormWkp q W 1 u + C₁ * eLpNormWkp q W (k + 1) D :=
          add_le_add (hC₀ u (hu.of_le (by omega))) (hC₁ D hDk)
      _ ≤ C₀ * eLpNormWkp q W (k + 1 + 1) u + C₁ * eLpNormWkp q W (k + 1 + 1) u := by
          gcongr
      _ = (C₀ + C₁ : ℝ≥0) * eLpNormWkp q W (k + 1 + 1) u := by
          push_cast
          ring

/-- **Order one with exponent above two from `kp > 2`.** If `1 ≤ p` and `2 < k p`, every
`u ∈ W^{k,p}_loc(Ω, F)` lies in `W^{1,r}_loc(Ω, F)` for some `r > 2`. For `p > 2` take `r = p`;
otherwise lower the order with the critical exponent and induct. -/
theorem MemWkpLoc.exists_two_lt_memWkpLoc_one_of_two_lt_mul {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hkp : 2 < (k : ℝ≥0) * p) (hu : MemWkpLoc p Ω k u) :
    ∃ r : ℝ≥0, 2 < r ∧ MemWkpLoc r Ω 1 u := by
  induction k generalizing p with
  | zero => simp at hkp
  | succ k ih =>
    by_cases hp : 2 < p
    · exact ⟨p, hp, hu.of_le (by omega)⟩
    have hp1 : 1 ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
    obtain ⟨s, hps, hgap, hks⟩ := exists_sobolev_exponent_step hp1 (not_lt.1 hp) hkp
    have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨(Fact.out : (1 : ℝ≥0∞) ≤ p).trans
      (ENNReal.coe_le_coe.2 hps)⟩
    exact ih hks (hu.of_succ_of_inv_sub_inv_le hps hgap)

/-- **Morrey for `kp > 2`: continuity.** If `1 ≤ p` and `2 < k p`, the precise representative of
`u ∈ W^{k,p}_loc(Ω, F)` is continuous on `Ω`. It agrees with `u` almost everywhere on `Ω`
(`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`). -/
theorem MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hkp : 2 < (k : ℝ≥0) * p) (hu : MemWkpLoc p Ω k u) :
    ContinuousOn (preciseRepresentative volume u) Ω := by
  obtain ⟨r, hr, hu1⟩ := hu.exists_two_lt_memWkpLoc_one_of_two_lt_mul hkp
  exact hu1.continuousOn_preciseRepresentative (by exact_mod_cast hr)

/-- **Morrey for `kp > 2`: continuous representatives.** If `1 ≤ p` and `2 < k p`, every
`u ∈ W^{k,p}_loc(Ω, F)` agrees almost everywhere on `Ω` with a function continuous on `Ω`. -/
theorem MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hkp : 2 < (k : ℝ≥0) * p) (hu : MemWkpLoc p Ω k u) :
    ∃ g : ℂ → F, ContinuousOn g Ω ∧ u =ᵐ[volume.restrict Ω] g :=
  ⟨_, hu.continuousOn_preciseRepresentative_of_two_lt_mul hkp,
    hu.memLpLoc.ae_eq_preciseRepresentative Fact.out⟩

/-- **Morrey for `kp > 2`: the local bound.** Let `1 ≤ p < ∞` with `2 < k p`, and let the open
set `V` have compact closure inside the open set `W ⊆ ℂ`. There is a constant `C` such that every
`u ∈ W^{k,p}_loc(W, F)` satisfies `‖u‖_{L^∞(V)} ≤ C ‖u‖_{W^{k,p}(W)}`. Together with
`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul` this bounds the continuous
representative on `V`. -/
theorem exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hkp : 2 < (k : ℝ≥0) * p) {V : Opens ℂ} (hVc : IsCompact (closure (V : Set ℂ)))
    (hVW : closure (V : Set ℂ) ⊆ W) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, MemWkpLoc p W k u →
      eLpNorm u ∞ (volume.restrict V) ≤ C * eLpNormWkp p W k u := by
  induction k generalizing p W with
  | zero => simp at hkp
  | succ k ih =>
    by_cases hp : 2 < p
    · obtain ⟨C, hC⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_one (F := F) hp hVc hVW
      exact ⟨C, fun u hu => (hC u (hu.of_le (by omega))).trans
        (by gcongr; exact eLpNormWkp_mono_order (by omega))⟩
    have hp1 : 1 ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
    obtain ⟨s, hps, hgap, hks⟩ := exists_sobolev_exponent_step hp1 (not_lt.1 hp) hkp
    have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨(Fact.out : (1 : ℝ≥0∞) ≤ p).trans
      (ENNReal.coe_le_coe.2 hps)⟩
    obtain ⟨W', hVW', hW'W, hW'c⟩ := Opens.exists_between_and_isCompact_closure hVc hVW
    obtain ⟨C₁, hC₁⟩ := exists_eLpNormWkp_le_mul_eLpNormWkp_succ (F := F) (k := k) hps hgap
      hW'c hW'W
    obtain ⟨C₂, hC₂⟩ := ih hks hVW'
    refine ⟨C₂ * C₁, fun u hu => ?_⟩
    have hu' : MemWkpLoc s W' k u :=
      (hu.of_succ_of_inv_sub_inv_le hps hgap).mono (subset_closure.trans hW'W)
    calc eLpNorm u ∞ (volume.restrict V) ≤ C₂ * eLpNormWkp s W' k u := hC₂ u hu'
      _ ≤ C₂ * (C₁ * eLpNormWkp p W (k + 1) u) := by gcongr; exact hC₁ u hu
      _ = (C₂ * C₁ : ℝ≥0) * eLpNormWkp p W (k + 1) u := by push_cast; ring

end TauCeti
