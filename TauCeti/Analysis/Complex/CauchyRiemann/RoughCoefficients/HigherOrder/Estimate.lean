/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Estimate
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder.Basic
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Higher
import TauCeti.Data.ENNReal.Holder
import TauCeti.Data.ENNReal.Mul
import TauCeti.Topology.Sets.Opens

/-!
# Interior estimates of every order for real Cauchy–Riemann equations

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For coefficients `J, S : ℂ → End V` with `J² = -1` and a weak solution `ξ` of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution`, the interior estimate of order `k` on a set `U` with
compact closure in `Ω` is

`‖ξ‖_{W^{k+1,q}(U)} ≤ C (‖η‖_{W^{k,q}(Ω)} + ‖ξ‖_{L^q(Ω)})`

with one constant `C` for all coefficients bounded by `M` in `W^{max k 1, p}(Ω) × W^{k,p}(Ω)`
(`TauCeti.CRInteriorEstimate`). This file proves the induction step of McDuff–Salamon,
Proposition B.4.9, for the estimate: if the estimate of order `k` holds on every open set, so does
the estimate of order `k + 1` (`TauCeti.CRInteriorEstimate.succ`). The estimate of order `0` is
the estimate ladder `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le` at `r = q`
(`TauCeti.crInteriorEstimate_zero`), and induction on `k` gives the interior estimates of every
order, uniformly in bounded sets of coefficients (`TauCeti.crInteriorEstimate`).

## The argument

The step follows the qualitative induction `TauCeti.IsWeakCRSolution.memWkpLoc_succ` on nested
open sets `U ⋐ W₂ ⋐ W₁ ⋐ W ⋐ Ω`. The estimate of order `k` bounds `ξ` in `W^{k+1,q}(W)`. The
derivative `∂_t ξ` solves `∂_s (∂_t ξ) + J ∂_t (∂_t ξ) + (S + ∂_t J) ∂_t ξ = ∂_t η - (∂_t S) ξ`
(`TauCeti.IsWeakCRSolution.apply_I_of_hasWeakFDerivOn`), whose coefficients are bounded in terms
of `M` and whose right side is bounded in `W^{k,q}(W₁)` by the mixed-exponent product bound
`TauCeti.exists_eLpNormWkp_clm_apply_le_mul_eLpNormWkp_succ`, so the estimate of order `k` on `W₁`
bounds `∂_t ξ` in `W^{k+1,q}(W₂)`. Then `∂_s ξ = η - J ∂_t ξ - S ξ` is bounded in `W^{k+1,q}(U)`
by the product bound `TauCeti.exists_eLpNormWkp_succ_clm_apply_le`, and the two partial
derivatives bound `ξ` in `W^{k+2,q}(U)`
(`TauCeti.eLpNormWkp_succ_le_eLpNorm_add_apply_one_add_apply_I`).

## Main declarations

* `TauCeti.CRInteriorEstimate`: the uniform interior estimate of order `k`, with
  `TauCeti.crInteriorEstimate_iff` and its monotonicity in the bound and the set
  (`TauCeti.CRInteriorEstimate.mono_bound`, `TauCeti.CRInteriorEstimate.mono_set`).
* `TauCeti.CRInteriorEstimate.succ`: the step from order `k` to order `k + 1`.
* `TauCeti.crInteriorEstimate_zero`, `TauCeti.crInteriorEstimate`: the estimate of order `0`, and
  of every order.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemma B.4.6 and Proposition B.4.9.
-/

public section

open MeasureTheory TopologicalSpace Complex ContinuousLinearMap
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

variable (V) in
/-- **The uniform interior estimate of order `k`.** `CRInteriorEstimate V p q k M Ω U` says that
there is a constant `C` such that every weak solution `ξ ∈ L^q_loc(Ω)` of
`∂_s ξ + J ∂_t ξ + S ξ = η`, with Sobolev coefficients, `J² = -1`,
`‖J‖_{W^{max k 1, p}(Ω)} ≤ M`, `‖S‖_{W^{k,p}(Ω)} ≤ M` and `η ∈ W^{k,q}_loc(Ω)`, satisfies
`‖ξ‖_{W^{k+1,q}(U)} ≤ C (‖η‖_{W^{k,q}(Ω)} + ‖ξ‖_{L^q(Ω)})`. The constant does not depend on
`(J, S)`. -/
def CRInteriorEstimate (p q : ℝ≥0∞) (k : ℕ) (M : ℝ≥0) (Ω : Opens ℂ) (U : Set ℂ) :
    Prop :=
  ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
    IsWeakCRSolution q Ω J DJ S ξ η → IsSobolevCRCoefficients p Ω J DJ S →
    (∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) → eLpNormWkp p Ω (max k 1) J ≤ M →
    eLpNormWkp p Ω k S ≤ M → MemWkpLoc q Ω k η →
    eLpNormWkp q U (k + 1) ξ ≤ C * (eLpNormWkp q Ω k η + eLpNorm ξ q (volume.restrict Ω))

/-- The defining property of `TauCeti.CRInteriorEstimate`. -/
theorem crInteriorEstimate_iff {p q : ℝ≥0∞} {k : ℕ} {M : ℝ≥0} {Ω : Opens ℂ} {U : Set ℂ} :
    CRInteriorEstimate V p q k M Ω U ↔
      ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
        IsWeakCRSolution q Ω J DJ S ξ η → IsSobolevCRCoefficients p Ω J DJ S →
        (∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) → eLpNormWkp p Ω (max k 1) J ≤ M →
        eLpNormWkp p Ω k S ≤ M → MemWkpLoc q Ω k η →
        eLpNormWkp q U (k + 1) ξ ≤
          C * (eLpNormWkp q Ω k η + eLpNorm ξ q (volume.restrict Ω)) :=
  Iff.rfl

/-- The estimate for a bound `M` holds for every smaller bound. -/
theorem CRInteriorEstimate.mono_bound {p q : ℝ≥0∞} {k : ℕ} {M M' : ℝ≥0} {Ω : Opens ℂ}
    {U : Set ℂ} (h : CRInteriorEstimate V p q k M Ω U) (hM : M' ≤ M) :
    CRInteriorEstimate V p q k M' Ω U := by
  obtain ⟨C, hC⟩ := h
  have hM' : (M' : ℝ≥0∞) ≤ M := by exact_mod_cast hM
  exact ⟨C, fun J S DJ ξ η h hc hJ2 hJ hS hη =>
    hC J S DJ ξ η h hc hJ2 (hJ.trans hM') (hS.trans hM') hη⟩

/-- The estimate on `U` holds on every smaller set. -/
theorem CRInteriorEstimate.mono_set {p q : ℝ≥0∞} {k : ℕ} {M : ℝ≥0} {Ω : Opens ℂ}
    {U U' : Set ℂ} (h : CRInteriorEstimate V p q k M Ω U) (hU : U' ⊆ U) :
    CRInteriorEstimate V p q k M Ω U' := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun J S DJ ξ η h hc hJ2 hJ hS hη =>
    (eLpNormWkp_mono_set hU).trans (hC J S DJ ξ η h hc hJ2 hJ hS hη)⟩

omit [CompleteSpace V] in
/-- The bound for `∂_s ξ = η - J ∂_t ξ - S ξ` in `W^{k+1,q}(U)` from bounds for `J`, `S`, `∂_t ξ`
and `ξ` on a larger set `W₂`, through the product bound `hCq`. -/
private theorem eLpNormWkp_partial_s_le {p q : ℝ≥0} (hq1 : (1 : ℝ≥0∞) ≤ q) {k : ℕ}
    {U W₂ : Set ℂ} {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    {Cq M cT Ca : ℝ≥0} {A : ℝ≥0∞}
    (hCq : ∀ (B : ℂ → V →L[ℝ] V) (u : ℂ → V), eLpNormWkp q U (k + 1) (fun z => B z (u z)) ≤
      Cq * eLpNormWkp p W₂ (k + 1) B * eLpNormWkp q W₂ (k + 1) u)
    (heq : ∀ᵐ z ∂volume.restrict U, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (hη : eLpNormWkp q U (k + 1) η ≤ ↑(1 : ℝ≥0) * A) (hJ : eLpNormWkp p W₂ (k + 1) J ≤ M)
    (hS : eLpNormWkp p W₂ (k + 1) S ≤ M)
    (hT : eLpNormWkp q W₂ (k + 1) (fun z => Dξ z I) ≤ ↑cT * A)
    (hX : eLpNormWkp q W₂ (k + 1) ξ ≤ ↑Ca * A) :
    eLpNormWkp q U (k + 1) (fun z => Dξ z 1) ≤ ↑(1 + Cq * M * cT + Cq * M * Ca) * A := by
  rw [eLpNormWkp_congr_ae (g := fun z => η z - J z (Dξ z I) - S z (ξ z))
    (heq.mono fun z hz => by dsimp only; rw [← hz]; abel)]
  refine (eLpNormWkp_sub_le (f := fun z => η z - J z (Dξ z I)) (g := fun z => S z (ξ z))
    hq1).trans (ENNReal.add_le_coe_mul ((eLpNormWkp_sub_le (f := η) (g := fun z => J z (Dξ z I))
      hq1).trans (ENNReal.add_le_coe_mul hη ?_)) ?_)
  · exact ENNReal.le_coe_mul_of_le_mul_mul (hCq J (fun z => Dξ z I)) hJ hT
  · exact ENNReal.le_coe_mul_of_le_mul_mul (hCq S ξ) hS hX

/-- The bound for `∂_t ξ` in `W^{k+1,q}(W₂)`: `∂_t ξ` solves the equation with zeroth-order
coefficient `S + ∂_t J` and right side `∂_t η - (∂_t S) ξ` on `W₁`, whose data are bounded by
the product bound `hCp`, so the estimate `hCb` of order `k` applies. -/
private theorem eLpNormWkp_partial_t_le [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) {k : ℕ}
    {Ω W W₁ : Opens ℂ} (hWle : W ≤ Ω) (hW₁le : W₁ ≤ W) {W₂ : Set ℂ}
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    {Cb Cp M Ca : ℝ≥0} {A : ℝ≥0∞}
    (hCb : ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolution q W₁ J DJ S ξ η → IsSobolevCRCoefficients p W₁ J DJ S →
      (∀ᵐ z ∂volume.restrict W₁, J z * J z = -1) → eLpNormWkp p W₁ (max k 1) J ≤ ↑(M + M) →
      eLpNormWkp p W₁ k S ≤ ↑(M + M) → MemWkpLoc q W₁ k η →
      eLpNormWkp q W₂ (k + 1) ξ ≤ Cb * (eLpNormWkp q W₁ k η + eLpNorm ξ q (volume.restrict W₁)))
    (hCp : ∀ (B : ℂ → V →L[ℝ] V) (u : ℂ → V), eLpNormWkp q W₁ k (fun z => B z (u z)) ≤
      Cp * eLpNormWkp p W k B * eLpNormWkp q W (k + 1) u)
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hco : IsSobolevCRCoefficients p Ω J DJ S)
    (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hJk : eLpNormWkp p Ω (max k 1) J ≤ M)
    (hSM : eLpNormWkp p Ω (k + 1) S ≤ M) (hξ : MemWkpLoc q Ω (k + 1) ξ)
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (hDξk : MemWkpLoc q Ω k Dξ)
    (hDS : HasWeakFDerivOn volume Ω S DS) (hDSk : MemWkpLoc p Ω k DS)
    (hDη : HasWeakFDerivOn volume Ω η Dη) (hDηk : MemWkpLoc q Ω k Dη)
    (hDJM : eLpNormWkp p Ω k DJ ≤ M) (ha : eLpNormWkp q Ω (k + 1) η ≤ ↑(1 : ℝ≥0) * A)
    (hX : eLpNormWkp q W (k + 1) ξ ≤ ↑Ca * A) :
    eLpNormWkp q W₂ (k + 1) (fun z => Dξ z I) ≤ ↑(Cb * (1 + Cp * M * Ca + Ca)) * A := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  have hW₁Ω : W₁ ≤ Ω := hW₁le.trans hWle
  have hT := (h.apply_I_of_hasWeakFDerivOn hco hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top hDS
    hDSk.memLpLoc hDξ hDξk.memLpLoc hDη).mono hW₁Ω
  have hDSξ : MemWkpLoc q Ω k (fun z => DS z I (ξ z)) :=
    (hDSk.clm_comp (apply ℝ (V →L[ℝ] V) I)).bilin_of_memWkpLoc_succ
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp hξ
  have hη' : eLpNormWkp q W₁ k (fun z => Dη z I - DS z I (ξ z)) ≤ ↑(1 + Cp * M * Ca) * A := by
    refine (eLpNormWkp_sub_le (f := fun z => Dη z I) (g := fun z => DS z I (ξ z)) hq1).trans
      (ENNReal.add_le_coe_mul ?_ ?_)
    · exact ((eLpNormWkp_mono_set hW₁Ω).trans
        (eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn hDη (by simp))).trans ha
    · exact ENNReal.le_coe_mul_of_le_mul_mul (hCp (fun z => DS z I) ξ)
        ((eLpNormWkp_mono_set hWle).trans
          ((eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn hDS (by simp)).trans hSM)) hX
  have hDξIq : eLpNorm (fun z => Dξ z I) q (volume.restrict W₁) ≤ ↑Ca * A := by
    rw [← eLpNormWkp_zero]
    exact (eLpNormWkp_mono_order (Nat.zero_le k)).trans ((eLpNormWkp_mono_set hW₁le).trans
      ((eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn (hDξ.mono hWle) (by simp)).trans
        hX))
  have hc' := hco.add_zeroth (hco.memLpLoc_deriv_apply I)
  refine (hCb J (fun z => S z + DJ z I) DJ _ _ hT ⟨hc'.hasWeakFDerivOn.mono hW₁Ω,
    hc'.memLpLoc_coeff.mono_set hW₁Ω, hc'.memLpLoc_deriv.mono_set hW₁Ω,
    hc'.memLpLoc_zeroth.mono_set hW₁Ω⟩ (ae_mono (Measure.restrict_mono hW₁Ω le_rfl) hJ2)
    ((eLpNormWkp_mono_set hW₁Ω).trans (hJk.trans (by push_cast; exact le_self_add))) ?_
    (((hDηk.clm_comp (apply ℝ V I)).sub hDSξ).mono hW₁Ω)).trans ?_
  · refine (eLpNormWkp_add_le (f := S) (g := fun z => DJ z I)
      (by exact_mod_cast hq.le.trans hqp)).trans ?_
    push_cast
    exact add_le_add ((eLpNormWkp_mono_set hW₁Ω).trans
      ((eLpNormWkp_mono_order k.le_succ).trans hSM))
      ((eLpNormWkp_apply_le_of_norm_le_one DJ (by simp)).trans
        ((eLpNormWkp_mono_set hW₁Ω).trans hDJM))
  · rw [show (↑(Cb * (1 + Cp * M * Ca + Ca)) : ℝ≥0∞) * A = Cb * (↑(1 + Cp * M * Ca + Ca) * A) by
      push_cast; ring]
    exact mul_le_mul_right (ENNReal.add_le_coe_mul hη' hDξIq) _

/-- **The induction step of the interior estimates** (McDuff–Salamon, Proposition B.4.9). Let
`V` be finite-dimensional, `p > 2`, `1/p + 1/q < 1` and `q ≤ p`. If the uniform interior estimate
of order `k` holds for every open set and every bound, then so does the estimate of order
`k + 1`: for `U` with compact closure in `Ω` and every `M`, there is one constant `C` such that
`‖ξ‖_{W^{k+2,q}(U)} ≤ C (‖η‖_{W^{k+1,q}(Ω)} + ‖ξ‖_{L^q(Ω)})` for all weak solutions with
`‖J‖_{W^{k+1,p}(Ω)} ≤ M` and `‖S‖_{W^{k+1,p}(Ω)} ≤ M`. -/
theorem CRInteriorEstimate.succ [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ (Ω : Opens ℂ) (U : Set ℂ) (M : ℝ≥0), IsCompact (closure U) → closure U ⊆ Ω →
      CRInteriorEstimate V p q k M Ω U)
    {Ω : Opens ℂ} {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    CRInteriorEstimate V p q (k + 1) M Ω U := by
  have hq1 : (1 : ℝ≥0∞) < q := ENNReal.one_lt_right_of_inv_add_inv_lt_one hpq
  have hq : 1 < q := by exact_mod_cast hq1
  -- Nested open sets `U ⋐ W₂ ⋐ W₁ ⋐ W ⋐ Ω` and the constants of the estimates used on them.
  obtain ⟨W, hUW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hUc hUΩ
  obtain ⟨W₁, hUW₁, hW₁W, hW₁c⟩ := Opens.exists_between_and_isCompact_closure hUc hUW
  obtain ⟨W₂, hUW₂, hW₂W₁, hW₂c⟩ := Opens.exists_between_and_isCompact_closure hUc hUW₁
  have hWle : W ≤ Ω := subset_closure.trans hWΩ
  have hW₁le : W₁ ≤ W := subset_closure.trans hW₁W
  have hW₂W : (W₂ : Set ℂ) ⊆ W := subset_closure.trans (hW₂W₁.trans hW₁le)
  have hUle : U ⊆ Ω := subset_closure.trans (hUW.trans hWle)
  obtain ⟨Ca, hCa⟩ := hk Ω W M hWc hWΩ
  obtain ⟨Cb, hCb⟩ := hk W₁ W₂ (M + M) hW₂c hW₂W₁
  obtain ⟨Cp, hCp⟩ := exists_eLpNormWkp_clm_apply_le_mul_eLpNormWkp_succ (F := V) (G := V) hp hq
    hqp k hW₁c hW₁W
  obtain ⟨Cq, hCq⟩ := exists_eLpNormWkp_succ_clm_apply_le (F := V) (G := V) hp hq hqp k hUc hUW₂
  set cT := Cb * (1 + Cp * M * Ca + Ca)
  refine ⟨Ca + (‖smulRightL ℝ ℝ ℝ ℂ V reCLM‖₊ * (1 + Cq * M * cT + Cq * M * Ca) +
    ‖smulRightL ℝ ℝ ℝ ℂ V imCLM‖₊ * cT), fun J S DJ ξ η h hco hJ2 hJM hSM hη => ?_⟩
  rw [max_eq_left (Nat.le_add_left 1 k)] at hJM
  have hJk := (eLpNormWkp_mono_order (max_le k.le_succ (Nat.le_add_left 1 k))).trans hJM
  -- Qualitative regularity and weak derivatives on `Ω`; `ξ` on `W` by the estimate of order `k`.
  have hS1 := memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top hSM)
  have hξ : MemWkpLoc q Ω (k + 1) ξ := h.memWkpLoc_succ hco hp hJ2 hpq hqp
    (memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top hJM)).of_succ
    hS1.of_succ hη.of_succ
  obtain ⟨Dξ, hDξ, hDξk⟩ := hξ.exists_weakFDeriv_of_isOpen
  obtain ⟨DS, hDS, hDSk⟩ := hS1.exists_weakFDeriv_of_isOpen
  obtain ⟨Dη, hDη, hDηk⟩ := hη.exists_weakFDeriv_of_isOpen
  set A := eLpNormWkp q Ω (k + 1) η + eLpNorm ξ q (volume.restrict Ω)
  have ha : eLpNormWkp q Ω (k + 1) η ≤ ↑(1 : ℝ≥0) * A := by simp [A]
  have hX : eLpNormWkp q W (k + 1) ξ ≤ ↑Ca * A := (hCa J S DJ ξ η h hco hJ2 hJk
    ((eLpNormWkp_mono_order k.le_succ).trans hSM) hη.of_succ).trans
    (mul_le_mul_right (add_le_add (eLpNormWkp_mono_order k.le_succ) le_rfl) _)
  -- `∂_t ξ` on `W₂`, `∂_s ξ` on `U`, and the two partial derivatives bound `ξ` on `U`.
  have hT₂ := eLpNormWkp_partial_t_le hp hq hqp hpq hWle hW₁le hCb hCp h hco hJ2 hJk hSM hξ hDξ
    hDξk hDS hDSk hDη hDηk ((eLpNormWkp_le_eLpNormWkp_succ_of_hasWeakFDerivOn
      hco.hasWeakFDerivOn).trans hJM) ha hX
  have hDξ1 := eLpNormWkp_partial_s_le hq1.le hCq
    (Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hUle le_rfl))
      ((hco.isWeakCRSolution_iff_ae hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top hDξ hξ.memLpLoc
        hDξk.memLpLoc h.locallyIntegrableOn).1 h))
    ((eLpNormWkp_mono_set hUle).trans ha) ((eLpNormWkp_mono_set (hW₂W.trans hWle)).trans hJM)
    ((eLpNormWkp_mono_set (hW₂W.trans hWle)).trans hSM) hT₂
    ((eLpNormWkp_mono_set hW₂W).trans hX)
  have hdec := eLpNormWkp_succ_le_eLpNorm_add_apply_one_add_apply_I (k := k + 1) hq1.le
    (hDξ.mono fun z hz => hUle (interior_subset hz)); simp only [eNorm_eq_nnNorm] at hdec
  exact hdec.trans (ENNReal.add_le_coe_mul
    ((eLpNorm_le_eLpNormWkp.trans (eLpNormWkp_mono_set (subset_closure.trans hUW))).trans hX)
    (ENNReal.add_le_coe_mul (ENNReal.coe_mul_le_coe_mul hDξ1) (ENNReal.coe_mul_le_coe_mul
      ((eLpNormWkp_mono_set (subset_closure.trans hUW₂)).trans hT₂))))

/-- **The interior estimate of order `0`.** Let `V` be finite-dimensional, `p > 2`,
`1/p + 1/q < 1` and `q ≤ p`. For `U` with compact closure in `Ω` and every `M`, there is one
constant `C` with `‖ξ‖_{W^{1,q}(U)} ≤ C (‖η‖_{L^q(Ω)} + ‖ξ‖_{L^q(Ω)})` for all weak solutions with
`‖J‖_{W^{1,p}(Ω)} ≤ M` and `‖S‖_{Lᵖ(Ω)} ≤ M`. This is the estimate ladder
`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le` at `r = q`. -/
theorem crInteriorEstimate_zero [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) {Ω : Opens ℂ} {U : Set ℂ}
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    CRInteriorEstimate V p q 0 M Ω U := by
  have hq1 : (1 : ℝ≥0∞) < q := ENNReal.one_lt_right_of_inv_add_inv_lt_one hpq
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le (V := V)
    (by exact_mod_cast hp) hpq hq1
    ENNReal.coe_ne_top (by exact_mod_cast hqp) hUc hUΩ M
  refine ⟨C, fun J S DJ ξ η h hco hJ2 hJ hS hη => ?_⟩
  rw [eLpNormWkp_zero] at hS ⊢
  exact hC J S DJ ξ η h hco hJ2 hJ hS (memWkpLoc_zero_iff.1 hη)

/-- **The interior estimates of every order** (McDuff–Salamon, Lemma B.4.6 and Proposition B.4.9).
Let `V` be finite-dimensional, `p > 2`, `1/p + 1/q < 1` and `q ≤ p`. For every `k`, every `U` with
compact closure in `Ω` and every `M`, there is one constant `C` such that every weak solution
`ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` with `J² = -1`, `‖J‖_{W^{max k 1, p}(Ω)} ≤ M`,
`‖S‖_{W^{k,p}(Ω)} ≤ M` and `η ∈ W^{k,q}_loc(Ω)` satisfies
`‖ξ‖_{W^{k+1,q}(U)} ≤ C (‖η‖_{W^{k,q}(Ω)} + ‖ξ‖_{L^q(Ω)})`. The order-`0` case is
`TauCeti.crInteriorEstimate_zero` and each further order is `TauCeti.CRInteriorEstimate.succ`. -/
theorem crInteriorEstimate [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p) (k : ℕ) {Ω : Opens ℂ} {U : Set ℂ}
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    CRInteriorEstimate V p q k M Ω U := by
  induction k generalizing Ω U M with
  | zero => exact crInteriorEstimate_zero hp hpq hqp hUc hUΩ M
  | succ k ih =>
    exact CRInteriorEstimate.succ hp hpq hqp (fun _ _ M hUc hUΩ => ih hUc hUΩ M) hUc hUΩ M

end TauCeti
