/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound
import TauCeti.Data.ENNReal.Mul
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Local bounds for mixed-exponent products at every order

Let `p > 2`, `1 < q ≤ p` and let `Ω` be an open planar domain. Fix real normed spaces `F`, `G`
and `H` with `F` and `G` finite-dimensional and `H` complete. For every `k`, on a set `U` whose
closure is compact and contained in `Ω`, there is a constant `C` such that for every continuous
bilinear map `B : F × G → H`
`‖B(f, g)‖_{W^{k+1,q}(U)} ≤ C ‖B‖ ‖f‖_{W^{k+1,p}(Ω)} ‖g‖_{W^{k+1,q}(Ω)}`.
This is the local bound that accompanies the membership statement
`TauCeti.MemWkpLoc.bilin_succ`; at `q = p` it is the local bound for the algebra property of
`W^{k+1,p}_loc`. The constant depends on the spaces, the exponents, the order and the sets, and is
uniform in `B`, `f` and `g`. No membership hypothesis is needed: the bound holds trivially when a
norm on the right is infinite.

The proof is by induction on `k`, starting from the order-one bound
`TauCeti.exists_eLpNormWkp_one_bilin_le`. By the weak Leibniz rule the weak derivative of
`B(f, g)` is `B(Df, g) + B(f, Dg)`, a sum of two products of the same kind for the bilinear maps
`B.precompL ℂ` and `B.precompR ℂ`, whose operator norms are at most `‖B‖`.

## Main declarations

* `TauCeti.exists_eLpNormWkp_bilin_le`: the bound at every positive order.
* `TauCeti.exists_eLpNormWkp_clm_apply_le`: the field form `z ↦ A z (u z)` for a coefficient field
  `A` of linear maps.
* `TauCeti.exists_eLpNormWkp_compL_le`: the composition form `z ↦ A z ∘L C z`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

/-- The `W^{k,p}` norm is bounded by the `W^{k+1,p}` norm. -/
private theorem eLpNormWkp_le_eLpNormWkp_add_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ≥0∞} {V : Set ℂ} (k : ℕ) (u : ℂ → E) :
    eLpNormWkp r V k u ≤ eLpNormWkp r V (k + 1) u := by
  induction k generalizing E with
  | zero =>
    rw [eLpNormWkp_zero]
    exact eLpNorm_le_eLpNormWkp
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ (k := k + 1)]
    gcongr
    exact ih _

/-- **Local bound for mixed-exponent products at every positive order.** Fix real normed spaces
`F`, `G` and `H` with `F` and `G` finite-dimensional and `H` complete. For `p > 2`, `1 < q ≤ p`,
every `k` and a set `U` whose closure is compact and contained in `Ω`, there is a constant `C`
such that `‖B(f, g)‖_{W^{k+1,q}(U)} ≤ C ‖B‖ ‖f‖_{W^{k+1,p}(Ω)} ‖g‖_{W^{k+1,q}(Ω)}` for every
continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. At `k = 0`
this is `TauCeti.exists_eLpNormWkp_one_bilin_le`; at `q = p` it is the local bound for the algebra
property of `W^{k+1,p}_loc`. -/
theorem exists_eLpNormWkp_bilin_le [CompleteSpace H] (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (k : ℕ) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp q U (k + 1) (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω (k + 1) f * eLpNormWkp q Ω (k + 1) g := by
  induction k generalizing F G H with
  | zero => exact exists_eLpNormWkp_one_bilin_le hp hq hqp hU hUΩ
  | succ k ih =>
    -- The order-`k + 1` bound for `B` controls the `L^q` part, and those for `B.precompL ℂ` and
    -- `B.precompR ℂ` control the two terms of the weak derivative given by the Leibniz rule.
    obtain ⟨C₀, hC₀⟩ := ih (F := F) (G := G) (H := H)
    obtain ⟨Cl, hCl⟩ := ih (F := ℂ →L[ℝ] F) (G := G) (H := ℂ →L[ℝ] H)
    obtain ⟨Cr, hCr⟩ := ih (F := F) (G := ℂ →L[ℝ] G) (H := ℂ →L[ℝ] H)
    refine ⟨C₀ + Cl + Cr + 1, fun B f g => ?_⟩
    have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
    let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨hq1.trans (by exact_mod_cast hqp)⟩
    have hq0 : (q : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hq1).ne'
    have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hUm : volume.restrict U ≤ volume.restrict Ω :=
      Measure.restrict_mono (subset_closure.trans hUΩ) le_rfl
    -- If `B = 0` or either factor vanishes almost everywhere on `Ω`, so does the product on `U`.
    have hvanish (h : (fun z => B (f z) (g z)) =ᵐ[volume.restrict Ω] 0) :
        eLpNormWkp q U (k + 1 + 1) (fun z => B (f z) (g z)) = 0 := by
      rw [eLpNormWkp_congr_ae (ae_mono hUm h), eLpNormWkp_zero_fun]
    refine ENNReal.le_mul_mul_of_ne_top_imp_le (fun hCB => hvanish (.of_forall fun z => ?_))
      (fun hf0 => hvanish ?_) (fun hg0 => hvanish ?_) fun _ hf hg => ?_
    · -- `eNorm_eq_zero` does not elaborate on this iterated operator space, so go through `‖B‖`.
      have hB : ‖B‖ₑ = 0 := (mul_eq_zero.1 hCB).resolve_left fun h => by
        exact (ENNReal.coe_ne_zero.2 (add_pos_of_nonneg_of_pos zero_le one_pos).ne') h
      simp [B.opNorm_zero_iff.1 <| (norm_nonneg B).antisymm' <| by simpa [← ofReal_norm] using hB]
    · filter_upwards [ae_eq_zero_of_eLpNormWkp_eq_zero hp0 hf0] with z hz
      simp [hz]
    · filter_upwards [ae_eq_zero_of_eLpNormWkp_eq_zero hq0 hg0] with z hz
      simp [hz]
    -- Weak derivatives of the factors realizing their norms on `Ω`.
    obtain ⟨Df, hDf, hDfk, hfΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hf
    obtain ⟨Dg, hDg, hDgk, hgΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hg
    set X := eLpNormWkp p Ω (k + 1 + 1) f
    set Y := eLpNormWkp q Ω (k + 1 + 1) g
    have hfX : eLpNormWkp p Ω (k + 1) f ≤ X := eLpNormWkp_le_eLpNormWkp_add_one _ f
    have hgY : eLpNormWkp q Ω (k + 1) g ≤ Y := eLpNormWkp_le_eLpNormWkp_add_one _ g
    have hDfX : eLpNormWkp p Ω (k + 1) Df ≤ X := hfΩ ▸ le_add_self
    have hDgY : eLpNormWkp q Ω (k + 1) Dg ≤ Y := hgΩ ▸ le_add_self
    -- The weak Leibniz rule on `Ω`, with `f` locally bounded.
    have hfloc : MemWkpLoc p Ω 1 f :=
      (memWkpLoc_of_eLpNormWkp_ne_top hf).of_le (by omega)
    have hLeib := hDf.bilin_of_memLpLoc B hp hq hqp
      ((hfloc.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top)
      (memLp_of_eLpNormWkp_ne_top hDfk).memLpLoc hDg (memLp_of_eLpNormWkp_ne_top hg).memLpLoc
      (memLp_of_eLpNormWkp_ne_top hDgk).memLpLoc
    have hint : Opens.interior U ≤ Ω := fun z hz => hUΩ (subset_closure (interior_subset hz))
    calc
      _ ≤ eLpNorm (fun z => B (f z) (g z)) q (volume.restrict U) +
          eLpNormWkp q U (k + 1)
            (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) :=
        eLpNormWkp_succ_le (hLeib.mono hint)
      _ ≤ eLpNormWkp q U (k + 1) (fun z => B (f z) (g z)) +
          (eLpNormWkp q U (k + 1) (fun z => B.precompL ℂ (Df z) (g z)) +
            eLpNormWkp q U (k + 1) (fun z => B.precompR ℂ (f z) (Dg z))) :=
        add_le_add eLpNorm_le_eLpNormWkp (eLpNormWkp_add_le hq1)
      _ ≤ C₀ * ‖B‖ₑ * X * Y + (Cl * ‖B‖ₑ * X * Y + Cr * ‖B‖ₑ * X * Y) := by
        gcongr
        · exact (hC₀ B f g).trans (by gcongr)
        · refine (hCl (B.precompL ℂ) Df g).trans ?_
          gcongr
          exact eNorm_le_iff_norm_le.2 (B.norm_precompL_le ℂ)
        · refine (hCr (B.precompR ℂ) f Dg).trans ?_
          gcongr
          exact eNorm_le_iff_norm_le.2 (B.norm_precompR_le ℂ)
      _ = ↑(C₀ + Cl + Cr) * ‖B‖ₑ * X * Y := by
        push_cast
        ring
      _ ≤ _ := by
        gcongr ?_ * _ * _ * _
        exact_mod_cast le_self_add

/-- **Local bound for coefficient fields acting on local Sobolev maps.** For `p > 2`,
`1 < q ≤ p`, every `k` and a set `U` whose closure is compact and contained in `Ω`, there is a
constant `C` such that `‖z ↦ A z (u z)‖_{W^{k+1,q}(U)} ≤ C ‖A‖_{W^{k+1,p}(Ω)} ‖u‖_{W^{k+1,q}(Ω)}`
for every coefficient field `A : ℂ → F →L[ℝ] G` and every `u : ℂ → F`. This is the bound that
accompanies `TauCeti.MemWkpLoc.clm_apply_succ`. -/
theorem exists_eLpNormWkp_clm_apply_le (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) (k : ℕ)
    {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → F →L[ℝ] G) (u : ℂ → F),
      eLpNormWkp q U (k + 1) (fun z => A z (u z)) ≤
        C * eLpNormWkp p Ω (k + 1) A * eLpNormWkp q Ω (k + 1) u := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le (F := F →L[ℝ] G) (G := F) (H := G) hp hq hqp k
    hU hUΩ
  refine ⟨C, fun A u => (hC (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) A u).trans ?_⟩
  calc
    _ ≤ C * 1 * eLpNormWkp p Ω (k + 1) A * eLpNormWkp q Ω (k + 1) u := by
      gcongr
      exact (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_one.2 ContinuousLinearMap.norm_id_le)
    _ = _ := by rw [mul_one]

/-- **Local bound for compositions of local Sobolev fields of linear maps.** For `p > 2`,
`1 < q ≤ p`, every `k` and a set `U` whose closure is compact and contained in `Ω`, there is a
constant `C` such that `‖z ↦ A z ∘L T z‖_{W^{k+1,q}(U)} ≤ C ‖A‖_{W^{k+1,p}(Ω)} ‖T‖_{W^{k+1,q}(Ω)}`
for all fields `A : ℂ → G →L[ℝ] H` and `T : ℂ → F →L[ℝ] G`. This is the bound that accompanies
`TauCeti.MemWkpLoc.compL_succ`. -/
theorem exists_eLpNormWkp_compL_le [FiniteDimensional ℝ H] (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p) (k : ℕ) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → G →L[ℝ] H) (T : ℂ → F →L[ℝ] G),
      eLpNormWkp q U (k + 1) (fun z => (A z).comp (T z)) ≤
        C * eLpNormWkp p Ω (k + 1) A * eLpNormWkp q Ω (k + 1) T := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le (F := G →L[ℝ] H) (G := F →L[ℝ] G)
    (H := F →L[ℝ] H) hp hq hqp k hU hUΩ
  refine ⟨C, fun A T => (hC (ContinuousLinearMap.compL ℝ F G H) A T).trans ?_⟩
  calc
    _ ≤ C * 1 * eLpNormWkp p Ω (k + 1) A * eLpNormWkp q Ω (k + 1) T := by
      gcongr
      exact (ofReal_norm _).symm.trans_le
        (ENNReal.ofReal_le_one.2 (ContinuousLinearMap.norm_compL_le ℝ F G H))
    _ = _ := by rw [mul_one]

end TauCeti
