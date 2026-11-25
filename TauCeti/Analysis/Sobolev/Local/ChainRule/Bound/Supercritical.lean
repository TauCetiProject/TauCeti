/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Sobolev.Local.ChainRule.Supercritical
import TauCeti.Data.ENNReal.Mul
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Supercritical

/-!
# Local bounds for composition for `kp > 2`, including `p ≤ 2`

Let `Ω ⊆ ℂ` be open, let `1 < p` and `k p > 2`, and let `F` and `G` be finite-dimensional. Let
`g : F → G` be `Cᵏ` on an open set `W` and let `L ⊆ W` be compact. On a set `U` whose closure is
compact and contained in `Ω` there is a constant `C` such that

`‖g ∘ u‖_{W^{k,p}(U)} ≤ C (1 + ‖u‖_{W^{k,p}(Ω)})^k`

for every `u` continuous on `Ω` with `u(Ω) ⊆ L` (`TauCeti.exists_eLpNormWkp_comp_le_of_two_lt_mul`).
This is the bound that accompanies the membership theorem
`TauCeti.MemWkpLoc.contDiffOn_comp_of_two_lt_mul`.

## Proof

As for the membership theorem, the proof bounds more generally `B(g ∘ u, v)` in `W^{m,p}(U)` for
`m ≤ k`, a continuous bilinear map `B`, a `Cᵐ` map `g` and a multiplier `v` with `m ≤ b` and
`(b + k - m) p > 2`, by `C (1 + ‖u‖_{W^{k,p}(Ω)})^m ‖v‖_{W^{b,p}(Ω)}`. This is an induction on `m`.
By the weak Leibniz rule `TauCeti.HasWeakFDerivOn.bilin_comp_of_two_lt_mul`,

`D B(g ∘ u, v) = B(Dg(u) ∘ Du, v) + B(g ∘ u, Dv)`.

The second term is the case `m - 1` for the multiplier `Dv`. The first is `Φ(Du, v)` evaluated at
`Dg(u)`, for the bilinear map `Φ = ContinuousLinearMap.compPrecompL ℂ F B`. On an open set `V`
between `U` and `Ω`, the case `m - 1` for `Dg` bounds it by `‖Φ(Du, v)‖_{W^{m-1,p}(V)}`, and the
product bound `TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul` bounds that by
`‖Du‖_{W^{k-1,p}(Ω)} ‖v‖_{W^{b,p}(Ω)}`, raising the power by one. The case `B(x, c) = c x` and
`v = 1` on `V` gives the theorem.

## Main declarations

* `TauCeti.exists_eLpNormWkp_comp_le_of_two_lt_mul`: the local bound for `g ∘ u` in `W^{k,p}`
  for `kp > 2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

universe uF uG uH

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The order-zero case of the induction: for `g` continuous on a neighbourhood of the compact set
`L`, `‖B(g ∘ u, v)‖_{Lᵖ(U)} ≤ C ‖v‖_{W^{b,p}(Ω)}` when `u` is continuous on `Ω` and maps it into
`L`. -/
private theorem exists_eLpNorm_bilin_comp_le {G V H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (B : G →L[ℝ] V →L[ℝ] H) {p : ℝ≥0∞} {g : F → G} {W L : Set F}
    (hg : ContinuousOn g W) (hL : IsCompact L) (hLW : L ⊆ W) {Ω : Opens ℂ} {U : Set ℂ}
    (hUΩ : closure U ⊆ Ω) (b : ℕ) :
    ∃ C : ℝ≥0, ∀ (u : ℂ → F) (v : ℂ → V), ContinuousOn u Ω → MapsTo u Ω L →
      eLpNorm (fun z => B (g (u z)) (v z)) p (volume.restrict U) ≤
        C * eLpNormWkp p Ω b v := by
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (hg.mono hLW)
  refine ⟨‖B‖₊ * M.toNNReal + 1, fun u v huc huL => ?_⟩
  have hK : MeasurableSet (closure U) := isClosed_closure.measurableSet
  have hvΩ : eLpNorm v p (volume.restrict (closure U)) ≤ eLpNormWkp p Ω b v :=
    (eLpNorm_mono_measure v (Measure.restrict_mono hUΩ le_rfl)).trans eLpNorm_le_eLpNormWkp
  -- A map `v` that is not almost everywhere strongly measurable has infinite `Lᵖ` norm.
  by_cases hvm : AEStronglyMeasurable v (volume.restrict (closure U))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hvm, top_le_iff] at hvΩ
    rw [hvΩ, ENNReal.mul_top (by simp)]
    exact le_top
  have hgu : ContinuousOn (fun z => g (u z)) (closure U) :=
    hg.comp (huc.mono hUΩ) ((huL.mono_left hUΩ).mono_right hLW)
  calc
    _ ≤ eLpNorm (fun z => B (g (u z)) (v z)) p (volume.restrict (closure U)) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono subset_closure le_rfl)
    _ ≤ (‖B‖₊ * M.toNNReal) • eLpNorm v p (volume.restrict (closure U)) := by
      refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
        (B.aestronglyMeasurable_comp₂ (hgu.aestronglyMeasurable hK) hvm)
        ((ae_restrict_mem hK).mono fun z hz => ?_) p
      have hgz : ‖g (u z)‖ ≤ M.toNNReal := (hM _ (huL (hUΩ hz))).trans (Real.le_coe_toNNReal M)
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_mul, coe_nnNorm, coe_nnNorm,
        coe_nnNorm]
      exact (B.le_opNorm₂ _ _).trans (by gcongr)
    _ ≤ ↑(‖B‖₊ * M.toNNReal + 1) * eLpNormWkp p Ω b v := by
      rw [ENNReal.smul_def, smul_eq_mul]
      gcongr
      exact_mod_cast le_self_add

/-- The product bound of `TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul` for one fixed
bilinear map `Φ`, with its norm absorbed into the constant. Stating it for an abstract target
space `E` keeps the operator norm of `Φ` within reach of instance search when `E` is itself a
space of operators. -/
private theorem exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul_of_fixed {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Φ : (ℂ →L[ℝ] F) →L[ℝ] V →L[ℝ] E) {p : ℝ≥0}
    (hp : 1 < p) {a b c : ℕ} (hca : c ≤ a) (hcb : c ≤ b) (habc : 2 < ((a + b - c : ℕ) : ℝ≥0) * p)
    {Ω : Opens ℂ} {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ N : ℝ≥0, ∀ (D : ℂ → ℂ →L[ℝ] F) (v : ℂ → V),
      eLpNormWkp p U c (fun z => Φ (D z) (v z)) ≤
        N * eLpNormWkp p Ω a D * eLpNormWkp p Ω b v := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul (F := ℂ →L[ℝ] F) (G := V)
    (H := E) hp hca hcb habc hU hUΩ
  refine ⟨C * ‖Φ‖₊, fun D v => (hC Φ D v).trans (le_of_eq ?_)⟩
  rw [ENNReal.coe_mul, eNorm_eq_nnNorm]

/-- The arithmetic of the inductive step: the three bounds for the `Lᵖ` part and the two
Leibniz terms combine into one bound with the power raised by one. -/
private theorem add_add_le_mul_one_add_pow_succ_mul (C₀ Cl Cr N : ℝ≥0) (X Y : ℝ≥0∞) (m : ℕ) :
    C₀ * (1 + X) ^ m * Y + (Cl * (1 + X) ^ m * (N * X * Y) + Cr * (1 + X) ^ m * Y) ≤
      ↑(C₀ + Cr + Cl * N + 1) * (1 + X) ^ (m + 1) * Y := by
  have hpow : (1 + X) ^ m ≤ (1 + X) ^ (m + 1) := pow_le_pow_right₀ le_self_add (by omega)
  have hpowX : (1 + X) ^ m * X ≤ (1 + X) ^ (m + 1) := by
    rw [pow_succ]
    exact mul_le_mul' le_rfl (le_add_self : X ≤ 1 + X)
  calc
    _ = C₀ * (1 + X) ^ m * Y + (Cl * N * ((1 + X) ^ m * X) * Y + Cr * (1 + X) ^ m * Y) := by
      ring
    _ ≤ C₀ * (1 + X) ^ (m + 1) * Y +
        (Cl * N * (1 + X) ^ (m + 1) * Y + Cr * (1 + X) ^ (m + 1) * Y) := by
      gcongr
    _ = ↑(C₀ + Cr + Cl * N) * (1 + X) ^ (m + 1) * Y := by
      push_cast
      ring
    _ ≤ _ := by
      gcongr ?_ * _ * _
      exact_mod_cast le_self_add

/-- The Leibniz step of the induction. For `u` and `v` of finite norms `X = ‖u‖_{W^{k+1,p}(Ω)}`
and `Y = ‖v‖_{W^{b+1,p}(Ω)}` there are weak derivatives `Du` and `Dv` of norms at most `X` and `Y`
such that `‖B(g ∘ u, v)‖_{W^{m+1,p}(U)}` is at most the sum of the `W^{m,p}(U)` norms of
`B(g ∘ u, v)`, of `Φ(Du, v)` evaluated at `Dg(u)`, and of `B(g ∘ u, Dv)`. -/
private theorem exists_eLpNormWkp_succ_bilin_comp_le {G V H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (B : G →L[ℝ] V →L[ℝ] H) {Φ : (ℂ →L[ℝ] F) →L[ℝ] V →L[ℝ] (F →L[ℝ] G) →L[ℝ] ℂ →L[ℝ] H}
    (hΦ : ∀ D v A, Φ D v A = B.precompL ℂ (A.comp D) v) {p : ℝ≥0} (hp : 1 < p) {k b m : ℕ}
    (hkp : 2 < ((k + 1 : ℕ) : ℝ≥0) * p) {W : Set F} (hW : IsOpen W) {g : F → G}
    (hg : ContDiffOn ℝ 1 g W) {Ω : Opens ℂ} {U : Set ℂ} (hUΩ : U ⊆ Ω) {u : ℂ → F} {v : ℂ → V}
    (huc : ContinuousOn u Ω) (huW : MapsTo u Ω W) (hX : eLpNormWkp p Ω (k + 1) u ≠ ∞)
    (hY : eLpNormWkp p Ω (b + 1) v ≠ ∞) :
    ∃ (Du : ℂ → ℂ →L[ℝ] F) (Dv : ℂ → ℂ →L[ℝ] V),
      eLpNormWkp p Ω k Du ≤ eLpNormWkp p Ω (k + 1) u ∧
      eLpNormWkp p Ω b Dv ≤ eLpNormWkp p Ω (b + 1) v ∧
      eLpNormWkp p U (m + 1) (fun z => B (g (u z)) (v z)) ≤
        eLpNormWkp p U m (fun z => B (g (u z)) (v z)) +
          (eLpNormWkp p U m (fun z =>
              ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] H) (fderiv ℝ g (u z)) (Φ (Du z) (v z))) +
            eLpNormWkp p U m (fun z => B.precompR ℂ (g (u z)) (Dv z))) := by
  obtain ⟨Du, hDu, -, hXeq⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hX
  obtain ⟨Dv, hDv, -, hYeq⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hY
  have hLeib := hDu.bilin_comp_of_two_lt_mul B hp hkp (memWkpLoc_of_eLpNormWkp_ne_top hX) huc hW
    huW hg hDv ((memWkpLoc_of_eLpNormWkp_ne_top hY).of_le (by omega))
  have hΦfun : (fun z => B.precompL ℂ ((fderiv ℝ g (u z)).comp (Du z)) (v z)) =
      fun z => ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] H) (fderiv ℝ g (u z)) (Φ (Du z) (v z)) :=
    funext fun z => by simp only [ContinuousLinearMap.apply_apply, hΦ]
  refine ⟨Du, Dv, le_add_self.trans_eq hXeq.symm, le_add_self.trans_eq hYeq.symm, ?_⟩
  rw [← hΦfun]
  exact (eLpNormWkp_succ_le (hLeib.mono fun z hz => hUΩ (interior_subset hz))).trans
    (add_le_add eLpNorm_le_eLpNormWkp (eLpNormWkp_add_le (by exact_mod_cast hp.le)))

/-- The general bound behind `TauCeti.exists_eLpNormWkp_comp_le_of_two_lt_mul`: for `1 < p` and
`kp > 2`, a continuous bilinear map `B`, a `Cᵐ` map `g` on `W ⊇ L` with `m ≤ k`, and orders
`m ≤ b` with `(b + k - m) p > 2`, there is `C` with
`‖B(g ∘ u, v)‖_{W^{m,p}(U)} ≤ C (1 + ‖u‖_{W^{k,p}(Ω)})^m ‖v‖_{W^{b,p}(Ω)}` for every `u`
continuous on `Ω` with `u(Ω) ⊆ L` and every `v`. The values of `g`, `v` and `B` lie in a universe
at least that of `F`, so that the statement is closed under the passage from `g` to `fderiv ℝ g`. -/
private theorem exists_eLpNormWkp_bilin_comp_le_aux {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {W L : Set F} (hW : IsOpen W) (hL : IsCompact L) (hLW : L ⊆ W)
    (m : ℕ) (hmk : m ≤ k) {G V H : Type (max uF uH)} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (B : G →L[ℝ] V →L[ℝ] H) {g : F → G} {b : ℕ} (hg : ContDiffOn ℝ m g W) (hmb : m ≤ b)
    (hbkm : 2 < ((b + k - m : ℕ) : ℝ≥0) * p) {Ω : Opens ℂ} {U : Set ℂ}
    (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (u : ℂ → F) (v : ℂ → V), ContinuousOn u Ω → MapsTo u Ω L →
      eLpNormWkp p U m (fun z => B (g (u z)) (v z)) ≤
        C * (1 + eLpNormWkp p Ω k u) ^ m * eLpNormWkp p Ω b v := by
  induction m generalizing G V H g b Ω U with
  | zero =>
    obtain ⟨C, hC⟩ := exists_eLpNorm_bilin_comp_le B (p := p) hg.continuousOn hL hLW hUΩ b
    exact ⟨C, fun u v huc huL => by simpa using hC u v huc huL⟩
  | succ m ih =>
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨V', hUV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hU hUΩ
    -- `Φ = B.compPrecompL ℂ F`, kept opaque: unfolding it makes unification slow.
    obtain ⟨Φ, hΦdef⟩ : ∃ Φ : (ℂ →L[ℝ] F) →L[ℝ] V →L[ℝ] (F →L[ℝ] G) →L[ℝ] ℂ →L[ℝ] H,
        ∀ D v A, Φ D v A = B.precompL ℂ (A.comp D) v :=
      ⟨B.compPrecompL ℂ F, B.compPrecompL_apply⟩
    -- The order-`m` bounds for `B` itself (the `Lᵖ` part), for `B.precompR ℂ` (the term with
    -- `Dv`) and for `Dg` against `Φ(Du, v)` on `V'`, and the product bound for `Φ`.
    obtain ⟨C₀, hC₀⟩ := ih (by omega) B (hg.of_le (by norm_cast; omega)) (b := b + 1) (by omega)
      ((hbkm.trans_le (mul_le_mul_left (Nat.cast_le.2 (by omega)) _))) hU hUΩ
    obtain ⟨Cr, hCr⟩ := ih (V := ℂ →L[ℝ] V) (H := ℂ →L[ℝ] H) (by omega) (B.precompR ℂ)
      (hg.of_le (by norm_cast; omega)) (b := b) (by omega)
      (by rwa [show b + (k + 1) - m = b + 1 + (k + 1) - (m + 1) by omega]) hU hUΩ
    obtain ⟨Cl, hCl⟩ := ih (G := F →L[ℝ] G) (V := (F →L[ℝ] G) →L[ℝ] ℂ →L[ℝ] H)
      (H := ℂ →L[ℝ] H) (by omega) (ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] H))
      (hg.fderiv_of_isOpen hW (by push_cast; rfl)) (b := m) le_rfl
      (by rwa [Nat.add_sub_cancel_left]) hU hUV
    obtain ⟨N, hN⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul_of_fixed
      (E := (F →L[ℝ] G) →L[ℝ] ℂ →L[ℝ] H) Φ hp (a := k) (b := b + 1) (c := m) (by omega)
      (by omega) (by rwa [show k + (b + 1) - m = b + 1 + (k + 1) - (m + 1) by omega]) hVc hVΩ
    refine ⟨C₀ + Cr + Cl * N + 1, fun u v huc huL => ?_⟩
    have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
    have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hp1).ne'
    have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
    set X := eLpNormWkp p Ω (k + 1) u
    set Y := eLpNormWkp p Ω (b + 1) v
    -- The reduction to finite norms: the factor `C (1 + X)^(m + 1)` vanishes never, and is
    -- infinite when `X` is.
    refine ENNReal.le_mul_of_ne_top_imp_le (fun h => absurd h (mul_ne_zero (by positivity)
      (pow_ne_zero _ (by simp)))) (fun hY0 => ?_) fun ha hY => ?_
    · -- If `v` vanishes almost everywhere on `Ω`, so does the product on `U`.
      have h0 : (fun z => B (g (u z)) (v z)) =ᵐ[volume.restrict U] 0 :=
        Filter.Eventually.mono (ae_mono (Measure.restrict_mono hUΩ' le_rfl)
          (ae_eq_zero_of_eLpNormWkp_eq_zero hp0 hY0)) fun z hz => by simp [hz]
      rw [eLpNormWkp_congr_ae h0, eLpNormWkp_zero_fun]
    have hX : X ≠ ∞ := fun h => ha (by
      rw [h, add_top, ENNReal.top_pow (by omega), ENNReal.mul_top (by positivity)])
    obtain ⟨Du, Dv, hDuX, hDvY, hstep⟩ := exists_eLpNormWkp_succ_bilin_comp_le (m := m) B hΦdef hp
      hkp hW (hg.of_le (by norm_cast; omega)) hUΩ' huc (huL.mono_right hLW) hX hY
    have hVΩ' : (V' : Set ℂ) ⊆ Ω := subset_closure.trans hVΩ
    refine hstep.trans ((add_le_add (hC₀ u v huc huL) (add_le_add ?_ ((hCr u Dv huc huL).trans
      (by gcongr)))).trans (add_add_le_mul_one_add_pow_succ_mul C₀ Cl Cr N X Y m))
    refine (hCl u _ (huc.mono hVΩ') (huL.mono_left hVΩ')).trans ?_
    gcongr
    · exact eLpNormWkp_mono_set hVΩ'
    · exact (hN Du v).trans (by gcongr)

variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {Ω : Opens ℂ}

/-- **Local bound for composition for `kp > 2`.** Let `1 < p` and `k p > 2`, let `g : F → G` be
`Cᵏ` on an open set `W`, let `L ⊆ W` be compact and let `U` have compact closure contained in
`Ω`. There is a constant `C` such that `‖g ∘ u‖_{W^{k,p}(U)} ≤ C (1 + ‖u‖_{W^{k,p}(Ω)})^k` for
every `u` continuous on `Ω` with `u(Ω) ⊆ L`. This includes `p ≤ 2` for `k ≥ 2`, and is the bound
that accompanies `TauCeti.MemWkpLoc.contDiffOn_comp_of_two_lt_mul`. -/
theorem exists_eLpNormWkp_comp_le_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {g : F → G} {W L : Set F} (hW : IsOpen W)
    (hg : ContDiffOn ℝ k g W) (hL : IsCompact L) (hLW : L ⊆ W) {U : Set ℂ}
    (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContinuousOn u Ω → MapsTo u Ω L →
      eLpNormWkp p U k (fun z => g (u z)) ≤ C * (1 + eLpNormWkp p Ω k u) ^ k := by
  -- Move the values to `ULift G`, in a universe at least that of `F`, and multiply by the
  -- constant `c⁻¹ 1` of `ULift ℝ` on an open set `V` between `U` and `Ω`, of finite measure.
  let e : G ≃L[ℝ] ULift.{uF} G := (LinearIsometryEquiv.ulift ℝ G).symm.toContinuousLinearEquiv
  let c : ULift.{max uF uG} ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.ulift
  let B : ULift.{uF} G →L[ℝ] ULift.{max uF uG} ℝ →L[ℝ] ULift.{uF} G :=
    ((ContinuousLinearMap.compL ℝ _ ℝ _).flip (c : ULift.{max uF uG} ℝ →L[ℝ] ℝ)).comp
      (ContinuousLinearMap.lsmul ℝ ℝ).flip
  obtain ⟨V, hUV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hU hUΩ
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_comp_le_aux hp hkp hW hL hLW k le_rfl B
    (e.contDiff.comp_contDiffOn hg) le_rfl (by rwa [Nat.add_sub_cancel]) hU hUV
  set Y := eLpNormWkp p V k (fun _ : ℂ => c.symm 1)
  have hY : Y ≠ ∞ := ((contDiff_const (c := c.symm 1)).memWkpLoc (p := (p : ℝ≥0∞)) (k := k)
    (U := Ω)).eLpNormWkp_ne_top_of_closure_subset hVc hVΩ
  refine ⟨‖(e.symm : ULift.{uF} G →L[ℝ] G)‖₊ * C * Y.toNNReal, fun u huc huL => ?_⟩
  have hVΩ' : (V : Set ℂ) ⊆ Ω := subset_closure.trans hVΩ
  calc
    _ ≤ ‖(e.symm : ULift.{uF} G →L[ℝ] G)‖ₑ *
        eLpNormWkp p U k (fun z => B (e (g (u z))) (c.symm 1)) := by
      convert eLpNormWkp_clm_comp_le (e.symm : ULift.{uF} G →L[ℝ] G) using 2
      ext z
      simp [B]
    _ ≤ ‖(e.symm : ULift.{uF} G →L[ℝ] G)‖ₑ * (C * (1 + eLpNormWkp p Ω k u) ^ k * Y) := by
      gcongr
      exact (hC u _ (huc.mono hVΩ') (huL.mono_left hVΩ')).trans
        (by gcongr; exact eLpNormWkp_mono_set hVΩ')
    _ = _ := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hY, eNorm_eq_nnNorm]
      ring

end TauCeti
