/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.Drift
import TauCeti.Analysis.Sobolev.W1p.LevelSet
import TauCeti.MeasureTheory.Function.Holder

/-!
# Global boundedness of weak subsolutions with small lower-order coefficients in `L^q`

Let `Ω ⊆ ℝⁿ` be open with finite measure, let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and let `q > max(2, n)`. Consider the operator

`L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u`

with lower-order coefficients that need not be bounded: `b, e ∈ L^q(Ω; ℝⁿ)` and
`c ∈ L^{q/2}(Ω)`, subject to the weak sign condition `∫ c φ + ⟪e, ∇φ⟫ ≥ 0` for every nonnegative
`φ ∈ H¹₀(Ω)`, that is `-∂ᵢeⁱ + c ≥ 0` weakly. This file proves the weak maximum principle with
data for weak subsolutions of `L u ≤ g + ∂ᵢFⁱ`, `g ∈ L^{q/2}(Ω)`, `F ∈ L^q(Ω; ℝⁿ)`, meaning

`∫ ⟪a ∇u, ∇φ⟫ + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ + ∫ c u φ ≤ ∫ g φ - ∫ ⟪F, ∇φ⟫`

for every nonnegative `φ ∈ H¹₀(Ω)`, when the lower-order coefficients are small in the
scale-invariant norms

`(‖b‖_q + ‖e‖_q) |Ω| ^ (1/n - 1/q) + ‖c‖_{q/2} |Ω| ^ (2/n - 2/q) ≤ η λ`,

with `η > 0` depending only on `n`, `q` and the normalization of the Haar measure: if `u ≤ k` on
`∂Ω` for a level `k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost everywhere in `Ω`

`u ≤ k + C (‖g‖_{q/2} |Ω| ^ (2/n - 2/q) + ‖F‖_q |Ω| ^ (1/n - 1/q)) / λ`

(`TauCeti.PDE.exists_ae_value_le_add_of_small_lowerOrder`). In the sign convention of Rosales,
whose operator is `∂ᵢ(aⁱʲ ∂ⱼu + bⁱ u) + cⁱ ∂ᵢu + d u`, the coefficients here are `e = b_R`,
`b = -c_R` and `c = -d_R`, and the sign condition is his weak non-positivity of `(b_R, d_R)`.

Since `q > n`, the smallness hypothesis is what dilation produces. If `u` is a subsolution on a
ball of radius `ρ`, then `u(x₀ + ρ ·)` is a subsolution on the unit ball for the coefficients
`ρ b(x₀ + ρ ·)`, `ρ e(x₀ + ρ ·)` and `ρ² c(x₀ + ρ ·)`. Up to a dimensional factor, their
scale-invariant norms are those of `b`, `e` and `c` on the ball of radius `ρ`, namely
`ρ ^ (1 - n/q) ‖b‖_{L^q(B_ρ)}` and `ρ ^ (2 - 2n/q) ‖c‖_{L^{q/2}(B_ρ)}`, which tend to zero with
`ρ`. This is how the
maximum principle enters the proof of Hopf's boundary point lemma for weak supersolutions of
divergence-form equations with Hölder principal coefficients and lower-order coefficients in `L^q`
by Rosales: after rescaling a boundary neighbourhood, the lower-order coefficients of the rescaled
operator are as small as needed.

## The argument

For a level `l ≥ k`, test the subsolution inequality against `w = (u - l)⁺ ∈ H¹₀(Ω)`. Above the
level `u = w + l`, and below it `w` and `∇w` vanish, so the lower-order terms split into terms in
`w` alone and `l` times the sign condition tested against `w`, which is nonnegative. The terms in
`w` are bounded by Hölder's inequality in three factors
(`TauCeti.integral_norm_mul_norm_mul_norm_le`) and the Sobolev inequality `‖w‖_s ≤ S ‖∇w‖₂` with
`1/q + 1/s = 1/2`:

`|∫ w ⟪e, ∇w⟫| ≤ ‖e‖_q S ‖∇w‖₂²`, `|∫ ⟪b, ∇w⟫ w| ≤ ‖b‖_q S ‖∇w‖₂²` and
`|∫ c w²| ≤ ‖c‖_{q/2} S² ‖∇w‖₂²`.

When `(‖b‖_q + ‖e‖_q) S + ‖c‖_{q/2} S² ≤ λ/2` they are absorbed by ellipticity, and the truncation
satisfies `λ/2 ‖∇w‖₂² ≤ ∫ g w - ∫ ⟪F, ∇w⟫`. Stampacchia's bound
`TauCeti.PDE.exists_ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le` turns this
energy inequality into the bound on `u`. On a set of finite measure the Sobolev constant is
`S = K |Ω| ^ (1/n - 1/q)`
(`TauCeti.PDE.exists_forall_eLpNorm_value_le_toNNReal_mul_measureReal_rpow`), which gives the
scale-invariant smallness condition.

## Main declarations

* `TauCeti.PDE.exists_ae_value_le_add_of_small_lowerOrder`: the weak maximum principle with data
  for lower-order coefficients `b, e ∈ L^q` and `c ∈ L^{q/2}` that are small in the
  scale-invariant norms, `q > max(2, n)`.
* `TauCeti.PDE.exists_ae_abs_value_le_of_small_lowerOrder`: the two-sided bound for weak solutions
  of the Dirichlet problem with zero boundary values.

Bounded drifts that are not small are treated in
`TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.LowerOrder`, and the weak maximum
principle without data for a drift in `L^q` that is not small in
`TauCeti.Analysis.PDE.MaximumPrinciple.LpDrift`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.16 and the remark on lower-order coefficients in `L^q` that follows it.
* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. (2019),
  arXiv:1806.07003, Lemma 3.2 and the proof of Theorem 4.1.
* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier 15 (1965).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- The pointwise bound of a first-order term: `|f ⟪d, G⟫| ≤ ‖d‖ ‖G‖ |f|`. -/
private theorem norm_mul_inner_le (f : ℝ) (d G : EuclideanSpace ℝ ι) :
    ‖f * ⟪d, G⟫‖ ≤ ‖d‖ * (‖G‖ * ‖f‖) := by
  rw [norm_mul]
  nlinarith [norm_inner_le_norm (𝕜 := ℝ) d G, norm_nonneg f]

omit [DecidableEq ι] in
/-- Hölder's inequality and the Sobolev inequality for a first-order lower-order term:
`-∫ w ⟪d, ∇w⟫ ≤ ‖d‖_p S ‖∇w‖₂²` when `1/p + 1/t = 1/2` and `‖w‖_t ≤ S ‖∇w‖₂`. -/
private theorem neg_integral_value_mul_inner_gradient_le {p t : ℝ≥0∞}
    (hpt : p⁻¹ + t⁻¹ = 2⁻¹) {S : ℝ≥0} {w : W1p mu Omega 2}
    (hS : eLpNorm (W1p.value w) t (mu.restrict Omega) ≤ S * ‖W1p.gradient w‖ₑ)
    {d : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hd : MemLp d p (mu.restrict Omega)) :
    -(∫ x in Omega, W1p.value w x * ⟪d x, W1p.gradient w x⟫ ∂mu) ≤
      (eLpNorm d p (mu.restrict Omega)).toReal * S * ‖W1p.gradient w‖ ^ 2 := by
  have : p.HolderTriple t 2 := ⟨hpt⟩
  have hwt := W1p.memLp_value_of_eLpNorm_le hS
  calc -(∫ x in Omega, W1p.value w x * ⟪d x, W1p.gradient w x⟫ ∂mu)
      ≤ ∫ x in Omega, ‖d x‖ * (‖W1p.gradient w x‖ * ‖W1p.value w x‖) ∂mu :=
        (neg_le_abs _).trans <| abs_integral_le_integral_abs.trans <|
          integral_mono_of_nonneg (ae_of_all _ fun x ↦ abs_nonneg _)
            (hd.integrable_norm_mul_norm_mul_norm (r := 2) (s := 2) (Lp.memLp _) hwt)
            (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).symm.trans_le (norm_mul_inner_le _ _ _))
    _ ≤ (eLpNorm d p (mu.restrict Omega)).toReal * ((eLpNorm (W1p.gradient w) 2
          (mu.restrict Omega)).toReal * (eLpNorm (W1p.value w) t (mu.restrict Omega)).toReal) :=
        integral_norm_mul_norm_mul_norm_le (r := 2) (s := 2) hd (Lp.memLp _) hwt
    _ ≤ (eLpNorm d p (mu.restrict Omega)).toReal * (‖W1p.gradient w‖ * (S * ‖W1p.gradient w‖)) := by
        rw [← Lp.norm_def]
        gcongr
        exact W1p.toReal_eLpNorm_value_le_mul_norm_gradient hS
    _ = _ := by ring

omit [DecidableEq ι] in
/-- Hölder's inequality and the Sobolev inequality for the zeroth-order term:
`-∫ c w² ≤ ‖c‖_r S² ‖∇w‖₂²` when `1/r + 2/t = 1` and `‖w‖_t ≤ S ‖∇w‖₂`. -/
private theorem neg_integral_mul_value_mul_value_le {r t : ℝ≥0∞}
    (hrt : r⁻¹ + t⁻¹ + t⁻¹ = 1) {S : ℝ≥0} {w : W1p mu Omega 2}
    (hS : eLpNorm (W1p.value w) t (mu.restrict Omega) ≤ S * ‖W1p.gradient w‖ₑ)
    (hc : MemLp c r (mu.restrict Omega)) :
    -(∫ x in Omega, c x * W1p.value w x * W1p.value w x ∂mu) ≤
      (eLpNorm c r (mu.restrict Omega)).toReal * S ^ 2 * ‖W1p.gradient w‖ ^ 2 := by
  have : r.HolderTriple t (r⁻¹ + t⁻¹)⁻¹ := ⟨by rw [inv_inv]⟩
  have : t.HolderTriple (r⁻¹ + t⁻¹)⁻¹ 1 := ⟨by rw [inv_inv, inv_one, ← hrt]; ring⟩
  have hwt := W1p.memLp_value_of_eLpNorm_le hS
  have hsob := W1p.toReal_eLpNorm_value_le_mul_norm_gradient hS
  calc -(∫ x in Omega, c x * W1p.value w x * W1p.value w x ∂mu)
      ≤ ∫ x in Omega, ‖c x‖ * (‖W1p.value w x‖ * ‖W1p.value w x‖) ∂mu :=
        (neg_le_abs _).trans <| abs_integral_le_integral_abs.trans <|
          integral_mono_of_nonneg (ae_of_all _ fun x ↦ abs_nonneg _)
            (hc.integrable_norm_mul_norm_mul_norm (s := (r⁻¹ + t⁻¹)⁻¹) hwt hwt)
            (ae_of_all _ fun x ↦ by simp only [abs_mul, ← Real.norm_eq_abs, mul_assoc, le_refl])
    _ ≤ (eLpNorm c r (mu.restrict Omega)).toReal *
          ((eLpNorm (W1p.value w) t (mu.restrict Omega)).toReal *
            (eLpNorm (W1p.value w) t (mu.restrict Omega)).toReal) :=
        integral_norm_mul_norm_mul_norm_le (s := (r⁻¹ + t⁻¹)⁻¹) hc hwt hwt
    _ ≤ (eLpNorm c r (mu.restrict Omega)).toReal *
          ((S * ‖W1p.gradient w‖) * (S * ‖W1p.gradient w‖)) := by
        gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
/-- **The lower-order energy is absorbed.** If `‖v‖_t ≤ S ‖∇v‖₂`, `b, e ∈ Lᵖ` and `c ∈ Lʳ` with
`1/p + 1/t = 1/2` and `1/r + 2/t = 1`, then the lower-order part of the energy of `v` is bounded
below:

`-(∫ v ⟪e, ∇v⟫ + ∫ ⟪b, ∇v⟫ v + ∫ c v²) ≤ ((‖b‖_p + ‖e‖_p) S + ‖c‖_r S²) ‖∇v‖₂²`. -/
private theorem neg_integral_lowerOrder_le {p r t : ℝ≥0∞} (hpt : p⁻¹ + t⁻¹ = 2⁻¹)
    (hrt : r⁻¹ + t⁻¹ + t⁻¹ = 1) {S : ℝ≥0} {v : W1p mu Omega 2}
    (hS : eLpNorm (W1p.value v) t (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    (hb : MemLp b p (mu.restrict Omega)) (he : MemLp e p (mu.restrict Omega))
    (hc : MemLp c r (mu.restrict Omega)) :
    -(∫ x in Omega, W1p.value v x * ⟪e x, W1p.gradient v x⟫ ∂mu +
        ∫ x in Omega, ⟪b x, W1p.gradient v x⟫ * W1p.value v x ∂mu +
        ∫ x in Omega, c x * W1p.value v x * W1p.value v x ∂mu) ≤
      (((eLpNorm b p (mu.restrict Omega)).toReal + (eLpNorm e p (mu.restrict Omega)).toReal) * S +
        (eLpNorm c r (mu.restrict Omega)).toReal * S ^ 2) * ‖W1p.gradient v‖ ^ 2 := by
  have hcomm : ∫ x in Omega, ⟪b x, W1p.gradient v x⟫ * W1p.value v x ∂mu =
      ∫ x in Omega, W1p.value v x * ⟪b x, W1p.gradient v x⟫ ∂mu :=
    integral_congr_ae (ae_of_all _ fun _ ↦ mul_comm _ _)
  linarith [neg_integral_value_mul_inner_gradient_le hpt hS he,
    neg_integral_value_mul_inner_gradient_le hpt hS hb,
    neg_integral_mul_value_mul_value_le hrt hS hc]

omit [DecidableEq ι] in
/-- The integrability of the lower-order terms tested against `v ∈ Lᵗ ∩ H¹(Ω)`, on a set of finite
measure, for `e ∈ Lᵖ` and `c ∈ Lʳ` with `1/p + 1/t = 1/2` and `1/r + 2/t = 1`. -/
private theorem integrable_lowerOrder (hOmega : mu Omega ≠ ∞) {p r t : ℝ≥0∞}
    (hpt : p⁻¹ + t⁻¹ = 2⁻¹) (hrt : r⁻¹ + t⁻¹ + t⁻¹ = 1) (he : MemLp e p (mu.restrict Omega))
    (hc : MemLp c r (mu.restrict Omega)) {v : W1p mu Omega 2}
    (hvt : MemLp (W1p.value v) t (mu.restrict Omega)) :
    Integrable (fun x ↦ ⟪e x, W1p.gradient v x⟫) (mu.restrict Omega) ∧
      Integrable (fun x ↦ c x * W1p.value v x) (mu.restrict Omega) ∧
      Integrable (fun x ↦ W1p.value v x * ⟪e x, W1p.gradient v x⟫) (mu.restrict Omega) ∧
      Integrable (fun x ↦ c x * W1p.value v x * W1p.value v x) (mu.restrict Omega) := by
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hOmega
  set G := W1p.gradient v
  -- The exponents: `p ≥ 2`, and `c v` is integrable since `1/r + 1/t ≤ 1`.
  have hp2 : (2 : ℝ≥0∞) ≤ p := by
    rw [← ENNReal.inv_le_inv, ← hpt]
    exact le_self_add
  have : p.HolderTriple t 2 := ⟨hpt⟩
  have : r.HolderTriple t (r⁻¹ + t⁻¹)⁻¹ := ⟨by rw [inv_inv]⟩
  have : t.HolderTriple (r⁻¹ + t⁻¹)⁻¹ 1 := ⟨by rw [inv_inv, inv_one, ← hrt]; ring⟩
  have hσ : 1 ≤ (r⁻¹ + t⁻¹)⁻¹ := by
    rw [ENNReal.one_le_inv, ← hrt]
    exact le_self_add
  refine ⟨(he.mono_exponent hp2).integrable_inner_of_holderConjugate (Lp.memLp G),
    memLp_one_iff_integrable.1 ((hc.fun_mul hvt).mono_exponent hσ), ?_, ?_⟩
  · exact (he.integrable_norm_mul_norm_mul_norm (r := 2) (s := 2) (Lp.memLp G) hvt).mono'
      (hvt.aestronglyMeasurable.mul (he.aestronglyMeasurable.inner (Lp.aestronglyMeasurable G)))
      (ae_of_all _ fun x ↦ norm_mul_inner_le _ _ _)
  · exact (hc.integrable_norm_mul_norm_mul_norm (s := (r⁻¹ + t⁻¹)⁻¹) hvt hvt).mono'
      ((hc.aestronglyMeasurable.mul hvt.aestronglyMeasurable).mul hvt.aestronglyMeasurable)
      (ae_of_all _ fun x ↦ by rw [norm_mul, norm_mul, mul_assoc])

omit [DecidableEq ι] in
/-- **The lower-order terms tested against a truncation.** Let `l ≥ 0`, let `w = (u - l)⁺` lie in
`Lᵗ(Ω)` on a set `Ω` of finite measure, and let `e ∈ Lᵖ` and `c ∈ Lʳ` with `1/p + 1/t = 1/2` and
`1/r + 2/t = 1`. Since `u = w + l` above the level and `w`, `∇w` vanish below it, the
lower-order terms of the weak form of `u` tested against `w` are those of `w` tested against
itself plus `l` times the sign condition tested against `w`:

`∫ u ⟪e, ∇w⟫ + ∫ ⟪b, ∇u⟫ w + ∫ c u w = ∫ w ⟪e, ∇w⟫ + ∫ ⟪b, ∇w⟫ w + ∫ c w² + l ∫ (c w + ⟪e, ∇w⟫)`.
-/
private theorem integral_lowerOrder_posPartAbove_eq (hOmega : mu Omega ≠ ∞)
    {p r t : ℝ≥0∞} (hpt : p⁻¹ + t⁻¹ = 2⁻¹) (hrt : r⁻¹ + t⁻¹ + t⁻¹ = 1)
    (he : MemLp e p (mu.restrict Omega)) (hc : MemLp c r (mu.restrict Omega)) {l : ℝ}
    (hl : 0 ≤ l) (u : W1p mu Omega 2)
    (hwt : MemLp (W1p.value (W1p.posPartAbove (by norm_num) hl u)) t (mu.restrict Omega)) :
    ∫ x in Omega, W1p.value u x *
          ⟪e x, W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x⟫ ∂mu +
        ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ *
          W1p.value (W1p.posPartAbove (by norm_num) hl u) x ∂mu +
        ∫ x in Omega, c x * W1p.value u x * W1p.value (W1p.posPartAbove (by norm_num) hl u) x ∂mu =
      ∫ x in Omega, W1p.value (W1p.posPartAbove (by norm_num) hl u) x *
          ⟪e x, W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x⟫ ∂mu +
        ∫ x in Omega, ⟪b x, W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x⟫ *
          W1p.value (W1p.posPartAbove (by norm_num) hl u) x ∂mu +
        ∫ x in Omega, c x * W1p.value (W1p.posPartAbove (by norm_num) hl u) x *
          W1p.value (W1p.posPartAbove (by norm_num) hl u) x ∂mu +
        l * ∫ x in Omega, c x * W1p.value (W1p.posPartAbove (by norm_num) hl u) x +
          ⟪e x, W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x⟫ ∂mu := by
  set w := W1p.posPartAbove (by norm_num) hl u
  obtain ⟨hint_e, hint_cw, hint_ew, hint_cww⟩ := integrable_lowerOrder hOmega hpt hrt he hc hwt
  -- Above the level `u = w + l`, below it `w` and `∇w` vanish.
  have hcases : ∀ᵐ x ∂mu.restrict Omega,
      (W1p.value u x = W1p.value w x + l ∧ W1p.gradient w x = W1p.gradient u x) ∨
        (W1p.value w x = 0 ∧ W1p.gradient w x = 0) := W1p.ae_posPartAbove_cases (by norm_num) hl u
  have hsplit_e : ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient w x⟫ ∂mu =
      ∫ x in Omega, W1p.value w x * ⟪e x, W1p.gradient w x⟫ ∂mu +
        l * ∫ x in Omega, ⟪e x, W1p.gradient w x⟫ ∂mu := by
    rw [← integral_const_mul, ← integral_add hint_ew (hint_e.const_mul l)]
    refine integral_congr_ae (hcases.mono fun x hx ↦ ?_)
    rcases hx with ⟨hv, -⟩ | ⟨-, hg⟩
    · simp only [hv]
      ring
    · simp [hg]
  have hsplit_c : ∫ x in Omega, c x * W1p.value u x * W1p.value w x ∂mu =
      ∫ x in Omega, c x * W1p.value w x * W1p.value w x ∂mu +
        l * ∫ x in Omega, c x * W1p.value w x ∂mu := by
    rw [← integral_const_mul, ← integral_add hint_cww (hint_cw.const_mul l)]
    refine integral_congr_ae (hcases.mono fun x hx ↦ ?_)
    rcases hx with ⟨hv, -⟩ | ⟨hv, -⟩
    · simp only [hv]
      ring
    · simp [hv]
  rw [hsplit_e, W1p.integral_inner_gradient_mul_value_posPartAbove (by norm_num) hl u b, hsplit_c,
    integral_add hint_cw hint_e]
  ring

/-- **The energy inequality of a truncation with small lower-order coefficients.** Let `u` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u ≤ g + ∂ᵢFⁱ` with `(u - k)⁺ ∈ H¹₀(Ω)`, under
the sign condition, with `b, e ∈ Lᵖ`, `c ∈ Lʳ` and a Sobolev inequality `‖v‖_t ≤ S ‖∇v‖₂`, where
`1/p + 1/t = 1/2` and `1/r + 2/t = 1`. If `(‖b‖_p + ‖e‖_p) S + ‖c‖_r S² ≤ λ/2`, then at every level
`l ≥ k` the truncation `w = (u - l)⁺` satisfies `λ/2 ‖∇w‖₂² ≤ ∫ g w - ∫ ⟪F, ∇w⟫`. -/
private theorem half_mul_norm_gradient_posPartAbove_sq_le_of_small_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hOmega : mu Omega ≠ ∞)
    {p r t : ℝ≥0∞} (hpt : p⁻¹ + t⁻¹ = 2⁻¹) (hrt : r⁻¹ + t⁻¹ + t⁻¹ = 1) {S : ℝ≥0}
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) t (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    (hb : MemLp b p (mu.restrict Omega)) (he : MemLp e p (mu.restrict Omega))
    (hc : MemLp c r (mu.restrict Omega))
    (hsmall : ((eLpNorm b p (mu.restrict Omega)).toReal +
        (eLpNorm e p (mu.restrict Omega)).toReal) * S +
          (eLpNorm c r (mu.restrict Omega)).toReal * S ^ 2 ≤ lam / 2)
    (hsign : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu)
    {g : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u : W1p mu Omega 2}
    (hu : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (φ : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu +
            ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value (φ : W1p mu Omega 2) x ∂mu +
            ∫ x in Omega, c x * W1p.value u x * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤
          ∫ x in Omega, g x * W1p.value (φ : W1p mu Omega 2) x ∂mu -
            ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l : ℝ} (hkl : k ≤ l) :
    lam / 2 * ‖W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)‖ ^ 2 ≤
      ∫ x in Omega, g x * W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x ∂mu -
        ∫ x in Omega, ⟪F x, W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x⟫
          ∂mu := by
  have hl : 0 ≤ l := hk.trans hkl
  set w := W1p.posPartAbove (by norm_num) hl u
  have hw0 : w ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  have hSw := hS w hw0
  have hwt := W1p.memLp_value_of_eLpNorm_le hSw
  -- Ellipticity: `λ ‖∇w‖₂² ≤ a(w, w) ≤ a(u, w)`.
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha aestronglyMeasurable_zero
    aestronglyMeasurable_zero (fun x hx eta xi ↦ h.upper_bound hx eta xi) (beta := 0)
    (fun x _ ↦ by simp) (gamma := 0) fun x _ ↦ by simp
  have hell : lam * ‖W1p.gradient w‖ ^ 2 ≤ energyFormH1 a 0 0 u w := by
    have h₁ := mul_norm_gradient_sq_sub_le_energyFormH1_self h hcoeff (beta := 0)
      (fun x _ ↦ by simp) (fun x _ ↦ le_rfl) w
    have h₂ := energyFormH1_posPartAbove_self_le hcoeff (ae_of_all _ fun _ ↦ le_refl (0 : ℝ))
      hl u
    simp only [zero_mul, sub_zero] at h₁
    exact h₁.trans h₂
  -- The lower-order terms: those of `w`, absorbed, and `l` times the sign condition.
  have hsplit := integral_lowerOrder_posPartAbove_eq (b := b) hOmega hpt hrt he hc hl u hwt
  have habsorb := neg_integral_lowerOrder_le hpt hrt hSw hb he hc
  have hsign_w := hsign ⟨w, hw0⟩ (W1p.value_posPartAbove_nonneg_ae (by norm_num) hl u)
  have htest := hu ⟨w, hw0⟩ (W1p.value_posPartAbove_nonneg_ae (by norm_num) hl u)
  simp only at htest hsign_w
  nlinarith [mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖W1p.gradient w‖),
    mul_nonneg hl hsign_w]

/-- The exponents of the scale-invariant bounds: for `q > 2` and `1/s = 1/2 - 1/q`, the relations
`1/q + 1/s = 1/2` and `2/q + 2/s = 1` hold in `ℝ≥0∞`. -/
private theorem inv_add_inv_eq_of_inv_eq_sub {q s : ℝ≥0} (hq : 2 < (q : ℝ))
    (hs : (s : ℝ)⁻¹ = 2⁻¹ - (q : ℝ)⁻¹) :
    (q : ℝ≥0∞)⁻¹ + (s : ℝ≥0∞)⁻¹ = 2⁻¹ ∧
      ((q / 2 : ℝ≥0) : ℝ≥0∞)⁻¹ + (s : ℝ≥0∞)⁻¹ + (s : ℝ≥0∞)⁻¹ = 1 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    norm_num at hq
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := inv_strictAnti₀ two_pos hq
    simp only [NNReal.coe_zero, inv_zero] at hs
    linarith
  -- Both identities are checked in `ℝ`, where they follow from `hs`.
  constructor
  · rw [← ENNReal.toReal_eq_toReal_iff' (by simp [hq0, hs0]) (by simp)]
    simp [ENNReal.toReal_add, hq0, hs0, hs]
  · rw [← ENNReal.toReal_eq_toReal_iff' (by simp [hq0, hs0]) (by simp)]
    simp [ENNReal.toReal_add, hq0, hs0, hs]
    ring

/-- The scale-invariant smallness condition gives the smallness condition with the Sobolev
constant `K P`: if `B P + D P² ≤ λ / (2 (K + K²))`, then `B (K P) + D (K P)² ≤ λ / 2`. -/
private theorem add_mul_add_sq_mul_le_half {K B D P lam : ℝ} (hK : 0 < K) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hsmall : B * P + D * P ^ 2 ≤ (2 * (K + K ^ 2))⁻¹ * lam) :
    B * (K * P) + D * (K * P) ^ 2 ≤ lam / 2 := by
  calc B * (K * P) + D * (K * P) ^ 2 = K * (B * P) + K ^ 2 * (D * P ^ 2) := by ring
    _ ≤ (K + K ^ 2) * (B * P + D * P ^ 2) := by
        nlinarith [mul_nonneg hB hP, mul_nonneg hD (sq_nonneg P), sq_nonneg K]
    _ ≤ (K + K ^ 2) * ((2 * (K + K ^ 2))⁻¹ * lam) := by gcongr
    _ = lam / 2 := by field_simp

/-- **The weak maximum principle with data for small lower-order coefficients in `L^q`**
(Gilbarg–Trudinger, Theorem 8.16 and the remark that follows it; Rosales, Lemma 3.2). Let `n ≥ 1`
be the dimension and let `q > max(2, n)`. There are `η > 0` and `C > 0`, depending only on `n`,
`q` and the normalization of the additive Haar measure `mu`, with the following property. Let `Ω`
have finite measure, let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `b, e ∈ L^q(Ω; ℝⁿ)` and `c ∈ L^{q/2}(Ω)` satisfy the weak sign condition
`∫ c φ + ⟪e, ∇φ⟫ ≥ 0` for every nonnegative `φ ∈ H¹₀(Ω)` and the smallness condition

`(‖b‖_q + ‖e‖_q) |Ω| ^ (1/n - 1/q) + ‖c‖_{q/2} |Ω| ^ (2/n - 2/q) ≤ η λ`,

and let `g ∈ L^{q/2}(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`. If `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u ≤ g + ∂ᵢFⁱ` in `Ω`,

that is `∫ ⟪a ∇u, ∇φ⟫ + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ + ∫ c u φ ≤ ∫ g φ - ∫ ⟪F, ∇φ⟫` for every
nonnegative `φ ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω` for a level `k ≥ 0`, in the sense that
`(u - k)⁺ ∈ H¹₀(Ω)`, then almost everywhere in `Ω`

`u ≤ k + C (‖g‖_{q/2} |Ω| ^ (2/n - 2/q) + ‖F‖_q |Ω| ^ (1/n - 1/q)) / λ`.

The smallness condition and the bound are invariant under dilations of `Ω`. -/
theorem exists_ae_value_le_add_of_small_lowerOrder [Nonempty ι] {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {lam Lam : ℝ} {g : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k),
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp b q (mu.restrict Omega) → MemLp e q (mu.restrict Omega) →
      MemLp c (q / 2 : ℝ≥0) (mu.restrict Omega) →
      ((eLpNorm b q (mu.restrict Omega)).toReal + (eLpNorm e q (mu.restrict Omega)).toReal) *
          mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) +
        (eLpNorm c (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
          mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - 2 / (q : ℝ)) ≤ η * lam →
      (∀ φ : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
          0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
            ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu) →
      MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ φ : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (φ : W1p mu Omega 2) +
              ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu +
              ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value (φ : W1p mu Omega 2) x ∂mu +
              ∫ x in Omega, c x * W1p.value u x * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤
            ∫ x in Omega, g x * W1p.value (φ : W1p mu Omega 2) x ∂mu -
              ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
        k + C * (((eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
            mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - 2 / (q : ℝ)) +
          (eLpNorm F q (mu.restrict Omega)).toReal *
            mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹)) / lam) := by
  set n : ℕ := Fintype.card ι
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  have hqinv2 : (q : ℝ)⁻¹ < 2⁻¹ := inv_strictAnti₀ two_pos hq
  -- The Sobolev inequality at the exponent `s` with `1/q + 1/s = 1/2`, with constant
  -- `K |Ω| ^ (1/n - 1/q)`.
  obtain ⟨K, hK, hsob⟩ := exists_forall_eLpNorm_value_le_toNNReal_mul_measureReal_rpow (mu := mu)
    (inv_pos.2 hq0) ((inv_lt_inv₀ hq0 hn0).2 hqn) hqinv2
  obtain ⟨C₀, hC₀, hstamp⟩ :=
    exists_ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le (mu := mu) hq hqn
  set s : ℝ≥0 := Real.toNNReal (2⁻¹ - (q : ℝ)⁻¹)⁻¹
  have hs : (s : ℝ)⁻¹ = 2⁻¹ - (q : ℝ)⁻¹ := by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 (sub_pos.2 hqinv2).le), inv_inv]
  obtain ⟨hpt, hrt⟩ := inv_add_inv_eq_of_inv_eq_sub hq hs
  refine ⟨(2 * (K + K ^ 2))⁻¹, 2 * C₀, by positivity, by positivity,
    fun {Omega a b e c lam Lam g F u k} hk hOmega h ha hb he hc hsmall hsign hg hF hu hboundary
      ↦ ?_⟩
  have hlam := h.pos
  set m := mu.real (Omega : Set (EuclideanSpace ℝ ι))
  have hm : 0 ≤ m := measureReal_nonneg
  set S : ℝ≥0 := Real.toNNReal (K * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹))
  have hpow2 : (m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) ^ 2 = m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) := by
    rw [← Real.rpow_mul_natCast hm]
    ring_nf
  -- The smallness condition with the Sobolev constant `S = K |Ω| ^ (1/n - 1/q)`.
  have hsmallS : ((eLpNorm b q (mu.restrict Omega)).toReal +
      (eLpNorm e q (mu.restrict Omega)).toReal) * S +
        (eLpNorm c (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal * S ^ 2 ≤ lam / 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [← hpow2] at hsmall
    exact add_mul_add_sq_mul_le_half hK (by positivity) ENNReal.toReal_nonneg (by positivity)
      hsmall
  -- The energy inequality of the truncations, and Stampacchia's bound with `λ/2`.
  have hbound := hstamp hk hOmega (half_pos hlam) hg hF hboundary fun l hkl ↦
    half_mul_norm_gradient_posPartAbove_sq_le_of_small_lowerOrder h ha hOmega hpt hrt
      (hsob hOmega) hb he hc hsmallS hsign hu hk hboundary hkl
  filter_upwards [hbound] with x hx
  refine hx.trans_eq ?_
  rw [div_div_eq_mul_div]
  ring

omit [DecidableEq ι] in
/-- The weak form `∫ ⟪a ∇u, ∇φ⟫ + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ + ∫ c u φ` is odd in `u`. -/
private theorem weakForm_neg (u φ : W1p mu Omega 2) :
    energyFormH1 a 0 0 (-u) φ + ∫ x in Omega, W1p.value (-u) x * ⟪e x, W1p.gradient φ x⟫ ∂mu +
        ∫ x in Omega, ⟪b x, W1p.gradient (-u) x⟫ * W1p.value φ x ∂mu +
        ∫ x in Omega, c x * W1p.value (-u) x * W1p.value φ x ∂mu =
      -(energyFormH1 a 0 0 u φ + ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient φ x⟫ ∂mu +
        ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value φ x ∂mu +
        ∫ x in Omega, c x * W1p.value u x * W1p.value φ x ∂mu) := by
  have hv := W1p.value_neg_ae u
  have hg := W1p.gradient_neg_ae u
  have h₁ : ∫ x in Omega, W1p.value (-u) x * ⟪e x, W1p.gradient φ x⟫ ∂mu =
      -∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient φ x⟫ ∂mu := by
    rw [← integral_neg]
    exact integral_congr_ae (hv.mono fun x hx ↦ by
      dsimp only
      rw [hx, Pi.neg_apply]
      ring)
  have h₂ : ∫ x in Omega, ⟪b x, W1p.gradient (-u) x⟫ * W1p.value φ x ∂mu =
      -∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value φ x ∂mu := by
    rw [← integral_neg]
    exact integral_congr_ae (hg.mono fun x hx ↦ by
      dsimp only
      rw [hx, Pi.neg_apply, inner_neg_right]
      ring)
  have h₃ : ∫ x in Omega, c x * W1p.value (-u) x * W1p.value φ x ∂mu =
      -∫ x in Omega, c x * W1p.value u x * W1p.value φ x ∂mu := by
    rw [← integral_neg]
    exact integral_congr_ae (hv.mono fun x hx ↦ by
      dsimp only
      rw [hx, Pi.neg_apply]
      ring)
  rw [energyFormH1_neg_left, h₁, h₂, h₃]
  ring

/-- **The two-sided bound for weak solutions with small lower-order coefficients in `L^q`.** There
are constants `η, C > 0`, depending only on `n`, `q` and `mu`, such that under the hypotheses of
`TauCeti.PDE.exists_ae_value_le_add_of_small_lowerOrder` with these constants, a weak solution
`u ∈ H¹₀(Ω)` of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u = g + ∂ᵢFⁱ` in `Ω`, `u = 0` on `∂Ω`,

that is `∫ ⟪a ∇u, ∇φ⟫ + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ + ∫ c u φ = ∫ g φ - ∫ ⟪F, ∇φ⟫` for every
`φ ∈ H¹₀(Ω)`, satisfies almost everywhere in `Ω`

`|u| ≤ C (‖g‖_{q/2} |Ω| ^ (2/n - 2/q) + ‖F‖_q |Ω| ^ (1/n - 1/q)) / λ`.

The bound from below is the bound from above for `-u`, a weak solution with data `-g` and `-F`. -/
theorem exists_ae_abs_value_le_of_small_lowerOrder [Nonempty ι] {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {lam Lam : ℝ} {g : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2},
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp b q (mu.restrict Omega) → MemLp e q (mu.restrict Omega) →
      MemLp c (q / 2 : ℝ≥0) (mu.restrict Omega) →
      ((eLpNorm b q (mu.restrict Omega)).toReal + (eLpNorm e q (mu.restrict Omega)).toReal) *
          mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) +
        (eLpNorm c (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
          mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - 2 / (q : ℝ)) ≤ η * lam →
      (∀ φ : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
          0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
            ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu) →
      MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ φ : W1p0 mu Omega 2,
        energyFormH1 a 0 0 (u : W1p mu Omega 2) (φ : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value (u : W1p mu Omega 2) x *
              ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu +
            ∫ x in Omega, ⟪b x, W1p.gradient (u : W1p mu Omega 2) x⟫ *
              W1p.value (φ : W1p mu Omega 2) x ∂mu +
            ∫ x in Omega, c x * W1p.value (u : W1p mu Omega 2) x *
              W1p.value (φ : W1p mu Omega 2) x ∂mu =
          ∫ x in Omega, g x * W1p.value (φ : W1p mu Omega 2) x ∂mu -
            ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p mu Omega 2) x⟫ ∂mu) →
      ∀ᵐ x ∂mu.restrict Omega, |W1p.value (u : W1p mu Omega 2) x| ≤
        C * (((eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
            mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - 2 / (q : ℝ)) +
          (eLpNorm F q (mu.restrict Omega)).toReal *
            mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹)) / lam) := by
  obtain ⟨η, C, hη, hC, hmain⟩ := exists_ae_value_le_add_of_small_lowerOrder (mu := mu) hq hqn
  refine ⟨η, C, hη, hC, fun {Omega a b e c lam Lam g F u} hOmega h ha hb he hc hsmall hsign hg hF
    hsol ↦ ?_⟩
  -- The bound from above for `u`.
  have hup := hmain le_rfl hOmega h ha hb he hc hsmall hsign hg hF (fun φ _ ↦ (hsol φ).le)
    (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl u.property)
  -- The bound from above for `-u`, a weak solution with data `-g` and `-F`.
  have hlo := hmain (u := -(u : W1p mu Omega 2)) (g := fun x ↦ -g x) (F := fun x ↦ -F x) le_rfl
    hOmega h ha hb he hc hsmall hsign hg.neg hF.neg (fun φ _ ↦ by
      rw [weakForm_neg, hsol φ]
      simp only [neg_mul, integral_neg, inner_neg_left]
      linarith)
    (W1p.posPartAbove_mem_w1p0Submodule (by norm_num) le_rfl (-u).property)
  have hnorm_g : eLpNorm (fun x ↦ -g x) (q / 2 : ℝ≥0) (mu.restrict Omega) =
      eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega) := eLpNorm_neg _ _ _
  have hnorm_F : eLpNorm (fun x ↦ -F x) q (mu.restrict Omega) = eLpNorm F q (mu.restrict Omega) :=
    eLpNorm_neg _ _ _
  rw [hnorm_g, hnorm_F] at hlo
  simpa only [zero_add] using (W1p.ae_abs_value_le_iff subset_rfl).2 ⟨hup, hlo⟩

end TauCeti.PDE
