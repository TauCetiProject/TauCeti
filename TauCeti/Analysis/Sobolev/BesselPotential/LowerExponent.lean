/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.MatrixMultiplier
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.OrderInterpolation
import TauCeti.Data.ENNReal.Holder

/-!
# Schwartz multipliers lower the exponent of `H^{s,p}`

Let `E` be a finite-dimensional real inner product space and `H^{s,p} = H^{s,p}(E, F)` Mathlib's
Bessel-potential spaces. On `ℝⁿ` the spaces `H^{s,p}` for different exponents are not nested.
For `q < p` the function `(1 + |x|²)^(-a/2)` with `n / p < a ≤ n / q` lies in `Lᵖ` but not in
`L^q`, since it decays too slowly at infinity, while a singularity `|x|^(-a)` near `0` with
`n / p ≤ a < n / q` lies in `L^q` but not in `Lᵖ` near `0`. Only the first obstruction concerns
decay, and it disappears after multiplication by a decaying function. This file proves the
corresponding multiplier statement: for a Schwartz function `φ` and exponents `1 < q ≤ p < ∞`,
multiplication by `φ` maps `H^{s,p}` into `H^{s,q}`, for every real order `s`
(`TemperedDistribution.MemSobolev.smulLeftCLM_schwartzMap_of_le`), and so defines a bounded operator
`H^{s,p}(E, F) → H^{s,q}(E, F)` (`BesselPotentialSpace.smulLeftCLMOfLE`). For `q = p` this is the
multiplication `BesselPotentialSpace.smulLeftCLMOfOneLt` on `H^{s,p}`
(`BesselPotentialSpace.smulLeftCLMOfLE_self`). In particular, an element of `H^{s,p}` that is fixed
by multiplication by a Schwartz function `φ`, for instance one supported in a compact set on a
neighbourhood of which `φ = 1`, lies in `H^{s,q}`
(`TemperedDistribution.MemSobolev.of_smulLeftCLM_schwartzMap_eq`). This is the inclusion
`H^{s,p} ⊆ H^{s,q}` for a common compact support.

## The argument

* **Order `0`.** `H^{0,p} = Lᵖ`, and a Schwartz function lies in `Lʳ` for the exponent `r` with
  `1 / q = 1 / r + 1 / p`, so Hölder's inequality (`MeasureTheory.MemLp.smul`) puts `φ u` in
  `L^q` for `u ∈ Lᵖ`.
* **Positive integer orders.** A distribution lies in `H^{k+1,p}` exactly when it lies in `Lᵖ`
  and its directional derivatives lie in `H^{k,p}`
  (`TemperedDistribution.memSobolev_natCast_add_one_iff`).
  By the Leibniz rule `∂_v (φ u) = (∂_v φ) u + φ ∂_v u`, and `∂_v φ` is again a Schwartz function,
  so induction on `k` applies, for all Schwartz multipliers at once.
* **Negative integer orders.** A distribution lies in `H^{-k-1,p}` exactly when it is
  `u + ∑ᵢ ∂ᵢ wᵢ` with `u` and `wᵢ` in `H^{-k,p}` (`TemperedDistribution.memSobolev_sub_one_iff`),
  and the Leibniz rule writes `φ (u + ∑ᵢ ∂ᵢ wᵢ)` as `φ u - ∑ᵢ (∂ᵢ φ) wᵢ + ∑ᵢ ∂ᵢ (φ wᵢ)`.
* **Real orders.** Complex interpolation between the integer orders `⌊s⌋` and `⌊s⌋ + 1`, on the
  source scale `H^{·,p}` and the target scale `H^{·,q}` at once
  (`TemperedDistribution.MemSobolev.map_of_forall_intCast`).

## Main results

* `TemperedDistribution.MemSobolev.smulLeftCLM_schwartzMap_of_le`: for `1 < q ≤ p < ∞` and a
  Schwartz function `φ`, if `f ∈ H^{s,p}` then `φ f ∈ H^{s,q}`, for every real `s`.
* `TemperedDistribution.MemSobolev.of_smulLeftCLM_schwartzMap_eq`: if moreover `φ f = f`, then
  `f ∈ H^{s,q}`.
* `BesselPotentialSpace.smulLeftCLMOfLE`: the bounded operator `H^{s,p}(E, F) → H^{s,q}(E, F)` of
  multiplication by `φ`, with `BesselPotentialSpace.toDistr_smulLeftCLMOfLE`.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8.2 (pointwise multipliers) and
  §3.3.2 (spaces of distributions with compact support on `ℝⁿ`).
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, Theorem 6.4.5 (7) (complex interpolation of the spaces `H^{s,p}`).
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv BesselPotentialSpace

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (1 ≤ q)]

/-- **Order `0`.** For exponents `q ≤ p` and a Schwartz function `φ`, if `f ∈ H^{0,p} = Lᵖ` then
`φ f ∈ H^{0,q} = L^q`, by Hölder's inequality with `φ ∈ Lʳ`, `1 / q = 1 / r + 1 / p`. -/
theorem MemSobolev.smulLeftCLM_schwartzMap_zero_of_le [NormedSpace ℂ F] [CompleteSpace F]
    (hqp : q ≤ p) (φ : 𝓢(E, ℂ))
    {f : 𝓢'(E, F)} (hf : MemSobolev 0 p f) :
    MemSobolev 0 q (TemperedDistribution.smulLeftCLM F (φ : E → ℂ) f) := by
  obtain ⟨f', rfl⟩ := memSobolev_zero_iff.1 hf
  -- The exponent `r` with `1 / r = 1 / q - 1 / p`.
  have := ENNReal.HolderTriple.of_le hqp
  have hmem : MemLp (fun x ↦ φ x • f' x) q volume :=
    (φ.memLp (q⁻¹ - p⁻¹)⁻¹).smul (Lp.memLp f')
  refine memSobolev_zero_iff.2 ⟨hmem.toLp _, ?_⟩
  exact ((Lp.toTemperedDistribution_eq_smulLeftCLM_iff φ.hasTemperateGrowth _ f').2
    hmem.coeFn_toLp).symm

variable [InnerProductSpace ℂ F] [CompleteSpace F]
  (hp : 1 < p) (hp_top : p ≠ ∞) (hq : 1 < q) (hq_top : q ≠ ∞) (hqp : q ≤ p)
include hp hp_top hq hq_top hqp

/-- **Positive integer orders.** For `1 < q ≤ p < ∞` and a Schwartz function `φ`, if
`f ∈ H^{k,p}` then `φ f ∈ H^{k,q}`, for every natural number `k`. -/
private theorem MemSobolev.smulLeftCLM_schwartzMap_natCast_of_le {k : ℕ} (φ : 𝓢(E, ℂ))
    {f : 𝓢'(E, F)} (hf : MemSobolev k p f) :
    MemSobolev k q (TemperedDistribution.smulLeftCLM F (φ : E → ℂ) f) := by
  induction k generalizing φ f with
  | zero =>
    rw [Nat.cast_zero] at hf ⊢
    exact hf.smulLeftCLM_schwartzMap_zero_of_le hqp φ
  | succ k ih =>
    rw [Nat.cast_succ] at hf ⊢
    have hf' := (memSobolev_natCast_add_one_iff hp hp_top).1 hf
    refine (memSobolev_natCast_add_one_iff hq hq_top).2
      ⟨hf'.1.smulLeftCLM_schwartzMap_zero_of_le hqp φ, fun v ↦ ?_⟩
    -- `∂_v (φ f) = (∂_v φ) f + φ ∂_v f`, and `∂_v φ` is again a Schwartz function.
    rw [lineDerivOp_smulLeftCLM_schwartzMap]
    exact (ih (∂_{v} φ) (hf.mono_of_one_lt hp hp_top (by linarith))).add (ih φ (hf'.2 v))

/-- **Negative integer orders.** For `1 < q ≤ p < ∞` and a Schwartz function `φ`, if
`f ∈ H^{-k,p}` then `φ f ∈ H^{-k,q}`, for every natural number `k`. -/
private theorem MemSobolev.smulLeftCLM_schwartzMap_neg_natCast_of_le {k : ℕ} (φ : 𝓢(E, ℂ))
    {f : 𝓢'(E, F)} (hf : MemSobolev (-k) p f) :
    MemSobolev (-k) q (TemperedDistribution.smulLeftCLM F (φ : E → ℂ) f) := by
  induction k generalizing φ f with
  | zero =>
    rw [Nat.cast_zero, neg_zero] at hf ⊢
    exact hf.smulLeftCLM_schwartzMap_zero_of_le hqp φ
  | succ k ih =>
    have hk : -((k + 1 : ℕ) : ℝ) = -k - 1 := by push_cast; ring
    rw [hk] at hf ⊢
    set b := stdOrthonormalBasis ℝ E
    -- Write `f = u + ∑ᵢ ∂ᵢ wᵢ` with `u` and `wᵢ` in `H^{-k,p}`. Then
    -- `φ f = φ u - ∑ᵢ (∂ᵢ φ) wᵢ + ∑ᵢ ∂ᵢ (φ wᵢ)`, each of whose terms lies in `H^{-k-1,q}`.
    obtain ⟨u, w, hu, hw, rfl⟩ := (memSobolev_sub_one_iff hp hp_top b).1 hf
    refine (memSobolev_sub_one_iff hq hq_top b).2
      ⟨TemperedDistribution.smulLeftCLM F (φ : E → ℂ) u -
          ∑ i, TemperedDistribution.smulLeftCLM F ((∂_{b i} φ : 𝓢(E, ℂ)) : E → ℂ) (w i),
        fun i ↦ TemperedDistribution.smulLeftCLM F (φ : E → ℂ) (w i),
        (ih φ hu).sub (MemSobolev.sum fun i _ ↦ ih _ (hw i)), fun i ↦ ih φ (hw i), ?_⟩
    simp only [map_add, map_sum, lineDerivOp_smulLeftCLM_schwartzMap]
    rw [Finset.sum_add_distrib]
    abel

omit hp hq_top in
/-- **Schwartz multipliers lower the exponent of `H^{s,p}`.** Let `1 < q ≤ p < ∞` and let `φ` be
a Schwartz function. If a tempered distribution `f` lies in `H^{s,p}`, then `φ f` lies in
`H^{s,q}`, for every real order `s`. For `q = p` this is
`TemperedDistribution.MemSobolev.smulLeftCLM_schwartzMap`. -/
theorem MemSobolev.smulLeftCLM_schwartzMap_of_le {s : ℝ} (φ : 𝓢(E, ℂ)) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) :
    MemSobolev s q (TemperedDistribution.smulLeftCLM F (φ : E → ℂ) f) := by
  have hp : 1 < p := hq.trans_le hqp
  have hq_top : q ≠ ∞ := ne_top_of_le_ne_top hp_top hqp
  refine hf.map_of_forall_intCast hp hp_top hq hq_top _ fun k _ g hg ↦ ?_
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact_mod_cast hg.smulLeftCLM_schwartzMap_natCast_of_le hp hp_top hq hq_top hqp φ
  · push_cast at hg ⊢
    exact hg.smulLeftCLM_schwartzMap_neg_natCast_of_le hp hp_top hq hq_top hqp φ

omit hp hq_top in
/-- **The inclusion `H^{s,p} ⊆ H^{s,q}` for a common compact support.** Let `1 < q ≤ p < ∞` and
let `φ` be a Schwartz function. A tempered distribution `f ∈ H^{s,p}` with `φ f = f`, for instance
one supported in a compact set on a neighbourhood of which `φ = 1`, lies in `H^{s,q}`. -/
theorem MemSobolev.of_smulLeftCLM_schwartzMap_eq {s : ℝ} {φ : 𝓢(E, ℂ)} {f : 𝓢'(E, F)}
    (hφf : TemperedDistribution.smulLeftCLM F (φ : E → ℂ) f = f) (hf : MemSobolev s p f) :
    MemSobolev s q f :=
  hφf ▸ hf.smulLeftCLM_schwartzMap_of_le hp_top hq hqp φ

end TemperedDistribution

namespace BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {s : ℝ}

/-- **Multiplication by a Schwartz function from `H^{s,p}` to `H^{s,q}`.** For `1 < q ≤ p < ∞` and
a Schwartz function `φ`, multiplication by `φ` is a bounded operator
`H^{s,p}(E, F) → H^{s,q}(E, F)`, for every real order `s`
(`TemperedDistribution.MemSobolev.smulLeftCLM_schwartzMap_of_le`). It acts on the underlying
tempered distributions by `TemperedDistribution.smulLeftCLM`
(`BesselPotentialSpace.toDistr_smulLeftCLMOfLE`), and for `q = p` it is
`BesselPotentialSpace.smulLeftCLMOfOneLt` (`BesselPotentialSpace.smulLeftCLMOfLE_self`). -/
def smulLeftCLMOfLE (hq : 1 < q) (hp_top : p ≠ ∞) (hqp : q ≤ p) (φ : 𝓢(E, ℂ)) :
    H^{s, p}(E, F) →L[ℂ] H^{s, q}(E, F) :=
  mapCLM (TemperedDistribution.smulLeftCLM F (φ : E → ℂ)) fun u ↦
    u.memSobolev_toDistr.smulLeftCLM_schwartzMap_of_le hp_top hq hqp φ

@[simp]
theorem toDistr_smulLeftCLMOfLE (hq : 1 < q) (hp_top : p ≠ ∞) (hqp : q ≤ p) (φ : 𝓢(E, ℂ))
    (u : H^{s, p}(E, F)) :
    (smulLeftCLMOfLE hq hp_top hqp φ u).toDistr =
      TemperedDistribution.smulLeftCLM F (φ : E → ℂ) u.toDistr :=
  toDistr_mapCLM _ _ u

/-- For `q = p`, `BesselPotentialSpace.smulLeftCLMOfLE` is the multiplication
`BesselPotentialSpace.smulLeftCLMOfOneLt` on `H^{s,p}`. -/
@[simp]
theorem smulLeftCLMOfLE_self (hp : 1 < p) (hp_top : p ≠ ∞) (φ : 𝓢(E, ℂ)) :
    (smulLeftCLMOfLE hp hp_top le_rfl φ : H^{s, p}(E, F) →L[ℂ] H^{s, p}(E, F)) =
      smulLeftCLMOfOneLt hp hp_top φ := by
  ext1 u
  exact ext (by simp)

end BesselPotentialSpace
