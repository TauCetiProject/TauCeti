/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.EllipticRegularity.Basic
public import TauCeti.Analysis.Pseudodifferential.BesovSpace
public import TauCeti.Analysis.Holder.Zygmund
import TauCeti.Analysis.Pseudodifferential.Smoothing
import TauCeti.Analysis.Sobolev.BesselPotential.Besov

/-!
# Interior elliptic regularity on Besov and Hölder–Zygmund spaces

Let `a` be a scalar symbol of order `m` on `ℝⁿ`, elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove`), let `ψ` be a compactly supported Schwartz function, and let
`c` be a symbol with compact spatial support that agrees with `a` near `tsupport ψ`, for instance
`χ(x) a(x, ξ)` for a cutoff `χ` equal to `1` near `tsupport ψ`. This file proves that `Op(c)`
gains back on the Besov scale `B^s_{p,q}`, near `tsupport ψ`, the `m` derivatives it takes away,
for every real `s` and all `1 ≤ p, q ≤ ∞`, on arbitrary tempered distributions:

* `TauCeti.Symbol.IsEllipticAbove.memBesov_smulLeftCLM_of_memBesov_quantizeTempered`: **interior
  elliptic regularity.** If `T` is a tempered distribution with `Op(c) T ∈ B^{s - m}_{p,q}`, then
  `ψ T ∈ B^s_{p,q}`. No a priori regularity of `T` is assumed.
* `TauCeti.Symbol.IsEllipticAbove.exists_norm_le_of_toDistr_eq_smulLeftCLM`: **the interior
  estimate** `‖ψ u‖_{B^s_{p,q}} ≤ C (‖Op(c) u‖_{B^{s - m}_{p,q}} + ‖u‖_{B^r_{p,q}})` for
  `u ∈ B^s_{p,q}` and every `r ≤ s`, with `C` independent of `u`.
* `TauCeti.Symbol.IsEllipticAbove.exists_smulLeftCLM_eq_toLpTop`: **the Schauder regularity of
  elliptic operators.** For `0 < α < 1` and natural numbers `k` and `l` with `k + m = l`, if
  `Op(c) T` is a bounded `C^k` function with bounded derivatives through order `k` and `α`-Hölder
  `k`-th derivative (`TauCeti.CkHolderSpace k α`), then `ψ T` is such a function of class
  `C^{l,α}`.

For `p = q = ∞` the Besov spaces are the Hölder–Zygmund spaces `𝒞^s = B^s_{∞,∞}`, where operators
of order `0` need not be bounded on `L^∞`, and at non-integer order `k + α` they are the bounded
Hölder spaces (`TauCeti.BesovSpace.ckHolderSpaceEquiv`). This is how the Schauder statement
follows from the Besov one. Since `Op(c) T` vanishes at positions outside the spatial support of
`c`, the hypothesis of the Schauder statement only concerns `Op(c) T` on a compact set.

## The argument

The local parametrix
(`TauCeti.Symbol.IsEllipticAbove.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add`) is a
symbol `b` of order `-m` with compact spatial support such that

`Op(b) Op(c) T = ψ T + Op(r) T`

for every tempered distribution `T`, with a smoothing symbol `r` of compact spatial support. The
operator `Op(b)` maps `B^{s - m}_{p,q}` into `B^s_{p,q}`
(`TemperedDistribution.MemBesov.quantizeTempered`). The smoothing term `Op(r) T` lies in every
Besov space (`TauCeti.Symbol.IsSmoothing.memBesov_quantizeTempered`), since it is a Schwartz
function (`TauCeti.Symbol.IsSmoothing.exists_hasCompactSupport_quantizeTempered_eq`) and Schwartz
functions lie in every Besov space (`SchwartzMap.memBesov`). For the estimate, the smoothing
symbol has every real order, so its quantization is bounded from `B^r_{p,q}` to `B^s_{p,q}` for
every `r` (`TauCeti.Symbol.quantizeBesov`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (3.32)–(3.34) (the Hölder–Zygmund mapping) and (4.6)–(4.11) (elliptic regularity
  by the parametrix).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap Topology ENNReal NNReal ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {φ : ContDiffBump (0 : CoordinateSpace n)}

/-! ### Smoothing operators -/

section Smoothing

variable {r : Symbol n ℂ ℂ m}

/-- **Smoothing operators on Besov spaces.** A smoothing symbol `r` with compact spatial support
maps every tempered distribution `T`, of any order and growth, into every Besov space
`B^s_{p,q}`, `q ≠ 0`. -/
theorem IsSmoothing.memBesov_quantizeTempered (hsm : r.IsSmoothing)
    (hr : r.HasCompactSpatialSupport) (T : 𝓢'(CoordinateSpace n, ℂ))
    (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] {q : ℝ≥0∞}
    (hq : q ≠ 0) : (quantizeTempered ℂ r hr.isUniform T).MemBesov φ s p q := by
  obtain ⟨f, -, hf⟩ := hsm.exists_hasCompactSupport_quantizeTempered_eq hr T
  exact hf ▸ f.memBesov φ s p hq

end Smoothing

/-! ### Interior regularity -/

section Regularity

variable {a c : Symbol n ℂ ℂ m} {R : ℝ} {ψ : 𝓢(CoordinateSpace n, ℂ)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Interior elliptic regularity on Besov spaces.** Let `a` be a scalar symbol elliptic of order
`m`, let `ψ` be a compactly supported Schwartz function, and let `c` be a symbol with compact
spatial support that agrees with `a` on a neighbourhood of `tsupport ψ`. If
`Op(c) T ∈ B^{s - m}_{p,q}` for a tempered distribution `T`, then `ψ T ∈ B^s_{p,q}`. For
`p = q = ∞` this is regularity on the Hölder–Zygmund scale `𝒞^s`. -/
theorem IsEllipticAbove.memBesov_smulLeftCLM_of_memBesov_quantizeTempered
    (ha : a.IsEllipticAbove R) (hc : c.HasCompactSpatialSupport) (hψ : HasCompactSupport ψ)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    {s : ℝ} {T : 𝓢'(CoordinateSpace n, ℂ)}
    (hT : (quantizeTempered ℂ c hc.isUniform T).MemBesov φ (s - m) p q) :
    (smulLeftCLM ℂ ψ T).MemBesov φ s p q := by
  obtain ⟨b, hb, r, hr, hrS, h⟩ :=
    ha.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add ℂ hc hψ hca
  have h₁ := hT.quantizeTempered hb.isUniform
  rw [h, sub_neg_eq_add, sub_add_cancel] at h₁
  convert h₁.sub (hrS.memBesov_quantizeTempered hr T φ s p (one_pos.trans_le Fact.out).ne')
    using 1
  exact (add_sub_cancel_right _ _).symm

/-- **The interior elliptic estimate on Besov spaces.** Let `a` be a scalar symbol elliptic of
order `m`, let `ψ` be a compactly supported Schwartz function, and let `c` be a symbol with compact
spatial support that agrees with `a` on a neighbourhood of `tsupport ψ`. For all real `s` and
`r ≤ s` there is a constant `C` with

`‖ψ u‖_{B^s_{p,q}} ≤ C (‖Op(c) u‖_{B^{s - m}_{p,q}} + ‖u‖_{B^r_{p,q}})`

for every `u ∈ B^s_{p,q}`, where `ψ u` is any element `v` of `B^s_{p,q}` with the tempered
distribution `ψ u`. -/
theorem IsEllipticAbove.exists_norm_le_of_toDistr_eq_smulLeftCLM (ha : a.IsEllipticAbove R)
    (hc : c.HasCompactSpatialSupport) (hψ : HasCompactSupport ψ)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    (s : ℝ) {r : ℝ} (hr : r ≤ s) :
    ∃ C, ∀ u v : BesovSpace ℂ φ s p q, v.toDistr = smulLeftCLM ℂ ψ u.toDistr →
      ‖v‖ ≤ C * (‖quantizeBesov ℂ φ p q c hc.isUniform (s' := s - m) rfl u‖ +
        ‖BesovSpace.inclusion ℂ φ p hr le_rfl u‖) := by
  obtain ⟨b, hb, e, he, heS, h⟩ :=
    ha.exists_isSmoothing_and_quantizeTempered_eq_smulLeftCLM_add ℂ hc hψ hca
  -- A representative `e'` of the smoothing symbol `e` of order `r - s`.
  obtain ⟨e', he'⟩ := isSmoothing_iff.1 heS (r - s)
  have he'c := he.of_coefficient_eq he'
  set Q := quantizeBesov ℂ φ p q b hb.isUniform (s := s - m) (s' := s) (by ring)
  set E := quantizeBesov ℂ φ p q e' he'c.isUniform (s := r) (s' := s) (by ring)
  refine ⟨max ‖Q‖ ‖E‖, fun u v hv ↦ ?_⟩
  -- `v = ψ u = Q (Op(c) u) - E u`.
  set c' := quantizeBesov ℂ φ p q c hc.isUniform (s' := s - m) rfl u
  set u' := BesovSpace.inclusion ℂ φ p hr le_rfl u
  have hvQE : v = Q c' - E u' := by
    refine BesovSpace.ext ?_
    rw [hv, BesovSpace.toDistr_sub, toDistr_quantizeBesov, toDistr_quantizeBesov,
      toDistr_quantizeBesov, BesovSpace.toDistr_inclusion, h u.toDistr,
      quantizeTempered_congr he.isUniform he'c.isUniform he'.symm, add_sub_cancel_right]
  calc ‖v‖ ≤ ‖Q c'‖ + ‖E u'‖ := hvQE ▸ norm_sub_le _ _
    _ ≤ ‖Q‖ * ‖c'‖ + ‖E‖ * ‖u'‖ := add_le_add (Q.le_opNorm c') (E.le_opNorm u')
    _ ≤ _ := by
      rw [mul_add]
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]

/-- **Schauder regularity of elliptic operators.** Let `a` be a scalar symbol elliptic of order
`m`, let `ψ` be a compactly supported Schwartz function, and let `c` be a symbol with compact
spatial support that agrees with `a` on a neighbourhood of `tsupport ψ`. Let `0 < α < 1` and let
`k` and `l` be natural numbers with `k + m = l`. If `Op(c) T` is (the tempered distribution of) a
bounded `C^k` function with bounded derivatives through order `k` and `α`-Hölder `k`-th
derivative, then so is `ψ T`, with `l` in place of `k`. -/
theorem IsEllipticAbove.exists_smulLeftCLM_eq_toLpTop (ha : a.IsEllipticAbove R)
    (hc : c.HasCompactSpatialSupport) (hψ : HasCompactSupport ψ)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) {k l : ℕ} (hkl : (k : ℝ) + m = l)
    {T : 𝓢'(CoordinateSpace n, ℂ)} (f : CkHolderSpace k α (CoordinateSpace n) ℂ)
    (hT : quantizeTempered ℂ c hc.isUniform T =
      BoundedContinuousFunction.toLpTop volume ℂ f.toBoundedContinuousFunction) :
    ∃ g : CkHolderSpace l α (CoordinateSpace n) ℂ, smulLeftCLM ℂ ψ T =
      BoundedContinuousFunction.toLpTop volume ℂ g.toBoundedContinuousFunction := by
  let φ : ContDiffBump (0 : CoordinateSpace n) := default
  have hf := (BesovSpace.ofCkHolderSpace ℂ φ k α f).memBesov_toDistr
  rw [BesovSpace.toDistr_ofCkHolderSpace, ← hT,
    show (k : ℝ) + α = l + α - m by linarith] at hf
  set u := (ha.memBesov_smulLeftCLM_of_memBesov_quantizeTempered hc hψ hca hf).toBesovSpace
  refine ⟨BesovSpace.toCkHolderSpace ℂ φ l hα0 hα1 u, ?_⟩
  rw [BesovSpace.toLpTop_toCkHolderSpace, MemBesov.toDistr_toBesovSpace]

end Regularity

end Symbol

end TauCeti
