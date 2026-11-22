/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
public import TauCeti.Analysis.Pseudodifferential.Lp.Tempered
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.FourierMultiplier
import TauCeti.Analysis.Pseudodifferential.Symbol.Dyadic
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.AlmostDiagonal
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Pseudodifferential operators on Besov spaces

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{αβ} ⟨ξ⟩^(m - |β|)` hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). This file proves that its quantization `Op(a)`, acting on tempered
distributions (`TauCeti.Symbol.quantizeTempered`), maps the inhomogeneous Besov space `B^s_{p,q}` to
`B^{s-m}_{p,q}` for every real `s` and all `1 ≤ p, q ≤ ∞`
(`TauCeti.Symbol.IsUniform.exists_toDistr_eq_quantizeTempered_and_norm_le`,
`TemperedDistribution.MemBesov.quantizeTempered`, `TauCeti.Symbol.quantizeBesov`). For
`p = q = ∞` this is the mapping `𝒞^s → 𝒞^{s-m}` of the Hölder–Zygmund scale, which at positive
non-integer orders `k + α` is the scale of the bounded Hölder spaces
(`TauCeti.BesovSpace.ckHolderSpaceEquiv`). Unlike the `Lᵖ` and `Hˢ` theories, no Calderón–Zygmund
or `L²` argument is involved, and the endpoints `p = 1, ∞` are included.

## The argument

The Bessel potential reduces the order to `0`: `Op(a) = Op(a ⟨ξ / 2π⟩ ^ (-m)) ∘ J^m`
(`TauCeti.Symbol.IsUniform.quantizeTempered_eq_comp_besselPotential`), and `J^m` is an
isomorphism `B^s_{p,q} ≃ B^{s-m}_{p,q}`. For a symbol of order `0`, `Op(a)` is almost diagonal
with respect to the Littlewood–Paley blocks `Δⱼ`: for every `N` there is `K` with

`‖Δⱼ Op(a) Δₖ u‖_p ≤ K 2^{-N |j - k|} ‖Δₖ u‖_p`,

and for `N > |s|` such an operator is bounded on `B^s_{p,q}`
(`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le`). The three ranges
of `j` are handled as follows.

* **`Op(a)` on a block.** A tempered distribution whose spectrum lies in the `k`-th dyadic annulus
  is fixed by the Fourier multiplier of a cutoff equal to `1` near that annulus, so
  `Op(a) Δₖ u = Op(b) Δₖ u` for the symbol `b(x, ξ)` cut off in the frequency to a fixed number of
  Littlewood–Paley pieces (`TauCeti.Symbol.IsUniform.quantizeTempered_fourierMultiplierCLM`). A
  piece at frequency `2^i` has an integrable kernel with row and column integrals bounded
  independently of `i`, by the integrated dyadic estimates
  `TauCeti.Symbol.IsUniform.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le`; so on the
  tempered distribution of an `Lᵖ` function the quantization of such a piece is an `Lᵖ` function,
  bounded by the row and column integrals of its kernel
  (`TauCeti.Symbol.IsUniform.exists_quantizeTempered_littlewoodPaleyPieceOfOrder_eq_and_norm_le`).
  So `‖Op(a) Δₖ u‖_p ≤ C ‖Δₖ u‖_p`, and `j = k` follows.
* **High output frequencies, `j > k`.** A derivative falls either on the input or on the position
  variable of the symbol, `∂_v Op(a) = Op(a) ∂_v + Op(∂_{x, v} a)`
  (`TauCeti.Symbol.lineDerivOp_quantizeTempered_eq_add`), and Bernstein's inequality bounds the
  derivatives of the block `Δₖ u` by `2^k`. So the derivatives of order `N` of `Op(a) Δₖ u` are
  `O(2^{kN} ‖Δₖ u‖_p)`, and the reverse Bernstein inequality on the `j`-th annulus gives
  `‖Δⱼ Op(a) Δₖ u‖_p = O(2^{(k - j) N} ‖Δₖ u‖_p)`.
* **Low output frequencies, `j < k`.** On the `k`-th annulus `Δₖ u = ∑ᵢ ∂ᵢ gᵢ` with
  `‖gᵢ‖_p = O(2^{-k} ‖Δₖ u‖_p)`, and the commutator `Op(a) ∂ᵢ = ∂ᵢ Op(a) - Op(∂_{x_i} a)` moves the
  derivative onto `Δⱼ`, where it costs `2^j`. Each repetition gains a factor `2^{j - k}`.

## Main declarations

* `TauCeti.Symbol.IsUniform.exists_toDistr_eq_quantizeTempered_and_norm_le`: the bound
  `‖Op(a) u‖_{B^{s-m}_{p,q}} ≤ C ‖u‖_{B^s_{p,q}}`.
* `TemperedDistribution.MemBesov.quantizeTempered`: `Op(a)` maps `B^s_{p,q}` into
  `B^{s-m}_{p,q}`.
* `TauCeti.Symbol.quantizeBesov`: `Op(a)` as a bounded operator `B^s_{p,q} → B^{s-m}_{p,q}`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3,
  (3.32)–(3.34) (the Hölder–Zygmund mapping of pseudodifferential operators).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8 (almost diagonal operators on
  Besov spaces).
-/

public section

noncomputable section

open MeasureTheory Complex Function
open scoped SchwartzMap ENNReal NNReal LineDeriv FourierTransform

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

section Dyadic

variable [CompleteSpace F]

/-! ### Blocks -/

open Distribution TemperedDistribution Metric

variable (φ : ContDiffBump (0 : CoordinateSpace n))

/-- The frequencies off the support of the `k`-th piece of the Littlewood–Paley partition of `φ`:
the complement of the closed ball of radius `φ.rOut` for `k = 0`, and for `k ≥ 1` the complement of
the annulus `2^{k-1} φ.rIn ≤ ‖ζ‖ ≤ 2^k φ.rOut`. -/
private def offSpectrum (k : ℕ) : Set (CoordinateSpace n) :=
  if k = 0 then (closedBall 0 φ.rOut)ᶜ
  else ball 0 (2 ^ k * φ.rIn / 2) ∪ (closedBall 0 (2 ^ k * φ.rOut))ᶜ

omit [CompleteSpace F] in
/-- The Fourier transform of `Δₖ u` vanishes off the spectrum of the `k`-th piece. -/
private theorem isVanishingOn_offSpectrum (k : ℕ) (u : 𝓢'(CoordinateSpace n, F)) :
    IsVanishingOn (𝓕 (littlewoodPaleyBlock F φ k u) : 𝓢'(CoordinateSpace n, F))
      (offSpectrum φ k) := by
  rcases k with _ | k
  · simpa [offSpectrum] using isVanishingOn_fourier_littlewoodPaleyBlock φ 0 u
  · have h := isVanishingOn_fourier_littlewoodPaleyBlock_succ φ k u
    rw [Set.compl_sdiff] at h
    simpa [offSpectrum, show 2 ^ (k + 1) * φ.rIn / 2 = 2 ^ k * φ.rIn by ring] using h

/-- **The enlarged cutoff is `1` near the spectrum of the `k`-th piece**, for a width depending
only on `φ`. -/
private theorem exists_tsupport_enlargedLittlewoodPaley_sub_one_subset :
    ∃ L : ℕ, ∀ k, tsupport (fun ζ ↦ ((φ.enlargedLittlewoodPaley L k ζ : ℝ) : ℂ) - 1) ⊆
      offSpectrum φ k := by
  obtain ⟨L, hL⟩ := φ.exists_tsupport_enlargedLittlewoodPaley_sub_one_subset
  refine ⟨L, fun k ↦ ?_⟩
  have h : (fun ζ ↦ ((φ.enlargedLittlewoodPaley L k ζ : ℝ) : ℂ) - 1) =
      ((↑) : ℝ → ℂ) ∘ fun ζ ↦ φ.enlargedLittlewoodPaley L k ζ - 1 := by
    ext ζ
    simp
  rw [h]
  refine (tsupport_comp_subset ofReal_zero _).trans ((hL k).trans ?_)
  rintro ζ (hζ | ⟨hk, hζ⟩)
  · rcases eq_or_ne k 0 with rfl | hk
    · simpa [offSpectrum] using hζ
    · simp only [offSpectrum, ite_eq_right hk]
      exact Or.inr hζ
  · simp only [offSpectrum, ite_eq_right hk]
    exact Or.inl (mem_ball_zero_iff.2 hζ)

/-- **Quantization of a block.** For a uniform symbol `a` of order `0` there is `C`, depending
only on `a` and `φ`, with the following property. For `1 ≤ p ≤ ∞`, if the Fourier transform of
`f ∈ Lᵖ` vanishes off the spectrum of the `k`-th Littlewood–Paley piece, then `Op(a) f` is an `Lᵖ`
function of norm at most `C ‖f‖_p`. -/
private theorem IsUniform.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
      (f : Lp F p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
        (offSpectrum φ k) →
      ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
        quantizeTempered F a ha f = v ∧ ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨L, hL⟩ := exists_tsupport_enlargedLittlewoodPaley_sub_one_subset φ
  -- Dilating `φ` by `2π` converts cutoffs in the frequency `ζ` of Mathlib's Fourier transform
  -- into cutoffs in the angular frequency `ξ = 2πζ` of the quantization.
  set ψ := φ.dilate Real.two_pi_pos
  obtain ⟨C, hC, hpiece⟩ :=
    ha.exists_quantizeTempered_littlewoodPaleyPieceOfOrder_eq_and_norm_le (F := F) ψ
  refine ⟨2 * L * C, by positivity, fun k {p} _ f hf ↦ ?_⟩
  set g : CoordinateSpace n → ℂ := fun ζ ↦ ((φ.enlargedLittlewoodPaley L k ζ : ℝ) : ℂ)
  have hg : g.HasTemperateGrowth := φ.hasTemperateGrowth_ofReal_enlargedLittlewoodPaley L k
  have hgf : fourierMultiplierCLM F g (f : 𝓢'(CoordinateSpace n, F)) = f :=
    fourierMultiplierCLM_eq_self_of_isVanishingOn hf hg (hL k)
  set s := Finset.Ico (k + 1 - L) (k + L)
  have hb (i : ℕ) := ha.littlewoodPaleyPieceOfOrder ψ i
  have hq : quantizeTempered F a ha (f : 𝓢'(CoordinateSpace n, F)) =
      ∑ i ∈ s, quantizeTempered F (a.littlewoodPaleyPieceOfOrder ψ i) (hb i) f := by
    conv_lhs => rw [← hgf]
    rw [ha.quantizeTempered_fourierMultiplierCLM (IsUniform.sum fun i _ ↦ hb i) hg ?_,
      quantizeTempered_sum hb s, sum_apply]
    intro x ξ
    simp only [coefficient_sum, Finset.sum_apply, coefficient_littlewoodPaleyPieceOfOrder,
      coefficient_littlewoodPaleyPiece, ContDiffBump.inhomogeneousLittlewoodPaley_dilate, g,
      ContDiffBump.enlargedLittlewoodPaley_apply, ← Finset.sum_smul, Complex.coe_smul, s, ψ]
  choose v hv hvn using fun i ↦ hpiece i f
  simp only [Real.rpow_zero, mul_one] at hvn
  refine ⟨∑ i ∈ s, v i, ?_, ?_⟩
  · rw [hq, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hv i
  · calc ‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, C * ‖f‖ := Finset.sum_le_sum fun i _ ↦ hvn i
      _ = s.card * (C * ‖f‖) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * L : ℕ) * (C * ‖f‖) := by
          gcongr
          rw [Nat.card_Ico]
          omega
      _ = 2 * L * C * ‖f‖ := by push_cast; ring

/-- **Blocks of the quantization of a block.** For a uniform symbol `a` of order `0` there is `C`
such that for `1 ≤ p ≤ ∞`, if the Fourier transform of `f ∈ Lᵖ` vanishes off the spectrum of the
`k`-th Littlewood–Paley piece, then every block `Δⱼ Op(a) f` is an `Lᵖ` function of norm at most
`C ‖f‖_p`. -/
private theorem
    IsUniform.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le_of_isVanishingOn
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
      (f : Lp F p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
        (offSpectrum φ k) →
      ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock F φ j (quantizeTempered F a ha f) = v ∧ ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₀, hC₀, hD⟩ := ha.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
  refine ⟨max CΔ 0 * C₀, by positivity, fun j k {p} _ f hf ↦ ?_⟩
  obtain ⟨v₀, hv₀, hv₀n⟩ := hD k f hf
  obtain ⟨v, hv, hvn⟩ := hΔ j v₀
  refine ⟨v, by rw [hv₀, hv], ?_⟩
  calc ‖v‖ ≤ CΔ * ‖v₀‖ := hvn
    _ ≤ max CΔ 0 * (C₀ * ‖f‖) := by gcongr; exact le_max_left _ _
    _ = _ := by rw [mul_assoc]

private theorem compl_closedBall_subset_offSpectrum (k : ℕ) :
    (closedBall (0 : CoordinateSpace n) (2 ^ k * φ.rOut))ᶜ ⊆ offSpectrum φ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [offSpectrum]
  · simp only [offSpectrum, ite_eq_right hk]
    exact Set.subset_union_right

/-- **Derivatives of the quantization of a block.** For a uniform symbol `a` of order `0` and
directions `w₁, …, w_M`, there is `C` such that for `1 ≤ p ≤ ∞`, if the Fourier transform of
`f ∈ Lᵖ` vanishes off the spectrum of the `k`-th Littlewood–Paley piece, then
`∂_{w₁} ⋯ ∂_{w_M} Op(a) f` is an `Lᵖ` function of norm at most `C 2^{kM} ‖f‖_p`. -/
private theorem IsUniform.exists_iteratedLineDerivOp_quantizeTempered_eq_and_norm_le (M : ℕ) :
    ∀ {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) (w : Fin M → CoordinateSpace n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
        (f : Lp F p (volume : Measure (CoordinateSpace n))),
        IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
          (offSpectrum φ k) →
        ∃ y : Lp F p (volume : Measure (CoordinateSpace n)),
          ∂^{w} (quantizeTempered F a ha f) = y ∧ ‖y‖ ≤ C * (2 ^ k) ^ M * ‖f‖ := by
  induction M with
  | zero =>
    intro a ha w
    obtain ⟨C, hC, h⟩ := ha.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
    refine ⟨C, hC, fun k {p} _ f hf ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := h k f hf
    exact ⟨v, by rw [LineDeriv.iteratedLineDerivOp_fin_zero, hv], by simpa using hvn⟩
  | succ M ih =>
    intro a ha w
    set v := w (Fin.last M)
    obtain ⟨C₁, hC₁, h₁⟩ := ih ha (Fin.init w)
    obtain ⟨C₂, hC₂, h₂⟩ := ih (ha.lineSpatialDeriv v) (Fin.init w)
    obtain ⟨CB, hCB, hB⟩ :=
      exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := CoordinateSpace n) (F := F)
    have hrOut := φ.rOut_pos
    refine ⟨C₁ * (CB * φ.rOut * ‖v‖) + C₂, by positivity, fun k {p} _ f hf ↦ ?_⟩
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
    -- `∂_v f` is again a block, smaller by `2^k`.
    obtain ⟨g, hg, hgn⟩ := hB (p := p) (R := 2 ^ k * φ.rOut) (by positivity) f
      (hf.mono (compl_closedBall_subset_offSpectrum φ k)) v
    have hgv : IsVanishingOn (𝓕 (g : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
        (offSpectrum φ k) := hg ▸ isVanishingOn_fourier_lineDerivOp hf v
    obtain ⟨y₁, hy₁, hy₁n⟩ := h₁ k g hgv
    obtain ⟨y₂, hy₂, hy₂n⟩ := h₂ k f hf
    refine ⟨y₁ + y₂, ?_, ?_⟩
    · rw [LineDeriv.iteratedLineDerivOp_succ_right, lineDerivOp_quantizeTempered_eq_add, hg,
        LineDeriv.iteratedLineDerivOp_add, hy₁, hy₂, Lp.toTemperedDistribution_add]
    · calc ‖y₁ + y₂‖ ≤ ‖y₁‖ + ‖y₂‖ := norm_add_le _ _
        _ ≤ C₁ * (2 ^ k) ^ M * (CB * (2 ^ k * φ.rOut) * ‖v‖ * ‖f‖) +
            C₂ * (2 ^ k) ^ M * ‖f‖ := add_le_add (hy₁n.trans (by gcongr)) hy₂n
        _ ≤ (C₁ * (CB * φ.rOut * ‖v‖) + C₂) * (2 ^ k) ^ (M + 1) * ‖f‖ := by
          have hM : 0 ≤ C₂ * (2 ^ k) ^ M * ‖f‖ := by positivity
          rw [pow_succ]
          nlinarith

/-- **High output frequencies.** For a uniform symbol `a` of order `0` and `M : ℕ` there is `C`
such that for `1 ≤ p ≤ ∞` and `k < j`, if the Fourier transform of `f ∈ Lᵖ` vanishes off the
spectrum of the `k`-th Littlewood–Paley piece, then `‖Δⱼ Op(a) f‖_p ≤ C (2^k / 2^j)^M ‖f‖_p`. -/
private theorem IsUniform.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le_of_lt
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {j k : ℕ}, k < j →
      ∀ f : Lp F p (volume : Measure (CoordinateSpace n)),
        IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
          (offSpectrum φ k) →
        ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
          littlewoodPaleyBlock F φ j (quantizeTempered F a ha f) = v ∧
            ‖v‖ ≤ C * ((2 : ℝ) ^ k / 2 ^ j) ^ M * ‖f‖ := by
  set b := stdOrthonormalBasis ℝ (CoordinateSpace n)
  obtain ⟨Cr, hCr, hrev⟩ :=
    exists_norm_littlewoodPaleyBlock_succ_le_of_iteratedLineDerivOp (F := F) φ M
  choose C hC hder using fun i : Fin M → Fin (Module.finrank ℝ (CoordinateSpace n)) ↦
    ha.exists_iteratedLineDerivOp_quantizeTempered_eq_and_norm_le (F := F) φ M (⇑b ∘ i)
  obtain ⟨C₀, -, hD⟩ := ha.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  have hCs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ hC i
  refine ⟨Cr * (∑ i, C i) * 2 ^ M, by positivity, fun {p} _ {j k} hkj f hf ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨v₀, hv₀, -⟩ := hD k f hf
  obtain ⟨w, hw, -⟩ := hΔ (j + 1) v₀
  have hwT : littlewoodPaleyBlock F φ (j + 1) (quantizeTempered F a ha f) = w := by
    rw [hv₀, hw]
  refine ⟨w, hwT, ?_⟩
  have hA (i : Fin M → Fin (Module.finrank ℝ (CoordinateSpace n))) :
      ∃ y : Lp F p (volume : Measure (CoordinateSpace n)),
        ∂^{⇑b ∘ i} (quantizeTempered F a ha f) = y ∧ ‖y‖ ≤ (∑ i, C i) * (2 ^ k) ^ M * ‖f‖ := by
    obtain ⟨y, hy, hyn⟩ := hder i k f hf
    have hCi : C i ≤ ∑ i, C i := Finset.single_le_sum (fun i _ ↦ hC i) (Finset.mem_univ i)
    exact ⟨y, hy, hyn.trans (by gcongr)⟩
  refine (hrev j (quantizeTempered F a ha f) w hwT hA).trans_eq ?_
  rw [div_pow, pow_succ, mul_pow]
  field_simp

private theorem offSpectrum_succ (k : ℕ) :
    offSpectrum φ (k + 1) = ball (0 : CoordinateSpace n) (2 ^ k * φ.rIn) ∪
      (closedBall 0 (2 * φ.rOut / φ.rIn * (2 ^ k * φ.rIn)))ᶜ := by
  rw [φ.two_mul_rOut_div_rIn_mul, offSpectrum, ite_eq_right k.succ_ne_zero,
    show 2 ^ (k + 1) * φ.rIn / 2 = 2 ^ k * φ.rIn by ring]

variable (F) in
/-- The bound `‖Δⱼ Op(a) f‖_p ≤ C (2^j / 2^k)^N ‖f‖_p` for every `1 ≤ p ≤ ∞`, every `j` and every
`f ∈ Lᵖ` whose Fourier transform vanishes off the spectrum of the `(k + 1)`-st Littlewood–Paley
piece. -/
private def LowFrequencyBound (a : Symbol n ℂ ℂ 0) (ha : a.IsUniform) (N : ℕ) (C : ℝ) : Prop :=
  ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ) (f : Lp F p (volume : Measure (CoordinateSpace n))),
    IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
      (offSpectrum φ (k + 1)) →
    ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
      littlewoodPaleyBlock F φ j (quantizeTempered F a ha f) = v ∧
        ‖v‖ ≤ C * ((2 : ℝ) ^ j / 2 ^ k) ^ N * ‖f‖

omit [CompleteSpace F] in
/-- The commutator `Op(a) ∂ᵢ = ∂ᵢ Op(a) - Op(∂_{x_i} a)` applied to a sum of derivatives, and
moved through the block `Δⱼ`. -/
private theorem littlewoodPaleyBlock_quantizeTempered_sum_lineDerivOp {a : Symbol n ℂ ℂ m}
    (ha : a.IsUniform) (j : ℕ) (g : Fin n → 𝓢'(CoordinateSpace n, F)) :
    littlewoodPaleyBlock F φ j
        (quantizeTempered F a ha (∑ i, ∂_{EuclideanSpace.basisFun (Fin n) ℝ i} (g i))) =
      ∑ i, (∂_{EuclideanSpace.basisFun (Fin n) ℝ i}
          (littlewoodPaleyBlock F φ j (quantizeTempered F a ha (g i))) -
        littlewoodPaleyBlock F φ j
          (quantizeTempered F (Symbol.spatialDeriv i a) (ha.spatialDeriv i) (g i))) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [EuclideanSpace.basisFun_apply,
    eq_sub_of_add_eq (lineDerivOp_quantizeTempered a ha i (g i)).symm, map_sub,
    littlewoodPaleyBlock_lineDerivOp]

/-- **The inductive step for low output frequencies.** Writing `f = ∑ᵢ ∂ᵢ gᵢ` with
`‖gᵢ‖_p = O(2^{-k} ‖f‖_p)`, the commutator `Op(a) ∂ᵢ = ∂ᵢ Op(a) - Op(∂_{x_i} a)` moves the
derivative onto the block `Δⱼ`, where it costs `2^j`: bounds of order `N` for `a` and its spatial
derivatives give a bound of order `N + 1` for `a`. -/
private theorem IsUniform.exists_lowFrequencyBound_succ {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform)
    {N : ℕ} {C : ℝ} (hC : 0 ≤ C) (h : LowFrequencyBound F φ a ha N C) {C' : Fin n → ℝ}
    (hC' : ∀ i, 0 ≤ C' i)
    (h' : ∀ i, LowFrequencyBound F φ (Symbol.spatialDeriv i a) (ha.spatialDeriv i) N (C' i)) :
    ∃ C'' : ℝ, LowFrequencyBound F φ a ha (N + 1) C'' := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  obtain ⟨c, -, hdec⟩ := b.exists_eq_sum_lineDerivOp_and_norm_le (F := F) (2 * φ.rOut / φ.rIn)
  obtain ⟨CB, hCB, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := CoordinateSpace n) (F := F)
  have hrIn := φ.rIn_pos
  have hrOut := φ.rOut_pos
  refine ⟨∑ i, (CB * φ.rOut * C + C' i) * (c / φ.rIn), fun {p} _ j k f hf ↦ ?_⟩
  obtain ⟨g, hfg, hg⟩ := hdec (by positivity : (0 : ℝ) < 2 ^ k * φ.rIn) f
    (by rw [← offSpectrum_succ]; exact hf)
  choose v hv hvn using fun i ↦ h j k (g i) (offSpectrum_succ φ k ▸ (hg i).1)
  choose z hz hzn using fun i ↦ h' i j k (g i) (offSpectrum_succ φ k ▸ (hg i).1)
  -- The blocks `v i = Δⱼ Op(a) gᵢ` have spectrum in the ball of radius `2^j φ.rOut`.
  choose y hy hyn using fun i ↦ hB (p := p) (by positivity : (0 : ℝ) < 2 ^ j * φ.rOut) (v i)
    (hv i ▸ isVanishingOn_fourier_littlewoodPaleyBlock φ j _) (b i)
  refine ⟨∑ i, (y i - z i), ?_, ?_⟩
  · rw [hfg, littlewoodPaleyBlock_quantizeTempered_sum_lineDerivOp, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hv, hy, hz, Lp.toTemperedDistribution_sub]
  set r : ℝ := 2 ^ j / 2 ^ k
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  have hterm (i : Fin n) : ‖y i - z i‖ ≤
      (CB * φ.rOut * C + C' i) * (c / φ.rIn) * r ^ (N + 1) * ‖f‖ := by
    have hb1 : ‖b i‖ = 1 := b.orthonormal.1 i
    have hgi := (hg i).2
    have hCi := hC' i
    calc ‖y i - z i‖ ≤ ‖y i‖ + ‖z i‖ := norm_sub_le _ _
      _ ≤ CB * (2 ^ j * φ.rOut) * ‖b i‖ * (C * r ^ N * ‖g i‖) + C' i * r ^ N * ‖g i‖ :=
          add_le_add ((hyn i).trans (by gcongr; exact hvn i)) (hzn i)
      _ = (CB * φ.rOut * C * 2 ^ j + C' i) * r ^ N * ‖g i‖ := by rw [hb1]; ring
      _ ≤ (CB * φ.rOut * C * 2 ^ j + C' i * 2 ^ j) * r ^ N * (c / (2 ^ k * φ.rIn) * ‖f‖) := by
          gcongr
          exact le_mul_of_one_le_right hCi hj
      _ = _ := by
          rw [show (2 : ℝ) ^ j = r * 2 ^ k by simp only [r]; field_simp, pow_succ]
          field_simp
  calc ‖∑ i, (y i - z i)‖ ≤ ∑ i, ‖y i - z i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (CB * φ.rOut * C + C' i) * (c / φ.rIn) * r ^ (N + 1) * ‖f‖ :=
        Finset.sum_le_sum fun i _ ↦ hterm i
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- **Low output frequencies.** For a uniform symbol `a` of order `0` and `N : ℕ` there is `C`
such that for `1 ≤ p ≤ ∞`, if the Fourier transform of `f ∈ Lᵖ` vanishes off the spectrum of the
`(k + 1)`-st Littlewood–Paley piece, then `‖Δⱼ Op(a) f‖_p ≤ C (2^j / 2^k)^N ‖f‖_p` for every `j`. -/
private theorem IsUniform.exists_lowFrequencyBound (N : ℕ) :
    ∀ {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform), ∃ C : ℝ, 0 ≤ C ∧ LowFrequencyBound F φ a ha N C := by
  induction N with
  | zero =>
    intro a ha
    obtain ⟨C, hC, h⟩ :=
      ha.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
    refine ⟨C, hC, fun {p} _ j k f hf ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := h j (k + 1) f hf
    exact ⟨v, hv, by rwa [pow_zero, mul_one]⟩
  | succ N ih =>
    intro a ha
    obtain ⟨C, hC, h⟩ := ih ha
    choose C' hC' h' using fun i ↦ ih (ha.spatialDeriv i)
    obtain ⟨C'', h''⟩ := ha.exists_lowFrequencyBound_succ φ hC h hC' h'
    refine ⟨max C'' 0, le_max_right _ _, fun {p} _ j k f hf ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := h'' j k f hf
    exact ⟨v, hv, hvn.trans (by gcongr; exact le_max_left _ _)⟩

/-- **Almost diagonality.** For a uniform symbol `a` of order `0` and `N : ℕ` there is `K` such
that for `1 ≤ p ≤ ∞` and every block `Δₖ u = f ∈ Lᵖ` of a tempered distribution, every block
`Δⱼ Op(a) f` is an `Lᵖ` function of norm at most `K 2^{-N |j - k|} ‖f‖_p`. -/
private theorem IsUniform.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ) (u : 𝓢'(CoordinateSpace n, F))
      (f : Lp F p (volume : Measure (CoordinateSpace n))), littlewoodPaleyBlock F φ k u = f →
      ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock F φ j (quantizeTempered F a ha f) = v ∧
          ‖v‖ ≤ K * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖f‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    ha.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le_of_lt (F := F) φ N
  obtain ⟨C₂, hC₂, h₂⟩ := ha.exists_lowFrequencyBound (F := F) φ N
  obtain ⟨C₀, hC₀, h₀⟩ :=
    ha.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
  have hrIn := φ.rIn_pos
  refine ⟨C₁ + C₂ * φ.rIn ^ N * (2 / φ.rIn) ^ N + C₀, by positivity,
    fun {p} _ j k u f hf ↦ ?_⟩
  refine exists_littlewoodPaleyBlock_eq_and_norm_le_of_block_le φ (quantizeTempered F a ha)
    hC₀ hC₁ (by positivity) (fun k u f hf ↦ h₀ k k f (hf ▸ isVanishingOn_offSpectrum φ k u))
    (fun hkj u f hf ↦ h₁ hkj f (hf ▸ isVanishingOn_offSpectrum φ _ u))
    (fun j k u f hf ↦ ?_) j k u f hf
  obtain ⟨v, hv, hvn⟩ := h₂ j k f (hf ▸ isVanishingOn_offSpectrum φ (k + 1) u)
  refine ⟨v, hv, hvn.trans_eq ?_⟩
  rw [div_pow, div_pow, mul_pow]
  field_simp

end Dyadic

/-! ### Mapping properties on Besov spaces -/

section Besov

open Distribution TemperedDistribution

variable [CompleteSpace F] {φ : ContDiffBump (0 : CoordinateSpace n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Uniform symbols of order zero on Besov spaces.** A symbol `a` of order `0` whose estimates
are uniform in the position quantizes to a bounded operator on every Besov space
`B^s_{p,q}`. -/
private theorem IsUniform.exists_toDistr_eq_quantizeTempered_and_norm_le_of_zero
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) (s : ℝ) :
    ∃ C : ℝ, ∀ u : BesovSpace F φ s p q, ∃ v : BesovSpace F φ s p q,
      v.toDistr = quantizeTempered F a ha u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  set N : ℕ := ⌊|s|⌋₊ + 1
  have hN : |s| < N := by
    simp only [N, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  obtain ⟨K, hK, hT⟩ := ha.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le (F := F) φ N
  refine ⟨K * ∑' d : ℤ, ((2 : ℝ) ^ (|s| - N)) ^ d.natAbs, fun u ↦ ?_⟩
  exact BesovSpace.exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le
    (quantizeTempered F a ha) hN hK u fun j k ↦ hT j k u.toDistr (u.block k)
      (BesovSpace.coe_block u k).symm

/-- **Pseudodifferential operators on Besov spaces.** A symbol `a` of order `m` whose estimates
are uniform in the position quantizes to a bounded operator `B^s_{p,q} → B^{s-m}_{p,q}`, for every
real `s` and all `1 ≤ p, q ≤ ∞`. For `p = q = ∞` this is the mapping `𝒞^s → 𝒞^{s-m}` of the
Hölder–Zygmund scale. -/
theorem IsUniform.exists_toDistr_eq_quantizeTempered_and_norm_le {a : Symbol n ℂ ℂ m}
    (ha : a.IsUniform) (s : ℝ) :
    ∃ C : ℝ, ∀ u : BesovSpace F φ s p q, ∃ v : BesovSpace F φ (s - m) p q,
      v.toDistr = quantizeTempered F a ha u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  set J := BesovSpace.besselPotentialEquiv F φ p q m (s := s) rfl
  obtain ⟨C₀, h₀⟩ := ((ha.comp (isUniform_besselPotential (-m))).inclusion
    (add_neg_cancel m).le).exists_toDistr_eq_quantizeTempered_and_norm_le_of_zero (F := F)
      (φ := φ) (p := p) (q := q) (s - m)
  refine ⟨max C₀ 0 * ‖(J : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ (s - m) p q)‖,
    fun u ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := h₀ (J u)
  refine ⟨v, ?_, ?_⟩
  · rw [hv, BesovSpace.toDistr_besselPotentialEquiv, ← ha.quantizeTempered_eq_comp_besselPotential]
  · calc ‖v‖ ≤ C₀ * ‖J u‖ := hvn
      _ ≤ max C₀ 0 * ‖J u‖ := by gcongr; exact le_max_left _ _
      _ ≤ max C₀ 0 * (‖(J : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ (s - m) p q)‖ * ‖u‖) := by
          gcongr
          exact (J : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ (s - m) p q).le_opNorm u
      _ = _ := by ring

/-- **Pseudodifferential operators preserve Besov regularity up to their order.** If `u` lies in
the Besov space `B^s_{p,q}` and `a` is a symbol of order `m` whose estimates are uniform in the
position, then `Op(a) u` lies in `B^{s-m}_{p,q}`. -/
theorem _root_.TemperedDistribution.MemBesov.quantizeTempered {s : ℝ}
    {u : 𝓢'(CoordinateSpace n, F)} (hu : u.MemBesov φ s p q)
    {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) :
    (quantizeTempered F a ha u).MemBesov φ (s - m) p q := by
  obtain ⟨C, hC⟩ := ha.exists_toDistr_eq_quantizeTempered_and_norm_le (F := F) (φ := φ)
    (p := p) (q := q) s
  obtain ⟨v, hv, -⟩ := hC hu.toBesovSpace
  rw [hu.toDistr_toBesovSpace] at hv
  exact hv ▸ v.memBesov_toDistr

variable (F φ p q) in
/-- **Pseudodifferential operators on Besov spaces.** For a symbol `a` of order `m` whose
estimates are uniform in the position, the quantization `Op(a)` as a bounded operator
`B^s_{p,q} → B^{s'}_{p,q}` for `s' = s - m`. It is the restriction of the action of `Op(a)` on
tempered distributions (`TauCeti.Symbol.toDistr_quantizeBesov`). -/
def quantizeBesov (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) {s s' : ℝ} (hs : s' = s - m) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s' p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := MemBesov.toBesovSpace (u := quantizeTempered F a ha u.toDistr)
        (by subst hs; exact u.memBesov_toDistr.quantizeTempered ha)
      map_add' u v := BesovSpace.ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, BesovSpace.toDistr_add, map_add]
      map_smul' c u := BesovSpace.ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, BesovSpace.toDistr_smul, map_smul,
          RingHom.id_apply] } <| by
    subst hs
    obtain ⟨C, hC⟩ := ha.exists_toDistr_eq_quantizeTempered_and_norm_le (F := F) (φ := φ)
      (p := p) (q := q) s
    refine ⟨C, fun u ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := hC u
    refine le_of_eq_of_le (congrArg norm (BesovSpace.ext ?_)) hvn
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MemBesov.toDistr_toBesovSpace, hv]

/-- On tempered distributions, `TauCeti.Symbol.quantizeBesov` acts as `Op(a)`. -/
@[simp]
theorem toDistr_quantizeBesov (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) {s s' : ℝ}
    (hs : s' = s - m) (u : BesovSpace F φ s p q) :
    (quantizeBesov F φ p q a ha hs u).toDistr = quantizeTempered F a ha u.toDistr :=
  MemBesov.toDistr_toBesovSpace _

end Besov

end Symbol

end TauCeti

