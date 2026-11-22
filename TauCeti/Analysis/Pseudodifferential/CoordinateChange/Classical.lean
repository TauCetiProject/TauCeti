/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Homogeneous
public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.CoordinateChange.Basic
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Changes of coordinates for classical pseudodifferential operators

Let `κ` be a diffeomorphism of `ℝⁿ` and `a ∼ ∑ⱼ a_{m-j}` a classical symbol of order `m`
vanishing at positions outside a compact set. By Kuranishi's trick
(`TauCeti.exists_forall_quantizeSchwartzValue_comp_eq_compAmplitude`), the operator `Op(a)`
transported to the coordinates `x` with `z = κ x`, and cut off by `ψ`, is the left quantization of
an amplitude

`c(x, y, ξ) = g(x, y) • a(κ x, M(x, y) ξ)`,

where `M(x, y)` is a smooth family of invertible linear maps on the support of the weight `g`.
This file shows that its symbol `b` is again **classical**, so the classical calculus is invariant
under changes of coordinates, and that its principal symbol is the pullback of that of `a` by the
cotangent map of `κ`:

`σ(b)(x, ξ) = ψ(x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`.

The full symbol is the asymptotic sum `b ∼ ∑ₖ leftTerm c k` of the left expansion of `c`
(`TauCeti.Amplitude.isAsymptoticSum_leftSymbol`). Since `M(x, y)` is linear in the frequency,
each `g(x, y) • a_{m-j}(κ x, M(x, y) ξ)` is a homogeneous amplitude of degree `m - j`
(`TauCeti.HomogeneousSymbol.compAmplitude`), and at large frequencies it agrees with the amplitude
of the cut-off term `χ(η) a_{m-j}(z, η)`: on the compact support of `g`, `‖M(x, y) ξ‖` is
comparable to `‖ξ‖`. So the term `leftTerm c k` of order `m - k` is classical, with homogeneous
terms the left terms of these homogeneous amplitudes
(`TauCeti.Amplitude.coefficient_leftTerm_eq_of_eq`), and an asymptotic sum of classical symbols
of decreasing orders is classical (`TauCeti.ClassicalSymbol.ofIsAsymptoticSum`). The homogeneous
term of degree `m - j` of `b` is

`b_{m-j}(x, ξ) = ∑_{k ≤ j} ((-i)^k / k!) ∑_{|w| = k} ∂_y^w ∂_ξ^w h_{m-j+k}((x, y), ξ)|_{y = x}`,

with `h_{m-i}((x, y), ξ) = g(x, y) • a_{m-i}(κ x, M(x, y) ξ)`.

## Main declarations

* `TauCeti.ClassicalSymbol.leftSymbolCompAmplitude`: the left symbol of the amplitude
  `g(x, y) • a(κ x, M(x, y) ξ)` of a classical symbol `a`, as a classical symbol, with principal
  symbol `g(x, x) • σ(a)(κ x, M(x, x) ξ)`.
* `TauCeti.ClassicalSymbol.exists_quantizeSchwartzValue_comp_eq`: **changes of coordinates for
  classical symbols**: the transported operator is `Op(b)` for a classical symbol `b` with
  principal symbol `ψ(x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.17 and the remarks on classical symbols following Definition 18.1.5.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Finset
open scoped ContDiff SchwartzMap

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} {κ : CoordinateSpace n → CoordinateSpace n}
  {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
  {g : CoordinateSpace n × CoordinateSpace n → ℝ}

/-! ### Cut-off homogeneous symbols in moving frequency coordinates -/

namespace HomogeneousSymbol

/-- At large frequencies, the amplitude `g(x, y) • χ(M(x, y) ξ) h(κ x, M(x, y) ξ)` of the cut-off
term of a homogeneous symbol `h` is the homogeneous amplitude `g(x, y) • h(κ x, M(x, y) ξ)`: on
the compact support of `g`, `‖ξ‖ ≤ c ‖M(x, y) ξ‖`. The radius does not depend on `h`. -/
private theorem exists_coefficient_compAmplitude_cutoffSymbol_eq
    (χ : FrequencyCutoff (CoordinateSpace n)) (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) :
    ∃ R, 0 ≤ R ∧ ∀ {m : ℝ} (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
      (x y ξ : CoordinateSpace n), R < ‖ξ‖ →
        ((cutoffSymbol χ h).compAmplitude hκ hM hg hgc hgM).coefficient (x, y, ξ) =
          (h.compAmplitude hκ hM hg hgM).coefficient ((x, y), ξ) := by
  obtain ⟨c, hc, hcS⟩ :=
    exists_norm_clm_apply_le_and_norm_le_of_isUnit hgc.isCompact hM.continuous.continuousOn hgM
  refine ⟨2 * c, by positivity, fun h x y ξ hξ ↦ ?_⟩
  rw [Symbol.coefficient_compAmplitude, coefficient_compAmplitude, coefficient_cutoffSymbol]
  by_cases hxy : (x, y) ∈ tsupport g
  · have h2 : 2 ≤ ‖M (x, y) ξ‖ := by nlinarith [(hcS _ hxy ξ).2]
    rw [χ.apply_eq_one_of_two_le_norm h2, one_smul]
  · simp [image_eq_zero_of_notMem_tsupport hxy]

end HomogeneousSymbol

/-! ### The left symbol of the amplitude of a classical symbol -/

namespace ClassicalSymbol

open HomogeneousSymbol

section LeftSymbol

variable (a : ClassicalSymbol n V W m) (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
  (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w))

/-- The amplitude of `a` is that of the remainder `a - ∑_{j<N} χ(η) a_{m-j}` plus those of the
cut-off terms `χ(η) a_{m-j}`. -/
private theorem coefficient_compAmplitude_eq_add_sum (χ : FrequencyCutoff (CoordinateSpace n))
    (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (a.toSymbol.compAmplitude hκ hM hg hgc hgM).coefficient p =
      ((a.remainder χ N).compAmplitude hκ hM hg hgc hgM).coefficient p +
        ∑ j ∈ range N,
          ((cutoffSymbol χ (a.term j)).compAmplitude hκ hM hg hgc hgM).coefficient p := by
  simp [coefficient_remainder, smul_sub, Finset.smul_sum]

/-- The term `leftTerm c k` of the left expansion of the amplitude `c = g • a(κ x, M ξ)` is
classical: its remainder after the homogeneous terms `leftTerm (g • a_{m-j}(κ x, M ξ)) k`, `j < N`,
has order `m - k - N`. -/
private theorem exists_remainder_leftTerm (χ : FrequencyCutoff (CoordinateSpace n)) (k N : ℕ) :
    ∃ r : Symbol n V W (m - k - N), ∀ p, r.coefficient p =
      ((a.toSymbol.compAmplitude hκ hM hg hgc hgM).leftTerm k).coefficient p -
        ∑ j ∈ range N,
          χ p.2 • (((a.term j).compAmplitude hκ hM hg hgM).leftTerm k).coefficient p := by
  obtain ⟨R, hR0, hR⟩ := exists_coefficient_compAmplitude_cutoffSymbol_eq (V := V) (W := W) χ hκ hM
    hg hgc hgM
  -- The left terms of each cut-off term agree with the homogeneous ones at large frequencies.
  have hs (j : ℕ) : ∃ s : Symbol n V W (m - k - N), ∀ p, s.coefficient p =
      (((cutoffSymbol χ (a.term j)).compAmplitude hκ hM hg hgc hgM).leftTerm k).coefficient p -
        χ p.2 • (((a.term j).compAmplitude hκ hM hg hgM).leftTerm k).coefficient p := by
    have hsm : (((cutoffSymbol χ (a.term j)).compAmplitude hκ hM hg hgc hgM).leftTerm k -
        cutoffSymbol χ (((a.term j).compAmplitude hκ hM hg hgM).leftTerm k)).IsSmoothing :=
      Symbol.isSmoothing_of_coefficient_eq_zero (max (R + 1) 2) fun x ξ hξ ↦ by
        rw [Symbol.coefficient_sub, Pi.sub_apply,
          coefficient_cutoffSymbol_of_two_le_norm _ _ (le_of_max_le_right hξ),
          Amplitude.coefficient_leftTerm_eq_of_eq hR0 (hR _) k
            (by linarith [le_of_max_le_left hξ]), sub_self]
    obtain ⟨s, hs⟩ := Symbol.isSmoothing_iff.1 hsm (m - k - N)
    exact ⟨s, fun p ↦ by rw [hs]; simp⟩
  choose s hs using hs
  refine ⟨Symbol.inclusion (le_of_eq (by ring))
    (((a.remainder χ N).compAmplitude hκ hM hg hgc hgM).leftTerm k) + ∑ j ∈ range N, s j,
    fun p ↦ ?_⟩
  rw [Amplitude.coefficient_leftTerm_eq_add_sum (range N)
    (a.coefficient_compAmplitude_eq_add_sum hκ hM hg hgc hgM χ N) k p]
  simp only [Symbol.coefficient_add, Symbol.coefficient_inclusion, Symbol.coefficient_sum,
    Pi.add_apply, Finset.sum_apply, hs, Finset.sum_sub_distrib]
  abel

/-- The term `leftTerm c k` of order `m - k` of the left expansion of the amplitude
`c = g • a(κ x, M ξ)`, as a classical symbol whose homogeneous terms are the left terms of the
homogeneous amplitudes `g • a_{m-j}(κ x, M ξ)`. -/
private def leftTermCompAmplitude (k : ℕ) : ClassicalSymbol n V W (m - k) where
  toSymbol := (a.toSymbol.compAmplitude hκ hM hg hgc hgM).leftTerm k
  term j := (((a.term j).compAmplitude hκ hM hg hgM).leftTerm k).castDegree (by ring)
  exists_remainder' := ⟨default, fun N ↦ by
    simpa using a.exists_remainder_leftTerm hκ hM hg hgc hgM default k N⟩

private theorem toSymbol_leftTermCompAmplitude (k : ℕ) :
    (a.leftTermCompAmplitude hκ hM hg hgc hgM k).toSymbol =
      (a.toSymbol.compAmplitude hκ hM hg hgc hgM).leftTerm k :=
  (rfl)

variable [CompleteSpace W]

/-- **The left symbol of the amplitude of a classical symbol is classical.** For a classical symbol
`a` of order `m`, a smooth family `M(x, y)` of linear maps and a smooth compactly supported weight
`g(x, y)` such that `M` is invertible on the support of `g`, the left symbol of the amplitude
`c(x, y, ξ) = g(x, y) • a(κ x, M(x, y) ξ)` (`TauCeti.Symbol.compAmplitude`) is a classical symbol
of order `m`. Its homogeneous term of degree `m - j` is the sum over `k ≤ j` of the left terms
`leftTerm k` of the homogeneous amplitudes `g(x, y) • a_{m-j+k}(κ x, M(x, y) ξ)`
(`TauCeti.ClassicalSymbol.coefficient_term_leftSymbolCompAmplitude`). -/
def leftSymbolCompAmplitude : ClassicalSymbol n V W m :=
  ofIsAsymptoticSum (a.leftTermCompAmplitude hκ hM hg hgc hgM) (by
    simpa only [toSymbol_leftTermCompAmplitude] using Amplitude.isAsymptoticSum_leftSymbol
      (a.toSymbol.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM))

@[simp]
theorem toSymbol_leftSymbolCompAmplitude :
    (a.leftSymbolCompAmplitude hκ hM hg hgc hgM).toSymbol =
      (a.toSymbol.compAmplitude hκ hM hg hgc hgM).leftSymbol
        (a.toSymbol.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM) :=
  toSymbol_ofIsAsymptoticSum _ _

/-- The homogeneous term of degree `m - j` of the left symbol of `g(x, y) • a(κ x, M(x, y) ξ)` is
`∑_{k ≤ j} leftTerm (g(x, y) • a_{m-j+k}(κ x, M(x, y) ξ)) k`. -/
@[simp]
theorem coefficient_term_leftSymbolCompAmplitude (j : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    ((a.leftSymbolCompAmplitude hκ hM hg hgc hgM).term j).coefficient p =
      ∑ k ∈ range (j + 1),
        (((a.term (j - k)).compAmplitude hκ hM hg hgM).leftTerm k).coefficient p := by
  rw [leftSymbolCompAmplitude, coefficient_term_ofIsAsymptoticSum]
  simp [leftTermCompAmplitude]

/-- **The principal symbol** of the left symbol of `g(x, y) • a(κ x, M(x, y) ξ)` is the restriction
`g(x, x) • σ(a)(κ x, M(x, x) ξ)` of the principal amplitude to the diagonal. -/
@[simp]
theorem coefficient_principal_leftSymbolCompAmplitude (x ξ : CoordinateSpace n) :
    (a.leftSymbolCompAmplitude hκ hM hg hgc hgM).principal.coefficient (x, ξ) =
      g (x, x) • a.principal.coefficient (κ x, M (x, x) ξ) := by
  rw [leftSymbolCompAmplitude, coefficient_principal_ofIsAsymptoticSum]
  simp [leftTermCompAmplitude]

end LeftSymbol

/-! ### Changes of coordinates -/

variable [CompleteSpace V] [CompleteSpace W]

/-- **Changes of coordinates for classical symbols.** Let `κ` be a smooth homeomorphism of `ℝⁿ`,
`a` a classical symbol of order `m` vanishing at positions outside a compact set `K`, and `ψ` a
smooth compactly supported cutoff such that `Dκ` is invertible on the support of `ψ`. Suppose the
averaged derivative `hadamardFactor κ y x` of `κ` on the segment from `y` to `x` is invertible
whenever `κ x ∈ K` and `y` lies in the support of `ψ`. Then the transported operator
`u ↦ Op(a) ((ψ u) ∘ κ⁻¹) ∘ κ` is `Op(b)` for a **classical** symbol `b` of order `m`, whose
principal symbol is the pullback of that of `a` by the cotangent map of `κ`:

`σ(b)(x, ξ) = ψ(x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`. -/
theorem exists_quantizeSchwartzValue_comp_eq (a : ClassicalSymbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (haK : ∀ z ∉ K, ∀ η, a.toSymbol.coefficient (z, η) = 0)
    (κ : CoordinateSpace n ≃ₜ CoordinateSpace n) (hκ : ContDiff ℝ ∞ κ)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hκ' : ∀ y ∈ tsupport ψ, IsUnit (fderiv ℝ κ y))
    (hΦ : ∀ x, κ x ∈ K → ∀ y ∈ tsupport ψ, IsUnit (hadamardFactor κ y x)) :
    ∃ b : ClassicalSymbol n V W m, (∀ x ξ, b.principal.coefficient (x, ξ) =
        ψ x • a.principal.coefficient
          (κ x, ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ κ x)) ξ)) ∧
      ∀ u v : 𝓢(CoordinateSpace n, V), (∀ y, v (κ y) = ψ y • u y) → ∀ x,
        quantizeSchwartzValue a.toSymbol.coefficient v (κ x) =
          quantizeSchwartzValue b.toSymbol.coefficient u x := by
  obtain ⟨M, hM, g, hg, hgc, hgM, hdiag, hop⟩ :=
    exists_forall_quantizeSchwartzValue_comp_eq_compAmplitude (V := V) (W := W) hK κ hκ hψ hψc hκ'
      hΦ
  refine ⟨a.leftSymbolCompAmplitude hκ hM hg hgc hgM, fun x ξ ↦ ?_, fun u v huv x ↦ ?_⟩
  swap
  · rw [toSymbol_leftSymbolCompAmplitude]
    exact hop a.toSymbol haK u v huv x
  rw [coefficient_principal_leftSymbolCompAmplitude]
  exact hdiag a.principal.coefficient
    (fun z hz ↦ a.coefficient_principal_eq_zero_of_forall_coefficient_eq_zero (haK z hz)) x ξ

end ClassicalSymbol

end TauCeti
