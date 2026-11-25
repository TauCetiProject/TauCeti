/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.TruncatedParametrix
import TauCeti.Algebra.BigOperators.NatAntidiagonal

/-!
# The right parametrix of a differential operator with parameter

Let `a((x, ξ), z)` be a strongly parameter-dependent symbol of order `m` (`TauCeti.ParameterSymbol`)
which is elliptic with parameter and polynomial of degree less than `d` in the frequency, such as
the symbol of `A - z` for an elliptic differential operator `A` of order `2` whose principal symbol
takes no values in `Λ` (then `m = 2`, since `z` counts as two frequency orders); the symbol
`(s + ‖ξ‖²) - z` of `s - Δ - z` is an example (`TauCeti.ParameterSymbol.shiftedLaplacian`). Its
formal right parametrix `b₀, b₁, …` (`TauCeti.ParameterSymbol.rightInverseTerms`), with `bⱼ` of
order `-m - j`, solves the formal composition equations order by order. This file turns the first
`N` of these terms into a local right-parametrix identity for the operators, whose remainder decays
uniformly in the spectral parameter `z`. It is an input to the comparison of the quantized
parametrix with the resolvent `(A - z)⁻¹`, which this file does not make.

Let `Bₙ = ∑_{j < N} bⱼ` (`TauCeti.ParameterSymbol.rightParametrix`), and let `ψ` and `ψ₁` be
smooth cutoffs in the position, with `ψ₁` compactly supported and equal to `1` near the support of
`ψ`. Then for every spectral parameter `z` and every Schwartz function `u`,

`ψ · Op(a(z)) (ψ₁ · Op(Bₙ(z)) u) = ψ · u + Op(ψ rₙ(z)) u`

(`TauCeti.ParameterSymbol.smul_quantizeSchwartzValue_rightParametrix_eq_add`), with an explicit
remainder symbol `rₙ` of order `-N` (`TauCeti.ParameterSymbol.rightParametrixRemainder`). If
moreover `ψ` has compact support then, since `z` counts as two frequency orders, the remainder
operators have norms

`‖Op(ψ rₙ(z))‖_{H^s → H^s} ≤ C (1 + ‖z‖ ^ (1 / 2)) ^ (-N)`

uniformly in `z ∈ Λ`
(`TauCeti.ParameterSymbol.exists_norm_quantizeSobolev_rightParametrixRemainder_le`). So for such
`ψ` the localized parametrix inverts `A - z` near the support of `ψ` up to an error of size
`‖z‖ ^ (-N / 2)`.

Two facts make the identity exact. Since `a` is polynomial in the frequency, the composition
expansion of `a(z) # (ψ₁ Bₙ(z))` stops after `d` terms
(`TauCeti.Symbol.coefficient_sharp_eq_sum_of_mixedDeriv_eq_zero`), so no remainder of the ordinary
calculus, whose estimates would not be uniform in `z`, appears. Near the support of `ψ` the cutoff
`ψ₁` is `1`, so it disappears from the terms of the expansion. What is left,
`∑_{k < d} ∑_{j < N} sharpTerm a bⱼ k`, is the identity plus the terms with `j + k ≥ N`, by the
formal composition equations `∑_{j + k = L} sharpTerm a bⱼ k = δ_{L,0}`
(`TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_rightInverseTerms`); those terms have order
`-(j + k) ≤ -N` and make up `rₙ`.

## Main declarations

* `TauCeti.ParameterSymbol.rightParametrixRemainder`: the remainder of order `-N` of the truncated
  right parametrix `TauCeti.ParameterSymbol.rightParametrix`.
* `TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_rightParametrix`: the symbol identity
  `∑_{k < d} sharpTerm a Bₙ k = 1 + rₙ`.
* `TauCeti.ParameterSymbol.smul_quantizeSchwartzValue_rightParametrix_eq_add`: the operator
  identity above.
* `TauCeti.ParameterSymbol.exists_norm_quantizeSobolev_rightParametrixRemainder_le`: the decay of
  the remainder operators in the spectral parameter.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9 and §11.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

open Finset TopologicalSpace
open scoped ContDiff Topology SchwartzMap

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : Opens ℂ} {m : ℝ}

section Parametrix

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace V] {a : ParameterSymbol n Λ V W m}

/-! ### The remainder of the truncated right parametrix -/

variable (a) in
/-- The remainder of the truncated right parametrix of a symbol `a` elliptic with parameter and
polynomial of degree less than `d` in the frequency: the sum of the composition terms
`sharpTerm a bⱼ k` with `j < N` and `N ≤ j + k < N + d`, a parameter-dependent symbol of order
`-N`. The terms with `k ≥ d` vanish, so these are all the terms with `j + k ≥ N`
(`TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_rightParametrix`). -/
noncomputable def rightParametrixRemainder (ha : a.IsElliptic) (d N : ℕ) :
    ParameterSymbol n Λ W W (-N) :=
  ∑ j ∈ range N, ∑ i ∈ range d, inclusion (sharpTerm_inverseTerms_order_le N j i)
    (a.sharpTerm (a.rightInverseTerms ha j) (N - j + i))

@[simp]
theorem coefficient_rightParametrixRemainder (ha : a.IsElliptic) (d N : ℕ) :
    (a.rightParametrixRemainder ha d N).coefficient = ∑ j ∈ range N, ∑ i ∈ range d,
      (a.sharpTerm (a.rightInverseTerms ha j) (N - j + i)).coefficient := by
  simp [rightParametrixRemainder, coefficient_sum]

/-- **The truncated right parametrix.** Let `a` be elliptic with parameter and polynomial of
degree less than `d` in the frequency, and `N ≥ 1`. Then the composition terms of `a` with the sum
`Bₙ = ∑_{j < N} bⱼ` of the first `N` terms of its formal right parametrix add up to the identity
plus the remainder `rₙ` of order `-N`: `∑_{k < d} sharpTerm a Bₙ k = 1 + rₙ`. -/
theorem sum_coefficient_sharpTerm_rightParametrix (ha : a.IsElliptic) {d N : ℕ} (hN : N ≠ 0)
    (hd : ∀ x, ∀ z ∈ Λ, ∀ w : List (Fin n), w.length = d →
      coordinateDeriv w (fun η => a.coefficient ((x, η), z)) = 0)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    ∑ k ∈ range d, (a.sharpTerm (a.rightParametrix ha N) k).coefficient ((x, ξ), z) =
      ContinuousLinearMap.id ℂ W + (a.rightParametrixRemainder ha d N).coefficient ((x, ξ), z) := by
  set T : ℕ → ℕ → W →L[ℂ] W := fun j k =>
    (a.sharpTerm (a.rightInverseTerms ha j) k).coefficient ((x, ξ), z)
  have hT0 (j : ℕ) {k : ℕ} (hk : d ≤ k) : T j k = 0 :=
    coefficient_sharpTerm_eq_zero_of_coordinateDeriv_eq_zero hd _ hk x ξ hz
  -- For each `j`, split the terms `k < d` at `k = N - j`; the terms beyond `d` vanish.
  have hsplit (j : ℕ) : ∑ k ∈ range d, T j k =
      ∑ k ∈ range (N - j), T j k + ∑ i ∈ range d, T j (N - j + i) := by
    rw [← Finset.sum_range_add, add_comm, Finset.sum_range_add,
      Finset.sum_eq_zero (s := range (N - j)) fun i _ => hT0 j (Nat.le_add_right d i), add_zero]
  -- The terms with `j + k < N` add up to the identity by the formal composition equations.
  have hdiag : ∑ j ∈ range N, ∑ k ∈ range (N - j), T j k = ContinuousLinearMap.id ℂ W :=
    Nat.sum_range_sum_range_sub_eq
      (fun L => sum_coefficient_sharpTerm_rightInverseTerms ha L x ξ hz) hN
  simp_rw [coefficient_sharpTerm_rightParametrix ha N _ x ξ z]
  rw [Finset.sum_comm, coefficient_rightParametrixRemainder]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, hdiag]

/-! ### The operator identity and the decay of the remainder -/

/-- **The right parametrix of a differential operator with parameter.** Let `a` be a symbol of
order `m` elliptic with parameter and polynomial of degree less than `d` in the frequency, such as
the symbol of `A - z` for an elliptic differential operator `A` of order `2`, and `N ≥ 1`. Let `ψ`,
`ψ₁` be smooth real functions of the position, `ψ₁` compactly supported and equal to `1` near the
support of `ψ`. Then for every spectral parameter `z ∈ Λ` and every Schwartz function `u`, with
`w = ψ₁ · Op(Bₙ(z)) u`, where `Bₙ = ∑_{j < N} bⱼ` is the truncated right parametrix,

`ψ · Op(a(z)) w = ψ · u + Op(ψ rₙ(z)) u`,

with the remainder symbol `rₙ` of order `-N`. If moreover `ψ` has compact support, the remainder
operators have norms decaying like `‖z‖ ^ (-N / 2)`
(`TauCeti.ParameterSymbol.exists_norm_quantizeSobolev_rightParametrixRemainder_le`). -/
theorem smul_quantizeSchwartzValue_rightParametrix_eq_add [CompleteSpace W] (ha : a.IsElliptic)
    {d N : ℕ} (hN : N ≠ 0) (hd : ∀ x, ∀ z ∈ Λ, ∀ w : List (Fin n), w.length = d →
      coordinateDeriv w (fun η => a.coefficient ((x, η), z)) = 0)
    {ψ ψ₁ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ₁ : ContDiff ℝ ∞ ψ₁)
    (hψ₁c : HasCompactSupport ψ₁) (hψψ₁ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ψ₁ x = 1) {z : ℂ}
    (hz : z ∈ Λ) (u : 𝓢(CoordinateSpace n, W)) (w : 𝓢(CoordinateSpace n, V))
    (hw : ⇑w = quantizeSchwartzValue
      (((ofSpatial (fun x => ψ₁ x • ContinuousLinearMap.id ℂ V) (hψ₁.smul contDiff_const)).comp
        (a.rightParametrix ha N)).toSymbol z).coefficient u)
    (x : CoordinateSpace n) :
    (ψ x : ℂ) • quantizeSchwartzValue (a.toSymbol z).coefficient w x =
      (ψ x : ℂ) • u x + quantizeSchwartzValue
        (((ofSpatial (fun x => ψ x • ContinuousLinearMap.id ℂ W) (hψ.smul contDiff_const)).comp
          (a.rightParametrixRemainder ha d N)).toSymbol z).coefficient u x := by
  set Q := ((ofSpatial (fun x => ψ₁ x • ContinuousLinearMap.id ℂ V)
    (hψ₁.smul contDiff_const)).comp (a.rightParametrix ha N)).toSymbol z
  have hQ : Q.HasCompactSpatialSupport := hasCompactSpatialSupport_toSymbol _ z hψ₁c
    fun y hy ξ => by simp [hz, image_eq_zero_of_notMem_tsupport hy]
  have hQB : ∀ᶠ y in 𝓝ˢ (tsupport fun y => (ψ y : ℂ)), ∀ ξ, Q.coefficient (y, ξ) =
      ((a.rightParametrix ha N).toSymbol z).coefficient (y, ξ) := by
    have hts : tsupport (fun y => (ψ y : ℂ)) = tsupport ψ := by
      simp [tsupport, Function.support]
    rw [hts]
    filter_upwards [hψψ₁] with y hy ξ
    simp [Q, hz, hy]
  -- `ψ a(z)`, as the left factor of the composition terms.
  have hΨA (y ξ : CoordinateSpace n) :
      ((Symbol.ofSpatial (fun x => ψ x • ContinuousLinearMap.id ℂ W)
        (hψ.smul contDiff_const)).comp (a.toSymbol z)).coefficient (y, ξ) =
        (ψ y : ℂ) • (a.toSymbol z).coefficient (y, ξ) := by
    simp [ContinuousLinearMap.smul_comp, Complex.coe_smul]
  -- Near the support of `ψ`, `Q` is the truncated parametrix, which may replace it in the terms.
  have hterm (k : ℕ) (ξ : CoordinateSpace n) :
      (ψ x : ℂ) • ((a.toSymbol z).sharpTerm Q k).coefficient (x, ξ) =
        (ψ x : ℂ) • (a.sharpTerm (a.rightParametrix ha N) k).coefficient ((x, ξ), z) := by
    rw [← Symbol.coefficient_sharpTerm_of_eq_smul_of_eventuallyEq hΨA
        (.of_forall fun _ _ => rfl) k x ξ,
      Symbol.coefficient_sharpTerm_of_eq_smul_of_eventuallyEq hΨA hQB k x ξ,
      ← toSymbol_sharpTerm _ _ _ z, coefficient_toSymbol]
  -- Since `a(z)` is polynomial in the frequency, `a(z) # Q` is the sum of `d` composition terms.
  have hsharp (ξ : CoordinateSpace n) :
      (ψ x : ℂ) • ((a.toSymbol z).sharp Q hQ).coefficient (x, ξ) =
        (ψ x : ℂ) • (ContinuousLinearMap.id ℂ W +
          (a.rightParametrixRemainder ha d N).coefficient ((x, ξ), z)) := by
    rw [Symbol.coefficient_sharp_eq_sum_of_mixedDeriv_eq_zero hQ (N := d) fun β hβ y η => by
        simpa [mixedDeriv_def] using congrFun (hd y z hz β hβ) η,
      Finset.sum_apply, Finset.smul_sum, Finset.sum_congr rfl fun k _ => hterm k ξ,
      ← Finset.smul_sum, sum_coefficient_sharpTerm_rightParametrix ha hN hd x ξ hz]
  -- `w` is `Op(Q) u`, so the operator identity follows from the symbol identity `hsharp`.
  have hw' : w = (hQ.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
      (Q.contDiff_quantizeSchwartzValue u) :=
    SchwartzMap.ext fun y => by rw [hw, HasCompactSupport.toSchwartzMap_toFun]
  rw [hw', toSymbol_comp, toSymbol_ofSpatial _ _ hz]
  exact Symbol.smul_quantizeSchwartzValue_sharp_eq_add hQ _ hψ u x fun ξ => by
    rw [coefficient_toSymbol]
    exact hsharp ξ

end Parametrix

section Sobolev

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Decay of the remainder in the spectral parameter.** For a compactly supported smooth `ψ`,
the remainder operators `Op(ψ rₙ(z)) : H^s → H^s` of the truncated right parametrix
(`TauCeti.ParameterSymbol.smul_quantizeSchwartzValue_rightParametrix_eq_add`) have norms at most
`C (1 + ‖z‖ ^ (1 / 2)) ^ (-N)`, uniformly in `z ∈ Λ`. -/
theorem exists_norm_quantizeSobolev_rightParametrixRemainder_le
    {a : ParameterSymbol n Λ V W m} (ha : a.IsElliptic) (d N : ℕ) {ψ : CoordinateSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (s : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Λ,
      ∀ hc : (Symbol.inclusion (by simp) (((ofSpatial (fun x => ψ x • ContinuousLinearMap.id ℂ W)
        (hψ.smul contDiff_const)).comp (a.rightParametrixRemainder ha d N)).toSymbol z) :
          Symbol n W W 0).HasCompactSpatialSupport,
      ‖Symbol.quantizeSobolev _ hc s‖ ≤ C * (1 + Real.sqrt ‖z‖) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_quantizeSobolev_inclusion_toSymbol_le
    ((ofSpatial (fun x => ψ x • ContinuousLinearMap.id ℂ W) (hψ.smul contDiff_const)).comp
      (a.rightParametrixRemainder ha d N)) (m' := 0) (by simp) le_rfl ⟨tsupport ψ, hψc⟩
    (fun x hx ξ z => by
      by_cases hz : z ∈ Λ
      · simp [hz, image_eq_zero_of_notMem_tsupport hx]
      · exact coefficient_of_notMem _ _ hz) s
  refine ⟨C, hC, fun z hz hc => ?_⟩
  simpa using hbound z hz

end Sobolev

end ParameterSymbol

end TauCeti
