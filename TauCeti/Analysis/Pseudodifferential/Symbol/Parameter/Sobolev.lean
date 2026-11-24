/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Evaluation

/-!
# Sobolev bounds for parameter-dependent symbols, with decay in the spectral parameter

Let `a((x, ξ), z)` be a strongly parameter-dependent symbol of order `m ≤ 0`
(`TauCeti.ParameterSymbol`) that vanishes at the positions outside a fixed compact set, for every
frequency and every spectral parameter. At each spectral parameter `z` its quantization `Op(a(z))`
is bounded `H^s → H^{s - m'}` for every `m' ≥ m` (`TauCeti.Symbol.quantizeSobolev` of the symbol
`TauCeti.ParameterSymbol.toSymbol a z` of order `m'`). For `m ≤ m' ≤ 0` its operator norm decays
in the spectral parameter:

`‖Op(a(z))‖_{H^s → H^{s - m'}} ≤ C (1 + ‖z‖ ^ (1 / 2)) ^ (m - m')`

uniformly in `z ∈ Λ` (`TauCeti.ParameterSymbol.exists_norm_quantizeSobolev_inclusion_toSymbol_le`).
Thus giving up `m' - m` orders of smoothing gains decay like `‖z‖ ^ ((m - m') / 2)`; for `m' = m`
the bound is uniform in `z`. This is the form of the estimates used to integrate resolvents along a
contour around the spectrum: a symbol of order `-2`, such as the resolvent symbol
`(s + ‖ξ‖² - z)⁻¹` of `TauCeti.ParameterSymbol.shiftedLaplacian` multiplied by a cutoff in the
position, gives operators on `H^s` (`m' = 0`) of norm `O(‖z‖⁻¹)`, and a symbol of order `-N` gives
`O(‖z‖ ^ (-N / 2))`.

The proof combines the uniform seminorm decay of the symbols at the spectral parameters
(`TauCeti.ParameterSymbol.exists_seminorm_inclusion_toSymbol_le`) with the bound of the Sobolev
operator norm by finitely many seminorms of the symbol, uniform over the symbols vanishing outside
a fixed compact set (`TauCeti.Symbol.exists_norm_quantizeSobolev_le_sum_seminorm`).

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open TopologicalSpace
open scoped BesselPotentialSpace

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : Opens ℂ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m m' : ℝ}

/-- **Sobolev bounds with decay in the spectral parameter.** Let `a` be a parameter-dependent
symbol of order `m` vanishing at the positions outside a compact set `K`, and let
`m ≤ m' ≤ 0`. Then the quantizations `Op(a(z)) : H^s → H^{s - m'}` of its symbols at the spectral
parameters `z ∈ Λ`, viewed as symbols of order `m'`, have operator norms at most
`C (1 + ‖z‖ ^ (1 / 2)) ^ (m - m')` for a constant `C` independent of `z`. -/
theorem exists_norm_quantizeSobolev_inclusion_toSymbol_le (a : ParameterSymbol n Λ V W m)
    (h : m ≤ m') (h' : m' ≤ 0) (K : Compacts (CoordinateSpace n))
    (ha : ∀ x ∉ K, ∀ ξ z, a.coefficient ((x, ξ), z) = 0) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Λ,
      ‖(Symbol.inclusion h (a.toSymbol z)).quantizeSobolev
          ((a.hasCompactSpatialSupport_toSymbol z K.isCompact fun x hx ξ => ha x hx ξ z).inclusion
            h) s‖ ≤
        C * (1 + Real.sqrt ‖z‖) ^ (m - m') := by
  obtain ⟨t, C, hC, hop⟩ :=
    Symbol.exists_norm_quantizeSobolev_le_sum_seminorm (V := V) (W := W) (m := m') K s
  choose D hD hdec using fun α : List (Fin n) => a.exists_seminorm_inclusion_toSymbol_le h h' K α []
  refine ⟨C * ∑ α ∈ t, D α, mul_nonneg hC (Finset.sum_nonneg fun α _ => hD α), fun z hz => ?_⟩
  refine (hop _ _ fun x hx ξ => by
    rw [Symbol.coefficient_inclusion, coefficient_toSymbol, ha x hx ξ z]).trans ?_
  rw [mul_assoc, Finset.sum_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => hdec α z hz) hC

end ParameterSymbol

end TauCeti
