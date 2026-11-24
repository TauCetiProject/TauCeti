/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol.Topology
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical

/-!
# Continuous lifts of principal symbols

Every homogeneous symbol `a` of degree `m` on `ℝⁿ` is the principal symbol of a classical symbol
of order `m`, namely of its cut-off term `χ(ξ) a(x, ξ)` for a frequency cutoff `χ`
(`TauCeti.ClassicalSymbol.ofHomogeneous`). The cut-off term depends continuously on `a` for the
C^∞ topology on compact sets of positions times the unit sphere of frequencies
(`TauCeti.HomogeneousSymbol.continuous_cutoffSymbol`). This file deduces that continuous families
and homotopies of principal symbols lift to continuous families of full symbols, with a
prescribed full symbol at one parameter value.

## Main results

* `TauCeti.ClassicalSymbol.continuous_toSymbol_replacePrincipal`: the full symbol of the
  classical symbol `TauCeti.ClassicalSymbol.replacePrincipal χ b a = b + χ(ξ) (a - b_m)(x, ξ)`,
  obtained from `b` by replacing its principal symbol with `a`, depends continuously on `a`.
* `TauCeti.ClassicalSymbol.exists_lift_of_continuous`: **continuous lifts with a prescribed
  initial value.** A continuous family `t ↦ a_t` of homogeneous symbols of degree `m` is the
  family of principal symbols of classical symbols `b_t` whose full symbols depend continuously
  on `t`, with `b_{t₀}` any prescribed classical symbol with principal symbol `a_{t₀}`; for a
  given cutoff `χ` their remainders after `N ≥ 1` terms do not depend on `t`.

## References

* R. B. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.2: the quantization of
  principal symbols by frequency cutoffs.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### Continuous lifts of principal symbols -/

namespace ClassicalSymbol

open HomogeneousSymbol

variable (χ : FrequencyCutoff (CoordinateSpace n)) (b : ClassicalSymbol n V W m)

/-- The full symbol of `b.replacePrincipal χ a` depends continuously on `a`. -/
theorem continuous_toSymbol_replacePrincipal :
    Continuous fun a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m =>
      (b.replacePrincipal χ a).toSymbol := by
  simp only [toSymbol_replacePrincipal]
  exact continuous_const.add
    ((continuous_cutoffSymbol V W m χ).comp (continuous_id.sub continuous_const))

/-- **Continuous lifts of principal symbols with a prescribed initial value.** Let `t ↦ a_t` be a
continuous family of homogeneous symbols of degree `m`, and `b₀` a classical symbol whose principal
symbol is `a_{t₀}`. Then there are classical symbols `b_t` with principal symbols `a_t`, full
symbols depending continuously on `t`, and `b_{t₀} = b₀`; their lower order terms, and their
remainders after `N ≥ 1` terms for the cutoff `χ`, are those of `b₀`. -/
theorem exists_lift_of_continuous {T : Type*} [TopologicalSpace T]
    {a : T → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} (ha : Continuous a)
    {t₀ : T} {b₀ : ClassicalSymbol n V W m} (hb₀ : b₀.principal = a t₀) :
    ∃ b' : T → ClassicalSymbol n V W m, Continuous (fun t => (b' t).toSymbol) ∧
      (∀ t, (b' t).principal = a t) ∧ b' t₀ = b₀ ∧ (∀ t j, (b' t).term (j + 1) = b₀.term (j + 1)) ∧
      ∀ t N, (b' t).remainder χ (N + 1) = b₀.remainder χ (N + 1) :=
  ⟨fun t => b₀.replacePrincipal χ (a t), (continuous_toSymbol_replacePrincipal χ b₀).comp ha,
    fun t => principal_replacePrincipal χ b₀ (a t), by simp [← hb₀],
    fun t j => term_replacePrincipal_succ χ b₀ (a t) j,
    fun t N => remainder_replacePrincipal_succ χ b₀ (a t) N⟩

end ClassicalSymbol

end TauCeti
