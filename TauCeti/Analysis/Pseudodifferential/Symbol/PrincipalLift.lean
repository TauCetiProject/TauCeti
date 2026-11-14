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

* `TauCeti.ClassicalSymbol.replacePrincipal`: the classical symbol `b + χ(ξ) (a - b_m)(x, ξ)`
  obtained from `b` by replacing its principal symbol with `a`. It keeps the lower order terms
  and, for the same cutoff, the remainders after `N ≥ 1` terms
  (`TauCeti.ClassicalSymbol.term_replacePrincipal_succ`,
  `TauCeti.ClassicalSymbol.remainder_replacePrincipal_succ`), and its full symbol depends
  continuously on `a` (`TauCeti.ClassicalSymbol.continuous_toSymbol_replacePrincipal`).
* `TauCeti.ClassicalSymbol.exists_lift_of_continuous`: **continuous lifts with a prescribed
  initial value.** A continuous family `t ↦ a_t` of homogeneous symbols of degree `m` is the
  family of principal symbols of classical symbols `b_t` whose full symbols depend continuously
  on `t`, with `b_{t₀}` any prescribed classical symbol with principal symbol `a_{t₀}`.

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

/-! ### Replacing the principal symbol of a classical symbol -/

namespace ClassicalSymbol

open HomogeneousSymbol

variable (χ : FrequencyCutoff (CoordinateSpace n)) (b : ClassicalSymbol n V W m)
  (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

/-- The classical symbol obtained from `b` by replacing its principal symbol with `a`:
`b + χ(ξ) (a - b_m)(x, ξ)`. It has principal symbol `a` and the lower order terms of `b`. -/
def replacePrincipal : ClassicalSymbol n V W m :=
  b + ofHomogeneous χ (a - b.principal)

@[simp]
theorem toSymbol_replacePrincipal :
    (b.replacePrincipal χ a).toSymbol = b.toSymbol + cutoffSymbol χ (a - b.principal) := by
  simp [replacePrincipal]

@[simp]
theorem principal_replacePrincipal : (b.replacePrincipal χ a).principal = a := by
  simp [replacePrincipal, principal_add]

@[simp]
theorem term_replacePrincipal_succ (j : ℕ) :
    (b.replacePrincipal χ a).term (j + 1) = b.term (j + 1) := by
  simp [replacePrincipal]

/-- Replacing the principal symbol does not change the remainders after `N ≥ 1` terms for the
cutoff `χ` used in the replacement. -/
@[simp]
theorem remainder_replacePrincipal_succ (N : ℕ) :
    (b.replacePrincipal χ a).remainder χ (N + 1) = b.remainder χ (N + 1) := by
  ext1
  funext p
  have h0 : ((b.replacePrincipal χ a).term 0).coefficient p = a.coefficient p := by
    rw [← coefficient_principal, principal_replacePrincipal]
  rw [coefficient_remainder, coefficient_remainder, Finset.sum_range_succ',
    Finset.sum_range_succ', h0, toSymbol_replacePrincipal, ← coefficient_principal]
  simp only [term_replacePrincipal_succ, Symbol.coefficient_add, Pi.add_apply,
    coefficient_cutoffSymbol, HomogeneousSymbol.coefficient_sub, Pi.sub_apply, smul_sub]
  abel

@[simp]
theorem replacePrincipal_principal : b.replacePrincipal χ b.principal = b := by
  simp [replacePrincipal]

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
symbols depending continuously on `t`, and `b_{t₀} = b₀`; their lower order terms do not depend on
`t`. -/
theorem exists_lift_of_continuous {T : Type*} [TopologicalSpace T]
    {a : T → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} (ha : Continuous a)
    {t₀ : T} {b₀ : ClassicalSymbol n V W m} (hb₀ : b₀.principal = a t₀) :
    ∃ b' : T → ClassicalSymbol n V W m, Continuous (fun t => (b' t).toSymbol) ∧
      (∀ t, (b' t).principal = a t) ∧ b' t₀ = b₀ ∧ ∀ t j, (b' t).term (j + 1) = b₀.term (j + 1) :=
  have χ : FrequencyCutoff (CoordinateSpace n) := default
  ⟨fun t => b₀.replacePrincipal χ (a t), (continuous_toSymbol_replacePrincipal χ b₀).comp ha,
    fun t => principal_replacePrincipal χ b₀ (a t), by simp [← hb₀],
    fun t j => term_replacePrincipal_succ χ b₀ (a t) j⟩

end ClassicalSymbol

end TauCeti
