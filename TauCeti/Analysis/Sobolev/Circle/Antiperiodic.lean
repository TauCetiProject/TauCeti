/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Laurent
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Basic

import TauCeti.Analysis.Fourier.AddCircle

/-!
# Antiperiodic loops in the circle Sobolev spaces

A loop `u` of period `T` is antiperiodic of antiperiod `T / 2` when `u (x + T / 2) = -u x`. Since
`fourier n (T / 2) = (-1) ^ n` (`TauCeti.fourier_coe_half_period`), the rotation by `T / 2`
multiplies the `n`-th Fourier coefficient by `(-1) ^ n`, so the antiperiodic loops are exactly the
loops whose even Fourier coefficients vanish. This file introduces the corresponding subspace
`TauCeti.CircleSobolev.antiperiodic s E` of the Fourier-coefficient Sobolev space `H^s(E)`, the
frequency-support subspace `TauCeti.CircleSobolev.supported s E {n | Odd n}`. It is defined by
the vanishing of the even coefficients, so it does not depend on the period `T`; its
description through the rotation by `T / 2` (`TauCeti.CircleSobolev.rotate_half_period_eq_neg_iff`)
and, for `s > 1/2`, through the continuous representative
(`TauCeti.CircleSobolev.mem_antiperiodic_iff_toContinuousMap`) holds for every period.

A loop of period `T / 2`, read as a loop of period `T`, is invariant under the rotation by `T / 2`.
For such a loop `S` of real-linear maps the first-order operator `L_S ζ = ζ' - S ζ` commutes with
that rotation (`TauCeti.CircleSobolev.loopOperator_rotate_of_invariant`), so it maps
antiperiodic loops to antiperiodic loops (`TauCeti.CircleSobolev.loopOperator_mem_antiperiodic`).
These are the loops twisted by the nontrivial real sign character of the circle of period `T / 2`,
realized on its double cover as the `-1`-eigenspace of the deck rotation.

## Main definitions

* `TauCeti.CircleSobolev.antiperiodic s E`: the subspace of `H^s(E)` of the loops whose even
  Fourier coefficients vanish, that is, `TauCeti.CircleSobolev.supported s E {n | Odd n}`.

## Main statements

* `TauCeti.CircleSobolev.isClosed_antiperiodic`: the subspace is closed
  (`TauCeti.CircleSobolev.isClosed_supported`).
* `TauCeti.CircleSobolev.rotate_half_period_eq_neg_iff`: an element of `H^s(E)` lies in
  `antiperiodic s E` exactly when the rotation by half the period negates it.
* `TauCeti.CircleSobolev.mem_antiperiodic_iff_toContinuousMap`: for `s > 1/2`, exactly when its
  continuous representative satisfies `u (x + T / 2) = -u x`.
* `TauCeti.CircleSobolev.loopOperator_mem_antiperiodic`: for a loop `S` invariant under the
  rotation by `T / 2`, the operator `L_S` preserves antiperiodicity. The inclusions `H^s ⊆ H^t`
  preserve it too (`TauCeti.CircleSobolev.inclusion_mem_supported_iff`).
-/

public section

noncomputable section

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (s E) in
/-- The loops in `H^s(E)` whose even Fourier coefficients vanish, the frequency-support subspace
`CircleSobolev.supported s E {n | Odd n}`. For every period `T` these are the loops antiperiodic
of antiperiod `T / 2` (`CircleSobolev.rotate_half_period_eq_neg_iff`,
`CircleSobolev.mem_antiperiodic_iff_toContinuousMap`). -/
abbrev antiperiodic : Submodule ℂ (CircleSobolev s E) :=
  supported s E {n | Odd n}

theorem mem_antiperiodic_iff {a : CircleSobolev s E} :
    a ∈ antiperiodic s E ↔ ∀ n : ℤ, Even n → a.coeff n = 0 := by
  simp [mem_supported']

/-- The antiperiodic loops form a closed subspace of `H^s(E)`. -/
theorem isClosed_antiperiodic : IsClosed (antiperiodic s E : Set (CircleSobolev s E)) :=
  isClosed_supported _

/-- An element of `H^s(E)` is antiperiodic exactly when the rotation by half the period `T`
negates it. -/
theorem rotate_half_period_eq_neg_iff {T : ℝ} (hT : T ≠ 0) {a : CircleSobolev s E} :
    rotate ((T / 2 : ℝ) : AddCircle T) a = -a ↔ a ∈ antiperiodic s E := by
  rw [CircleSobolev.ext_iff, funext_iff, mem_antiperiodic_iff]
  refine forall_congr' fun n ↦ ?_
  rw [coeff_rotate, coeff_neg, Pi.neg_apply, fourier_coe_half_period hT]
  rcases Int.even_or_odd n with hn | hn
  · rw [hn.neg_one_zpow, one_smul, eq_neg_iff_add_eq_zero, ← two_smul ℂ, smul_eq_zero]
    simp [hn]
  · simp [hn.neg_one_zpow, Int.not_even_iff_odd.2 hn]

/-- For `s > 1/2`, an element of `H^s(E)` is antiperiodic exactly when its continuous
representative `u` satisfies `u (x + T / 2) = -u x`. -/
theorem mem_antiperiodic_iff_toContinuousMap {T : ℝ} [Fact (0 < T)] [CompleteSpace E]
    (hs : 1 / 2 < s) {a : CircleSobolev s E} :
    a ∈ antiperiodic s E ↔
      ∀ x, toContinuousMap T hs a (x + (T / 2 : ℝ)) = -toContinuousMap T hs a x := by
  rw [← rotate_half_period_eq_neg_iff (Fact.out : 0 < T).ne',
    ← (toContinuousMap_injective T hs).eq_iff]
  simp [ContinuousMap.ext_iff]

/-- For a loop `S` invariant under the rotation by half the period, the operator
`L_S ζ = ζ' - S ζ` maps antiperiodic loops to antiperiodic loops. -/
theorem loopOperator_mem_antiperiodic {T : ℝ} [Fact (0 < T)] [FiniteDimensional ℂ E]
    {S : C(AddCircle T, E →L[ℝ] E)} (hS : ∀ x, S (x + (T / 2 : ℝ)) = S x)
    {a : CircleSobolev 1 E} (ha : a ∈ antiperiodic 1 E) :
    loopOperator T S a ∈ antiperiodic 0 E := by
  have hT : T ≠ 0 := (Fact.out : 0 < T).ne'
  rw [← rotate_half_period_eq_neg_iff hT, ← loopOperator_rotate_of_invariant T hS,
    (rotate_half_period_eq_neg_iff hT).2 ha, map_neg]

end CircleSobolev

end TauCeti
