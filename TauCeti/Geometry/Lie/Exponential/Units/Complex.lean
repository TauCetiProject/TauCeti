/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.OneParameter

import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
# Continuous one-parameter subgroups of the complex units

Every continuous homomorphism from the additive real line to `ℂˣ` is an exponential, without
any differentiability hypothesis. The proof lifts the homomorphism through the covering map
`exp : ℂ → ℂ \ {0}`.

## Main results

* `TauCeti.existsUnique_eq_expUnitHom_complex`: continuous homomorphisms `ℝ → ℂˣ` are
  exponentials.
-/

public section
noncomputable section

namespace TauCeti

open Complex

/-- **Continuous homomorphisms `ℝ → ℂˣ` are exponentials.** Every continuous homomorphism from
the additive real line to `ℂˣ` is `t ↦ exp (t * s)` for a unique `s : ℂ`. Unlike
`existsUnique_eq_expUnitHom`, no differentiability is assumed. -/
theorem existsUnique_eq_expUnitHom_complex (φ : Multiplicative ℝ →ₜ* ℂˣ) :
    ∃! s : ℂ, φ = expUnitHom s := by
  refine existsUnique_of_exists_of_unique ?_ fun s t hs ht ↦ expUnitHom_injective (hs ▸ ht)
  -- Lift `φ` through the covering map `exp : ℂ → ℂ \ {0}`; the lift is additive and continuous,
  -- hence real-linear.
  let p : ℂ → {z : ℂ // z ≠ 0} := fun z ↦ ⟨_, z.exp_ne_zero⟩
  have cov : IsCoveringMap p := isCoveringMap_exp
  let f : C(ℝ, {z : ℂ // z ≠ 0}) :=
    ⟨fun t ↦ ⟨φ (.ofAdd t), (φ _).ne_zero⟩, by fun_prop⟩
  obtain ⟨L, ⟨hL0, hL⟩, -⟩ := cov.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [p, f]))
  have hLt (t : ℝ) : exp (L t) = φ (.ofAdd t) :=
    congrArg Subtype.val (congrFun hL t)
  -- The two sides are lifts of the same map and agree at zero.
  have hadd (a t : ℝ) : L (a + t) = L a + L t := by
    exact congrFun (cov.eq_of_comp_eq (L.continuous.comp (continuous_const_add a))
      (continuous_const.add L.continuous)
      (funext fun u ↦ Subtype.ext (by simp [p, exp_add, hLt, ofAdd_add, map_mul])) 0
      (by simp [hL0])) t
  let A : ℝ →+ ℂ := ⟨⟨L, hL0⟩, hadd⟩
  refine ⟨L 1, ContinuousMonoidHom.ext fun t ↦ Units.ext ?_⟩
  rw [← ofAdd_toAdd t, coe_expUnitHom_complex, ← hLt]
  congr 1
  simpa [A] using map_real_smul A L.continuous (Multiplicative.toAdd t) 1

end TauCeti
