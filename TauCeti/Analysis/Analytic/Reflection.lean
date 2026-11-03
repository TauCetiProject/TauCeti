/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Vanishing order and reflection

For a nonzero analytic germ satisfying `f (2a - z) = ε • f z`, the scalar `ε` is
`(-1) ^ ord_a(f)`. Thus a reflection functional equation determines the parity of the
vanishing order. The statement uses an equality of germs, not a global functional equation.
-/

public section

open Filter Topology

/-- The scalar in a reflection equation for a nonzero analytic germ is the sign of its
vanishing order. This applies to vector-valued germs as well as scalar-valued ones. -/
theorem AnalyticAt.neg_one_pow_analyticOrderNatAt_eq_of_reflection
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {f : 𝕜 → E} {a ε : 𝕜} (hf : AnalyticAt 𝕜 f a)
    (hfinite : analyticOrderAt f a ≠ ⊤)
    (heq : (fun z ↦ f (2 * a - z)) =ᶠ[𝓝 a] fun z ↦ ε • f z) :
    (-1 : 𝕜) ^ analyticOrderNatAt f a = ε := by
  have hn := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp
    (Nat.cast_analyticOrderNatAt hfinite).symm
  have hd := heq.iteratedDeriv_eq (analyticOrderNatAt f a)
  rw [iteratedDeriv_comp_const_sub, iteratedDeriv_fun_const_smul_field] at hd
  have hcenter : 2 * a - a = a := by ring
  simp only [hcenter] at hd
  exact smul_left_injective 𝕜 hn.2 hd
