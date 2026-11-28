/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Roots of a polynomial are isolated

A nonzero polynomial over `R` has finitely many roots in an integral domain `A` that is a faithful
`R`-algebra. When `A` carries a T₁ topology, finite sets are closed, so every point `x` of `A` has
a neighbourhood containing no root of the polynomial other than (possibly) `x` itself. Over a
Hausdorff integral domain `R`, if `g w * P.eval w = 0` everywhere for `P ≠ 0` and `g` is continuous
at a non-isolated point `w₀`, then `g w₀ = 0` (`Polynomial.eq_zero_of_mul_eval_eq_zero`).

## Main results

* `Polynomial.eventually_aeval_eq_zero_imp_eq`: near any point `x`, every root of a nonzero
  polynomial is `x`.
* `Polynomial.eq_zero_of_mul_eval_eq_zero`: if `g w * P.eval w = 0` everywhere for `P ≠ 0` and
  `g` is continuous at a non-isolated point `w₀`, then `g w₀ = 0`.
-/

public section

open Filter Topology

namespace Polynomial

/-- The roots of a nonzero polynomial are isolated: near any point `x` of a T₁ faithful algebra
that is an integral domain, every root of the polynomial is `x`. -/
theorem eventually_aeval_eq_zero_imp_eq {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [FaithfulSMul R A] [TopologicalSpace A] [T1Space A] {f : R[X]} (hf : f ≠ 0)
    (x : A) : ∀ᶠ w in 𝓝 x, aeval w f = 0 → w = x := by
  have hfin : {w : A | aeval w f = 0}.Finite := by
    simpa [IsRoot, eval_map_algebraMap] using finite_setOfPred_isRoot
      ((Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R A)).2 hf)
  filter_upwards [(hfin.sdiff (t := {x})).isClosed.compl_mem_nhds (by simp)] with w hw h0
  by_contra hne
  exact hw ⟨h0, hne⟩

/-- If `g : R → R` is continuous at a non-isolated point `w₀` of a Hausdorff integral domain `R`
and `g w * P.eval w = 0` everywhere for a nonzero polynomial `P : R[X]`, then `g w₀ = 0`. -/
theorem eq_zero_of_mul_eval_eq_zero {R : Type*} [CommRing R] [IsDomain R] [TopologicalSpace R]
    [T2Space R] {g : R → R} {w₀ : R} [(𝓝[≠] w₀).NeBot] (hg : ContinuousAt g w₀) {P : R[X]}
    (hP0 : P ≠ 0) (hgP : ∀ w, g w * P.eval w = 0) : g w₀ = 0 := by
  have hne : ∀ᶠ w in 𝓝[≠] w₀, P.eval w ≠ 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_aeval_eq_zero_imp_eq (A := R) hP0 w₀] with w hw hne h0
    exact hne (hw (by simpa using h0))
  have heq : g =ᶠ[𝓝[≠] w₀] fun _ ↦ (0 : R) := by
    filter_upwards [hne] with w hw
    exact (mul_eq_zero.mp (hgP w)).resolve_right hw
  exact tendsto_nhds_unique (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' heq.symm)

end Polynomial
