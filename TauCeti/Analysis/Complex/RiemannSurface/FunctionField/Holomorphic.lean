/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
import Mathlib.RingTheory.Valuation.Integral

/-!
# Meromorphic functions holomorphic on a subset of a Riemann surface

Let `X` be a connected Riemann surface and `s` a subset of `X`. The meromorphic functions on `X`
with no pole in `s` form a `ℂ`-subalgebra of the field `M(X)` of meromorphic functions
(`TauCeti.RiemannSurface.MeromorphicFunction.holomorphicSubalgebra`). For `s` open this is the
ring of meromorphic functions on `X` whose restriction to `s` is holomorphic; for instance, on a
compactified modular curve `X_Γ` and `s` the image of the upper half-plane, it is the ring of
modular functions holomorphic on the open modular curve `Y_Γ`.

At each point `x` the order `ord_x` is an additive valuation on `M(X)`, and `f` has no pole at
`x` exactly when `ord_x f ≥ 0`. So this subalgebra is the intersection, over `x ∈ s`, of the
valuation rings of the `ord_x`. Valuation rings are integrally closed, hence so is the
intersection: a meromorphic function integral over a subalgebra of functions holomorphic on `s`
is itself holomorphic on `s`
(`TauCeti.RiemannSurface.MeromorphicFunction.mem_holomorphicSubalgebra_of_isIntegral`). Concretely,
if `f ⁿ + a_{n-1} f ^ (n-1) + ⋯ + a₀ = 0` with every `aᵢ` finite at `x`, then `f` is finite at `x`.

## Main declarations

* `TauCeti.RiemannSurface.MeromorphicFunction.holomorphicSubalgebra`: the meromorphic functions
  without poles in `s`, characterized by
  `TauCeti.RiemannSurface.MeromorphicFunction.mem_holomorphicSubalgebra`.
* `TauCeti.RiemannSurface.MeromorphicFunction.mem_holomorphicSubalgebra_of_isIntegral`: integral
  dependence over functions holomorphic on `s` preserves holomorphy on `s`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§1, 8.
* Mathlib's `Valuation.Integers.isIntegral_iff_v_le_one` in
  `Mathlib/RingTheory/Valuation/Integral.lean`, applied to the valuations `ord_x`.
-/

public noncomputable section

open OnePoint

open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X] {s : Set X} {f : MeromorphicFunction X}

variable (s) in
/-- The **meromorphic functions holomorphic on `s`**: the `ℂ`-subalgebra of the meromorphic
functions on `X` with no pole in `s`. -/
def holomorphicSubalgebra : Subalgebra ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x ∈ s, f x ≠ ∞}
  mul_mem' {f g} hf hg x hx := by
    rw [← order_nonneg_iff, (order x).map_mul]
    exact add_nonneg (order_nonneg_iff.mpr (hf x hx)) (order_nonneg_iff.mpr (hg x hx))
  add_mem' {f g} hf hg x hx := by
    rw [← order_nonneg_iff]
    exact (le_min (order_nonneg_iff.mpr (hf x hx)) (order_nonneg_iff.mpr (hg x hx))).trans
      ((order x).map_add f g)
  algebraMap_mem' c x _ := by simp

-- Not `@[simp]`: unfolding membership would pre-empt the `simp` lemmas stating that pullbacks and
-- automorphisms preserve the subalgebra.
/-- A meromorphic function is holomorphic on `s` exactly when it has no pole in `s`. -/
theorem mem_holomorphicSubalgebra : f ∈ holomorphicSubalgebra s ↔ ∀ x ∈ s, f x ≠ ∞ :=
  Iff.rfl

/-- **Integral dependence preserves holomorphy.** A meromorphic function integral over a
subalgebra of meromorphic functions holomorphic on `s` is holomorphic on `s`. -/
theorem mem_holomorphicSubalgebra_of_isIntegral {A : Subalgebra ℂ (MeromorphicFunction X)}
    (hA : A ≤ holomorphicSubalgebra s) (hf : IsIntegral A f) : f ∈ holomorphicSubalgebra s := by
  intro x hx
  -- the functions without a pole at `x` are the integers of the valuation `ord_x`
  let v := AddValuation.toValuation (order x)
  have hint : IsIntegral v.integer f :=
    hf.map_of_comp_eq ((A.val : A →+* MeromorphicFunction X).codRestrict v.integer
      fun g ↦ mem_integer_toValuation_order_iff.mpr (hA g.property x hx)) (RingHom.id _) rfl
  exact mem_integer_toValuation_order_iff.mp ((Valuation.integer.integers v).mem_of_integral hint)

end TauCeti.RiemannSurface.MeromorphicFunction
