/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Generator
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Separation

/-!
# Meromorphic functions with a single pole, and point separation

Let `X` be a compact connected Hausdorff Riemann surface. This file produces meromorphic functions
on `X` with a pole of exactly prescribed order at one point and no other poles, and deduces the
separation properties of the field `M(X)` of meromorphic functions on which its algebraic
description rests.

Along the staircase `k[x]`, `k = 0, 1, 2, …`, Riemann–Roch eventually raises `h⁰` by one at every
step (`TauCeti.RiemannSurface.eventually_finrank_divisorSheaf_add_nsmul_ofPoint_succ`), and a
section of `𝒪((k + 1)[x])` which is not a section of `𝒪(k[x])` is a meromorphic function with a
pole of order exactly `k + 1` at `x` and no other pole
(`TauCeti.RiemannSurface.MeromorphicFunction.exists_order_eq_neg_of_finrank_lt`). Consequently:

* the meromorphic functions separate points: every point is the only pole of some meromorphic
  function, so two distinct points take different values under some meromorphic function;
* the order `ord_x : M(X) → ℤ ∪ {∞}` at a point is surjective, so it is a normalized discrete
  valuation, and different points have different orders;
* for a finite holomorphic map `β : X → ℙ¹`, the field `M(X)` has degree exactly `deg β` over the
  rational functions `ℂ(t)` pulled back along `β`, and is generated over `ℂ(t)` by a single
  meromorphic function, since the points of an unbranched fibre are pairwise separated.

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.eventually_exists_order_eq_neg`: for all large `k`,
  a meromorphic function with a pole of order exactly `k` at `x` and no other pole.
* `TauCeti.RiemannSurface.MeromorphicFunction.exists_apply_eq_infty_and_forall_ne_infty`: a
  meromorphic function whose only pole is `x`.
* `TauCeti.RiemannSurface.MeromorphicFunction.exists_apply_ne_apply_of_ne`: meromorphic functions
  separate points.
* `TauCeti.RiemannSurface.MeromorphicFunction.order_surjective`: `ord_x` is surjective.
* `TauCeti.RiemannSurface.MeromorphicFunction.order_injective`: `x ↦ ord_x` is injective.
* `TauCeti.RiemannSurface.MeromorphicFunction.exists_adjoin_simple_eq_top`: `M(X)` is a simple
  extension of `ℂ(t)`.
* `TauCeti.RiemannSurface.MeromorphicFunction.finrank_ratFunc_eq_degree`: the degree theorem
  `[M(X) : ℂ(t)] = deg β`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, Springer, 1981, §16 (Riemann–Roch for
  divisors), Theorem 14.12 (a meromorphic function with a single pole) and Corollary 8.3 with
  Theorem 14.13 (the degree of the field of meromorphic functions).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, Corollary 1.93, for the equality `[M(X) : ℂ(t)] = degree β`.
-/

public noncomputable section

open CategoryTheory Filter Opposite OnePoint
open TauCeti.Topology TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]

/-- **Functions with a single pole of prescribed order.** On a compact connected Riemann surface,
for all large `k` some meromorphic function has a pole of
order exactly `k` at `x` and is holomorphic at every other point. -/
theorem eventually_exists_order_eq_neg (x : X) :
    ∀ᶠ k : ℕ in atTop, ∃ f : MeromorphicFunction X,
      order x f = ((-k : ℤ) : WithTop ℤ) ∧ ∀ y ≠ x, 0 ≤ order y f := by
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (eventually_finrank_divisorSheaf_add_nsmul_ofPoint_succ 0 x)
  refine eventually_atTop.2 ⟨N + 1, fun k hk ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj := hN j (by omega)
  rw [zero_add, zero_add, succ_nsmul, (divisorSheafSectionsEquiv _ ⊤).finrank_eq,
    (divisorSheafSectionsEquiv _ ⊤).finrank_eq] at hj
  obtain ⟨f, hfx, hf⟩ :=
    exists_order_eq_neg_of_finrank_lt (D := j • WeilDivisor.ofPoint x) (x := x) (by omega)
  -- The values of `ofPoint x`, read off its `WeilDivisor.coeff` lemmas.
  have hpx : WeilDivisor.ofPoint x x = 1 := WeilDivisor.coeff_ofPoint_self x
  refine ⟨f, by simp [hfx, hpx], fun y hy ↦ ?_⟩
  have hpy : WeilDivisor.ofPoint x y = 0 := WeilDivisor.coeff_ofPoint_of_ne hy
  simpa [hpy] using hf y

/-- **Meromorphic functions separate points.** On a compact connected Riemann surface,
every point `x` is the only pole of some meromorphic function. -/
theorem exists_apply_eq_infty_and_forall_ne_infty (x : X) :
    ∃ f : MeromorphicFunction X, f x = ∞ ∧ ∀ y ≠ x, f y ≠ ∞ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_exists_order_eq_neg x)
  obtain ⟨f, hfx, hf⟩ := hN (N + 1) N.le_succ
  refine ⟨f, order_neg_iff.1 ?_, fun y hy ↦ order_nonneg_iff.1 (hf y hy)⟩
  rw [hfx]
  exact_mod_cast (by omega : (-(N + 1 : ℕ) : ℤ) < 0)

/-- **Meromorphic functions separate points.** On a compact connected Riemann surface,
two distinct points take different values under some meromorphic
function. -/
theorem exists_apply_ne_apply_of_ne {x y : X} (hxy : x ≠ y) :
    ∃ f : MeromorphicFunction X, f x ≠ f y := by
  obtain ⟨f, hfx, hf⟩ := exists_apply_eq_infty_and_forall_ne_infty x
  exact ⟨f, by rw [hfx]; exact (hf y hxy.symm).symm⟩

/-- **The order at a point is surjective.** On a compact connected Riemann surface,
every integer is the order at `x` of some meromorphic function, so
`ord_x` is a normalized discrete valuation of `M(X)`. -/
theorem order_surjective (x : X) : Function.Surjective (order (X := X) x) := by
  -- The quotient of functions with poles of orders `N + 1` and `N` at `x` and no other poles
  -- has order `1` at `x`, and its integer powers realize every integer.
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_exists_order_eq_neg x)
  obtain ⟨f, hf, -⟩ := hN N le_rfl
  obtain ⟨g, hg, -⟩ := hN (N + 1) N.le_succ
  have ht : order x (f / g) = 1 := by
    rw [AddValuation.map_div, hf, hg]
    norm_cast
    omega
  intro n
  induction n using WithTop.recTopCoe with
  | top => exact ⟨0, AddValuation.map_zero _⟩
  | coe m =>
    refine ⟨(f / g) ^ m, ?_⟩
    cases m with
    | ofNat n => simp [AddValuation.map_pow, ht]
    | negSucc n =>
      rw [zpow_negSucc, AddValuation.map_inv, AddValuation.map_pow, ht, nsmul_one]
      norm_cast

/-- **Different points have different orders.** On a compact connected Riemann surface,
the order `ord_x` determines the point `x`. -/
theorem order_injective : Function.Injective (order (X := X)) := by
  intro x y hxy
  by_contra hne
  obtain ⟨f, hfx, hf⟩ := exists_apply_eq_infty_and_forall_ne_infty x
  have hfy := order_neg_iff.2 hfx
  rw [hxy] at hfy
  exact hf y (Ne.symm hne) (order_neg_iff.1 hfy)

section RatFunc

variable (β : FiniteHolomorphicMap X (OnePoint ℂ))
  [Algebra (RatFunc ℂ) (MeromorphicFunction X)]

/-- **The meromorphic function field is a simple extension of `ℂ(t)`.** Let `β : X → ℙ¹` be a
finite holomorphic map from a compact connected Riemann surface, and let `ℂ(t)` act on `M(X)` by
pullback along `β`. Then some meromorphic function generates `M(X)` over `ℂ(t)`. -/
theorem exists_adjoin_simple_eq_top
    (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
      ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom) :
    ∃ f : MeromorphicFunction X, IntermediateField.adjoin (RatFunc ℂ) {f} = ⊤ := by
  obtain ⟨y₀, hy₀⟩ := β.finite_branchValues.infinite_compl.nonempty
  obtain ⟨f, hf, hinj⟩ := exists_forall_ne_infty_and_injOn (β.finite_fiber y₀)
    fun _ _ _ _ hxx' ↦ exists_apply_ne_apply_of_ne hxx'
  exact ⟨f, adjoin_simple_eq_top_of_injOn_fiber β h f hy₀ hf hinj⟩

/-- **The degree theorem.** Let `β : X → ℙ¹` be a finite holomorphic map from a compact connected
Riemann surface, and let `ℂ(t)` act on `M(X)` by pullback along
`β`. Then `M(X)` has degree exactly `deg β` over `ℂ(t)`. -/
theorem finrank_ratFunc_eq_degree
    (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
      ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom) :
    Module.finrank (RatFunc ℂ) (MeromorphicFunction X) = degree β := by
  obtain ⟨y₀, hy₀⟩ := β.finite_branchValues.infinite_compl.nonempty
  exact finrank_ratFunc_eq_degree_of_pairwise_separated_fiber β h hy₀
    fun _ _ _ _ hxx' ↦ exists_apply_ne_apply_of_ne hxx'

end RatFunc

end TauCeti.RiemannSurface.MeromorphicFunction
