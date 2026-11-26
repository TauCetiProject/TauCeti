/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FittingIdeal.Prod
public import TauCeti.RingTheory.FittingIdeal.ValuationRing
public import TauCeti.RingTheory.Valuation.AddValuation

/-!
# Fargues's degree of a finitely presented torsion module

Let `V` be a valuation ring with an additive valuation `v`, for instance the ring of integers
`O_C` of a complete algebraically closed nonarchimedean field with the valuation normalised by
`v(p) = 1`. Fargues defines the *degree* of a finitely presented torsion `V`-module `M` as the
valuation of its zeroth Fitting ideal, `deg M = v(Fitt₀ M)`. Over a valuation ring `Fitt₀ M` is
principal, and the degree is the valuation of any generator.

The degree is not a length. Over `O_C` the module `O_C ⧸ p^{1/2}` has no finite composition series,
since the submodules `p^q O_C ⧸ p^{1/2} O_C` for rational `0 < q < 1/2` form an infinite chain, yet
its degree is `1/2`. Over a discrete valuation ring with uniformizer `π` the degree is the length
times `v(π)`. Nor does the degree classify modules: `V ⧸ p × V ⧸ p` and `V ⧸ p²` both have
degree `2 v(p)`.

Every finitely presented torsion module over a valuation ring is a finite product of cyclic
modules `∏ i, V ⧸ (x i)` with all `x i ≠ 0`
(`TauCeti.exists_linearEquiv_pi_quotient_span_singleton_of_isTorsion`), and then its degree is
`∑ i, v (x i)` (`AddValuation.fittingDegree_congr`,
`AddValuation.fittingDegree_pi_quotient_span_singleton`).

What makes the degree useful is that it is additive in short exact sequences, as the length would
be. Fargues's degree of a finite flat group scheme over `O_C` is the degree of its module of
invariant differentials, and the additivity is what drives the existence of its Harder–Narasimhan
filtration.

The definition `AddValuation.fittingDegree v M` makes sense for every finite module over every
commutative ring: it is `v` of a chosen generator of `Fitt₀ M` when this ideal is principal, and
`⊤` otherwise. For a valuation `v` which is nonnegative on `V`, the value does not depend on the
chosen generator (`AddValuation.fittingDegree_eq_of_fittingIdeal_eq_span`). A module which is not
torsion, such as `V` itself, has `Fitt₀ = 0` and degree `⊤`.

## Main definitions

* `AddValuation.fittingDegree v M`: Fargues's degree `v(Fitt₀ M)` of a finite module `M`.

## Main results

* `AddValuation.fittingDegree_eq_generator`, `AddValuation.fittingDegree_of_not_isPrincipal`: the
  two cases of the definition.
* `AddValuation.fittingDegree_eq_of_fittingIdeal_eq_span`: if `Fitt₀ M = (x)`, then
  `deg M = v x`.
* `AddValuation.fittingDegree_quotient_span_singleton`: `deg (V ⧸ (x)) = v x`.
* `AddValuation.fittingDegree_pi_quotient_span_singleton`: `deg (∏ i, V ⧸ (x i)) = ∑ i, v (x i)`.
* `AddValuation.fittingDegree_eq_add_of_exact`: over a valuation ring,
  `deg B = deg A + deg C` for a short exact sequence `0 → A → B → C → 0` of finitely presented
  modules.
* `AddValuation.fittingDegree_eq_zero_iff`: over a Bézout ring, `deg M = 0` exactly when
  `M = 0`.
* `AddValuation.fittingDegree_ne_top_iff`: over a Bézout domain, `deg M` is finite exactly when
  `M` is torsion.
* `AddValuation.fittingDegree_baseChange`: the degree is invariant under extension of scalars to
  a ring with a valuation extending `v`.

## References

* L. Fargues, *La filtration de Harder–Narasimhan en théorie de Dieudonné et applications*,
  J. reine angew. Math. 645 (2010), §2, after Définition 3, and §3, Définitions 4 and 5.
-/

public section

open Module LinearMap TauCeti

open scoped TensorProduct

namespace AddValuation

variable {V Γ₀ : Type*} [CommRing V] [LinearOrderedAddCommMonoidWithTop Γ₀]
  (v : AddValuation V Γ₀) {M N : Type*} [AddCommGroup M] [Module V M] [Module.Finite V M]
  [AddCommGroup N] [Module V N] [Module.Finite V N]

variable (M) in
open Classical in
/-- **Fargues's degree** `deg M = v(Fitt₀ M)` of a finite `V`-module `M`: the valuation of a
generator of the zeroth Fitting ideal `Fitt₀ M` when this ideal is principal, as it is for every
finitely presented module over a valuation ring (`TauCeti.fittingIdeal_isPrincipal`), and `⊤`
otherwise. For `v` nonnegative on `V` it does not depend on the generator
(`AddValuation.fittingDegree_eq_of_fittingIdeal_eq_span`). -/
noncomputable def fittingDegree : Γ₀ :=
  if h : (fittingIdeal V M 0).IsPrincipal then
    haveI := h
    v (Submodule.IsPrincipal.generator (fittingIdeal V M 0))
  else ⊤

/-- When `Fitt₀ M` is principal, Fargues's degree of `M` is the valuation of the chosen generator of
`Fitt₀ M`. -/
theorem fittingDegree_eq_generator [(fittingIdeal V M 0).IsPrincipal] :
    v.fittingDegree M = v (Submodule.IsPrincipal.generator (fittingIdeal V M 0)) := by
  rw [fittingDegree, dite_eq_left ‹_›]

/-- When `Fitt₀ M` is not principal, Fargues's degree of `M` is `⊤`. -/
theorem fittingDegree_of_not_isPrincipal (h : ¬ (fittingIdeal V M 0).IsPrincipal) :
    v.fittingDegree M = ⊤ := by
  rw [fittingDegree, dite_eq_right h]

/-- If `Fitt₀ M` is generated by `x`, Fargues's degree of `M` is `v x`, for an additive valuation
`v` which is nonnegative on `V`. -/
theorem fittingDegree_eq_of_fittingIdeal_eq_span (hv : ∀ x, 0 ≤ v x) {x : V}
    (h : fittingIdeal V M 0 = Ideal.span {x}) : v.fittingDegree M = v x := by
  have hp : (fittingIdeal V M 0).IsPrincipal := ⟨x, h⟩
  rw [fittingDegree_eq_generator]
  -- The chosen generator and `x` generate the same ideal, so they divide each other.
  have hgx : Ideal.span {Submodule.IsPrincipal.generator (fittingIdeal V M 0)} = Ideal.span {x} :=
    (fittingIdeal V M 0).span_singleton_generator.trans h
  exact le_antisymm (map_le_map_of_dvd hv (Ideal.span_singleton_le_span_singleton.1 hgx.ge))
    (map_le_map_of_dvd hv (Ideal.span_singleton_le_span_singleton.1 hgx.le))

/-- Isomorphic modules have the same degree. -/
theorem fittingDegree_congr (e : M ≃ₗ[V] N) : v.fittingDegree M = v.fittingDegree N := by
  rw [fittingDegree, fittingDegree, fittingIdeal_congr e 0]

/-- The degree of a cyclic module `V ⧸ (x)` is `v x`. -/
theorem fittingDegree_quotient_span_singleton (hv : ∀ x, 0 ≤ v x) (x : V) :
    v.fittingDegree (V ⧸ Ideal.span {x}) = v x :=
  v.fittingDegree_eq_of_fittingIdeal_eq_span hv (fittingIdeal_quotient_zero _)

/-- The zero module has degree zero. -/
theorem fittingDegree_of_subsingleton (hv : ∀ x, 0 ≤ v x) [Subsingleton M] :
    v.fittingDegree M = 0 := by
  rw [v.fittingDegree_eq_of_fittingIdeal_eq_span hv (x := 1), v.map_one]
  rw [Ideal.span_singleton_one, fittingIdeal_zero_eq_top_iff]
  infer_instance

/-- The degree of a finite product of cyclic modules `∏ i, V ⧸ (x i)` is `∑ i, v (x i)`. -/
theorem fittingDegree_pi_quotient_span_singleton (hv : ∀ x, 0 ≤ v x) {ι : Type*} [Fintype ι]
    (x : ι → V) : v.fittingDegree ((i : ι) → V ⧸ Ideal.span {x i}) = ∑ i, v (x i) := by
  rw [v.fittingDegree_eq_of_fittingIdeal_eq_span hv (x := ∏ i, x i), map_prod]
  simp only [fittingIdeal_pi_zero, fittingIdeal_quotient_zero, Ideal.prod_span_singleton]

/-- The degree does not classify modules: `V ⧸ (x) × V ⧸ (x)` and `V ⧸ (x ^ 2)` both have degree
`2 v(x)`, although their first Fitting ideals `(x)` and `V` differ. -/
example (hv : ∀ x, 0 ≤ v x) (x : V) :
    v.fittingDegree ((V ⧸ Ideal.span {x}) × (V ⧸ Ideal.span {x})) =
      v.fittingDegree (V ⧸ Ideal.span {x ^ 2}) := by
  rw [v.fittingDegree_quotient_span_singleton hv, pow_two,
    v.fittingDegree_eq_of_fittingIdeal_eq_span hv (x := x * x)]
  rw [fittingIdeal_prod_zero, fittingIdeal_quotient_zero, Ideal.span_singleton_mul_span_singleton]

/-- A module which is not torsion, such as `V` itself, has `Fitt₀ = 0` and degree `⊤`. -/
example (hv : ∀ x, 0 ≤ v x) [Nontrivial V] : v.fittingDegree V = ⊤ := by
  rw [v.fittingDegree_eq_of_fittingIdeal_eq_span hv (x := 0), v.map_zero]
  rw [Ideal.span_singleton_eq_bot.2 rfl]
  exact fittingIdeal_eq_bot_of_lt_finrank (by simp)

section IsBezout

variable [IsBezout V]

/-- Over a Bézout ring, such as a valuation ring, Fargues's degree of a finitely presented module is
the valuation of a generator of its zeroth Fitting ideal, with no condition on the valuation. -/
theorem exists_fittingIdeal_eq_span_and_fittingDegree_eq [Module.FinitePresentation V M] :
    ∃ x : V, fittingIdeal V M 0 = Ideal.span {x} ∧ v.fittingDegree M = v x := by
  have := fittingIdeal_isPrincipal (V := V) (M := M) 0
  exact ⟨_, (fittingIdeal V M 0).span_singleton_generator.symm, v.fittingDegree_eq_generator⟩

/-- Over a Bézout ring, such as a valuation ring, with an additive valuation `v` which is
nonnegative and vanishes only at units, a finitely presented module has degree zero exactly when it
is zero. -/
theorem fittingDegree_eq_zero_iff (hv : ∀ x, 0 ≤ v x) (hunit : ∀ x, v x = 0 → IsUnit x)
    [Module.FinitePresentation V M] : v.fittingDegree M = 0 ↔ Subsingleton M := by
  obtain ⟨x, hx, hd⟩ := v.exists_fittingIdeal_eq_span_and_fittingDegree_eq (M := M)
  rw [hd, ← fittingIdeal_zero_eq_top_iff (R := V) (M := M), hx, Ideal.span_singleton_eq_top]
  exact ⟨hunit x, map_eq_zero_of_isUnit hv⟩

/-- **Fargues's degree is invariant under extension of scalars.** Let `W` be a `V`-algebra with an
additive valuation `w` which is nonnegative on `W` and extends `v`. Then a finitely presented
`V`-module `M` and its base change `W ⊗[V] M` have the same degree. This applies to an extension
of valuation rings, such as `O_K → O_C` for a complete algebraically closed field `C` containing a
valued field `K`. -/
theorem fittingDegree_baseChange {W : Type*} [CommRing W] [Algebra V W] (w : AddValuation W Γ₀)
    (hw : ∀ x, 0 ≤ w x) (hvw : ∀ a, w (algebraMap V W a) = v a)
    [Module.FinitePresentation V M] : w.fittingDegree (W ⊗[V] M) = v.fittingDegree M := by
  obtain ⟨x, hx, hd⟩ := v.exists_fittingIdeal_eq_span_and_fittingDegree_eq (M := M)
  rw [hd, ← hvw]
  refine w.fittingDegree_eq_of_fittingIdeal_eq_span hw ?_
  rw [fittingIdeal_baseChange, hx, Ideal.map_span, Set.image_singleton]

/-- Over a Bézout ring, such as a valuation ring, the degree of a product of finitely presented
modules is the sum of their degrees. -/
theorem fittingDegree_prod (hv : ∀ x, 0 ≤ v x) [Module.FinitePresentation V M]
    [Module.FinitePresentation V N] :
    v.fittingDegree (M × N) = v.fittingDegree M + v.fittingDegree N := by
  obtain ⟨a, ha, hda⟩ := v.exists_fittingIdeal_eq_span_and_fittingDegree_eq (M := M)
  obtain ⟨b, hb, hdb⟩ := v.exists_fittingIdeal_eq_span_and_fittingDegree_eq (M := N)
  rw [hda, hdb, ← v.map_mul]
  refine v.fittingDegree_eq_of_fittingIdeal_eq_span hv ?_
  rw [fittingIdeal_prod_zero, ha, hb, Ideal.span_singleton_mul_span_singleton]

variable [IsDomain V] in
/-- Over a Bézout domain, such as a valuation ring, with an additive valuation `v` which is infinite
only at zero, a finitely presented module has finite degree exactly when it is torsion. -/
theorem fittingDegree_ne_top_iff (hsupp : ∀ x, v x = ⊤ → x = 0)
    [Module.FinitePresentation V M] : v.fittingDegree M ≠ ⊤ ↔ Module.IsTorsion V M := by
  obtain ⟨x, hx, hd⟩ := v.exists_fittingIdeal_eq_span_and_fittingDegree_eq (M := M)
  rw [hd, ← fittingIdeal_zero_ne_bot_iff_isTorsion, hx, Ne, Ne, Ideal.span_singleton_eq_bot]
  exact not_congr ⟨hsupp x, fun h ↦ h ▸ v.map_zero⟩

end IsBezout

section ValuationRing

variable [IsDomain V] [ValuationRing V]

variable {A B C : Type*} [AddCommGroup A] [Module V A] [AddCommGroup B] [Module V B]
  [AddCommGroup C] [Module V C] {i : A →ₗ[V] B} {q : B →ₗ[V] C}

/-- **Fargues's degree is additive.** Over a valuation ring with an additive valuation `v`
nonnegative on it, `deg B = deg A + deg C` for a short exact sequence `0 → A → B → C → 0` of
finitely presented modules. -/
theorem fittingDegree_eq_add_of_exact (hv : ∀ x, 0 ≤ v x) [Module.FinitePresentation V A]
    [Module.Finite V B] [Module.FinitePresentation V C] (hi : Function.Injective i)
    (hq : Function.Surjective q) (hiq : Function.Exact i q) :
    v.fittingDegree B = v.fittingDegree A + v.fittingDegree C := by
  obtain ⟨a, ha, hda⟩ := v.exists_fittingIdeal_eq_span_and_fittingDegree_eq (M := A)
  obtain ⟨c, hc, hdc⟩ := v.exists_fittingIdeal_eq_span_and_fittingDegree_eq (M := C)
  rw [hda, hdc, ← v.map_mul]
  refine v.fittingDegree_eq_of_fittingIdeal_eq_span hv ?_
  rw [fittingIdeal_eq_mul_of_exact_of_finitePresentation hi hq hiq, ha, hc,
    Ideal.span_singleton_mul_span_singleton]

end ValuationRing

end AddValuation
