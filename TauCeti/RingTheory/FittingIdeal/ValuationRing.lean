/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ValuationRing
public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import TauCeti.RingTheory.FittingIdeal.Extension
public import TauCeti.RingTheory.FittingIdeal.Matrix

/-!
# Fitting ideals over a valuation ring

Let `V` be a valuation ring, that is a domain whose ideals are totally ordered, and `M` a finitely
presented `V`-module. No noetherian, discreteness or completeness hypothesis is made: the ring of
integers `O_C` of a complete algebraically closed nonarchimedean field is the motivating example.
This file shows that the zeroth Fitting ideal behaves on such modules like the determinant of a
square matrix.

* `Fitt₀(M)` is principal, since it is finitely generated and `V` is a Bézout ring.
* `Fitt₀` is multiplicative on short exact sequences `0 → A → B → C → 0` with `C` finitely
  presented. For `C` torsion, `C` is quadratically presented
  (`TauCeti.IsQuadraticallyPresented.of_isTorsion`), and this is the Dasgupta–Kakde formula for
  quadratically presented quotients; otherwise neither `B` nor `C` is torsion and both sides
  vanish.

These are the facts behind Fargues's degree of a finitely presented torsion module over a
rank-one valuation ring, the valuation of a generator of `Fitt₀(M)`, which is additive in exact
sequences although such modules have no finite composition series in general.

## Main results

* `TauCeti.fittingIdeal_isPrincipal`: over a valuation ring, the Fitting ideals of a finitely
  presented module are principal.
* `TauCeti.fittingIdeal_eq_mul_of_exact_of_finitePresentation`: over a valuation ring,
  `Fitt₀(B) = Fitt₀(A) Fitt₀(C)` for a short exact sequence `0 → A → B → C → 0` of finite modules
  with `C` finitely presented.

## References

* L. Fargues, *La filtration de Harder–Narasimhan en théorie de Dieudonné et applications*,
  J. reine angew. Math. 645 (2010), §2, after Définition 3.
* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023),
  Lemma 2.6.
-/

public section

open Module LinearMap

namespace TauCeti

variable {V M : Type*} [CommRing V] [IsDomain V] [ValuationRing V] [AddCommGroup M] [Module V M]

/-- Over a valuation ring, the Fitting ideals of a finitely presented module are principal. -/
theorem fittingIdeal_isPrincipal [Module.FinitePresentation V M] (k : ℕ) :
    (fittingIdeal V M k).IsPrincipal :=
  IsBezout.isPrincipal_of_FG _ (fittingIdeal_fg k)

variable {A B C : Type*} [AddCommGroup A] [Module V A] [AddCommGroup B] [Module V B]
  [AddCommGroup C] [Module V C] {i : A →ₗ[V] B} {q : B →ₗ[V] C}

/-- **The zeroth Fitting ideal is multiplicative over a valuation ring.** For a short exact
sequence `0 → A → B → C → 0` of finite modules over a valuation ring with `C` finitely presented,
`Fitt₀(B) = Fitt₀(A) Fitt₀(C)`. -/
theorem fittingIdeal_eq_mul_of_exact_of_finitePresentation [Module.Finite V A] [Module.Finite V B]
    [Module.FinitePresentation V C] (hi : Function.Injective i) (hq : Function.Surjective q)
    (hiq : Function.Exact i q) :
    fittingIdeal V B 0 = fittingIdeal V A 0 * fittingIdeal V C 0 := by
  -- A torsion `C` is quadratically presented; otherwise both sides vanish.
  by_cases hC : Module.IsTorsion V C
  · exact fittingIdeal_eq_mul_of_exact hi hq hiq (.of_isTorsion hC)
  -- A torsion `B` would have the torsion quotient `C`.
  have hB : ¬ Module.IsTorsion V B := fun hB ↦ hC fun ⦃c⦄ ↦ by
    obtain ⟨b, rfl⟩ := hq c
    obtain ⟨a, ha⟩ := hB (x := b)
    exact ⟨a, by rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, ha, map_zero]⟩
  rw [← fittingIdeal_zero_ne_bot_iff_isTorsion, not_not] at hB hC
  rw [hB, hC, Ideal.mul_bot]

end TauCeti
