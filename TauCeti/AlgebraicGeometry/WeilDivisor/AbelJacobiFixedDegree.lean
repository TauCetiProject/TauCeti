/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobiSum
public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegreeAddition

/-!
# Fixed-degree compatibility for Abel-Jacobi divisor classes

This file records fixed-degree effective-divisor and symmetric-power compatibility for the
formal Abel-Jacobi divisor class map.  For an effective divisor `D` of degree `d`, the
underlying divisor-level map sends

`D ↦ [D - deg(D) • [x₀]] ∈ Pic⁰`,

and therefore models the divisor-class shadow of the Abel map on symmetric powers
`Symᵈ X → Pic⁰ X`, `D ↦ 𝒪_X(D - d·x₀)`.

The file does not introduce a parallel fixed-degree Abel-map API.  It states the required
fixed-degree and `Sym.append` facts directly in terms of the existing divisor-level
homomorphisms `weightedAbelJacobiDivisorClass` and `unweightedAbelJacobiDivisorClass`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer C/D, "Relative effective
Cartier divisors and symmetric powers `Symᵈ X`" and the Abel-map lane
`D ↦ 𝒪_X(D - d·x₀)`, using the existing abstract `Pic⁰` quotient before the Picard scheme
exists.  No external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

namespace OrderSystem

variable (S : OrderSystem X G)

variable {d e : ℕ}

noncomputable section

/-! ### Weighted fixed-degree Abel-Jacobi classes -/

/-- Changing only the degree index of a fixed-degree divisor does not change its weighted
Abel-Jacobi class. -/
lemma weightedAbelJacobiDivisorClass_cast (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) {d e : ℕ} (hde : d = e)
    (D : EffectiveDivisorOfDegree X d) :
    S.weightedAbelJacobiDivisorClass w h hx₀
        (WeilDivisor.EffectiveDivisorOfDegree.cast hde D : WeilDivisor X) =
      S.weightedAbelJacobiDivisorClass w h hx₀ (D : WeilDivisor X) := by
  subst e
  simp

/-- The weighted Abel-Jacobi class of the zero effective divisor is zero. -/
lemma weightedAbelJacobiDivisorClass_zero_effective (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (EffectiveDivisorOfDegree.zero X) = 0 := by
  simp

/-- Appending symmetric-power divisors sends their weighted Abel-Jacobi class to the sum of
the two classes. -/
lemma weightedAbelJacobiDivisorClass_ofSym_append (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (s : Sym X d) (t : Sym X e) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (EffectiveDivisorOfDegree.ofSym (s.append t)) =
      S.weightedAbelJacobiDivisorClass w h hx₀ (EffectiveDivisorOfDegree.ofSym s) +
        S.weightedAbelJacobiDivisorClass w h hx₀ (EffectiveDivisorOfDegree.ofSym t) := by
  rw [← EffectiveDivisorOfDegree.add_ofSym]
  exact S.weightedAbelJacobiDivisorClass_add w h hx₀
    (EffectiveDivisorOfDegree.ofSym s) (EffectiveDivisorOfDegree.ofSym t)

/-! ### Unweighted fixed-degree Abel-Jacobi classes -/

/-- Changing only the degree index of a fixed-degree divisor does not change its unweighted
Abel-Jacobi class. -/
lemma unweightedAbelJacobiDivisorClass_cast (h : S.IsUnweightedDegreeZero) (x₀ : X)
    {d e : ℕ} (hde : d = e) (D : EffectiveDivisorOfDegree X d) :
    S.unweightedAbelJacobiDivisorClass h x₀
        (WeilDivisor.EffectiveDivisorOfDegree.cast hde D : WeilDivisor X) =
      S.unweightedAbelJacobiDivisorClass h x₀ (D : WeilDivisor X) := by
  subst e
  simp

/-- The unweighted Abel-Jacobi class of the zero effective divisor is zero. -/
lemma unweightedAbelJacobiDivisorClass_zero_effective (h : S.IsUnweightedDegreeZero) (x₀ : X) :
    S.unweightedAbelJacobiDivisorClass h x₀ (EffectiveDivisorOfDegree.zero X) = 0 := by
  simp

/-- Appending symmetric-power divisors sends their unweighted Abel-Jacobi class to the sum of
the two classes. -/
lemma unweightedAbelJacobiDivisorClass_ofSym_append (h : S.IsUnweightedDegreeZero) (x₀ : X)
    (s : Sym X d) (t : Sym X e) :
    S.unweightedAbelJacobiDivisorClass h x₀ (EffectiveDivisorOfDegree.ofSym (s.append t)) =
    S.unweightedAbelJacobiDivisorClass h x₀ (EffectiveDivisorOfDegree.ofSym s) +
      S.unweightedAbelJacobiDivisorClass h x₀ (EffectiveDivisorOfDegree.ofSym t)
      := by
  rw [← EffectiveDivisorOfDegree.add_ofSym]
  exact map_add (S.unweightedAbelJacobiDivisorClass h x₀)
    (EffectiveDivisorOfDegree.ofSym s : WeilDivisor X)
    (EffectiveDivisorOfDegree.ofSym t : WeilDivisor X)

end

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
