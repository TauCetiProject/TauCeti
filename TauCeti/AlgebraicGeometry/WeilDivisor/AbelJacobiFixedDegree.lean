/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobiFiniteSum
public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegreeAddition

/-!
# Abel maps on fixed-degree effective divisors

This file restricts the formal Abel-Jacobi divisor class map to the fixed-degree effective
divisor model of symmetric powers.  For an effective divisor `D` of degree `d`, the map sends

`D ↦ [D - deg(D) • [x₀]] ∈ Pic⁰`,

and therefore models the divisor-class shadow of the Abel map
`Symᵈ X → Pic⁰ X`, `D ↦ 𝒪_X(D - d·x₀)`.

The file records the weighted and unweighted forms, their evaluation on finitely supported
multiplicities, and the compatibility with fixed-degree addition and with `Sym.append`.

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

/-! ### Weighted fixed-degree Abel maps -/

/-- The weighted Abel map on effective divisors of fixed degree.

For a geometric weight `w x = [κ(x) : k]` and a rational base point `x₀` with `w x₀ = 1`,
this sends an effective divisor `D` to the class of `D - deg_w(D) • [x₀]` in the abstract
weighted `Pic⁰`. -/
noncomputable abbrev weightedAbelMapOfDegree (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (d : ℕ) :
    EffectiveDivisorOfDegree X d → S.picZero w h :=
  fun D => S.weightedAbelJacobiDivisorClass w h hx₀ (D : WeilDivisor X)

/-- Changing only the degree index of a fixed-degree divisor does not change its weighted Abel
map. -/
@[simp]
lemma weightedAbelMapOfDegree_cast (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) {d e : ℕ} (hde : d = e)
    (D : EffectiveDivisorOfDegree X d) :
    S.weightedAbelMapOfDegree w h hx₀ e (WeilDivisor.EffectiveDivisorOfDegree.cast hde D) =
      S.weightedAbelMapOfDegree w h hx₀ d D := by
  subst e
  simp [weightedAbelMapOfDegree]

/-- The weighted Abel map sends the zero effective divisor to zero. -/
@[simp]
lemma weightedAbelMapOfDegree_zero (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedAbelMapOfDegree w h hx₀ 0 (EffectiveDivisorOfDegree.zero X) = 0 := by
  simp [weightedAbelMapOfDegree]

/-- The weighted Abel map on the symmetric-power model. -/
noncomputable abbrev weightedAbelMapSym (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (d : ℕ) : Sym X d → S.picZero w h :=
  fun s => S.weightedAbelMapOfDegree w h hx₀ d (EffectiveDivisorOfDegree.ofSym s)

/-- The weighted Abel map on symmetric powers is induced by the fixed-degree divisor attached
to the symmetric-power point. -/
@[simp]
lemma weightedAbelMapSym_apply (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (s : Sym X d) :
    S.weightedAbelMapSym w h hx₀ d s =
      S.weightedAbelMapOfDegree w h hx₀ d (EffectiveDivisorOfDegree.ofSym s) :=
  rfl

/-- The weighted Abel map sends appended symmetric-power divisors to the sum of their Abel
classes. -/
@[simp]
lemma weightedAbelMapSym_append (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (s : Sym X d) (t : Sym X e) :
    S.weightedAbelMapSym w h hx₀ (d + e) (s.append t) =
      S.weightedAbelMapSym w h hx₀ d s + S.weightedAbelMapSym w h hx₀ e t := by
  rw [weightedAbelMapSym_apply, ← EffectiveDivisorOfDegree.add_ofSym]
  exact S.weightedAbelJacobiDivisorClass_add w h hx₀
    (EffectiveDivisorOfDegree.ofSym s) (EffectiveDivisorOfDegree.ofSym t)

/-! ### Unweighted fixed-degree Abel maps -/

/-- The unweighted Abel map on effective divisors of fixed degree. -/
noncomputable abbrev unweightedAbelMapOfDegree (h : S.IsUnweightedDegreeZero) (x₀ : X) (d : ℕ) :
    EffectiveDivisorOfDegree X d → S.unweightedPicZero h :=
  fun D => S.unweightedAbelJacobiDivisorClass h x₀ (D : WeilDivisor X)

/-- Changing only the degree index of a fixed-degree divisor does not change its unweighted
Abel map. -/
@[simp]
lemma unweightedAbelMapOfDegree_cast (h : S.IsUnweightedDegreeZero) (x₀ : X)
    {d e : ℕ} (hde : d = e) (D : EffectiveDivisorOfDegree X d) :
    S.unweightedAbelMapOfDegree h x₀ e (WeilDivisor.EffectiveDivisorOfDegree.cast hde D) =
      S.unweightedAbelMapOfDegree h x₀ d D := by
  subst e
  simp [unweightedAbelMapOfDegree]

/-- The unweighted Abel map sends the zero effective divisor to zero. -/
@[simp]
lemma unweightedAbelMapOfDegree_zero (h : S.IsUnweightedDegreeZero) (x₀ : X) :
    S.unweightedAbelMapOfDegree h x₀ 0 (EffectiveDivisorOfDegree.zero X) = 0 := by
  simp [unweightedAbelMapOfDegree]

/-- The unweighted Abel map on the symmetric-power model. -/
noncomputable abbrev unweightedAbelMapSym (h : S.IsUnweightedDegreeZero) (x₀ : X) (d : ℕ) :
    Sym X d → S.unweightedPicZero h :=
  fun s => S.unweightedAbelMapOfDegree h x₀ d (EffectiveDivisorOfDegree.ofSym s)

/-- The unweighted Abel map on symmetric powers is induced by the fixed-degree divisor attached
to the symmetric-power point. -/
@[simp]
lemma unweightedAbelMapSym_apply (h : S.IsUnweightedDegreeZero) (x₀ : X) (s : Sym X d) :
    S.unweightedAbelMapSym h x₀ d s =
      S.unweightedAbelMapOfDegree h x₀ d (EffectiveDivisorOfDegree.ofSym s) :=
  rfl

/-- The unweighted Abel map sends appended symmetric-power divisors to the sum of their Abel
classes. -/
@[simp]
lemma unweightedAbelMapSym_append (h : S.IsUnweightedDegreeZero) (x₀ : X)
    (s : Sym X d) (t : Sym X e) :
    S.unweightedAbelMapSym h x₀ (d + e) (s.append t) =
      S.unweightedAbelMapSym h x₀ d s + S.unweightedAbelMapSym h x₀ e t := by
  rw [unweightedAbelMapSym_apply, ← EffectiveDivisorOfDegree.add_ofSym]
  change S.unweightedAbelJacobiDivisorClass h x₀
      (EffectiveDivisorOfDegree.ofSym s + EffectiveDivisorOfDegree.ofSym t) =
    S.unweightedAbelJacobiDivisorClass h x₀ (EffectiveDivisorOfDegree.ofSym s) +
      S.unweightedAbelJacobiDivisorClass h x₀ (EffectiveDivisorOfDegree.ofSym t)
  rw [S.unweightedAbelJacobiDivisorClass_eq_weighted]
  exact S.weightedAbelJacobiDivisorClass_add (fun _ : X => (1 : ℤ))
    (show S.IsWeightedDegreeZero (fun _ : X => (1 : ℤ)) from h) (x₀ := x₀) rfl
    (EffectiveDivisorOfDegree.ofSym s) (EffectiveDivisorOfDegree.ofSym t)

end

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
