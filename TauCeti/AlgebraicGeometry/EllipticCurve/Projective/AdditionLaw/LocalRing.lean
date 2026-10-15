/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
-- Proof-only: an element is a unit exactly when its residue is nonzero.
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
-- Proof-only: the two laws take solutions to solutions.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Equation
-- Proof-only: a solution with nonsingular reduction is nonsingular in every field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
-- Proof-only: a vector with a unit coordinate is unimodular.
import TauCeti.LinearAlgebra.Unimodular

/-!
# The Bosma–Lenstra addition laws over a local ring

Let `W'` be a Weierstrass curve over a local ring `R` with residue field `k`, and let `P` and `Q`
be solutions of its projective Weierstrass equation whose reductions are nonsingular points of the
reduced curve `W'_k`. The two Bosma–Lenstra addition laws `addXYZ` and `dblAddXYZ` do not vanish
simultaneously at the reductions of `P` and `Q`, so one of the six coordinates of `addXYZ P Q` and
`dblAddXYZ P Q` is a unit of `R`. The law owning that coordinate is a unimodular solution `S`, and
it represents the sum at every field-valued specialization at once: for every ring homomorphism
`f : R →+* K` to a field, `f ∘ S` represents the sum of `f ∘ P` and `f ∘ Q` on `W'.map f`.

This is what makes the group law compatible with reduction modulo a valuation: a single `S`
represents both the sum over the fraction field of a valuation ring and the sum of the reductions
over its residue field. No hypothesis on the discriminant is needed, so this applies to the points
with nonsingular reduction on a curve with bad reduction. On an elliptic curve over `R` every
unimodular solution has nonsingular reduction.

## Main results

* `WeierstrassCurve.Projective.exists_isUnimodular_map_equiv_add`: over a local ring, the sum of two
  solutions with nonsingular reduction has a unimodular representative that computes the sum under
  every ring homomorphism to a field.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

universe u v

open IsLocalRing

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R] [IsLocalRing R] {W' : Projective R}

/-- **The sum of two points over a local ring.** Let `P` and `Q` be solutions of the projective
Weierstrass equation of `W'` over a local ring `R` whose reductions are nonsingular points of the
reduced curve. Then there is a unimodular solution `S` such that, for every ring homomorphism
`f : R →+* K` to a field, `f ∘ S` represents the sum of `f ∘ P` and `f ∘ Q` on `W'.map f`. One may
take for `S` whichever of the two Bosma–Lenstra addition laws `addXYZ P Q` and `dblAddXYZ P Q` has a
unit coordinate. -/
theorem exists_isUnimodular_map_equiv_add {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hP₀ : (W'.map (residue R)).Nonsingular (residue R ∘ P))
    (hQ₀ : (W'.map (residue R)).Nonsingular (residue R ∘ Q)) :
    ∃ S : Fin 3 → R, W'.Equation S ∧ Module.IsUnimodular R S ∧
      ∀ {K : Type v} [Field K] (f : R →+* K), f ∘ S ≈ (W'.map f).add (f ∘ P) (f ∘ Q) := by
  -- the laws do not both vanish at the reductions, so one of the six coordinates is a unit
  obtain ⟨a, ha, hu⟩ : ∃ a ∈ Set.range (W'.addXYZ P Q) ∪ Set.range (W'.dblAddXYZ P Q),
      IsUnit a := by
    by_contra! h
    have h₀ {T : Fin 3 → R} (hT : ∀ i, ¬IsUnit (T i)) : residue R ∘ T = 0 :=
      funext fun i ↦ not_not.mp (mt (residue_ne_zero_iff_isUnit _).mp (hT i))
    rcases addXYZ_ne_zero_or_dblAddXYZ_ne_zero hP₀ hQ₀ with h' | h'
    · exact h' (by rw [map_addXYZ]; exact h₀ fun i ↦ h _ (.inl ⟨i, rfl⟩))
    · exact h' (by rw [map_dblAddXYZ]; exact h₀ fun i ↦ h _ (.inr ⟨i, rfl⟩))
  rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨_, Equation.addXYZ hP hQ, hu.isUnimodular_pi, fun f ↦ ?_⟩
    -- a nonzero value of `addXYZ` is the sum itself
    have hne : (W'.map f).addXYZ (f ∘ P) (f ∘ Q) ≠ 0 :=
      Function.ne_iff.mpr ⟨i, by rw [map_addXYZ]; exact (hu.map f).ne_zero⟩
    rw [add_of_addXYZ_ne_zero hne, map_addXYZ]
  · refine ⟨_, Equation.dblAddXYZ hP hQ, hu.isUnimodular_pi, fun f ↦ ?_⟩
    -- a nonzero value of `dblAddXYZ` represents the sum
    rw [← map_dblAddXYZ]
    refine dblAddXYZ_equiv_add (nonsingular_map_of_nonsingular_map_residue hP hP₀ f)
      (nonsingular_map_of_nonsingular_map_residue hQ hQ₀ f) (Function.ne_iff.mpr ⟨i, ?_⟩)
    rw [map_dblAddXYZ]
    exact (hu.map f).ne_zero

end WeierstrassCurve.Projective
