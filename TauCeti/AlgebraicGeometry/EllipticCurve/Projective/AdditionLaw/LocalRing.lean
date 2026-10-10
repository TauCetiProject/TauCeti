/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic
-- Proof-only: the two laws take solutions to solutions.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Equation
-- Proof-only: a nonzero solution on an elliptic curve over a field is nonsingular.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
-- Proof-only: over a local ring, a unimodular vector has a unit coordinate.
import TauCeti.LinearAlgebra.Unimodular

/-!
# The Bosma–Lenstra addition laws over a local ring

Let `W'` be an elliptic curve over a local ring `R`, and let `P` and `Q` be unimodular solutions of
its projective Weierstrass equation. The six coordinates of the two Bosma–Lenstra addition laws
`addXYZ P Q` and `dblAddXYZ P Q` generate the unit ideal
(`WeierstrassCurve.Projective.span_range_addXYZ_union_range_dblAddXYZ_eq_top`), so in a local ring
one of them is a unit. The law owning that coordinate is again a unimodular solution `S`, and it
represents the sum at every field-valued specialization at once: for every ring homomorphism
`f : R →+* K` to a field, `f ∘ S` represents the sum of `f ∘ P` and `f ∘ Q` on `W'.map f`.

This is what makes the group law compatible with reduction modulo a valuation: a single `S`
represents both the sum over the fraction field of a valuation ring and the sum of the reductions
over its residue field.

## Main results

* `WeierstrassCurve.Projective.exists_isUnimodular_map_equiv_add`: over a local ring, the sum of two
  unimodular solutions has a unimodular representative that computes the sum under every ring
  homomorphism to a field.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

universe u v

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R] [IsLocalRing R] {W' : Projective R} [W'.IsElliptic]

/-- **The sum of two points over a local ring.** Let `P` and `Q` be unimodular solutions of the
projective Weierstrass equation of an elliptic curve `W'` over a local ring `R`. Then there is a
unimodular solution `S` such that, for every ring homomorphism `f : R →+* K` to a field, `f ∘ S`
represents the sum of `f ∘ P` and `f ∘ Q` on `W'.map f`. One may take for `S` whichever of the two
Bosma–Lenstra addition laws `addXYZ P Q` and `dblAddXYZ P Q` has a unit coordinate. -/
theorem exists_isUnimodular_map_equiv_add {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hP₁ : Module.IsUnimodular R P) (hQ₁ : Module.IsUnimodular R Q) :
    ∃ S : Fin 3 → R, W'.Equation S ∧ Module.IsUnimodular R S ∧
      ∀ {K : Type v} [Field K] (f : R →+* K), f ∘ S ≈ (W'.map f).add (f ∘ P) (f ∘ Q) := by
  -- the six coordinates generate the unit ideal, so one of them lies outside the maximal ideal
  obtain ⟨a, ha, hu⟩ : ∃ a ∈ Set.range (W'.addXYZ P Q) ∪ Set.range (W'.dblAddXYZ P Q),
      IsUnit a := by
    by_contra! h
    refine (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp ?_)
    rw [← span_range_addXYZ_union_range_dblAddXYZ_eq_top hP hQ hP₁ hQ₁, Ideal.span_le]
    exact fun a ha ↦ (IsLocalRing.mem_maximalIdeal a).mpr (h a ha)
  -- over a field, the images of `P` and `Q` are nonzero solutions, hence nonsingular
  have hns {K : Type v} [Field K] (f : R →+* K) {T : Fin 3 → R} (hT : W'.Equation T)
      (hT₁ : Module.IsUnimodular R T) : (W'.map f).Nonsingular (f ∘ T) := by
    obtain ⟨i, hi⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.mp hT₁
    exact (equation_iff_nonsingular_of_ne_zero
      (Function.ne_iff.mpr ⟨i, (hi.map f).ne_zero⟩)).mp (hT.map f)
  rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨_, Equation.addXYZ hP hQ, hu.isUnimodular_pi, fun f ↦ ?_⟩
    -- a nonzero value of `addXYZ` is the sum itself
    have hne : (W'.map f).addXYZ (f ∘ P) (f ∘ Q) ≠ 0 :=
      Function.ne_iff.mpr ⟨i, by rw [map_addXYZ]; exact (hu.map f).ne_zero⟩
    rw [add_of_addXYZ_ne_zero hne, map_addXYZ]
  · refine ⟨_, Equation.dblAddXYZ hP hQ, hu.isUnimodular_pi, fun f ↦ ?_⟩
    -- a nonzero value of `dblAddXYZ` represents the sum
    rw [← map_dblAddXYZ]
    refine dblAddXYZ_equiv_add (hns f hP hP₁) (hns f hQ hQ₁) (Function.ne_iff.mpr ⟨i, ?_⟩)
    rw [map_dblAddXYZ]
    exact (hu.map f).ne_zero

end WeierstrassCurve.Projective
