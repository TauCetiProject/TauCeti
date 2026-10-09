/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic
-- Proof-only: a residue is nonzero exactly at a unit.
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
-- Proof-only: the two laws take solutions to solutions.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Equation
-- Proof-only: a nonzero solution on an elliptic curve over a field is nonsingular.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
-- Proof-only: over a local ring, a unimodular vector has a unit coordinate.
import TauCeti.LinearAlgebra.Unimodular

/-!
# The Bosma–Lenstra addition laws over a local ring

Let `W'` be a Weierstrass curve over a local ring `R`, and let `P` and `Q` be solutions of its
projective Weierstrass equation whose reductions to the residue field are nonsingular points of
the reduced curve. The two Bosma–Lenstra addition laws `addXYZ` and `dblAddXYZ` do not vanish
simultaneously at the reductions of `P` and `Q`, so one of the six coordinates of the laws at `P`
and `Q` is a unit of `R`. The law owning that coordinate is a unimodular solution `S`, and it
represents the sum at every field-valued specialization where the specializations of `P` and `Q`
are nonsingular: for every ring homomorphism `f : R →+* K` to a field with `f ∘ P` and `f ∘ Q`
nonsingular, `f ∘ S` represents the sum of `f ∘ P` and `f ∘ Q` on `W'.map f`. When `W'` is an
elliptic curve every unimodular solution has nonsingular specializations, so no hypothesis on the
specializations remains.

This is what makes the group law compatible with reduction modulo a valuation: a single `S`
represents both the sum over the fraction field of a valuation ring and the sum of the reductions
over its residue field. Without ellipticity this is the additivity of reduction on the points with
nonsingular reduction.

## Main results

* `WeierstrassCurve.Projective.exists_isUnimodular_map_equiv_add_of_nonsingular`: over a local
  ring, the sum of two solutions with nonsingular reductions has a unimodular representative that
  computes the sum under every ring homomorphism to a field at which both specializations are
  nonsingular.
* `WeierstrassCurve.Projective.exists_isUnimodular_map_equiv_add`: over a local ring, the sum of two
  unimodular solutions on an elliptic curve has a unimodular representative that computes the sum
  under every ring homomorphism to a field.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

universe u v

open IsLocalRing

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R] [IsLocalRing R] {W' : Projective R}

/-- **The sum of two points with nonsingular reduction over a local ring.** Let `P` and `Q` be
solutions of the projective Weierstrass equation of a Weierstrass curve `W'` over a local ring `R`
whose reductions are nonsingular points of the reduced curve. Then there is a unimodular solution
`S` such that, for every ring homomorphism `f : R →+* K` to a field at which `f ∘ P` and `f ∘ Q` are
nonsingular, `f ∘ S` represents the sum of `f ∘ P` and `f ∘ Q` on `W'.map f`. One may take for `S`
whichever of the two Bosma–Lenstra addition laws `addXYZ P Q` and `dblAddXYZ P Q` has a unit
coordinate. -/
theorem exists_isUnimodular_map_equiv_add_of_nonsingular {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPk : (W'.map (residue R)).Nonsingular (residue R ∘ P))
    (hQk : (W'.map (residue R)).Nonsingular (residue R ∘ Q)) :
    ∃ S : Fin 3 → R, W'.Equation S ∧ Module.IsUnimodular R S ∧
      ∀ {K : Type v} [Field K] (f : R →+* K), (W'.map f).Nonsingular (f ∘ P) →
        (W'.map f).Nonsingular (f ∘ Q) → f ∘ S ≈ (W'.map f).add (f ∘ P) (f ∘ Q) := by
  -- one of the laws does not vanish at the reductions, so it has a coordinate that is a unit
  obtain ⟨a, ha, hu⟩ : ∃ a ∈ Set.range (W'.addXYZ P Q) ∪ Set.range (W'.dblAddXYZ P Q),
      IsUnit a := by
    rcases addXYZ_ne_zero_or_dblAddXYZ_ne_zero hPk hQk with h | h
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      rw [map_addXYZ] at hi
      exact ⟨_, .inl ⟨i, rfl⟩, (residue_ne_zero_iff_isUnit _).mp hi⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      rw [map_dblAddXYZ] at hi
      exact ⟨_, .inr ⟨i, rfl⟩, (residue_ne_zero_iff_isUnit _).mp hi⟩
  rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨_, Equation.addXYZ hP hQ, hu.isUnimodular_pi, fun f _ _ ↦ ?_⟩
    -- a nonzero value of `addXYZ` is the sum itself
    have hne : (W'.map f).addXYZ (f ∘ P) (f ∘ Q) ≠ 0 :=
      Function.ne_iff.mpr ⟨i, by rw [map_addXYZ]; exact (hu.map f).ne_zero⟩
    rw [add_of_addXYZ_ne_zero hne, map_addXYZ]
  · refine ⟨_, Equation.dblAddXYZ hP hQ, hu.isUnimodular_pi, fun f hPf hQf ↦ ?_⟩
    -- a nonzero value of `dblAddXYZ` represents the sum
    rw [← map_dblAddXYZ]
    refine dblAddXYZ_equiv_add hPf hQf (Function.ne_iff.mpr ⟨i, ?_⟩)
    rw [map_dblAddXYZ]
    exact (hu.map f).ne_zero

/-- **The sum of two points over a local ring.** Let `P` and `Q` be unimodular solutions of the
projective Weierstrass equation of an elliptic curve `W'` over a local ring `R`. Then there is a
unimodular solution `S` such that, for every ring homomorphism `f : R →+* K` to a field, `f ∘ S`
represents the sum of `f ∘ P` and `f ∘ Q` on `W'.map f`. One may take for `S` whichever of the two
Bosma–Lenstra addition laws `addXYZ P Q` and `dblAddXYZ P Q` has a unit coordinate. -/
theorem exists_isUnimodular_map_equiv_add [W'.IsElliptic] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hP₁ : Module.IsUnimodular R P) (hQ₁ : Module.IsUnimodular R Q) :
    ∃ S : Fin 3 → R, W'.Equation S ∧ Module.IsUnimodular R S ∧
      ∀ {K : Type v} [Field K] (f : R →+* K), f ∘ S ≈ (W'.map f).add (f ∘ P) (f ∘ Q) := by
  -- `P` and `Q` have a unit coordinate, so over a field their images are nonzero solutions, hence
  -- nonsingular
  obtain ⟨i, hi⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.mp hP₁
  obtain ⟨j, hj⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.mp hQ₁
  obtain ⟨S, hS, hS₁, hSf⟩ := exists_isUnimodular_map_equiv_add_of_nonsingular hP hQ
    ((equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, (hi.map _).ne_zero⟩)).mp
      (hP.map _))
    ((equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨j, (hj.map _).ne_zero⟩)).mp
      (hQ.map _))
  exact ⟨S, hS, hS₁, fun f ↦ hSf f
    ((equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, (hi.map f).ne_zero⟩)).mp
      (hP.map f))
    ((equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨j, (hj.map f).ne_zero⟩)).mp
      (hQ.map f))⟩

end WeierstrassCurve.Projective
