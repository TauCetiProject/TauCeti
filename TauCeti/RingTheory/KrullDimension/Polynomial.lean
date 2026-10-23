/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.KrullDimension.FiniteType
public import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Height of the origin over a closed point

In a polynomial ring over a Noetherian ring, the inverse image of a maximal ideal under
constant coefficient has height equal to the height of that ideal plus the number of
variables. This computes the dimension of the ambient local ring used for hypersurface
singularities over a local base.

## References

* H. Matsumura, *Commutative Algebra*, §13, Theorem 19: the height formula for flat algebras.
-/

public section

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] [IsNoetherianRing R] [Finite σ]

/-- The origin over a closed point has height the height of that point plus the number of
polynomial variables. -/
theorem _root_.Ideal.height_comap_mvPolynomial_constantCoeff (p : Ideal R) [p.IsMaximal] :
    (p.comap (constantCoeff : MvPolynomial σ R →+* R)).height = p.height + Nat.card σ := by
  let P := p.comap (constantCoeff : MvPolynomial σ R →+* R)
  have hsurj : Function.Surjective (constantCoeff : MvPolynomial σ R →+* R) :=
    fun r ↦ ⟨C r, constantCoeff_C σ r⟩
  have : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have : P.LiesOver p := ⟨by ext r; simp [P, Ideal.under_def]⟩
  let Q := P.map (Ideal.Quotient.mk (p.map (algebraMap R (MvPolynomial σ R))))
  have : Q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact Ideal.map_le_iff_le_comap.mpr (by intro r hr; simpa [P] using hr))
  let e : MvPolynomial σ (R ⧸ p) ≃+*
      (MvPolynomial σ R ⧸ p.map (algebraMap R (MvPolynomial σ R))) :=
    (quotientEquivQuotientMvPolynomial (σ := σ) p).toRingEquiv
  have : (Q.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  have hQ : Q.height = Nat.card σ := by
    rw [← e.height_comap Q]
    exact height_eq_natCard_of_isMaximal (k := R ⧸ p) (Q.comap e)
  calc
    _ = p.height + Q.height := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
    _ = _ := by rw [hQ]

/-- Adjoining polynomial coordinates and localizing at the closed origin raises local
Krull dimension by the number of coordinates. -/
theorem ringKrullDim_localization_comap_constantCoeff [IsLocalRing R] :
    ringKrullDim (Localization.AtPrime ((IsLocalRing.maximalIdeal R).comap
      (constantCoeff : MvPolynomial σ R →+* R))) = ringKrullDim R + Nat.card σ := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      ((IsLocalRing.maximalIdeal R).comap (constantCoeff : MvPolynomial σ R →+* R)),
    Ideal.height_comap_mvPolynomial_constantCoeff, WithBot.coe_add,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  -- The two natural-number casts into `WithBot ℕ∞` are definitionally equal.
  rfl

end MvPolynomial
