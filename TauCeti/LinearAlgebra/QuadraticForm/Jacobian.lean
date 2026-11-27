/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import TauCeti.LinearAlgebra.QuadraticForm.ExtendScalars
public import TauCeti.LinearAlgebra.QuadraticForm.GeometricRadical
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import TauCeti.RingTheory.Smooth.Hypersurface
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Tower
import TauCeti.RingTheory.MvPolynomial.Quotient.Fiber

/-!
# The Jacobian criterion for a projective quadric

The derivative of a coordinate quadratic form at a vector is its polar pairing with
that vector. Thus the equation and its first partials vanish together precisely on
the quadratic radical. Testing this on nonzero vectors over an algebraic closure detects
nondegeneracy over the original field, including in characteristic two.

Over an arbitrary base ring, fibrewise nondegeneracy is equivalent to the Jacobian
ideals being unit ideals on all the standard affine charts. This condition makes
each chart locally standard smooth.

## References

* SGA 7 II, Exposé XII, §1.1.
-/

public section

open MvPolynomial

namespace QuadraticForm

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

variable (L : Type*) [Field L] [Algebra K L]

/-- A quadratic form is nondegenerate exactly when at every nonzero zero of its equation
over a perfect extension some first partial is nonzero. -/
theorem nondegenerate_iff_forall_exists_aeval_pderiv_ne_zero [PerfectField L]
    (Q : QuadraticForm K (ι → K)) :
    Q.Nondegenerate ↔ ∀ x : ι → L, x ≠ 0 → aeval x Q.toMvPolynomial = 0 →
      ∃ i, aeval x (pderiv i Q.toMvPolynomial) ≠ 0 := by
  rw [← Q.nondegenerate_extendScalars_iff L, nondegenerate_iff_radical_eq_bot_of_perfectField,
    Submodule.eq_bot_iff]
  have hd (x : ι → L) (i : ι) :
      aeval x (pderiv i Q.toMvPolynomial) = (Q.extendScalars L).polarBilin x (Pi.single i 1) := by
    rw [← QuadraticMap.eval_pderiv_toMvPolynomial, toMvPolynomial_extendScalars,
      pderiv_map, ← aeval_eq_eval, aeval_map_algebraMap L]
  simp_rw [hd, ← extendScalars_apply_eq_aeval]
  constructor
  · intro h x hx hq
    by_contra! hall
    exact hx (h x (QuadraticMap.mem_radical_iff.mpr
      ⟨hq, (Pi.basisFun L ι).ext fun i ↦ by simpa using hall i⟩))
  · intro h x hx
    by_contra hne
    obtain ⟨hq, hp⟩ := QuadraticMap.mem_radical_iff.mp hx
    obtain ⟨i, hi⟩ := h x hne hq
    exact hi (DFunLike.congr_fun hp _)

open TauCeti (dehomogenize)

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Over a ring, the Jacobian ideals on all standard charts are unit ideals exactly
when the quadratic form is nondegenerate over every residue field of the base. -/
theorem forall_nondegenerate_extendScalars_residueField_iff
    (Q : QuadraticForm R (Fin (n + 1) → R)) :
    (∀ p : PrimeSpectrum R, (Q.extendScalars p.asIdeal.ResidueField).Nondegenerate) ↔
      ∀ i, Ideal.span (insert (dehomogenize i Q.toMvPolynomial)
        (Set.range fun j ↦ pderiv j (dehomogenize i Q.toMvPolynomial))) = ⊤ := by
  have hmap (i : Fin (n + 1)) (p : PrimeSpectrum R) :
      (Ideal.span (insert (dehomogenize i Q.toMvPolynomial)
        (Set.range fun j ↦ pderiv j (dehomogenize i Q.toMvPolynomial)))).map
          (MvPolynomial.map (algebraMap R p.asIdeal.ResidueField)) =
      Ideal.span (insert (dehomogenize i (Q.extendScalars p.asIdeal.ResidueField).toMvPolynomial)
        (Set.range fun j ↦
          pderiv j (dehomogenize i (Q.extendScalars p.asIdeal.ResidueField).toMvPolynomial))) := by
    simp only [Ideal.map_span, Set.image_insert_eq, ← Set.range_comp, Function.comp_def,
      ← pderiv_map, TauCeti.map_dehomogenize, toMvPolynomial_extendScalars]
  have hf (p : PrimeSpectrum R) :=
    (Q.extendScalars p.asIdeal.ResidueField).nondegenerate_iff_forall_exists_aeval_pderiv_ne_zero
      (AlgebraicClosure p.asIdeal.ResidueField)
  simp_rw [hf, MvPolynomial.IsHomogeneous.forall_exists_aeval_pderiv_ne_zero_iff
    (QuadraticMap.toMvPolynomial_isHomogeneous _)]
  conv_rhs => intro i; rw [Ideal.eq_top_iff_forall_map_residueField_eq_top]
  simp_rw [hmap]
  exact forall_comm

/-- On each standard affine chart of a fibrewise nondegenerate quadric over a ring,
the dehomogenized coordinate ring is locally standard smooth of relative dimension
`n - 1`, where the form has `n + 1` variables. -/
theorem locally_isStandardSmoothOfRelativeDimension_dehomogenize
    (Q : QuadraticForm R (Fin (n + 1) → R))
    (hQ : ∀ p : PrimeSpectrum R, (Q.extendScalars p.asIdeal.ResidueField).Nondegenerate)
    (i : Fin (n + 1)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (n - 1))
      (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span {dehomogenize i Q.toMvPolynomial})) := by
  simpa only [Fintype.card_fin] using
    MvPolynomial.locally_isStandardSmoothOfRelativeDimension_quotient _
      (Q.forall_nondegenerate_extendScalars_residueField_iff.mp hQ i)

end QuadraticForm
