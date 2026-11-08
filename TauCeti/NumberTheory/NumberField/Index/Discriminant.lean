/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import TauCeti.NumberTheory.NumberField.Index.PowerBasis
public import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Perfect
import TauCeti.NumberTheory.NumberField.Discriminant.OfIntegralBasis
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The index formula

For an integral primitive element `θ` of a number field `K`, the discriminant of the minimal
polynomial of `θ` over `ℤ`, the index `[𝓞 K : ℤ[θ]]` and the discriminant of `K` are related by

`disc (minpoly ℤ θ) = [𝓞 K : ℤ[θ]]² · disc K`.

The formula compares the discriminants of two `ℚ`-bases of `K`: the power basis
`1, θ, …, θ ^ (n - 1)`, whose discriminant is `disc (minpoly ℤ θ)`
(`discr_powerBasis_eq_minpoly_discr`), and an integral basis of `𝓞 K`, whose discriminant is
`disc K`. The change-of-basis matrix between them has integer entries, and its determinant is
`±[𝓞 K : ℤ[θ]]` (`Submodule.natAbs_det_basis_change`); the square of that determinant is the
factor relating the two discriminants.

## Main results

* `TauCeti.NumberField.IntegralPrimitiveElement.discr_minpoly_eq_index_sq_mul_discr`: the index
  formula `disc (minpoly ℤ θ) = [𝓞 K : ℤ[θ]]² · disc K`.
* `TauCeti.NumberField.IntegralPrimitiveElement.index_eq_one_of_squarefree_discr`: a squarefree
  polynomial discriminant forces index `1`.
* `TauCeti.NumberField.IntegralPrimitiveElement.not_dvd_index_of_not_dvd_discr_minpoly`: a
  natural number not dividing `disc (minpoly ℤ θ)` does not divide the index.
* `TauCeti.NumberField.IntegralPrimitiveElement.not_dvd_index_of_squarefree_map`: a prime modulo
  which `minpoly ℤ θ` is squarefree does not divide the index.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition (2.12).
-/

public section

open scoped NumberField
open Matrix Module

namespace TauCeti.NumberField.IntegralPrimitiveElement

variable {K : Type*} [Field K] [NumberField K]

/-- **The index formula.** For an integral primitive element `θ` of a number field `K`, the
discriminant of `minpoly ℤ θ` is the square of the index `[𝓞 K : ℤ[θ]]` times the discriminant
of `K`. -/
theorem discr_minpoly_eq_index_sq_mul_discr (θ : IntegralPrimitiveElement K) :
    (minpoly ℤ θ.1).discr = (θ.index : ℤ) ^ 2 * NumberField.discr K := by
  classical
  -- The power basis of `ℤ[θ]` over `ℤ`, as a basis of the sublattice `ℤ[θ]` of `𝓞 K`.
  set pb := Algebra.adjoin.powerBasis' θ.1.isIntegral with hpb
  have hfin : finrank ℤ (Algebra.adjoin ℤ ({θ.1} : Set (𝓞 K))) = finrank ℤ (𝓞 K) := by
    have h := θ.finrank_adjoin
    rwa [adjoin_def] at h
  have hcard : Fintype.card (Fin pb.dim) = finrank ℤ (𝓞 K) := by
    rw [Fintype.card_fin, ← pb.finrank, hfin]
  have h := (Subalgebra.toSubmodule (Algebra.adjoin ℤ ({θ.1} : Set (𝓞 K))))
    |>.discr_eq_cardQuot_sq_mul_discr (pb.basis.map (Subalgebra.toSubmoduleEquiv _).symm) hcard
  -- The powers of `θ` are the power basis of `θ`, up to the identification of the index sets.
  have hdim : θ.powerBasis.dim = pb.dim := by
    rw [← θ.powerBasis.finrank, ← _root_.NumberField.RingOfIntegers.rank K, ← hfin, pb.finrank]
  have hpow : Algebra.discr ℚ θ.powerBasis.basis =
      Algebra.discr ℚ (fun i : Fin pb.dim =>
        algebraMap (𝓞 K) K ((pb.basis.map (Subalgebra.toSubmoduleEquiv _).symm i : _) : 𝓞 K)) := by
    rw [← Algebra.discr_reindex ℚ θ.powerBasis.basis (finCongr hdim)]
    congr 1
    funext i
    simp [PowerBasis.basis_eq_pow, hpb, Subalgebra.toSubmoduleEquiv]
    rfl
  -- Assemble, after casting to `ℚ`.
  apply Int.cast_injective (α := ℚ)
  rw [← eq_intCast (algebraMap ℤ ℚ), ← θ.discr_powerBasis_eq_minpoly_discr, hpow, h, index_def,
    ← Submodule.cardQuot_apply, adjoin_def]
  push_cast
  rfl


/-- A natural number not dividing the discriminant of `minpoly ℤ θ` does not divide the index
`[𝓞 K : ℤ[θ]]`. -/
theorem not_dvd_index_of_not_dvd_discr_minpoly (θ : IntegralPrimitiveElement K) {p : ℕ}
    (hp : ¬ (p : ℤ) ∣ (minpoly ℤ θ.1).discr) : ¬ p ∣ θ.index := by
  intro h
  apply hp
  rw [θ.discr_minpoly_eq_index_sq_mul_discr]
  exact (dvd_pow (Int.natCast_dvd_natCast.mpr h) two_ne_zero).mul_right _

-- The corollary is the squarefree case of Dedekind's criterion, Layer 3.7 of the human-authored
-- roadmap `TauCetiRoadmap/NumberFieldArithmetic/README.md`.
/-- **A prime modulo which the minimal polynomial is squarefree does not divide the index.**
If `minpoly ℤ θ` is squarefree modulo the prime `p`, then its discriminant is nonzero modulo `p`,
so `p` does not divide `[𝓞 K : ℤ[θ]]` by the index formula. -/
theorem not_dvd_index_of_squarefree_map (θ : IntegralPrimitiveElement K) {p : ℕ} [Fact p.Prime]
    (hsq : Squarefree ((minpoly ℤ θ.1).map (Int.castRingHom (ZMod p)))) : ¬ p ∣ θ.index := by
  apply θ.not_dvd_index_of_not_dvd_discr_minpoly
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← eq_intCast (Int.castRingHom (ZMod p)),
    ← (minpoly.monic θ.1.isIntegral).discr_map]
  exact ((minpoly.monic θ.1.isIntegral).map _).discr_ne_zero_iff.mpr
    (PerfectField.separable_iff_squarefree.mpr hsq)

/-- **A squarefree polynomial discriminant forces index `1`.** If the discriminant of
`minpoly ℤ θ` is squarefree, then `ℤ[θ] = 𝓞 K`. -/
theorem index_eq_one_of_squarefree_discr (θ : IntegralPrimitiveElement K)
    (hsq : Squarefree (minpoly ℤ θ.1).discr) : θ.index = 1 := by
  have hu : IsUnit (θ.index : ℤ) :=
    hsq _ (by rw [← sq]; exact ⟨_, θ.discr_minpoly_eq_index_sq_mul_discr⟩)
  exact_mod_cast Int.isUnit_iff_natAbs_eq.mp hu

end TauCeti.NumberField.IntegralPrimitiveElement
