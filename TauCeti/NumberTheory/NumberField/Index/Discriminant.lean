/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import TauCeti.NumberTheory.NumberField.Index.PowerBasis
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import TauCeti.NumberTheory.NumberField.Discriminant.OfIntegralBasis

/-!
# The index formula

For an integral primitive element `θ` of a number field `K`, the discriminant of the minimal
polynomial of `θ` over `ℤ`, the index `[𝓞 K : ℤ[θ]]` and the discriminant of `K` are related by

`disc (minpoly ℤ θ) = [𝓞 K : ℤ[θ]]² · disc K`.

Both sides are discriminants of `ℚ`-bases of `K`: the left one of the power basis
`1, θ, …, θ ^ (n - 1)` (`discr_powerBasis_eq_minpoly_discr`), the right one of an integral basis
of `𝓞 K`. The change-of-basis matrix between them has integer entries, and its determinant is
`±[𝓞 K : ℤ[θ]]` (`Submodule.natAbs_det_basis_change`), which gives the formula.

## Main results

* `TauCeti.NumberField.IntegralPrimitiveElement.discr_minpoly_eq_index_sq_mul_discr`: the index
  formula `disc (minpoly ℤ θ) = [𝓞 K : ℤ[θ]]² · disc K`.

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
  -- The power basis of `ℤ[θ]` over `ℤ`, and an integral basis of `𝓞 K` reindexed to match it.
  set pb := Algebra.adjoin.powerBasis' θ.1.isIntegral with hpb
  have hfin : finrank ℤ (Algebra.adjoin ℤ ({θ.1} : Set (𝓞 K))) = finrank ℤ (𝓞 K) := by
    have h := θ.finrank_adjoin
    rwa [adjoin_def] at h
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (Fin pb.dim) := by
    rw [Fintype.card_fin, ← pb.finrank, hfin, finrank_eq_card_chooseBasisIndex]
  set b : Basis (Fin pb.dim) ℤ (𝓞 K) :=
    (_root_.NumberField.RingOfIntegers.basis K).reindex (Fintype.equivOfCardEq hcard) with hb
  set u : Fin pb.dim → 𝓞 K := fun i => (pb.basis i : 𝓞 K) with hu
  set P : Matrix (Fin pb.dim) (Fin pb.dim) ℤ := b.toMatrix u with hP
  -- The determinant of the change of basis is the index, up to sign.
  have hdet : P.det.natAbs = θ.index := by
    rw [hP, ← b.det_apply, index_def, adjoin_def]
    have h := Submodule.natAbs_det_basis_change b
      (Subalgebra.toSubmodule (Algebra.adjoin ℤ ({θ.1} : Set (𝓞 K))))
      (pb.basis.map (Subalgebra.toSubmoduleEquiv _).symm)
    have hcoe : (Subtype.val ∘ ⇑(pb.basis.map (Subalgebra.toSubmoduleEquiv _).symm)) = u := by
      funext i
      simp only [Function.comp_apply, Basis.map_apply, hu]
      rfl
    rw [hcoe] at h
    exact h
  -- Over `ℚ`, the powers of `θ` are obtained from the integral basis by that matrix.
  set w : Fin pb.dim → K := fun i => algebraMap (𝓞 K) K (b i) with hw
  have hw_discr : Algebra.discr ℚ w = (_root_.NumberField.discr K : ℚ) :=
    _root_.NumberField.discr_eq_of_integralBasis b
  have hv : (fun i : Fin pb.dim => algebraMap (𝓞 K) K (u i)) =
      w ᵥ* (P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ K) := by
    have h := b.toMatrix_map_vecMul u
    rw [← hP] at h
    funext j
    rw [← congrFun h j]
    simp [Matrix.vecMul, dotProduct, hw, map_sum, algebraMap_int_eq, map_intCast]
  have hdiscr_u : Algebra.discr ℚ (fun i : Fin pb.dim => algebraMap (𝓞 K) K (u i)) =
      ((P.det : ℤ) : ℚ) ^ 2 * (_root_.NumberField.discr K : ℚ) := by
    rw [hv, Algebra.discr_of_matrix_vecMul, hw_discr, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, algebraMap_int_eq, eq_intCast]
  -- The powers of `θ` are the power basis of `θ`, up to the identification of the index sets.
  have hdim : θ.powerBasis.dim = pb.dim := by
    rw [← θ.powerBasis.finrank, ← _root_.NumberField.RingOfIntegers.rank K, ← hfin, pb.finrank]
  have hpow : Algebra.discr ℚ θ.powerBasis.basis =
      Algebra.discr ℚ (fun i : Fin pb.dim => algebraMap (𝓞 K) K (u i)) := by
    rw [← Algebra.discr_reindex ℚ θ.powerBasis.basis (finCongr hdim)]
    congr 1
    funext i
    simp [PowerBasis.basis_eq_pow, hu, hpb]
  -- Assemble, after casting to `ℚ`.
  apply Int.cast_injective (α := ℚ)
  rw [← eq_intCast (algebraMap ℤ ℚ), ← θ.discr_powerBasis_eq_minpoly_discr, hpow, hdiscr_u, ← hdet]
  push_cast
  rw [sq_abs]

end TauCeti.NumberField.IntegralPrimitiveElement
