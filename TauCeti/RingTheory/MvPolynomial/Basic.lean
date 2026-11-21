/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.LinearAlgebra.Dimension.BaseChange

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Basic lemmas for multivariate polynomial rings

This file collects general algebraic properties of multivariate polynomial rings:

* `MvPolynomial.map f` is a finite ring map whenever `f` is: a family generating `S` over `R`
  generates `MvPolynomial σ S` over `MvPolynomial σ R` once its members are read as constants.
  This is the coefficient-extension half of the finiteness that Stacks 10.161.13 (tag 032O)
  records as "`R'[x^{1/q}]` is finite over `R[x]`"; the `expand` half lives in
  `TauCeti/RingTheory/MvPolynomial/Expand.lean`. Nothing here mentions `expand`, which is why it
  sits in this file rather than that one.
* When the variable type `ι` is a subsingleton (at most one variable), the univariate polynomial
  ring `R[X]` surjects onto `MvPolynomial ι R` via an `R`-algebra homomorphism.
* Clearing denominators in a multivariate polynomial over a localization `M⁻¹ R` multiplies it by
  the image of some `d ∈ M` into the image of `MvPolynomial ι R`, preserving nonvanishing and
  vanishing under injective algebra maps.

## Main results

* `TauCeti.MvPolynomial.finite_map`: `MvPolynomial.map f` is finite when `f` is.
* `TauCeti.MvPolynomial.exists_surjective_algHom_of_subsingleton`: `R[X]` surjects onto
  `MvPolynomial ι R` whenever `ι` is a subsingleton.
* `MvPolynomial.exists_map_eq_smul_of_isLocalization`: clearing denominators in a
  multivariate polynomial over a localization `M⁻¹ R`.
* `TauCeti.MvPolynomial.exists_ne_zero_and_aeval_eq_zero_of_isLocalization`: a nonzero polynomial
  relation over a localization `M⁻¹ R` evaluated along an injective map `D → E` yields a nonzero
  polynomial relation over `R` in `D`.

## Provenance

The finiteness argument for `MvPolynomial.finite_map` is Stacks 10.161.13 (tag 032O), which is
univariate and whose proof records it as "Since `R` is N-2 we see that `R′` is finite over `R` and
hence `R′[x^{1/q}]` is finite over `R[x]`"; the multivariate form is not claimed as source material.
-/

public section

open Polynomial

namespace MvPolynomial

/-- Clearing denominators in a multivariate polynomial `f` over a localization `K` of `R` at `M`
produces `d ∈ M` and a polynomial `f₁` over `R` whose image in `K` equals `d • f`. -/
theorem exists_map_eq_smul_of_isLocalization {R K ι : Type*}
    [CommRing R] [CommRing K] [Algebra R K] (M : Submonoid R) [IsLocalization M K]
    (f : MvPolynomial ι K) :
    ∃ (d : M) (f₁ : MvPolynomial ι R),
      MvPolynomial.map (algebraMap R K) f₁ = algebraMap R K d • f := by
  let := MvPolynomial.algebraMvPolynomial (R := R) (S := K) (σ := ι)
  obtain ⟨⟨f₁, _, d, hd, rfl⟩, h⟩ := IsLocalization.surj (M.map (MvPolynomial.C (σ := ι))) f
  refine ⟨⟨d, hd⟩, f₁, ?_⟩
  dsimp only at h
  rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, mul_comm, ← MvPolynomial.smul_eq_C_mul] at h
  exact h.symm

end MvPolynomial

namespace TauCeti

-- `MvPolynomial.algebraMvPolynomial` is deliberately not a global instance: it diamonds for
-- `Algebra (MvPolynomial σ R) (MvPolynomial σ (MvPolynomial σ S))`. Mathlib installs it locally
-- wherever the `MvPolynomial σ R`-algebra structure on `MvPolynomial σ S` is wanted, and the
-- pushout and scalar-tower instances used below are stated under it.
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Polynomial rings preserve module-finiteness of the coefficient map: `MvPolynomial.map f` is
a finite ring map whenever `f` is. -/
theorem MvPolynomial.finite_map {σ R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.Finite) : (MvPolynomial.map (σ := σ) f).Finite := by
  let _ : Algebra R S := f.toAlgebra
  have _ : Module.Finite R S := hf
  -- `MvPolynomial σ S` is the base change of `S` along `R → MvPolynomial σ R`. Stating that as a
  -- `have` is load-bearing: unifying `IsBaseChange.finite` against the goal directly forces the
  -- `MvPolynomial σ R`-algebra structure to be `(MvPolynomial.map f).toAlgebra`, for which the
  -- scalar tower is not an instance, whereas Mathlib's pushout is stated for `algebraMvPolynomial`.
  have h : Module.Finite (MvPolynomial σ R) (MvPolynomial σ S) :=
    IsBaseChange.finite
      (Algebra.IsPushout.out (R := R) (S := MvPolynomial σ R) (R' := S) (S' := MvPolynomial σ S))
  exact h

/-- When `ι` has at most one element, there is a surjective `R`-algebra homomorphism from the
univariate polynomial ring `R[X]` onto `MvPolynomial ι R`. -/
theorem MvPolynomial.exists_surjective_algHom_of_subsingleton (R ι : Type*)
    [CommSemiring R] [Subsingleton ι] :
    ∃ φ : R[X] →ₐ[R] MvPolynomial ι R, Function.Surjective φ := by
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i⟩⟩
  · refine ⟨(MvPolynomial.isEmptyAlgEquiv R ι).symm.toAlgHom.comp (Polynomial.aeval (0 : R)),
      (MvPolynomial.isEmptyAlgEquiv R ι).symm.surjective.comp ?_⟩
    simpa [Polynomial.coe_aeval_eq_eval] using Polynomial.eval_surjective (0 : R)
  · let _ : Unique ι := uniqueOfSubsingleton i
    exact ⟨(MvPolynomial.uniqueAlgEquiv R ι).symm.toAlgHom,
      (MvPolynomial.uniqueAlgEquiv R ι).symm.surjective⟩

/-- Clearing denominators in a nonzero multivariate polynomial over a localization `K` of `R` at
`M` produces a nonzero polynomial over `R` with the same vanishing under an injective algebra map
`D → E`. -/
theorem MvPolynomial.exists_ne_zero_and_aeval_eq_zero_of_isLocalization {R K D E ι : Type*}
    [CommRing R] [CommRing K] [Algebra R K] (M : Submonoid R) [IsLocalization M K]
    [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [Algebra K E] [Algebra D E]
    [IsScalarTower R K E] [IsScalarTower R D E]
    (hinj : Function.Injective (algebraMap D E)) (y : ι → D) {f : MvPolynomial ι K} (hf : f ≠ 0)
    (heval : MvPolynomial.aeval (fun i ↦ algebraMap D E (y i)) f = 0) :
    ∃ f₁ : MvPolynomial ι R, f₁ ≠ 0 ∧ MvPolynomial.aeval y f₁ = 0 := by
  obtain ⟨d, f₁, hf₁_map⟩ := _root_.MvPolynomial.exists_map_eq_smul_of_isLocalization M f
  refine ⟨f₁, fun h0 ↦ hf ?_, hinj ?_⟩
  · obtain ⟨u, hu⟩ := IsLocalization.map_units K d
    have hsmul : u • f = 0 := by rw [Units.smul_def, hu, ← hf₁_map, h0, map_zero]
    rw [← inv_smul_smul u f, hsmul, smul_zero]
  · have hmap : algebraMap D E (MvPolynomial.aeval y f₁) =
        MvPolynomial.aeval (fun i ↦ algebraMap D E (y i))
          (MvPolynomial.map (algebraMap R K) f₁) := by
      rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
        ← IsScalarTower.algebraMap_eq R K E, IsScalarTower.algebraMap_eq R D E,
        ← MvPolynomial.hom_eval₂]
    rw [map_zero, hmap, hf₁_map, map_smul, heval, smul_zero]

end TauCeti
