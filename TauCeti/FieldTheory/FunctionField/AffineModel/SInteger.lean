/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.Prime
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

/-!
# `S`-integers of an algebraic function field

Let `F / k` be an algebraic function field. For a set `T` of places, the ring of functions with
no pole outside `T` is the holomorphy ring `𝒪_{Tᶜ}`; when `T` is finite and nonempty this is the
ring of `T`-integers of `F` in the arithmetic of function fields (Rosen, Chapter 14). This file
identifies these rings with Mathlib's `S`-integers `Set.integer`, which are defined for a fixed
Dedekind domain `R` with fraction field `F` and a set `S` of height one primes of `R`, as the
functions of `p`-adic valuation at most one at every `p ∉ S`.

The dictionary is the correspondence between the places finite on an affine model `R` and the
height one primes of `R` (`TauCeti.Place.ofPrime`). Under it the `S`-integers of `R` are the
holomorphy ring of the places finite on `R` and not coming from `S`
(`Set.restrictScalars_integer_eq_holomorphyRing`), and the `S`-units are the functions without
zeros or poles at those places (`Set.mem_unit_iff_forall_ord_eq_zero`). Conversely, the holomorphy
ring of any set of places finite on `R` is a ring of `S`-integers of `R`
(`TauCeti.holomorphyRing_eq_restrictScalars_integer`).

Rings of `T`-integers also exist intrinsically, without a model: for `T` finite and nonempty,
`𝒪_{Tᶜ}` is itself an affine model, a finitely generated Dedekind domain
(`TauCeti.isDedekindDomain_holomorphyRing_compl` and `TauCeti.finiteType_holomorphyRing_compl`,
in `TauCeti/FieldTheory/FunctionField/AffineModel/IntegralClosure.lean`), so the results here
apply to it. No exactness hypothesis on the constant field is needed anywhere.

## Main results

* `Set.restrictScalars_integer_eq_holomorphyRing`: the `S`-integers of an affine model are a
  holomorphy ring.
* `Set.mem_unit_iff_forall_ord_eq_zero`: the `S`-units of an affine model are the functions of
  order zero at every place of `R` outside `S`.
* `TauCeti.holomorphyRing_eq_restrictScalars_integer`: a holomorphy ring of places finite on an
  affine model is a ring of `S`-integers of the model.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2.
* M. Rosen, *Number Theory in Function Fields*, GTM 210, Springer, 2002, Chapter 14.
-/

public section

open IsDedekindDomain

universe u v w

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-! ### `S`-integers and `S`-units of an affine model -/

section AffineModel

open TauCeti

variable {R : Type w} [CommRing R] [IsDedekindDomain R] [Algebra k R] [Algebra R F]
  [IsFractionRing R F] [IsScalarTower k R F]

namespace Set

variable (k) in
/-- **A function is an `S`-integer of an affine model `R` exactly when it is regular at the place
of every height one prime of `R` outside `S`.** -/
theorem mem_integer_iff_forall_mem_integers (S : Set (HeightOneSpectrum R)) {x : F} :
    x ∈ S.integer F ↔ ∀ p ∉ S, x ∈ (Place.ofPrime k F p).integers :=
  (Set.mem_integer_iff F S).trans <| forall₂_congr fun p _ ↦ by
    rw [Place.mem_integers_iff, Place.valuation_ofPrime]

/-- **The `S`-integers of an affine model are a holomorphy ring**: for a Dedekind `k`-algebra `R`
with fraction field `F` and a set `S` of height one primes of `R`, `S.integer F` is the ring of
functions regular at every place finite on `R` whose prime is not in `S`. -/
theorem restrictScalars_integer_eq_holomorphyRing (S : Set (HeightOneSpectrum R)) :
    (S.integer F).restrictScalars k = holomorphyRing (Place.ofPrime k F '' Sᶜ) := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_integer_iff_forall_mem_integers k,
    mem_holomorphyRing_iff, forall_mem_image, mem_compl_iff]

variable (k) in
/-- **The `S`-units of an affine model are the functions without zeros or poles at the place of
any height one prime outside `S`.** -/
theorem mem_unit_iff_forall_ord_eq_zero (S : Set (HeightOneSpectrum R)) {u : Fˣ} :
    u ∈ S.unit F ↔ ∀ p ∉ S, (Place.ofPrime k F p).ord (u : F) = 0 :=
  (Set.mem_unit_iff S F).trans <| forall₂_congr fun p _ ↦ by
    rw [Place.ord_eq_iff_valuation_eq_exp_neg _ u.ne_zero, Place.valuation_ofPrime, neg_zero,
      WithZero.exp_zero]

end Set

namespace TauCeti

/-- **A holomorphy ring of places finite on an affine model is a ring of `S`-integers of the
model**: if every place of `T` is finite on `R`, then `𝒪_T` is the ring of `S`-integers of `R`
for `S` the height one primes whose places are not in `T`. -/
theorem holomorphyRing_eq_restrictScalars_integer {T : Set (Place k F)}
    (hT : ∀ P ∈ T, ∀ r : R, algebraMap R F r ∈ P.integers) :
    holomorphyRing T = ((Place.ofPrime (R := R) k F ⁻¹' T)ᶜ.integer F).restrictScalars k := by
  rw [Set.restrictScalars_integer_eq_holomorphyRing, compl_compl,
    Set.image_preimage_eq_iff.mpr (by rwa [Place.range_ofPrime])]

end TauCeti

end AffineModel
