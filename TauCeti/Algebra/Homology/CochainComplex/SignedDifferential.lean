/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import TauCeti.Algebra.Homology.CochainComplex.ScaleDifferential
public import TauCeti.Data.ZMod.IntUnitsPower

/-!
# Multiplying the differential of a cochain complex by a sign

For `τ : ZMod 2`, `CochainComplex.signedDifferential K τ` is the cochain complex with the terms
of `K` and the differential `(-1)^τ d`, the instance of `CochainComplex.scaleDifferential` with
constant signs. The sign is Mathlib's power `(-1 : ℤˣ) ^ τ` of a unit of `ℤ` by an element of
`ZMod 2`, so that it only depends on the parity `τ`. Multiplying the term of degree `k` by
`(-1)^(τ k)` is an isomorphism `K.signedDifferential τ ≅ K`
(`CochainComplex.signedDifferentialIso`).

Such complexes appear in the super sign convention for tensor products of complexes whose terms
carry a parity independent of their degree: there the differential of the second factor of a
tensor product is multiplied by `(-1)^τ` when the first factor has independent parity `τ`, and the
isomorphism above is the comparison with the ordinary tensor product of complexes.

## Main definitions

* `CochainComplex.signedDifferential K τ`: the terms of `K` with the differential `(-1)^τ d`.
* `CochainComplex.signedDifferentialIso K τ`: the isomorphism `K.signedDifferential τ ≅ K`,
  multiplication by `(-1)^(τ k)` in degree `k`.
-/

public section

open CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C]

/-- The cochain complex with the terms of `K` and its differential multiplied by `(-1)^τ`. It is
an abbreviation, so that the API of `CochainComplex.scaleDifferential` applies to it. -/
abbrev signedDifferential (K : CochainComplex C ℤ) (τ : ZMod 2) : CochainComplex C ℤ :=
  K.scaleDifferential fun _ ↦ (-1 : ℤˣ) ^ τ

/-- **The sign comparison.** Multiplying the term of degree `k` by `(-1)^(τ k)` is an isomorphism
from `K.signedDifferential τ` to `K`. -/
def signedDifferentialIso (K : CochainComplex C ℤ) (τ : ZMod 2) : K.signedDifferential τ ≅ K :=
  K.scaleDifferentialIso _ (fun k ↦ (-1 : ℤˣ) ^ (τ * k)) (TauCeti.uzpow_mul_intCast_add_one τ)

@[simp]
theorem signedDifferentialIso_hom_f (K : CochainComplex C ℤ) (τ : ZMod 2) (k : ℤ) :
    (K.signedDifferentialIso τ).hom.f k = (((-1 : ℤˣ) ^ (τ * k) : ℤˣ) : ℤ) •
      (K.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ) k).hom := by
  simp [signedDifferentialIso]

@[simp]
theorem signedDifferentialIso_inv_f (K : CochainComplex C ℤ) (τ : ZMod 2) (k : ℤ) :
    (K.signedDifferentialIso τ).inv.f k = (((-1 : ℤˣ) ^ (τ * k) : ℤˣ) : ℤ) •
      (K.scaleDifferentialXIso (fun _ ↦ (-1 : ℤˣ) ^ τ) k).inv := by
  simp [signedDifferentialIso]

end CochainComplex
