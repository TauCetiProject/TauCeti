/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Lagrange
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.EllipticSimilitude
public import TauCeti.RingTheory.Polynomial.RootEnumeration
import TauCeti.LinearAlgebra.Matrix.Charpoly.Diagonal
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# Sign types of frames with an elliptic similitude

Let `E` be a CM field with a CM type `Φ`, write `Φ_w` for the embedding of `Φ` above the infinite
place `w`, and let `A` be a commutative `E`-algebra with an involution compatible with complex
conjugation on `E`, such as the finite adeles of `E`. For a matrix `y` over `E`, the complex roots
of the characteristic polynomial of `y` under `Φ_w` are numbered once and for all by the index
type `n` (`Polynomial.rootEnumeration`). For signs `ε_w : n → SignType`, the *sign polynomial*
`Matrix.signPolynomial (Φ_w) y ε_w` is the Lagrange polynomial taking the value `ε_w i` at the
`i`-th root.

A pair `(y, x)` with `x ∈ GL_n(A)` has *type* `(ε, ν, F)` (`Matrix.HasSignType`), for signs
`ε = (ε_w)`, `ν ∈ ℚ` and a set `F` of matrices over `A`, if for some matrix `β` over `E`: `y` is
an elliptic similitude of `β` with multiplier `ν` (`Matrix.IsEllipticSimilitude`); the Gram matrix
`xᴴ * β * x` of `β` in the frame `x` lies in `F`; and at each infinite place `w`, the complex form
`β^{Φ_w} * p_w(y^{Φ_w})` is positive definite, `p_w` being the sign polynomial of `ε_w`. In an
eigenbasis of `y^{Φ_w}` in which `β^{Φ_w}` is diagonal, this says that the diagonal entry of
`β^{Φ_w}` at the eigenvector of the `i`-th root has the sign `ε_w i`.

The signs are changed by moving the frame. Let `δ` be a polynomial over `E` whose value at the
`i`-th root under `Φ_w` has the sign `η_w i`, so that `δ(y)` is invertible
(`Matrix.isUnit_aeval_iff_forall_eval_rootEnumeration_ne_zero`). Replacing `β` by
`β * δ(y)` keeps `y` an elliptic similitude with multiplier `ν`, and multiplies the signs at the
roots by `η` (`Matrix.IsEllipticSimilitude.posDef_map_mul_aeval_signPolynomial_mul_iff`). If
moreover polynomials `c` over `E` and `g` over `A` satisfy `X * c ≡ ν` and `(conj g)(c) * g ≡ δ`
modulo the characteristic polynomial of `y`, where `conj g` has the conjugated coefficients of `g`,
then `g(y)` is invertible (`Matrix.isUnit_aeval_map_of_dvd`, with `p = (conj g)(c)`) and the Gram
matrix of `β` in the frame `g(y) * x` is that of `β * δ(y)` in the frame `x`
(`Matrix.conjTranspose_aeval_mul_map_mul_aeval_eq_map_mul_aeval`). Hence `(y, x)` has type
`(ε * η, ν, F)` if and only if `(y, g(y) * x)` has type `(ε, ν, F)`
(`Matrix.hasSignType_mul_iff_hasSignType_mul`). As `g(y)` is a polynomial in `y`, it commutes
with every matrix commuting with `y` (`Matrix.aeval_mul_eq_mul_aeval`).

For `A` the finite adeles, class field theory of the CM field `E[X]/(P)`, `P` the characteristic
polynomial, supplies `δ`, `c` and `g`: `δ` and `g` represent an element `a` with the prescribed
signs at the infinite places and a finite idele `u⁻¹` with `a * u * ū = 1`, and `c` represents the
conjugate of the root of `P`. This is how the signs of an elliptic similitude at the infinite places
are changed by a finite adelic frame in the comparison of traces between unitary groups.

## Main definitions

* `Matrix.signPolynomial φ y ε`: the polynomial with value `ε i` at the `i`-th complex root of
  the characteristic polynomial of `y` under `φ`.
* `Matrix.HasSignType y x Φ ε ν F`: the pair `(y, x)` has type `(ε, ν, F)`.

## Main results

* `Matrix.eval_signPolynomial_rootEnumeration`: the sign polynomial takes the value `ε i` at the
  `i`-th root when the characteristic polynomial is separable.
* `Matrix.IsEllipticSimilitude.posDef_map_mul_aeval_signPolynomial_mul_iff`: changing the form by
  `δ(y)` multiplies the signs by those of `δ` at the roots.
* `Matrix.hasSignType_mul_iff_hasSignType_mul`: **change of signs**, `(y, x)` has type
  `(ε * η, ν, F)` if and only if `(y, g(y) * x)` has type `(ε, ν, F)`.

## Provenance

The definitions and the change of signs follow the shorter formal proof of the ShortGRH family,
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC),
`src/Lib/Adelic/TraceFormula/ChangingSigns.lean` (`New.Variety.HasSignType`,
`New.Variety.posDef_mul_interpolate_iff`, `New.Variety.gram_aeval_eq_map_mul_aeval`,
`New.Variety.exists_aeval_hasSignType_mul_iff`); the formal proofs here are written
independently.
-/

public section

open Polynomial NumberField Finset
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R]

/-- The **sign polynomial** of `ε : n → SignType` for a matrix `y` over `R` and a ring
homomorphism `φ : R →+* ℂ`: the Lagrange polynomial taking the value `ε i` at the `i`-th complex
root of the characteristic polynomial of `y` under `φ`, in the numbering
`Polynomial.rootEnumeration` of these roots. -/
noncomputable def signPolynomial (φ : R →+* ℂ) (y : Matrix n n R) (ε : n → SignType) : ℂ[X] :=
  Lagrange.interpolate univ ((y.charpoly.map φ).rootEnumeration ℂ n) fun i ↦ (ε i : ℂ)

/-- If the characteristic polynomial of `y` is separable, the sign polynomial of `ε` takes the
value `ε i` at the `i`-th complex root under `φ`. -/
theorem eval_signPolynomial_rootEnumeration {y : Matrix n n R} (hy : y.charpoly.Separable)
    (φ : R →+* ℂ) (ε : n → SignType) (i : n) :
    (signPolynomial φ y ε).eval ((y.charpoly.map φ).rootEnumeration ℂ n i) = ε i :=
  Lagrange.eval_interpolate_at_node _ (injective_rootEnumeration_charpoly_map hy.map).injOn
    (mem_univ i)

end CommRing

variable {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]
  {A : Type*} [CommRing A] [StarRing A] [Algebra E A]

/-- A pair `(y, x)`, with `y` a matrix over the CM field `E` and `x` an invertible matrix over a
commutative `E`-algebra `A` with involution, **has type `(ε, ν, F)`** for the CM type `Φ`, signs
`ε w : n → SignType` at the infinite places `w`, `ν ∈ ℚ` and a set `F` of matrices over `A`, if
there is a matrix `β` over `E` such that `y` is an elliptic similitude of `β` with multiplier `ν`,
the Gram matrix `xᴴ * β * x` lies in `F`, and at every infinite place `w` the complex form
`β^{Φ_w} * p_w(y^{Φ_w})` is positive definite, `p_w` the sign polynomial of `ε w` at the
embedding `Φ_w` of `Φ` above `w`. -/
def HasSignType (y : Matrix n n E) (x : GL n A) (Φ : TauCeti.CMType E)
    (ε : InfinitePlace E → n → SignType) (ν : ℚ) (F : Set (Matrix n n A)) : Prop :=
  ∃ β : Matrix n n E, y.IsEllipticSimilitude β ν ∧
    (x : Matrix n n A)ᴴ * β.map (algebraMap E A) * x ∈ F ∧
    ∀ w : InfinitePlace E, (β.map (Φ.embedding w) *
      aeval (y.map (Φ.embedding w)) (signPolynomial (Φ.embedding w) y (ε w))).PosDef

/-- The defining property of `Matrix.HasSignType`. -/
theorem hasSignType_iff {y : Matrix n n E} {x : GL n A} {Φ : TauCeti.CMType E}
    {ε : InfinitePlace E → n → SignType} {ν : ℚ} {F : Set (Matrix n n A)} :
    y.HasSignType x Φ ε ν F ↔ ∃ β : Matrix n n E, y.IsEllipticSimilitude β ν ∧
      (x : Matrix n n A)ᴴ * β.map (algebraMap E A) * x ∈ F ∧
      ∀ w : InfinitePlace E, (β.map (Φ.embedding w) *
        aeval (y.map (Φ.embedding w)) (signPolynomial (Φ.embedding w) y (ε w))).PosDef :=
  Iff.rfl

variable {y β : Matrix n n E} {ν : ℚ}

/-- **Changing the form by `δ(y)` multiplies the signs by those of `δ`.** Let `y` be an elliptic
similitude of `β` and `φ` a complex embedding, and let `δ` be a polynomial over `E` whose value at
the `i`-th complex root of the characteristic polynomial of `y` under `φ` has the sign `η i`, that
is `0 < η i * δ^φ(r_i)`. Then `(β * δ(y))^φ * p_{ε * η}(y^φ)` is positive definite if and only if
`β^φ * p_ε(y^φ)` is, where `p_ε` is the sign polynomial of `ε`. -/
theorem IsEllipticSimilitude.posDef_map_mul_aeval_signPolynomial_mul_iff
    (h : y.IsEllipticSimilitude β ν) (φ : E →+* ℂ) {δ : E[X]} {η : n → SignType}
    (hη : ∀ i, 0 < (η i : ℂ) * (δ.map φ).eval ((y.charpoly.map φ).rootEnumeration ℂ n i))
    (ε : n → SignType) :
    ((β * aeval y δ).map φ * aeval (y.map φ) (signPolynomial φ y (ε * η))).PosDef ↔
      (β.map φ * aeval (y.map φ) (signPolynomial φ y ε)).PosDef := by
  set r := (y.charpoly.map φ).rootEnumeration ℂ n
  obtain ⟨P, d, b, hP, hb, -⟩ := h.exists_mul_eq_mul_diagonal φ
  rw [Matrix.map_mul, ← aeval_map, Matrix.mul_assoc, ← map_mul, posDef_mul_aeval_iff hP hb,
    posDef_mul_aeval_iff hP hb]
  refine forall_congr' fun i ↦ ?_
  -- The eigenvalue `d i` is the `j`-th numbered root for some `j`.
  obtain ⟨j, hj⟩ : d i ∈ Set.range r := by
    have hroot := mem_roots_charpoly_of_mul_eq_mul_diagonal hP i
    rw [charpoly_map, mem_roots ((charpoly_monic y).map φ).ne_zero] at hroot
    rw [(isRootEnumeration_rootEnumeration_charpoly_map φ y).range_eq_rootSet,
      mem_rootSet_of_ne ((charpoly_monic y).map φ).ne_zero, coe_aeval_eq_eval]
    exact hroot
  have hsep := h.separable_charpoly
  rw [← hj, eval_mul, eval_signPolynomial_rootEnumeration hsep,
    eval_signPolynomial_rootEnumeration hsep, Pi.mul_apply, SignType.coe_mul]
  -- `b * (δ(r_j) * (ε_j * η_j)) = (η_j * δ(r_j)) * (b * ε_j)`, and `η_j * δ(r_j) > 0`.
  have hcomm : b i * ((δ.map φ).eval (r j) * ((ε j : ℂ) * (η j : ℂ))) =
      ((η j : ℂ) * (δ.map φ).eval (r j)) * (b i * (ε j : ℂ)) := by ring
  rw [hcomm]
  exact mul_pos_iff_of_pos_left (hη j)

/-- **Change of signs.** Let `y` be a matrix over the CM field `E`, `η` signs at the infinite places
and `δ` a polynomial over `E` whose value at the `i`-th complex root of the characteristic
polynomial of `y` under the embedding `Φ_w` of the CM type above `w` has the sign `η w i`. Let `c`
be a polynomial over `E` with `X * c ≡ ν` modulo the characteristic polynomial of `y`, and `g` a
polynomial over `A` with `(conj g)(c) * g ≡ δ` modulo its image in `A[X]`, where `conj g` has the
conjugated coefficients of `g`. For an invertible matrix `U` over `A` equal to `g(y)` (such a `U`
exists by `Matrix.isUnit_aeval_iff_forall_eval_rootEnumeration_ne_zero` and
`Matrix.isUnit_aeval_map_of_dvd`), the pair `(y, x)` has type `(ε * η, ν, F)` if and only if
`(y, U * x)` has type `(ε, ν, F)`. -/
theorem hasSignType_mul_iff_hasSignType_mul [StarModule E A] {Φ : TauCeti.CMType E}
    {η : InfinitePlace E → n → SignType} {δ c : E[X]} {g : A[X]}
    (hη : ∀ w i, 0 < (η w i : ℂ) * (δ.map (Φ.embedding w)).eval
      ((y.charpoly.map (Φ.embedding w)).rootEnumeration ℂ n i))
    (hc : y.charpoly ∣ X * c - C (ν : E))
    (hg : y.charpoly.map (algebraMap E A) ∣
      (g.map (starRingEnd A)).comp (c.map (algebraMap E A)) * g - δ.map (algebraMap E A))
    {U : GL n A} (hU : (U : Matrix n n A) = aeval (y.map (algebraMap E A)) g)
    (ε : InfinitePlace E → n → SignType) (F : Set (Matrix n n A)) (x : GL n A) :
    y.HasSignType x Φ (ε * η) ν F ↔ y.HasSignType (U * x) Φ ε ν F := by
  -- `δ(y)` is invertible: by `hη`, `δ` vanishes at no root at an infinite place `w`.
  have hδ : IsUnit (aeval y δ) := by
    let w : InfinitePlace E := .mk (Classical.choice inferInstance)
    refine (isUnit_aeval_iff_forall_eval_rootEnumeration_ne_zero (Φ.embedding w) y δ).2
      fun i h0 ↦ lt_irrefl (0 : ℂ) ?_
    simpa only [h0, mul_zero] using hη w i
  -- The form `β` for `(y, U * x)` corresponds to the form `β * δ(y)` for `(y, x)`.
  refine (hδ.unit.mulRight.exists_congr fun β ↦ ?_).symm
  rw [Units.mulRight_apply, IsUnit.unit_spec, isEllipticSimilitude_mul_aeval_iff hδ]
  refine and_congr_right fun h ↦ and_congr ?_ (forall_congr' fun w ↦
    (h.posDef_map_mul_aeval_signPolynomial_mul_iff _ (hη w) (ε w)).symm)
  have hν : IsLeftRegular (ν : E) :=
    (IsRegular.of_ne_zero (Rat.cast_ne_zero.2 h.multiplier_ne_zero)).left
  -- The Gram matrix of `β` in the frame `U * x` is that of `β * δ(y)` in the frame `x`.
  have hframe : ((U * x : GL n A) : Matrix n n A)ᴴ * β.map (algebraMap E A) * (U * x : GL n A) =
      (x : Matrix n n A)ᴴ * (β * aeval y δ).map (algebraMap E A) * x := by
    rw [Units.val_mul, conjTranspose_mul, hU,
      ← conjTranspose_aeval_mul_map_mul_aeval_eq_map_mul_aeval hν h.conjTranspose_mul_mul hc hg]
    simp only [Matrix.mul_assoc]
  rw [hframe]

end Matrix
