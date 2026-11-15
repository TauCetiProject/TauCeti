/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.LinearAlgebra.Matrix.PosSemidef
public import Mathlib.Basic.NNReal.Star

/-!
# Positive-definite functions on `[0, ∞) × V`

This file records the Berg--Christensen--Ressel semigroup-group positive-definiteness predicate
for functions on `ℝ≥0 × V`. For an additive group `V`, the intended involution is
`(t, v) ↦ (t, -v)`, so the finite quadratic forms use the entries
`F (tᵢ + tⱼ, vᵢ - vⱼ)`.

The generic positive-definite-function predicate already captures the finite quadratic-form
condition. The BCR predicate is that predicate on the product `ℝ≥0 × WithNegStar V`: `ℝ≥0` carries
the trivial involution and `WithNegStar V` the negation, so the product involution is
`(t, v) ↦ (t, -v)`. The type synonym `WithNegStar V` avoids installing a global negation
`StarAddMonoid` instance on `V`, which would conflict with Mathlib's ordinary star conventions.

## Main declarations

* `TauCeti.IsSemigroupGroupPD`: the BCR positive-definiteness predicate on `ℝ≥0 × V`.
* `TauCeti.isSemigroupGroupPD_iff_isPositiveDefinite`: the bridge to the generic predicate on the
  involutive monoid `ℝ≥0 × WithNegStar V`.
* `TauCeti.isSemigroupGroupPD_iff_posSemidef`: the bridge to the associated
  positive-definite kernel.
* `TauCeti.isSemigroupGroupPD_iff`: the finite quadratic-form characterization.
* `TauCeti.IsSemigroupGroupPD.conj_symm`, diagonal, and origin lemmas: basic consequences of the
  semigroup-group positive-definiteness condition.
* `TauCeti.isSemigroupGroupPD_const_of_nonneg`, `TauCeti.isSemigroupGroupPD_zero`, and
  `TauCeti.isSemigroupGroupPD_one`: basic constant examples.
* `TauCeti.IsSemigroupGroupPD.add`, `TauCeti.IsSemigroupGroupPD.mul`, and finite
  `sum`/`prod`: closure properties inherited from positive-definite kernels.
* `TauCeti.IsSemigroupGroupPD.quadForm_two_nonneg`: the `2 × 2` BCR Hermitian sub-form is
  nonnegative.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open ComplexConjugate
open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

variable {V : Type*} [AddCommGroup V] {F G : ℝ≥0 × V → ℂ}

/-- A function on `ℝ≥0 × V` is semigroup-group positive definite, in the
Berg--Christensen--Ressel sense, if all finite quadratic forms formed using the involution
`(t, v) ↦ (t, -v)` are nonnegative:
`∑ᵢⱼ cᵢ conj(cⱼ) F(tᵢ + tⱼ, vᵢ - vⱼ) ≥ 0`.

It is the generic `IsPositiveDefinite` on the product `ℝ≥0 × WithNegStar V`, whose product
involution is the BCR involution; see `isSemigroupGroupPD_iff_isPositiveDefinite`. -/
def IsSemigroupGroupPD (F : ℝ≥0 × V → ℂ) : Prop :=
  IsPositiveDefinite fun p : ℝ≥0 × WithNegStar V => F (p.1, WithNegStar.ofNegStar p.2)

/-- Semigroup-group positive definiteness is positive definiteness on the involutive monoid
`ℝ≥0 × WithNegStar V`, whose product involution is `(t, v) ↦ (t, -v)`. -/
theorem isSemigroupGroupPD_iff_isPositiveDefinite :
    IsSemigroupGroupPD F ↔
      IsPositiveDefinite fun p : ℝ≥0 × WithNegStar V => F (p.1, WithNegStar.ofNegStar p.2) :=
  Iff.rfl

/-- The bridge from semigroup-group positive definiteness to the associated positive-definite
kernel. -/
theorem isSemigroupGroupPD_iff_posSemidef :
    IsSemigroupGroupPD F ↔
      Matrix.PosSemidef fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) := by
  let e : ℝ≥0 × V ≃ ℝ≥0 × WithNegStar V :=
    (Equiv.refl ℝ≥0).prodCongr WithNegStar.toNegStar.toEquiv
  have hK : Matrix.submatrix
      (Matrix.of fun a b : ℝ≥0 × WithNegStar V =>
        F ((a + star b).1, WithNegStar.ofNegStar (a + star b).2)) e e =
      Matrix.of fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) := by
    ext p q
    simp [e, sub_eq_add_neg]
  rw [isSemigroupGroupPD_iff_isPositiveDefinite, isPositiveDefinite_iff_posSemidef]
  exact (Matrix.posSemidef_submatrix_equiv e).symm.trans (iff_of_eq (congrArg _ hK))

/-- The kernel associated to a semigroup-group positive-definite function is positive definite. -/
theorem IsSemigroupGroupPD.posSemidef (hF : IsSemigroupGroupPD F) :
    Matrix.PosSemidef fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) :=
  isSemigroupGroupPD_iff_posSemidef.mp hF

/-- Build a semigroup-group positive-definite function from the associated positive-definite
kernel. -/
theorem IsSemigroupGroupPD.of_posSemidef
    (hF : Matrix.PosSemidef fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2)) :
    IsSemigroupGroupPD F :=
  isSemigroupGroupPD_iff_posSemidef.mpr hF

/-- A nonnegative complex constant is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_const_of_nonneg {k : ℂ} (hk : 0 ≤ k) :
    IsSemigroupGroupPD (fun _ : ℝ≥0 × V => k) :=
  IsSemigroupGroupPD.of_posSemidef <| by
    simpa using posSemidef_const_of_nonneg (α := ℝ≥0 × V) hk

/-- The zero function is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_zero :
    IsSemigroupGroupPD (fun _ : ℝ≥0 × V => (0 : ℂ)) :=
  isSemigroupGroupPD_const_of_nonneg le_rfl

/-- The constant-one function is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_one :
    IsSemigroupGroupPD (fun _ : ℝ≥0 × V => (1 : ℂ)) :=
  isSemigroupGroupPD_const_of_nonneg zero_le_one

/-- The finite quadratic-form characterization of semigroup-group positive definiteness. -/
theorem isSemigroupGroupPD_iff :
    IsSemigroupGroupPD F ↔
      (∀ p q : ℝ≥0 × V, conj (F (p.1 + q.1, p.2 - q.2))
        = F (q.1 + p.1, q.2 - p.2)) ∧
        ∀ {ι : Type*} [Fintype ι] (c : ι → ℂ) (p : ι → ℝ≥0 × V),
          0 ≤ ∑ i, ∑ j, c i * conj (c j) *
            F ((p i).1 + (p j).1, (p i).2 - (p j).2) := by
  classical
  constructor
  · intro hF
    refine ⟨fun p q => by
      simpa only [RCLike.star_def] using hF.posSemidef.isHermitian.apply q p, ?_⟩
    intro ι _ c p
    have hpos := (posSemidef_iff_finite_sum.mp hF.posSemidef).2 p
      (fun i => conj (c i))
    simpa only [RCLike.star_def, Complex.conj_conj, mul_comm, mul_left_comm, mul_assoc] using hpos
  · rintro ⟨hsymm, hpos⟩
    exact IsSemigroupGroupPD.of_posSemidef <| posSemidef_iff_finite_sum.mpr
      ⟨fun p q => by simpa only [RCLike.star_def] using hsymm p q, fun p x => by
        have h := hpos (fun i => conj (x i)) p
        simpa only [RCLike.star_def, Complex.conj_conj, mul_comm, mul_left_comm, mul_assoc] using h⟩

namespace IsSemigroupGroupPD

/-- Positive-definiteness holds for arbitrary finite BCR families: for every finite family of
scalars `c` and points `p`, the quadratic form
`∑ i, ∑ j, c i * conj (c j) * F ((p i).1 + (p j).1, (p i).2 - (p j).2)` is nonnegative. -/
theorem sum_nonneg (hF : IsSemigroupGroupPD F) {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p : ι → ℝ≥0 × V) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) *
      F ((p i).1 + (p j).1, (p i).2 - (p j).2) :=
  (isSemigroupGroupPD_iff.mp hF).2 c p

/-- The `2 × 2` BCR Hermitian sub-form at two points. -/
theorem quadForm_two_nonneg (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) (c₀ c₁ : ℂ) :
    0 ≤ c₀ * conj c₀ * F (p.1 + p.1, p.2 - p.2)
      + c₀ * conj c₁ * F (p.1 + q.1, p.2 - q.2)
      + c₁ * conj c₀ * F (q.1 + p.1, q.2 - p.2)
      + c₁ * conj c₁ * F (q.1 + q.1, q.2 - q.2) := by
  simpa [sub_eq_add_neg] using
    (isSemigroupGroupPD_iff_isPositiveDefinite.mp hF).quadForm_two_nonneg
      (p.1, WithNegStar.toNegStar p.2) (q.1, WithNegStar.toNegStar q.2) c₀ c₁

/-- A semigroup-group positive-definite function is conjugate symmetric for the BCR kernel:
`conj (F (t + u, v - w)) = F (u + t, w - v)`. -/
@[simp]
theorem conj_symm (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) :
    conj (F (p.1 + q.1, p.2 - q.2)) = F (q.1 + p.1, q.2 - p.2) := by
  simpa only [starRingEnd_apply] using hF.posSemidef.isHermitian.apply q p

/-- Values of a semigroup-group positive-definite function on the time diagonal `(t + t, 0)` are
real and nonnegative. -/
theorem diagonal_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) : 0 ≤ F (t + t, 0) := by
  simpa using hF.posSemidef.diag_nonneg (i := (t, 0))

/-- Values of a semigroup-group positive-definite function on the time diagonal `(t + t, 0)` have
zero imaginary part. -/
@[simp]
theorem diagonal_im (hF : IsSemigroupGroupPD F) (t : ℝ≥0) : (F (t + t, 0)).im = 0 :=
  ((Complex.nonneg_iff.mp (hF.diagonal_nonneg t)).2).symm

/-- The real part of a semigroup-group positive-definite function on the time diagonal
`(t + t, 0)` is nonnegative. -/
theorem diagonal_re_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    0 ≤ (F (t + t, 0)).re :=
  (Complex.nonneg_iff.mp (hF.diagonal_nonneg t)).1

/-- A semigroup-group positive-definite function on the time diagonal `(t + t, 0)` is equal to
its real part, viewed as a complex number. -/
theorem diagonal_eq_ofReal_re (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    F (t + t, 0) = ((F (t + t, 0)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using hF.diagonal_im t

/-- The value of a semigroup-group positive-definite function at `(0, 0)` is real and
nonnegative. -/
theorem map_zero_nonneg (hF : IsSemigroupGroupPD F) : 0 ≤ F (0, 0) := by
  simpa using hF.diagonal_nonneg 0

/-- The value of a semigroup-group positive-definite function at `(0, 0)` has zero imaginary
part. -/
@[simp]
theorem map_zero_im (hF : IsSemigroupGroupPD F) : (F (0, 0)).im = 0 :=
  by simpa using hF.diagonal_im 0

/-- The real part of the value of a semigroup-group positive-definite function at `(0, 0)` is
nonnegative. -/
theorem map_zero_re_nonneg (hF : IsSemigroupGroupPD F) : 0 ≤ (F (0, 0)).re :=
  by simpa using hF.diagonal_re_nonneg 0

/-- The value at `(0, 0)` of a semigroup-group positive-definite function is equal to its real
part, viewed as a complex number. -/
theorem map_zero_eq_ofReal_re (hF : IsSemigroupGroupPD F) : F (0, 0) = ((F (0, 0)).re : ℂ) := by
  simpa using hF.diagonal_eq_ofReal_re 0

/-- If a semigroup-group positive-definite function is nonzero at the origin, then the real
part of its value at the origin is strictly positive. -/
theorem map_zero_re_pos_of_ne_zero (hF : IsSemigroupGroupPD F) (h0 : F (0, 0) ≠ 0) :
    0 < (F (0, 0)).re := by
  refine lt_of_le_of_ne hF.map_zero_re_nonneg ?_
  intro hre
  apply h0
  apply Complex.ext
  · exact hre.symm
  · simpa using hF.map_zero_im

/-- Semigroup-group positive-definite functions are closed under addition. -/
theorem add (hF : IsSemigroupGroupPD F) (hG : IsSemigroupGroupPD G) :
    IsSemigroupGroupPD fun x => F x + G x :=
  IsSemigroupGroupPD.of_posSemidef <| hF.posSemidef.add hG.posSemidef

/-- Semigroup-group positive-definite functions are closed under multiplication by a
nonnegative complex scalar. -/
theorem const_mul {k : ℂ} (hk : 0 ≤ k) (hF : IsSemigroupGroupPD F) :
    IsSemigroupGroupPD fun x => k * F x :=
  IsSemigroupGroupPD.of_posSemidef <| hF.posSemidef.smul hk

/-- Semigroup-group positive-definite functions are closed under multiplication by a
nonnegative real scalar. -/
theorem smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (hF : IsSemigroupGroupPD F) :
    IsSemigroupGroupPD fun x => r • F x :=
  IsSemigroupGroupPD.of_posSemidef <|
    hF.posSemidef.smul (α := ℝ) hr

/-- Semigroup-group positive-definite functions are closed under pointwise multiplication
(Schur product). -/
theorem mul (hF : IsSemigroupGroupPD F) (hG : IsSemigroupGroupPD G) :
    IsSemigroupGroupPD fun x => F x * G x :=
  IsSemigroupGroupPD.of_posSemidef <| hF.posSemidef.hadamard hG.posSemidef

/-- Semigroup-group positive-definite functions are closed under finite sums. -/
theorem sum {ι : Type*} {s : Finset ι} {F : ι → ℝ≥0 × V → ℂ}
    (hF : ∀ i ∈ s, IsSemigroupGroupPD (F i)) :
    IsSemigroupGroupPD fun x => ∑ i ∈ s, F i x := by
  apply IsSemigroupGroupPD.of_posSemidef
  have heq : (∑ i ∈ s, fun a b : ℝ≥0 × V => F i (a.1 + b.1, a.2 - b.2)) =
      (fun a b : ℝ≥0 × V => ∑ i ∈ s, F i (a.1 + b.1, a.2 - b.2)) := by ext; simp
  exact heq ▸ Matrix.posSemidef_sum s (fun i hi => (hF i hi).posSemidef)

/-- Semigroup-group positive-definite functions are closed under finite products
(Schur products). -/
theorem prod {ι : Type*} {s : Finset ι} {F : ι → ℝ≥0 × V → ℂ}
    (hF : ∀ i ∈ s, IsSemigroupGroupPD (F i)) :
    IsSemigroupGroupPD fun x => ∏ i ∈ s, F i x :=
  IsSemigroupGroupPD.of_posSemidef <|
    posSemidef_schur_finset_prod fun i hi => (hF i hi).posSemidef

end IsSemigroupGroupPD

end TauCeti
