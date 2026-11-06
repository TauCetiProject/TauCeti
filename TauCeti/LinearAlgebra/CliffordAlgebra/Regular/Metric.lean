/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Regular.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Positivity
public import Mathlib.Analysis.InnerProductSpace.Defs
-- Private: naturality of the Clifford/exterior equivalence is used only in the map proof.
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The positive metric on real regular Clifford spinors

The scalar-part pairing `regularBilinForm Q x y = scalarTrace Q (star x * y)`
is intrinsic to the real Clifford algebra. For negative definite `Q` it is a positive
inner product, packaged as `regularInnerProductCore` without installing a global norm or
inner product instance. The Clifford monomials of any negative orthonormal basis are
orthonormal for it. This is the model metric for real regular spinor bundles.

Left multiplication by a vector is skew-adjoint; the parity-twisted right vector action
is self-adjoint. Parity and left Spin multiplication preserve the form. More generally,
every Clifford-unitary element acts isometrically, so the same metric works for the
geometric two-element group in rank zero, not just the native trivial Spin group.
Quadratic isometries preserve it as well.

The form and its algebraic identities make sense over any commutative ring with `2`
invertible; only positivity and the inner product core require real scalars and finite
dimension. No orientation or positive rank is assumed.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules* (1964).
-/

public section

noncomputable section

namespace CliffordAlgebra

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)] (Q : QuadraticForm R M)

/-- The scalar-part bilinear form on the regular Clifford module. It is positive for
negative definite real quadratic forms; `star` here is native Clifford conjugation. -/
def regularBilinForm : LinearMap.BilinForm R (CliffordAlgebra Q) where
  toFun x := scalarTrace Q ∘ₗ LinearMap.mulLeft R (star x)
  map_add' x y := by ext z; simp [add_mul]
  map_smul' r x := by ext z; simp

/-- The regular bilinear form is the scalar part of `star x * y`. -/
theorem regularBilinForm_apply (x y : CliffordAlgebra Q) :
    regularBilinForm Q x y = scalarTrace Q (star x * y) := (rfl)

/-- Clifford conjugation fixes the scalar part, so the regular form is symmetric. -/
theorem regularBilinForm_isSymm : (regularBilinForm Q).IsSymm := by
  constructor
  intro x y
  simp only [regularBilinForm_apply]
  calc
    scalarTrace Q (star x * y) = scalarTrace Q (star (star x * y)) := by
      symm
      rw [star_def, scalarTrace_reverse, scalarTrace_involute]
    _ = scalarTrace Q (star y * x) := by simp

@[simp]
theorem regularBilinForm_one_one : regularBilinForm Q 1 1 = 1 := by
  simp [regularBilinForm_apply]

/-- Left multiplication and Clifford conjugation are adjoint for the regular form. -/
theorem regularBilinForm_mul_left (a x y : CliffordAlgebra Q) :
    regularBilinForm Q (a * x) y = regularBilinForm Q x (star a * y) := by
  simp [regularBilinForm_apply, mul_assoc]

/-- Right multiplication has the same Clifford-conjugate adjoint. -/
theorem regularBilinForm_mul_right (a x y : CliffordAlgebra Q) :
    regularBilinForm Q (x * a) y = regularBilinForm Q x (y * star a) := by
  simp only [regularBilinForm_apply, star_mul, mul_assoc]
  rw [scalarTrace_mul_comm]
  simp [mul_assoc]

/-- Left multiplication by a Clifford generator is skew-adjoint. -/
theorem regularBilinForm_ι_mul_left (v : M) (x y : CliffordAlgebra Q) :
    regularBilinForm Q (ι Q v * x) y = -regularBilinForm Q x (ι Q v * y) := by
  simp [regularBilinForm_mul_left]

/-- Left multiplication by a vector scales squared lengths by the negative quadratic form. -/
theorem regularBilinForm_ι_mul_self (v : M) (x : CliffordAlgebra Q) :
    regularBilinForm Q (ι Q v * x) (ι Q v * x) =
      -Q v * regularBilinForm Q x x := by
  rw [regularBilinForm_ι_mul_left]
  simp [← mul_assoc, ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

/-- The grade involution is an isometry of the regular form. -/
@[simp]
theorem regularBilinForm_involute (x y : CliffordAlgebra Q) :
    regularBilinForm Q (involute x) (involute y) = regularBilinForm Q x y := by
  simp only [regularBilinForm_apply, star_def, reverse_involute]
  rw [← map_mul, scalarTrace_involute]

/-- Every Clifford-unitary element acts isometrically by left multiplication. -/
theorem regularBilinForm_unitary_mul {a : CliffordAlgebra Q} (ha : star a * a = 1)
    (x y : CliffordAlgebra Q) :
    regularBilinForm Q (a * x) (a * y) = regularBilinForm Q x y := by
  simp only [regularBilinForm_apply, star_mul, mul_assoc]
  rw [← mul_assoc (star a), ha, one_mul]

/-- The left regular Spin action preserves the scalar-part metric. -/
@[simp]
theorem regularBilinForm_spin_mul (g : spinGroup Q) (x y : CliffordAlgebra Q) :
    regularBilinForm Q ((g : CliffordAlgebra Q) * x) ((g : CliffordAlgebra Q) * y) =
      regularBilinForm Q x y :=
  regularBilinForm_unitary_mul Q (spinGroup.coe_star_mul_self g) x y

section Isometry

variable {N : Type*} [AddCommGroup N] [Module R N] {Q' : QuadraticForm R N}

/-- Every quadratic isometry preserves the regular scalar-part form, without a
finiteness or definiteness assumption. -/
theorem regularBilinForm_map (f : Q →qᵢ Q') (x y : CliffordAlgebra Q) :
    regularBilinForm Q' (map f x) (map f y) = regularBilinForm Q x y := by
  simp only [regularBilinForm_apply, ← map_star, ← map_mul, scalarTrace_apply,
    equivExterior_map]
  have h : ExteriorAlgebra.algebraMapInv.comp (ExteriorAlgebra.map f.toLinearMap) =
      ExteriorAlgebra.algebraMapInv :=
    ExteriorAlgebra.hom_ext <| LinearMap.ext fun m ↦ by
      simp [ExteriorAlgebra.algebraMapInv]
  exact AlgHom.congr_fun h _

/-- Quadratic isometry equivalences preserve the regular scalar-part form. -/
theorem regularBilinForm_equivOfIsometry (f : Q.IsometryEquiv Q')
    (x y : CliffordAlgebra Q) :
    regularBilinForm Q' (equivOfIsometry f x) (equivOfIsometry f y) =
      regularBilinForm Q x y :=
  regularBilinForm_map Q f.toIsometry x y

end Isometry

section Basis

variable {I : Type*} [LinearOrder I] {b : Module.Basis I R M}
  (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)

include hb

/-- The regular form in an orthogonal ordered-product basis has diagonal weights
`∏ i ∈ s, -Q (b i)`, including for degenerate forms. -/
theorem regularBilinForm_basis (s t : Finset I) :
    regularBilinForm Q (basis Q b s) (basis Q b t) =
      if s = t then ∏ i ∈ s, -Q (b i) else 0 := by
  simp only [regularBilinForm_apply, star_def, involute_basis hb, map_smul,
    smul_mul_assoc, map_smul, smul_eq_mul, scalarTrace_reverse_basis_mul_basis hb]
  split_ifs <;> simp_all [Finset.prod_neg]

/-- The monomials of a negative orthonormal basis are orthonormal in the regular metric. -/
theorem regularBilinForm_basis_of_neg_one (hQ : ∀ i, Q (b i) = -1) (s t : Finset I) :
    regularBilinForm Q (basis Q b s) (basis Q b t) = if s = t then 1 else 0 := by
  rw [regularBilinForm_basis Q hb]
  simp only [hQ, neg_neg, Finset.prod_const_one]

end Basis

end Algebra

section Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (Q : QuadraticForm ℝ V)

/-- For a negative semidefinite real form, the regular scalar-part form is nonnegative. -/
theorem regularBilinForm_self_nonneg (hQ : ∀ v, Q v ≤ 0) (x : CliffordAlgebra Q) :
    0 ≤ regularBilinForm Q x x := by
  have h := scalarTrace_conjStar_mul_self_nonneg hQ (ofBaseChangeAux ℂ Q x)
  rw [conjStar_ofBaseChangeAux, ← map_mul, scalarTrace_ofBaseChangeAux] at h
  rw [regularBilinForm_apply]
  exact Complex.zero_le_real.mp h

/-- For a negative definite real form, the regular scalar-part form is faithful. -/
@[simp]
theorem regularBilinForm_self_eq_zero_iff (hQ : (-Q).PosDef) (x : CliffordAlgebra Q) :
    regularBilinForm Q x x = 0 ↔ x = 0 := by
  have h := scalarTrace_conjStar_mul_self_eq_zero_iff hQ
    (x := ofBaseChangeAux ℂ Q x)
  rw [conjStar_ofBaseChangeAux, ← map_mul, scalarTrace_ofBaseChangeAux,
    map_eq_zero_iff _ (ofBaseChangeAux_injective (A := ℂ) Q)] at h
  rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℝ ℂ)] at h
  simpa only [regularBilinForm_apply] using h

/-- The regular scalar-part metric is strictly positive on nonzero real Clifford elements. -/
theorem regularBilinForm_self_pos (hQ : (-Q).PosDef) {x : CliffordAlgebra Q} (hx : x ≠ 0) :
    0 < regularBilinForm Q x x :=
  lt_of_le_of_ne (regularBilinForm_self_nonneg Q (fun v ↦ neg_nonneg.mp (hQ.nonneg v)) x)
    (fun h ↦ hx ((regularBilinForm_self_eq_zero_iff Q hQ x).mp h.symm))

/-- The intrinsic positive inner product on a real regular Clifford module of negative
definite form. This core is not a global instance, and does not replace any algebra norm. -/
abbrev regularInnerProductCore (hQ : (-Q).PosDef) :
    InnerProductSpace.Core ℝ (CliffordAlgebra Q) where
  inner x y := regularBilinForm Q x y
  conj_inner_symm x y := (regularBilinForm_isSymm Q).eq y x
  re_inner_nonneg x := regularBilinForm_self_nonneg Q
    (fun v ↦ neg_nonneg.mp (hQ.nonneg v)) x
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := (regularBilinForm_self_eq_zero_iff Q hQ x).mp hx

/-- The inner product core uses the scalar-part pairing, without a basis choice. -/
@[simp]
theorem regularInnerProductCore_inner (hQ : (-Q).PosDef) (x y : CliffordAlgebra Q) :
    (regularInnerProductCore Q hQ).inner x y = regularBilinForm Q x y := (rfl)

end Real

end CliffordAlgebra
