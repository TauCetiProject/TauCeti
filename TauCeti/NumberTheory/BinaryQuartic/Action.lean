/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuartic.Basic
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Changes of variables in binary quartics

The ordinary left action of `GL₂(R)` on binary quartics substitutes the row vector
`(x, y) M` into the form. `subst` also accepts singular matrices. The coefficient formulas
are identified with the existing `TauCeti.polynomialAction` on multivariate polynomials,
so equality of forms is formal polynomial equality, even over finite rings.

The invariants `I`, `J` and the discriminant have determinant weights four, six and twelve.
The determinant-to-the-minus-two substitution `twistedSMul` fixes all three invariants,
and scalar matrices act trivially under it.
These identities hold over arbitrary commutative rings, including characteristics two and three.

## References

* M. Bhargava, A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015),
  §2, (3)–(5), and §2.6, (32).
-/

public section

open Matrix

namespace TauCeti.BinaryQuartic

section Substitution

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluation of a binary quartic at `(x, y)`. -/
def eval (f : BinaryQuartic R) (x y : R) : R :=
  f 0 * x ^ 4 + f 1 * x ^ 3 * y + f 2 * x ^ 2 * y ^ 2 + f 3 * x * y ^ 3 + f 4 * y ^ 4

/-- The coefficient expression for evaluating a binary quartic. -/
theorem eval_def (f : BinaryQuartic R) (x y : R) :
    eval f x y =
      f 0 * x ^ 4 + f 1 * x ^ 3 * y + f 2 * x ^ 2 * y ^ 2 + f 3 * x * y ^ 3 + f 4 * y ^ 4 :=
  (rfl)

/-- Evaluating the zero quartic gives zero. -/
@[simp] theorem eval_zero (x y : R) : eval (0 : BinaryQuartic R) x y = 0 := by
  simp [eval_def]

/-- Evaluation is additive in the form. -/
@[simp] theorem eval_add (f g : BinaryQuartic R) (x y : R) :
    eval (f + g) x y = eval f x y + eval g x y := by
  simp only [eval_def, Pi.add_apply]
  ring

/-- Evaluation commutes with coefficientwise scalar multiplication. -/
@[simp] theorem eval_smul (r : R) (f : BinaryQuartic R) (x y : R) :
    eval (r • f) x y = r * eval f x y := by
  simp only [eval_def, Pi.smul_apply, smul_eq_mul]
  ring

/-- Evaluation commutes with base change of coefficients and coordinates. -/
@[simp] theorem eval_comp (φ : R →+* S) (f : BinaryQuartic R) (x y : R) :
    eval (φ ∘ f) (φ x) (φ y) = φ (eval f x y) := by
  simp [eval_def]

/-- The homogeneous polynomial represented by a binary quartic. -/
noncomputable def toMvPolynomial (f : BinaryQuartic R) : MvPolynomial (Fin 2) R :=
  eval (MvPolynomial.C ∘ f) (MvPolynomial.X 0) (MvPolynomial.X 1)

/-- The formal polynomial is evaluation at the two polynomial variables. -/
theorem toMvPolynomial_def (f : BinaryQuartic R) :
    toMvPolynomial f = eval (MvPolynomial.C ∘ f) (MvPolynomial.X 0) (MvPolynomial.X 1) :=
  (rfl)

/-- The formal polynomial of the zero quartic is zero. -/
@[simp] theorem toMvPolynomial_zero : toMvPolynomial (0 : BinaryQuartic R) = 0 := by
  simp [toMvPolynomial_def, eval_def]

/-- Conversion to a formal polynomial is additive. -/
@[simp] theorem toMvPolynomial_add (f g : BinaryQuartic R) :
    toMvPolynomial (f + g) = toMvPolynomial f + toMvPolynomial g := by
  simp only [toMvPolynomial_def, eval_def, Function.comp_apply, Pi.add_apply, map_add]
  ring

/-- Conversion to a formal polynomial commutes with coefficientwise scaling. -/
@[simp] theorem toMvPolynomial_smul (r : R) (f : BinaryQuartic R) :
    toMvPolynomial (r • f) = r • toMvPolynomial f := by
  simp only [toMvPolynomial_def, eval_def, Function.comp_apply, Pi.smul_apply,
    smul_eq_mul, map_mul, MvPolynomial.smul_eq_C_mul]
  ring

/-- Conversion to a formal polynomial commutes with base change of coefficients. -/
@[simp] theorem toMvPolynomial_comp (φ : R →+* S) (f : BinaryQuartic R) :
    toMvPolynomial (φ ∘ f) = MvPolynomial.map φ (toMvPolynomial f) := by
  simp [toMvPolynomial_def, eval_def]

/-- Evaluating the polynomial of a quartic agrees with evaluating its coefficient expression. -/
@[simp] theorem eval_toMvPolynomial (f : BinaryQuartic R) (x : Fin 2 → R) :
    MvPolynomial.eval x (toMvPolynomial f) = eval f (x 0) (x 1) := by
  simp [toMvPolynomial, eval]

/-- Recover the coefficient of `x^(4-i) y^i` from the formal polynomial of a quartic. -/
@[simp] theorem coeff_toMvPolynomial (f : BinaryQuartic R) (i : Fin 5) :
    (toMvPolynomial f).coeff
      (Finsupp.single 0 4 - Finsupp.single 0 i.val + Finsupp.single 1 i.val) = f i := by
  simp only [toMvPolynomial, eval, Function.comp_apply, MvPolynomial.X_pow_eq_monomial]
  fin_cases i <;> simp [MvPolynomial.X,
    MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_two]

/-- A binary quartic is determined by its formal polynomial, without an infinitude assumption
on the coefficient ring. -/
theorem toMvPolynomial_injective : Function.Injective (toMvPolynomial (R := R)) := by
  intro f g h
  funext i
  have hi := congrArg
    (fun p : MvPolynomial (Fin 2) R ↦
      p.coeff (Finsupp.single 0 4 - Finsupp.single 0 i.val + Finsupp.single 1 i.val)) h
  exact (coeff_toMvPolynomial f i).symm.trans (hi.trans (coeff_toMvPolynomial g i))

/-- The polynomial of a quartic is homogeneous of degree four, including for the zero form. -/
theorem toMvPolynomial_isHomogeneous (f : BinaryQuartic R) :
    (toMvPolynomial f).IsHomogeneous 4 := by
  simp only [toMvPolynomial, eval, Function.comp_apply]
  apply MvPolynomial.IsHomogeneous.add
  · apply MvPolynomial.IsHomogeneous.add
    · apply MvPolynomial.IsHomogeneous.add
      · apply MvPolynomial.IsHomogeneous.add
        · exact MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _
        · exact (MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _).mul
            (MvPolynomial.isHomogeneous_X _ _)
      · exact (MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _).mul
          (MvPolynomial.isHomogeneous_X_pow _ _)
    · exact (MvPolynomial.isHomogeneous_C_mul_X _ _).mul
        (MvPolynomial.isHomogeneous_X_pow _ _)
  · exact MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _

/-- Row-vector linear substitution: `subst M f` represents `f ((x, y) M)`. -/
def subst (M : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) : BinaryQuartic R :=
  ![eval f (M 0 0) (M 0 1),
    4 * f 0 * M 0 0 ^ 3 * M 1 0 + f 1 * M 0 0 ^ 3 * M 1 1 +
      3 * f 1 * M 0 0 ^ 2 * M 0 1 * M 1 0 + 2 * f 2 * M 0 0 ^ 2 * M 0 1 * M 1 1 +
      2 * f 2 * M 0 0 * M 0 1 ^ 2 * M 1 0 + 3 * f 3 * M 0 0 * M 0 1 ^ 2 * M 1 1 +
      f 3 * M 0 1 ^ 3 * M 1 0 + 4 * f 4 * M 0 1 ^ 3 * M 1 1,
    6 * f 0 * M 0 0 ^ 2 * M 1 0 ^ 2 + 3 * f 1 * M 0 0 ^ 2 * M 1 0 * M 1 1 +
      3 * f 1 * M 0 0 * M 0 1 * M 1 0 ^ 2 + f 2 * M 0 0 ^ 2 * M 1 1 ^ 2 +
      4 * f 2 * M 0 0 * M 0 1 * M 1 0 * M 1 1 + f 2 * M 0 1 ^ 2 * M 1 0 ^ 2 +
      3 * f 3 * M 0 0 * M 0 1 * M 1 1 ^ 2 + 3 * f 3 * M 0 1 ^ 2 * M 1 0 * M 1 1 +
      6 * f 4 * M 0 1 ^ 2 * M 1 1 ^ 2,
    4 * f 0 * M 0 0 * M 1 0 ^ 3 + 3 * f 1 * M 0 0 * M 1 0 ^ 2 * M 1 1 +
      f 1 * M 0 1 * M 1 0 ^ 3 + 2 * f 2 * M 0 0 * M 1 0 * M 1 1 ^ 2 +
      2 * f 2 * M 0 1 * M 1 0 ^ 2 * M 1 1 + f 3 * M 0 0 * M 1 1 ^ 3 +
      3 * f 3 * M 0 1 * M 1 0 * M 1 1 ^ 2 + 4 * f 4 * M 0 1 * M 1 1 ^ 3,
    eval f (M 1 0) (M 1 1)]

/-- The five coefficient formulas for row-vector substitution. -/
theorem subst_def (M : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) :
    subst M f =
  ![eval f (M 0 0) (M 0 1),
    4 * f 0 * M 0 0 ^ 3 * M 1 0 + f 1 * M 0 0 ^ 3 * M 1 1 +
      3 * f 1 * M 0 0 ^ 2 * M 0 1 * M 1 0 + 2 * f 2 * M 0 0 ^ 2 * M 0 1 * M 1 1 +
      2 * f 2 * M 0 0 * M 0 1 ^ 2 * M 1 0 + 3 * f 3 * M 0 0 * M 0 1 ^ 2 * M 1 1 +
      f 3 * M 0 1 ^ 3 * M 1 0 + 4 * f 4 * M 0 1 ^ 3 * M 1 1,
    6 * f 0 * M 0 0 ^ 2 * M 1 0 ^ 2 + 3 * f 1 * M 0 0 ^ 2 * M 1 0 * M 1 1 +
      3 * f 1 * M 0 0 * M 0 1 * M 1 0 ^ 2 + f 2 * M 0 0 ^ 2 * M 1 1 ^ 2 +
      4 * f 2 * M 0 0 * M 0 1 * M 1 0 * M 1 1 + f 2 * M 0 1 ^ 2 * M 1 0 ^ 2 +
      3 * f 3 * M 0 0 * M 0 1 * M 1 1 ^ 2 + 3 * f 3 * M 0 1 ^ 2 * M 1 0 * M 1 1 +
      6 * f 4 * M 0 1 ^ 2 * M 1 1 ^ 2,
    4 * f 0 * M 0 0 * M 1 0 ^ 3 + 3 * f 1 * M 0 0 * M 1 0 ^ 2 * M 1 1 +
      f 1 * M 0 1 * M 1 0 ^ 3 + 2 * f 2 * M 0 0 * M 1 0 * M 1 1 ^ 2 +
      2 * f 2 * M 0 1 * M 1 0 ^ 2 * M 1 1 + f 3 * M 0 0 * M 1 1 ^ 3 +
      3 * f 3 * M 0 1 * M 1 0 * M 1 1 ^ 2 + 4 * f 4 * M 0 1 * M 1 1 ^ 3,
    eval f (M 1 0) (M 1 1)] := (rfl)

/-- The coefficient formula for substitution agrees with the polynomial action on standard
vectors, fixing the row-vector convention. -/
theorem toMvPolynomial_subst (M : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) :
    toMvPolynomial (subst M f) = polynomialAction M (toMvPolynomial f) := by
  simp only [toMvPolynomial, eval, subst, Function.comp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_pow, map_ofNat,
    polynomialAction_X, Fin.sum_univ_two, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  ring

/-- Pointwise substitution by a matrix uses its columns as the new linear coordinates. -/
@[simp] theorem eval_subst (M : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) (x y : R) :
    eval (subst M f) x y = eval f (M 0 0 * x + M 1 0 * y) (M 0 1 * x + M 1 1 * y) := by
  simp [eval, subst]
  ring

/-- The identity matrix fixes every quartic. -/
@[simp] theorem subst_one (f : BinaryQuartic R) : subst 1 f = f := by
  apply toMvPolynomial_injective
  simp [toMvPolynomial_subst]

/-- Substitution is a left matrix action: the rightmost matrix acts on the form first. -/
theorem subst_mul (M N : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) :
    subst (M * N) f = subst M (subst N f) := by
  apply toMvPolynomial_injective
  simp only [toMvPolynomial_subst, polynomialAction_mul, AlgHom.comp_apply]

/-- Substitution sends the zero form to zero. -/
@[simp] theorem subst_zero (M : Matrix (Fin 2) (Fin 2) R) : subst M 0 = 0 := by
  funext i
  fin_cases i <;> simp [subst, eval]

/-- Substitution is additive in the form. -/
@[simp] theorem subst_add (M : Matrix (Fin 2) (Fin 2) R) (f g : BinaryQuartic R) :
    subst M (f + g) = subst M f + subst M g := by
  funext i
  fin_cases i <;> simp [subst, eval] <;> ring

/-- Substitution commutes with coefficientwise scalar multiplication. -/
@[simp] theorem subst_smul (M : Matrix (Fin 2) (Fin 2) R) (r : R) (f : BinaryQuartic R) :
    subst M (r • f) = r • subst M f := by
  funext i
  fin_cases i <;> simp [subst, eval, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Base change of coefficients commutes with matrix substitution. -/
@[simp] theorem subst_comp (φ : R →+* S) (M : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) :
    subst (M.map φ) (φ ∘ f) = φ ∘ subst M f := by
  funext i
  fin_cases i <;> simp [subst, eval, Matrix.map_apply, map_ofNat]

/-- A scalar matrix multiplies a quartic by the fourth power of the scalar. -/
@[simp] theorem subst_scalar (r : R) (f : BinaryQuartic R) :
    subst (Matrix.diagonal fun _ : Fin 2 ↦ r) f = r ^ 4 • f := by
  funext i
  fin_cases i <;> simp [subst, eval, Matrix.diagonal, Pi.smul_apply,
    smul_eq_mul] <;> ring

/-- The ordinary action of `GL₂` by row-vector substitution. -/
instance : DistribMulAction (GL (Fin 2) R) (BinaryQuartic R) where
  smul g f := subst (g : Matrix (Fin 2) (Fin 2) R) f
  one_smul := subst_one
  mul_smul g h f := subst_mul (g : Matrix (Fin 2) (Fin 2) R) h f
  smul_zero g := subst_zero (g : Matrix (Fin 2) (Fin 2) R)
  smul_add g f h := subst_add (g : Matrix (Fin 2) (Fin 2) R) f h

/-- The ordinary group action is the matrix substitution. -/
theorem smul_eq_subst (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    g • f = subst (g : Matrix (Fin 2) (Fin 2) R) f := (rfl)

/-- Evaluating the ordinary action substitutes the columns of the acting matrix. -/
@[simp] theorem eval_smul_generalLinearGroup (g : GL (Fin 2) R) (f : BinaryQuartic R)
    (x y : R) :
    eval (g • f) x y = eval f (g 0 0 * x + g 1 0 * y) (g 0 1 * x + g 1 1 * y) := by
  rw [smul_eq_subst, eval_subst]

/-- Base change of coefficients commutes with the ordinary `GL₂` action. -/
@[simp] theorem smul_comp (f : BinaryQuartic R) (φ : R →+* S) (g : GL (Fin 2) R) :
    Units.map (φ.mapMatrix (m := Fin 2) : Matrix (Fin 2) (Fin 2) R →*
      Matrix (Fin 2) (Fin 2) S) g • (φ ∘ f) = φ ∘ (g • f) := by
  rw [smul_eq_subst, smul_eq_subst, Units.coe_map]
  simp only [MonoidHom.coe_ofClass, RingHom.mapMatrix_apply, subst_comp]

/-- Scalar matrices have weight four under the ordinary action. -/
@[simp] theorem scalar_smul (u : Rˣ) (f : BinaryQuartic R) :
    GeneralLinearGroup.scalar (Fin 2) u • f = (u : R) ^ 4 • f := by
  rw [smul_eq_subst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, subst_scalar]

end Substitution

section Invariants

variable {R : Type*} [CommRing R]

/-- `I` has determinant weight four under every matrix substitution. -/
@[simp] theorem invI_subst (M : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) :
    invI (subst M f) = M.det ^ 4 * invI f := by
  simp [invI_def, subst, eval, Matrix.det_fin_two]
  ring

/-- `J` has determinant weight six under every matrix substitution. -/
@[simp] theorem invJ_subst (M : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) :
    invJ (subst M f) = M.det ^ 6 * invJ f := by
  simp [invJ_def, subst, eval, Matrix.det_fin_two]
  ring

/-- The integral discriminant has determinant weight twelve, including in characteristics
two and three and for singular substitution matrices. -/
@[simp] theorem disc_subst (M : Matrix (Fin 2) (Fin 2) R) (f : BinaryQuartic R) :
    disc (subst M f) = M.det ^ 12 * disc f := by
  -- Cancel 27 only over the universal integer coefficient ring, then specialize.
  let A := MvPolynomial (Fin 5 ⊕ (Fin 2 × Fin 2)) ℤ
  let F : BinaryQuartic A := fun i ↦ MvPolynomial.X (Sum.inl i)
  let N : Matrix (Fin 2) (Fin 2) A := fun i j ↦ MvPolynomial.X (Sum.inr (i, j))
  have h : disc (subst N F) = N.det ^ 12 * disc F := by
    apply mul_left_cancel₀ (by norm_num : (27 : A) ≠ 0)
    calc
      27 * disc (subst N F) = 4 * invI (subst N F) ^ 3 - invJ (subst N F) ^ 2 :=
        disc_relation _
      _ = N.det ^ 12 * (4 * invI F ^ 3 - invJ F ^ 2) := by
        rw [invI_subst, invJ_subst]
        ring
      _ = 27 * (N.det ^ 12 * disc F) := by rw [← disc_relation]; ring
  let φ : A →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (Sum.elim f fun ij ↦ M ij.1 ij.2)
  have hF : φ ∘ F = f := funext fun i ↦ MvPolynomial.eval₂Hom_X' _ _ (Sum.inl i)
  have hN : N.map φ = M := by
    ext i j
    exact MvPolynomial.eval₂Hom_X' _ _ (Sum.inr (i, j))
  have hdet : φ N.det = M.det := by
    rw [← hN, RingHom.map_det, RingHom.mapMatrix_apply]
  have h' := congrArg φ h
  simpa only [map_mul, map_pow, ← disc_comp, ← subst_comp, hF, hN, hdet] using h'

/-- Relative invariance of `I` for the ordinary `GL₂` action. -/
@[simp] theorem invI_smul_generalLinearGroup (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    invI (g • f) = (GeneralLinearGroup.det g : R) ^ 4 * invI f := by
  rw [smul_eq_subst, invI_subst, GeneralLinearGroup.val_det_apply]

/-- Relative invariance of `J` for the ordinary `GL₂` action. -/
@[simp] theorem invJ_smul_generalLinearGroup (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    invJ (g • f) = (GeneralLinearGroup.det g : R) ^ 6 * invJ f := by
  rw [smul_eq_subst, invJ_subst, GeneralLinearGroup.val_det_apply]

/-- Relative invariance of the discriminant for the ordinary `GL₂` action. -/
@[simp] theorem disc_smul_generalLinearGroup (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    disc (g • f) = (GeneralLinearGroup.det g : R) ^ 12 * disc f := by
  rw [smul_eq_subst, disc_subst, GeneralLinearGroup.val_det_apply]

/-- The determinant-to-the-minus-two action used in two-descent. It is kept separate from the
ordinary action, which is used for integral orbit enumeration. -/
def twistedSMul (g : GL (Fin 2) R) (f : BinaryQuartic R) : BinaryQuartic R :=
  ((GeneralLinearGroup.det g)⁻¹ : Rˣ).val ^ 2 • (g • f)

/-- The twisted substitution is the ordinary one times the inverse determinant squared. -/
theorem twistedSMul_def (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    twistedSMul g f = ((GeneralLinearGroup.det g)⁻¹ : Rˣ).val ^ 2 • (g • f) := (rfl)

/-- The identity fixes a quartic under twisted substitution. -/
@[simp] theorem twistedSMul_one (f : BinaryQuartic R) : twistedSMul 1 f = f := by
  simp [twistedSMul_def]

/-- Twisted substitution satisfies the left action law. -/
theorem twistedSMul_mul (g h : GL (Fin 2) R) (f : BinaryQuartic R) :
    twistedSMul (g * h) f = twistedSMul g (twistedSMul h f) := by
  simp [twistedSMul_def, smul_eq_subst, subst_mul, subst_smul, smul_smul,
    mul_pow, mul_comm]

/-- Scalar matrices act trivially under twisted substitution. -/
@[simp] theorem twistedSMul_scalar (u : Rˣ) (f : BinaryQuartic R) :
    twistedSMul (GeneralLinearGroup.scalar (Fin 2) u) f = f := by
  simp [twistedSMul_def, GeneralLinearGroup.det_scalar, scalar_smul, smul_smul,
    ← pow_mul, ← mul_pow]

/-- The twisted action fixes `I`. -/
@[simp] theorem invI_twistedSMul (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    invI (twistedSMul g f) = invI f := by
  rw [twistedSMul_def, invI_smul, invI_smul_generalLinearGroup, ← mul_assoc, ← pow_mul]
  simp only [← mul_pow, Units.inv_mul, one_pow, one_mul]

/-- The twisted action fixes `J`. -/
@[simp] theorem invJ_twistedSMul (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    invJ (twistedSMul g f) = invJ f := by
  rw [twistedSMul_def, invJ_smul, invJ_smul_generalLinearGroup, ← mul_assoc, ← pow_mul]
  simp only [← mul_pow, Units.inv_mul, one_pow, one_mul]

/-- The twisted action fixes the integral discriminant, also in characteristic three. -/
@[simp] theorem disc_twistedSMul (g : GL (Fin 2) R) (f : BinaryQuartic R) :
    disc (twistedSMul g f) = disc f := by
  rw [twistedSMul_def, disc_smul, disc_smul_generalLinearGroup, ← mul_assoc, ← pow_mul]
  simp only [← mul_pow, Units.inv_mul, one_pow, one_mul]

/-- Ordinary and twisted substitution agree when the determinant has square one. -/
theorem twistedSMul_eq_smul {g : GL (Fin 2) R}
    (hg : (GeneralLinearGroup.det g : R) ^ 2 = 1) (f : BinaryQuartic R) :
    twistedSMul g f = g • f := by
  have hu : GeneralLinearGroup.det g ^ 2 = 1 := Units.ext hg
  have hi : (GeneralLinearGroup.det g)⁻¹ ^ 2 = 1 := by rw [inv_pow, hu, inv_one]
  have hv : ((GeneralLinearGroup.det g)⁻¹ : Rˣ).val ^ 2 = (1 : R) := congrArg Units.val hi
  rw [twistedSMul_def, hv, one_smul]

/-- The minus-identity fixes every quartic under the ordinary action. -/
@[simp] theorem neg_one_generalLinearGroup_smul (f : BinaryQuartic R) :
    (-1 : GL (Fin 2) R) • f = f := by
  have h : GeneralLinearGroup.scalar (Fin 2) (-1 : Rˣ) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal, Units.val_neg]
  rw [← h, scalar_smul]
  norm_num

end Invariants

end TauCeti.BinaryQuartic
