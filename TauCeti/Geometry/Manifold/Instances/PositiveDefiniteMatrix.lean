/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosDef
public import TauCeti.Analysis.Matrix.Exponential.Log
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Analysis.Calculus.ContDiff.Star
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Exponential coordinates on the positive-definite cone

The positive-definite matrices form an open submanifold of the real vector space of Hermitian
matrices. Over either `ℝ` or `ℂ`, the exponential is a global diffeomorphism from the Hermitian
matrices onto this cone, with inverse the continuous-functional-calculus logarithm. These are
the positive-factor coordinates for matrix polar decomposition.

The manifold structure is the native structure of an open subset of a normed space. In
particular it is induced by the Hermitian subspace with the ℓ² operator norm, independently of
the exponential chart. To state or use `Matrix.hermitianExpDiffeomorph`, first
`open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.
The smoothness and inverse identities come from `Matrix.contDiffOn_cfc_log`,
`Matrix.IsHermitian.cfc_log_exp`, and `Matrix.PosDef.exp_cfc_log`.

The unitary group acts on the cone by conjugation: for a unitary (over `ℝ`, orthogonal) matrix `V`,
`P ↦ V P Vᴴ` is a diffeomorphism of the cone (`Matrix.posDefUnitaryConj`), the restriction of a
real-linear automorphism of the Hermitian matrices that preserves positive definiteness. This is the
action on the positive factors under which the polar coordinates of
`TauCeti.Analysis.Matrix.Polar.Diffeomorph` are equivariant.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Sections 2.3 and 2.5.
-/

public noncomputable section

open NormedSpace TopologicalSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

section Cone

variable (n 𝕜 : Type*) [Finite n] [RCLike 𝕜]

/-- The positive-definite cone, as an open subset of the real space of Hermitian matrices.
Its subtype carries the standard open-submanifold structure. -/
def posDefOpens : Opens (selfAdjoint (Matrix n n 𝕜)) :=
  ⟨{A | (A : Matrix n n 𝕜).PosDef}, isOpen_setOfPred_posDef_selfAdjoint⟩

variable {n 𝕜}

/-- Membership in the positive-definite cone is positive definiteness of the underlying matrix. -/
@[simp]
theorem mem_posDefOpens (A : selfAdjoint (Matrix n n 𝕜)) :
    A ∈ posDefOpens n 𝕜 ↔ (A : Matrix n n 𝕜).PosDef := Iff.rfl

end Cone

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The inclusion of the positive-definite cone into the matrices is smooth, of every
regularity. -/
theorem contMDiff_coe_posDefOpens {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) 𝓘(ℝ, Matrix n n 𝕜) k
      (fun P : posDefOpens n 𝕜 ↦ ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜)) :=
  (selfAdjoint.contDiff_subtype_val ℝ).contMDiff.comp contMDiff_subtypeVal

variable (n 𝕜) in
/-- Exponential coordinates on the positive-definite cone: a global real diffeomorphism from
Hermitian matrices (symmetric matrices over `ℝ`), with inverse the matrix logarithm.
The regularity order `k` can be arbitrary, including analytic. The Hermitian space carries the
ℓ² operator norm: users should `open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`. -/
def hermitianExpDiffeomorph (k : ℕ∞ω) :
    selfAdjoint (Matrix n n 𝕜) ≃ₘ^k⟮𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)),
      𝓘(ℝ, selfAdjoint (Matrix n n 𝕜))⟯ posDefOpens n 𝕜 where
  toFun X := ⟨⟨exp (X : Matrix n n 𝕜), X.prop.exp⟩,
    (isHermitian_iff_isSelfAdjoint.mpr X.prop).posDef_exp⟩
  invFun P := ⟨cfc Real.log (P.val : Matrix n n 𝕜), cfc_predicate _ _⟩
  left_inv X := Subtype.ext ((isHermitian_iff_isSelfAdjoint.mpr X.prop).cfc_log_exp)
  right_inv P := Subtype.ext (Subtype.ext P.prop.exp_cfc_log)
  contMDiff_toFun := by
    apply (TauCeti.ContMDiff.subtypeVal_comp_iff (posDefOpens n 𝕜) _).mp
    have hexp : ContDiff ℝ k (exp : Matrix n n 𝕜 → Matrix n n 𝕜) :=
      NormedSpace.contDiff_exp ℝ
    have h := (selfAdjointPartL ℝ (Matrix n n 𝕜)).contDiff.comp
      (hexp.comp (selfAdjoint.contDiff_subtype_val ℝ))
    refine h.contMDiff.congr fun X ↦ ?_
    exact (X.prop.exp.selfAdjointPart_apply ℝ).symm
  contMDiff_invFun := by
    have hlog := (Matrix.contDiffOn_cfc_log (n := n) (𝕜 := 𝕜) (k := k)).restrict_scalars ℝ
    have h := (selfAdjointPartL ℝ (Matrix n n 𝕜)).contDiff.contMDiff.comp
      (hlog.contMDiffOn.comp_contMDiff contMDiff_coe_posDefOpens fun P ↦ P.prop)
    refine h.congr fun P ↦ ?_
    exact ((cfc_predicate Real.log (P.val : Matrix n n 𝕜)).selfAdjointPart_apply ℝ).symm

/-- The underlying matrix of exponential coordinates is the matrix exponential. -/
@[simp]
theorem coe_hermitianExpDiffeomorph_apply (k : ℕ∞ω) (X : selfAdjoint (Matrix n n 𝕜)) :
    (((hermitianExpDiffeomorph n 𝕜 k X).val : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      exp (X : Matrix n n 𝕜) := (rfl)

/-- The inverse coordinates are the continuous-functional-calculus matrix logarithm. -/
@[simp]
theorem coe_hermitianExpDiffeomorph_symm_apply (k : ℕ∞ω) (P : posDefOpens n 𝕜) :
    ((hermitianExpDiffeomorph n 𝕜 k).symm P : Matrix n n 𝕜) =
      cfc Real.log (P.val : Matrix n n 𝕜) := (rfl)

/-! ### Unitary conjugation -/

/-- Conjugation `P ↦ V P Vᴴ` of the positive-definite cone by a unitary matrix `V`. -/
private def unitaryConjAux (V : unitaryGroup n 𝕜) (P : posDefOpens n 𝕜) : posDefOpens n 𝕜 :=
  ⟨⟨V * ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) * star (V : Matrix n n 𝕜),
    P.val.prop.conjugate _⟩, (mem_posDefOpens _).2
      ((IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).2 P.prop)⟩

private theorem contMDiff_unitaryConjAux {k : ℕ∞ω} (V : unitaryGroup n 𝕜) :
    ContMDiff 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) k
      (unitaryConjAux V) := by
  apply (TauCeti.ContMDiff.subtypeVal_comp_iff (posDefOpens n 𝕜) _).mp
  have h : ContDiff ℝ k
      (fun X : Matrix n n 𝕜 ↦ (V : Matrix n n 𝕜) * X * star (V : Matrix n n 𝕜)) :=
    (contDiff_const.mul contDiff_id).mul contDiff_const
  refine (((selfAdjointPartL ℝ (Matrix n n 𝕜)).contDiff.comp h).contMDiff.comp
    contMDiff_coe_posDefOpens).congr fun P ↦ ?_
  exact ((P.val.prop.conjugate _).selfAdjointPart_apply ℝ).symm

private theorem unitaryConjAux_star_unitaryConjAux (V : unitaryGroup n 𝕜) (P : posDefOpens n 𝕜) :
    unitaryConjAux (star V) (unitaryConjAux V P) = P := by
  refine Subtype.ext (Subtype.ext ?_)
  simp only [unitaryConjAux, Unitary.coe_star, star_star, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul]
  rw [mul_assoc, Unitary.coe_star_mul_self, mul_one]

variable (n 𝕜) in
/-- **Unitary conjugation of the positive-definite cone**: for a unitary matrix `V` (an orthogonal
matrix when `𝕜 = ℝ`), `P ↦ V P Vᴴ` is a diffeomorphism of the positive-definite cone onto itself,
whose inverse is conjugation by `Vᴴ`. It is the action of the unitary group on the positive
factors of polar decompositions. The regularity order `k` can be arbitrary, including analytic. -/
def posDefUnitaryConj (k : ℕ∞ω) (V : unitaryGroup n 𝕜) :
    posDefOpens n 𝕜 ≃ₘ^k⟮𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)),
      𝓘(ℝ, selfAdjoint (Matrix n n 𝕜))⟯ posDefOpens n 𝕜 where
  toFun := unitaryConjAux V
  invFun := unitaryConjAux (star V)
  left_inv := unitaryConjAux_star_unitaryConjAux V
  right_inv P := by
    simpa only [star_star] using unitaryConjAux_star_unitaryConjAux (star V) P
  contMDiff_toFun := contMDiff_unitaryConjAux V
  contMDiff_invFun := contMDiff_unitaryConjAux (star V)

/-- The underlying matrix of the conjugate `V P Vᴴ`. -/
@[simp]
theorem coe_posDefUnitaryConj_apply (k : ℕ∞ω) (V : unitaryGroup n 𝕜) (P : posDefOpens n 𝕜) :
    (((posDefUnitaryConj n 𝕜 k V P : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) =
      V * ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) * star (V : Matrix n n 𝕜) := (rfl)

/-- The inverse of conjugation by `V` is conjugation by `Vᴴ`. -/
@[simp]
theorem posDefUnitaryConj_symm_apply (k : ℕ∞ω) (V : unitaryGroup n 𝕜) (P : posDefOpens n 𝕜) :
    (posDefUnitaryConj n 𝕜 k V).symm P = posDefUnitaryConj n 𝕜 k (star V) P := (rfl)

/-- Conjugation by the identity matrix is the identity. -/
@[simp]
theorem posDefUnitaryConj_one_apply (k : ℕ∞ω) (P : posDefOpens n 𝕜) :
    posDefUnitaryConj n 𝕜 k 1 P = P :=
  Subtype.ext (Subtype.ext (by simp))

/-- Conjugation is an action of the unitary group: conjugating by `V V'` is conjugating by `V'` and
then by `V`. -/
theorem posDefUnitaryConj_mul_apply (k : ℕ∞ω) (V V' : unitaryGroup n 𝕜) (P : posDefOpens n 𝕜) :
    posDefUnitaryConj n 𝕜 k (V * V') P = posDefUnitaryConj n 𝕜 k V (posDefUnitaryConj n 𝕜 k V' P) :=
  Subtype.ext (Subtype.ext (by simp [star_mul, mul_assoc]))

end Matrix
