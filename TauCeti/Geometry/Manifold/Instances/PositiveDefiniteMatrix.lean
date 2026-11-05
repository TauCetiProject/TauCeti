/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosDef
public import TauCeti.Analysis.Matrix.Exponential.Log
public import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Algebra.Module.Star

/-!
# Exponential coordinates on the positive-definite cone

The positive-definite matrices form an open submanifold of the real vector space of Hermitian
matrices. Over either `ℝ` or `ℂ`, the exponential is a global diffeomorphism from the Hermitian
matrices onto this cone, with inverse the continuous-functional-calculus logarithm. These are
the positive-factor coordinates for matrix polar decomposition.

The manifold structure is the native structure of an open subset of a normed space. In
particular it is induced by the Hermitian subspace, independently of the exponential chart.
The smoothness and inverse identities come from `Matrix.contDiffOn_cfc_log`,
`Matrix.IsHermitian.cfc_log_exp`, and `Matrix.PosDef.exp_cfc_log`.

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
  ⟨{A | (A : Matrix n n 𝕜).PosDef}, isOpen_setOf_posDef_selfAdjoint⟩

variable {n 𝕜}

/-- Membership in the positive-definite cone is positive definiteness of the underlying matrix. -/
@[simp]
theorem mem_posDefOpens (A : selfAdjoint (Matrix n n 𝕜)) :
    A ∈ posDefOpens n 𝕜 ↔ (A : Matrix n n 𝕜).PosDef := Iff.rfl

end Cone

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable (n 𝕜) in
/-- Exponential coordinates on the positive-definite cone: a global real diffeomorphism from
Hermitian matrices (symmetric matrices over `ℝ`), with inverse the matrix logarithm.
The regularity order `k` can be arbitrary, including analytic. -/
def hermitianExpDiffeomorph (k : ℕ∞ω) :
    selfAdjoint (Matrix n n 𝕜) ≃ₘ^k⟮𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)),
      𝓘(ℝ, selfAdjoint (Matrix n n 𝕜))⟯ posDefOpens n 𝕜 where
  toFun X := ⟨⟨exp (X : Matrix n n 𝕜), X.prop.exp⟩,
    (isHermitian_iff_isSelfAdjoint.mpr X.prop).posDef_exp⟩
  invFun P := ⟨cfc Real.log (P.1 : Matrix n n 𝕜), cfc_predicate _ _⟩
  left_inv X := Subtype.ext ((isHermitian_iff_isSelfAdjoint.mpr X.prop).cfc_log_exp)
  right_inv P := Subtype.ext (Subtype.ext P.prop.exp_cfc_log)
  contMDiff_toFun := by
    intro X₀
    -- Use the local-property lemma: the ContMDiff wrapper fixes the order at ∞.
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ X₀).mp
    have hexp : ContDiff ℝ k (exp : Matrix n n 𝕜 → Matrix n n 𝕜) :=
      NormedSpace.contDiff_exp ℝ
    -- The selfAdjoint subgroup and its real submodule have definitionally equal carriers
    -- and induced topologies, so subtypeL is the coercion from selfAdjoint.
    have h := (selfAdjointPartL ℝ (Matrix n n 𝕜)).contDiff.comp
      (hexp.comp (selfAdjoint.submodule ℝ (Matrix n n 𝕜)).subtypeL.contDiff)
    refine (h.contMDiff.congr fun X ↦ ?_).contMDiffAt
    exact (X.prop.exp.selfAdjointPart_apply ℝ).symm
  contMDiff_invFun := by
    have hlog := (Matrix.contDiffOn_cfc_log (n := n) (𝕜 := 𝕜) (k := k)).restrict_scalars ℝ
    -- As above, the real submodule has the same carrier and topology as selfAdjoint.
    have hι : ContDiff ℝ k (fun X : selfAdjoint (Matrix n n 𝕜) ↦
        (X : Matrix n n 𝕜)) :=
      (selfAdjoint.submodule ℝ (Matrix n n 𝕜)).subtypeL.contDiff
    have hval : ContMDiff 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜))
        𝓘(ℝ, Matrix n n 𝕜) k
        (fun P : posDefOpens n 𝕜 ↦ (P.1 : Matrix n n 𝕜)) :=
      hι.contMDiff.comp contMDiff_subtype_val
    have h := (selfAdjointPartL ℝ (Matrix n n 𝕜)).contDiff.contMDiff.comp
      (hlog.contMDiffOn.comp_contMDiff hval fun P ↦ P.prop)
    refine h.congr fun P ↦ ?_
    exact ((cfc_predicate Real.log (P.1 : Matrix n n 𝕜)).selfAdjointPart_apply ℝ).symm

/-- The underlying matrix of exponential coordinates is the matrix exponential. -/
@[simp]
theorem coe_hermitianExpDiffeomorph_apply (k : ℕ∞ω) (X : selfAdjoint (Matrix n n 𝕜)) :
    (((hermitianExpDiffeomorph n 𝕜 k X).1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      exp (X : Matrix n n 𝕜) := (rfl)

/-- The inverse coordinates are the continuous-functional-calculus matrix logarithm. -/
@[simp]
theorem coe_hermitianExpDiffeomorph_symm_apply (k : ℕ∞ω) (P : posDefOpens n 𝕜) :
    ((hermitianExpDiffeomorph n 𝕜 k).symm P : Matrix n n 𝕜) =
      cfc Real.log (P.1 : Matrix n n 𝕜) := (rfl)

end Matrix
