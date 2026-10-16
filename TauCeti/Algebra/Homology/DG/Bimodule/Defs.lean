/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Defs

/-!
# Differential graded bimodules

An `(A, B)`-bimodule has a left `A`-action and a right `B`-action that commute. Right actions
are written using `Bᵐᵒᵖ`: `op b • x` means `x b`. Both actions add degrees, and one
square-zero differential satisfies the left and right graded Leibniz rules. In particular,
`d(a x b) = d(a) x b + (-1)^|a| a d(x) b + (-1)^(|a|+|x|) a x d(b)`.

`IsDGBimodule` extends the existing left DG module predicate by the right Leibniz rule; the
shared differential laws are stored only once. Its `isDGRightModule` projection allows the
same module to enter the balanced tensor differential construction. The regular bimodule of
a DG algebra supplies the diagonal bimodule used in tensor composition.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

open MulOpposite

namespace TauCeti

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}

/-- A differential graded `(A, B)`-bimodule, with left `A` and right `B` actions.
The actions commute, preserve the grading, and obey their respective Leibniz rules for a
single degree-one square-zero differential. -/
structure IsDGBimodule [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
    (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB)
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
    (dM : M →ₗ[R] M) : Prop extends IsDGLeftModule hA ℳ dM where
  /-- The right Leibniz rule, with the sign determined by the degree of the module element. -/
  leibniz_right : ∀ {q : ℤ} {x : M}, x ∈ ℳ q → ∀ b : B,
    dM (op b • x) = op b • dM x + q.negOnePow • (op (dB b) • x)

namespace IsDGBimodule

variable [SMulCommClass A Bᵐᵒᵖ M]

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  {dM : M →ₗ[R] M}

/-- Forget the left action of a DG bimodule, retaining its right DG module structure. -/
theorem isDGRightModule (hM : IsDGBimodule hA hB ℳ dM) : IsDGRightModule hB ℳ dM where
  isHomogeneous := hM.isHomogeneous
  sq_zero := hM.sq_zero
  leibniz := hM.leibniz_right

/-- The three-term Leibniz rule for the two-sided action. Only the left algebra element and
the module element need to be homogeneous; the right algebra element is arbitrary. -/
theorem leibniz_smul_op_smul (hM : IsDGBimodule hA hB ℳ dM)
    {p q : ℤ} {a : A} {x : M} (ha : a ∈ 𝒜 p) (hx : x ∈ ℳ q) (b : B) :
    dM (a • (op b • x)) =
      op b • (dA a • x) + p.negOnePow • (op b • (a • dM x)) +
        (p + q).negOnePow • (op (dB b) • (a • x)) := by
  rw [smul_comm a (op b) x, hM.leibniz_right (SetLike.GradedSMul.smul_mem ha hx),
    hM.leibniz ha x, smul_add, smul_comm (op b) p.negOnePow (a • dM x)]
  simp only [vadd_eq_add]

end IsDGBimodule

/-- A DG algebra is its regular diagonal DG bimodule, with ordinary left and right
multiplication and its original differential. -/
theorem IsDGAlgebra.isDGBimodule (hA : IsDGAlgebra 𝒜 dA) : IsDGBimodule hA hA 𝒜 dA where
  toIsDGLeftModule := hA.isDGLeftModule
  leibniz_right := hA.isDGRightModule.leibniz

end TauCeti
