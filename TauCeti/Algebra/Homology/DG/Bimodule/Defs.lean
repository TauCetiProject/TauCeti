/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.Ring.NegOnePow

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

/-- The three-term Leibniz rule on homogeneous left scalars and module elements suffices
to construct a DG bimodule, by taking either the right or the left scalar to be one. -/
theorem of_leibniz_smul_op_smul (G : InternalGrading R M ℤ)
    [SetLike.GradedSMul 𝒜 G.piece]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece G.piece]
    (hD : LinearMap.IsHomogeneous dM G.piece G.piece 1) (hD₂ : ∀ x, dM (dM x) = 0)
    (hLeibniz : ∀ {p q : ℤ} {a : A}, a ∈ 𝒜 p → ∀ {x : M}, x ∈ G.piece q → ∀ b : B,
      dM (a • (op b • x)) =
        dA a • (op b • x) + p.negOnePow • (a • (op b • dM x)) +
          (p + q).negOnePow • (a • (op (dB b) • x))) :
    IsDGBimodule hA hB G.piece dM where
  isHomogeneous := hD
  sq_zero := hD₂
  leibniz := by
    intro p a ha z
    let L := Algebra.lsmul (A := A) R R M
    have h : dM ∘ₗ L a =
        L (dA a) + negOnePowCast R p • (L a ∘ₗ dM) := by
      apply G.linearMap_ext
      intro q x hx
      simpa only [L, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        Algebra.lsmul_apply, op_one, one_smul, hB.map_one_eq_zero, op_zero, zero_smul,
        smul_zero, add_zero, negOnePow_smul_eq_negOnePowCast_smul (R := R)] using hLeibniz ha hx 1
    simpa only [L, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Algebra.lsmul_apply, negOnePow_smul_eq_negOnePowCast_smul (R := R)]
      using LinearMap.congr_fun h z
  leibniz_right := by
    intro q x hx b
    simpa only [hA.map_one_eq_zero, zero_smul, smul_zero, Int.negOnePow_zero, zero_add, one_smul]
      using hLeibniz (SetLike.one_mem_graded 𝒜) hx b

open scoped TensorProduct

/-- When the two factor actions compose to the pure-tensor action, the enveloping
Leibniz rule gives the two DG bimodule Leibniz rules. -/
theorem of_leibniz_tmul_smul [Module (A ⊗[R] Bᵐᵒᵖ) M] (G : InternalGrading R M ℤ)
    [SetLike.GradedSMul 𝒜 G.piece]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece G.piece]
    (hsmul : ∀ (a : A) (b : Bᵐᵒᵖ) (x : M), a • (b • x) = (a ⊗ₜ[R] b) • x)
    (hD : LinearMap.IsHomogeneous dM G.piece G.piece 1) (hD₂ : ∀ x, dM (dM x) = 0)
    (hLeibniz : ∀ {p q : ℤ} {a : A}, a ∈ 𝒜 p → ∀ {x : M}, x ∈ G.piece q → ∀ b : B,
      dM ((a ⊗ₜ[R] op b) • x) = (dA a ⊗ₜ[R] op b) • x +
        negOnePowCast R p • ((a ⊗ₜ[R] op b) • dM x) +
        negOnePowCast R (p + q) • ((a ⊗ₜ[R] op (dB b)) • x)) :
    IsDGBimodule hA hB G.piece dM := by
  apply of_leibniz_smul_op_smul G hD hD₂
  intro p q a ha x hx b
  simpa only [hsmul, negOnePow_smul_eq_negOnePowCast_smul (R := R)] using hLeibniz ha hx b

end IsDGBimodule

/-- A DG algebra is its regular diagonal DG bimodule, with ordinary left and right
multiplication and its original differential. -/
theorem IsDGAlgebra.isDGBimodule (hA : IsDGAlgebra 𝒜 dA) : IsDGBimodule hA hA 𝒜 dA where
  toIsDGLeftModule := hA.isDGLeftModule
  leibniz_right := hA.isDGRightModule.leibniz

end TauCeti
