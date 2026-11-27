/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.CellResolution
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.ZeroAction
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Cohomology

/-!
# A cell attached along a cycle that acts by zero on the coefficients

Let `K = C_*(Ω_b B; R) e₀ ⊕ C_*(Ω_b B; R) e₁` with `D e₁ = x e₀` be the free module of the cocycle
`TauCeti.cycleCellCocycle R n x` of one `(n + 1)`-cell attached along an `n`-cycle `x` of the
chains on the Moore loops, and let `M` be a DG right module over `C_*(Ω_b B; R)`. If `x` acts by
zero on `M`, the twisted complex `M ⊗ K = M e₀ ⊕ M e₁` has the differential of `M` on each
summand, so its cohomology is

`Hᵏ(M ⊗ K) ≅ Hᵏ(M) × H^{k + n + 1}(M)`

(`TauCeti.cycleCellCocycleHomologyEquivOfOpSmulEqZero`), in homological terms the homology of the
cell complex with one cell in each of the degrees `0` and `n + 1`, tensored with the homology of
`M`. The attaching cycle is invisible.

This happens for the coefficients on which the loops act **trivially**, through the augmentation:
`M` restricted along the composite `C_*(Ω_b B; R) → R → C_*(Ω_b B; R)` of the augmentation `ε`
and the unit (`TauCeti.trivialLoopChainAction`). A chain `x` with `ε(x) = 0`, such as a cycle of
positive dimension, acts by zero on any such module
(`TauCeti.op_smul_eq_zero_of_loopChainAugmentation_eq_zero`). For the chains on the loops
themselves with the trivial action, the twisted homology is `Hᵏ(Ω_b B) × H^{k + n + 1}(Ω_b B)`
(`TauCeti.cycleCellCocycleTrivialActionHomologyEquiv`). With their action by multiplication
instead, the twisted complex is identified with the free module `K`, which is a resolution of `R`
when `K` is Brown's model of `B`, as it is for the spheres
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`): the
difference between the two is the content of the fibration theorem for the path-loop fibration.

## Main definitions

* `TauCeti.cycleCellCocycleHomologyEquivOfOpSmulEqZero`: the cohomology of the twisted complex
  when the attaching cycle acts by zero.
* `TauCeti.trivialLoopChainAction`: the composite of the augmentation and the unit of the chains on
  the loops.
* `TauCeti.cycleCellCocycleTrivialActionHomologyEquiv`: the cohomology of the twisted complex with
  coefficients in the chains on the loops, acted on trivially.

## Main results

* `TauCeti.cycleCellCocycle_m_op_smul_eq_zero`: the entries of the cocycle act by zero when the
  attaching cycle does.
* `TauCeti.op_smul_eq_zero_of_loopChainAugmentation_eq_zero`: a chain of augmentation zero acts by
  zero through the trivial action.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 7 (the fibration
  theorem).
-/

public noncomputable section

open MulOpposite

namespace TauCeti

variable {B : Type*} [TopologicalSpace B] {b : B} {R : Type*} [CommRing R]

/-! ### A cell attached along a cycle acting by zero -/

section ZeroAction

variable {n : ℕ} {x : loopChainAlgebra B b R}
  (hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
  (hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0)
  {M : Type*} [AddCommGroup M] [Module R M] [Module (loopChainAlgebra B b R)ᵐᵒᵖ M]
  [IsScalarTower R (loopChainAlgebra B b R)ᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).opposite.piece
    ℳ]
  {dM : M →ₗ[R] M} (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM)

omit [Module R M] [IsScalarTower R (loopChainAlgebra B b R)ᵐᵒᵖ M] in
/-- If the attaching cycle `x` acts by zero on `M`, so does every entry of the cocycle
`TauCeti.cycleCellCocycle R n x`. -/
theorem cycleCellCocycle_m_op_smul_eq_zero (h : ∀ α : M, op x • α = 0) (y z : Unit ⊕ Unit)
    (α : M) : op ((cycleCellCocycle R n x hx hdx).m y z) • α = 0 := by
  rcases y with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · simp
  · rcases z with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [h]

/-- **The twisted complex of a cell attached along a cycle acting by zero.** If the attaching
cycle `x` of `TauCeti.cycleCellCocycle R n x` acts by zero on `M`, the cohomology of the twisted
complex `M e₀ ⊕ M e₁` in degree `k` is `Hᵏ(M) × H^{k + n + 1}(M)`: the component of `e₀` gives the
first factor and the component of `e₁`, a generator of index `n + 1`, the second. -/
def cycleCellCocycleHomologyEquivOfOpSmulEqZero (h : ∀ α : M, op x • α = 0) (k : ℤ) :
    ((cycleCellCocycle R n x hx hdx).coefficientCochainComplex hM).homology k ≃ₗ[R]
      hM.cohomologyGrading k × hM.cohomologyGrading (k + ((n : ℤ) + 1)) :=
  RowFiniteTwistingCocycle.coefficientHomologyEquivOfForallOpSmulEqZero hM
      (cycleCellCocycle_m_op_smul_eq_zero hx hdx h) k ≪≫ₗ
    LinearEquiv.sumPiEquivProdPi R Unit Unit _ ≪≫ₗ
    ((LinearEquiv.piUnique R _).trans
        (LinearEquiv.ofEq _ _ (by rw [Sum.elim_inl, add_zero]))).prodCongr
      (LinearEquiv.piUnique R _)

end ZeroAction

/-! ### The trivial action of the chains on the loops -/

section TrivialAction

variable (B b R) in
/-- The **trivial action** of the chains on the loops: the composite of the augmentation
`C_*(Ω_b B; R) → R` with the unit `R → C_*(Ω_b B; R)`. A DG right module restricted along it is
acted on by a chain `a` through the scalar `ε(a)`. -/
def trivialLoopChainAction :
    DGAlgHom (loopChain_isDGAlgebra B b R) (loopChain_isDGAlgebra B b R) :=
  (loopChain_isDGAlgebra B b R).unitHom.comp (loopChainAugmentation B b R)

/-- The trivial action sends a chain to the unit times its augmentation. -/
@[simp]
theorem trivialLoopChainAction_apply (a : loopChainAlgebra B b R) :
    trivialLoopChainAction B b R a = algebraMap R _ (loopChainAugmentation B b R a) := by
  rw [trivialLoopChainAction, DGAlgHom.comp_apply, IsDGAlgebra.unitHom_apply]

variable {M : Type*} [AddCommGroup M] [Module (loopChainAlgebra B b R)ᵐᵒᵖ M]

/-- **A chain of augmentation zero acts by zero through the trivial action.** -/
theorem op_smul_eq_zero_of_loopChainAugmentation_eq_zero {a : loopChainAlgebra B b R}
    (ha : loopChainAugmentation B b R a = 0)
    (α : DGRightModule.RestrictScalars (trivialLoopChainAction B b R) M) : op a • α = 0 := by
  apply DGRightModule.RestrictScalars.ext
  rw [DGRightModule.RestrictScalars.val_op_smul, trivialLoopChainAction_apply, ha, map_zero,
    op_zero, zero_smul, DGRightModule.RestrictScalars.val_zero]

/- Instance search does not find the graded action of the chains on the loops on their restriction
along the trivial action through the general instance on restrictions, because it finds
different, though definitionally equal, instances on the chain algebra of the loop space; it is
restated here, as in `TauCeti.AlgebraicTopology.DGLocalSystem.Basic`. -/
/-- The action of `C_*(Ω_b B; R)` on its restriction along the trivial action respects degrees. -/
instance : SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).opposite.piece
    (IsDGRightModule.restrictScalarsGrading (ℳ := cubicalChainGrading (MooreLoopSpace B b) R)
      (trivialLoopChainAction B b R)) :=
  gradedSMul_restrictScalarsGrading (ℳ := cubicalChainGrading (MooreLoopSpace B b) R)
    (trivialLoopChainAction B b R)

variable {n : ℕ} {x : loopChainAlgebra B b R}
  (hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
  (hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0)

/-- **The twisted complex with coefficients in the chains on the loops, acted on trivially.** If
the attaching cycle `x` has augmentation zero, as every cycle of positive dimension does, the
cohomology of the twisted complex of `TauCeti.cycleCellCocycle R n x` with coefficients in the
chains `C_*(Ω_b B; R)` restricted along the trivial action is `Hᵏ(Ω_b B) × H^{k + n + 1}(Ω_b B)`,
in the cohomological grading `C^{-q} = C_q`. -/
def cycleCellCocycleTrivialActionHomologyEquiv (hε : loopChainAugmentation B b R x = 0) (k : ℤ) :
    ((cycleCellCocycle R n x hx hdx).coefficientCochainComplex
        ((loopChain_isDGAlgebra B b R).isDGRightModule.restrictScalars
          (trivialLoopChainAction B b R))).homology k ≃ₗ[R]
      (loopChain_isDGAlgebra B b R).isDGRightModule.cohomologyGrading k ×
        (loopChain_isDGAlgebra B b R).isDGRightModule.cohomologyGrading (k + ((n : ℤ) + 1)) :=
  cycleCellCocycleHomologyEquivOfOpSmulEqZero hx hdx _
      (op_smul_eq_zero_of_loopChainAugmentation_eq_zero hε) k ≪≫ₗ
    ((loopChain_isDGAlgebra B b R).isDGRightModule.restrictScalarsCohomologyGradingEquiv
        (trivialLoopChainAction B b R) k).prodCongr
      ((loopChain_isDGAlgebra B b R).isDGRightModule.restrictScalarsCohomologyGradingEquiv
        (trivialLoopChainAction B b R) _)

end TrivialAction

end TauCeti
