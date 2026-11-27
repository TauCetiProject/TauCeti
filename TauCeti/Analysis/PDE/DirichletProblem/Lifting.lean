/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.InnerProductSpace.Variational.Lifting

/-!
# The Dirichlet solution operator with boundary liftings

For a bounded energy form coercive on `H¹₀(Ω)`, `dirichletSolutionWithLiftingL` sends a pair
`(g, ℓ)` to the weak solution with boundary lifting `g ∈ H¹(Ω)` and forcing `ℓ ∈ H⁻¹(Ω)`.
It is a continuous linear map, with bounds in terms of the coercivity constant and the norm
of the energy form. No boundedness or boundary regularity of the open domain is needed.

The boundary condition is `u - g ∈ H¹₀(Ω)`. In particular, the solution depends only on the
class of the lifting modulo `H¹₀(Ω)`, not on its values in the interior. The characterization
`dirichletSolutionWithLiftingL_eq_iff` allows the operator to be used without unfolding it.
For zero forcing its action on liftings is an idempotent projection onto weakly homogeneous
solutions, which fixes every lifting with vanishing gradient when there is no mass term
(`dirichletSolutionWithLiftingL_eq_self_of_gradient_eq_zero`). More generally, a solved lifting
can replace the original lifting for any forcing.

For operator-norm expressions, use `open scoped DirichletLifting` together with the usual
Sobolev normed-space instances and the two `W1p0.instStrongDualNormed*` shortcuts.
The scope supplies the full canonical seminormed group and real normed space structures on
joint lifting operators, avoiding expansion of nested Sobolev subtypes in instance synthesis.

The construction uses `IsCoercive.solutionWithLifting`, which adds `g` to the Lax–Milgram
solution for the correction `u - g` with forcing `ℓ - B(g, ·)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.2.1–§6.2.2.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

attribute [local instance] W1p0.instStrongDualNormedAddCommGroup W1p0.instStrongDualNormedSpace

/-! ### Opt-in operator-space shortcuts

`open scoped DirichletLifting` activates the canonical structures and projection shortcuts
below. They are needed when operator-norm lemmas infer the operator space before its Sobolev
parameters are known; without them even `norm_nonneg` can exceed the default heartbeat limit.
They do not replace the canonical subtype topologies on the input or output spaces. -/

namespace DirichletLifting

/-- The canonical seminormed group structure on joint lifting operators, cached for synthesis. -/
scoped instance instSeminormedAddCommGroup :
    SeminormedAddCommGroup
      ((W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The canonical real normed space structure on joint lifting operators, cached for synthesis. -/
scoped instance instNormedSpace :
    NormedSpace ℝ
      ((W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2) :=
  ContinuousLinearMap.toNormedSpace

/-- Addition from the cached seminormed structure, avoiding topology comparisons in
`norm_add_le`. -/
scoped instance instAdd :
    Add ((W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2) :=
  instSeminormedAddCommGroup.toAdd

/-- Subtraction from the cached seminormed structure, avoiding topology comparisons in
`norm_sub_le`. -/
scoped instance instSub :
    Sub ((W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2) :=
  instSeminormedAddCommGroup.toSub

/-- Norm compatibility with scalar multiplication, cached for `norm_smul`. -/
scoped instance instNormSMulClass :
    NormSMulClass ℝ
      ((W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2) := inferInstance

end DirichletLifting

open scoped DirichletLifting

variable (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hcoercive : IsCoercive (energyFormH1L0 hcoeff))

private theorem liftingForm_eq :
    (energyFormH1L hcoeff).bilinearComp
      (w1p0Submodule mu Omega 2).toSubmodule.subtypeL
      (w1p0Submodule mu Omega 2).toSubmodule.subtypeL = energyFormH1L0 hcoeff := by
  ext u v
  simp [ContinuousLinearMap.bilinearComp_apply, energyFormH1L_apply, energyFormH1L0_apply]

include hcoercive in
private theorem liftingCoercive :
    IsCoercive ((energyFormH1L hcoeff).bilinearComp
      (w1p0Submodule mu Omega 2).toSubmodule.subtypeL
      (w1p0Submodule mu Omega 2).toSubmodule.subtypeL) := by
  exact (liftingForm_eq hcoeff).symm ▸ hcoercive

-- Choosing an explicitly characterized witness keeps the generated equation lemma small:
-- a direct specialization makes its type-checking expand the nested Sobolev instances.
private theorem exists_lifting_operator :
    ∃ T : (W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2,
      T = (liftingCoercive hcoeff hcoercive).solutionWithLifting :=
  ⟨_, rfl⟩

/-- The bounded linear Dirichlet solution map for an `H¹` boundary lifting and `H⁻¹` forcing.
It is characterized by `dirichletSolutionWithLiftingL_eq_iff`. -/
def dirichletSolutionWithLiftingL :
    (W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2 :=
  (exists_lifting_operator hcoeff hcoercive).choose

private theorem liftingOperator_eq :
    dirichletSolutionWithLiftingL hcoeff hcoercive =
      (liftingCoercive hcoeff hcoercive).solutionWithLifting :=
  (exists_lifting_operator hcoeff hcoercive).choose_spec

/-- The solution is the lifting plus its zero-boundary Lax–Milgram correction. -/
theorem dirichletSolutionWithLiftingL_apply (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ) =
      g + (hcoercive.solutionOfFunctional
        (ℓ - (energyFormH1L hcoeff g).comp
          (w1p0Submodule mu Omega 2).toSubmodule.subtypeL) : W1p mu Omega 2) := by
  simpa only [liftingOperator_eq, liftingForm_eq, Submodule.subtypeL_apply] using
    (liftingCoercive hcoeff hcoercive).solutionWithLifting_apply g ℓ

/-- The solution has the prescribed boundary class modulo the zero-boundary Sobolev space. -/
@[simp]
theorem dirichletSolutionWithLiftingL_sub_mem (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ) - g ∈ w1p0Submodule mu Omega 2 := by
  obtain ⟨w, hw⟩ := (liftingCoercive hcoeff hcoercive).solutionWithLifting_sub_mem_range g ℓ
  rw [liftingOperator_eq, ← hw, Submodule.subtypeL_apply, ← ClosedSubmodule.mem_toSubmodule_iff]
  exact w.property

/-- The Dirichlet solution operator satisfies the weak equation against every `H¹₀` test. -/
@[simp]
theorem energyFormH1_dirichletSolutionWithLiftingL (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) (v : W1p0 mu Omega 2) :
    energyFormH1 a b c (dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ)) v = ℓ v := by
  simpa only [liftingOperator_eq, energyFormH1L_apply, Submodule.subtypeL_apply] using
    (liftingCoercive hcoeff hcoercive).apply_solutionWithLifting g ℓ v

/-- Characterization of the solution operator by its boundary class and weak equation. -/
theorem dirichletSolutionWithLiftingL_eq_iff {g u : W1p mu Omega 2}
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} :
    dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ) = u ↔
      u - g ∈ w1p0Submodule mu Omega 2 ∧
        ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v := by
  simpa [liftingOperator_eq, Set.mem_range, energyFormH1L_apply] using
    (liftingCoercive hcoeff hcoercive).solutionWithLifting_eq_iff (g := g) (u := u) (ℓ := ℓ)

/-- Two liftings give the same solution for a fixed forcing exactly when they represent the
same boundary class. -/
theorem dirichletSolutionWithLiftingL_eq_iff_sub_mem (g g' : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ) =
        dirichletSolutionWithLiftingL hcoeff hcoercive (g', ℓ) ↔
      g - g' ∈ w1p0Submodule mu Omega 2 := by
  simpa [liftingOperator_eq, Set.mem_range] using
    (liftingCoercive hcoeff hcoercive).solutionWithLifting_eq_iff_sub_mem_range g g' ℓ

/-- A solved lifting can replace the original lifting, independently of either forcing. -/
@[simp]
theorem dirichletSolutionWithLiftingL_dirichletSolutionWithLiftingL (g : W1p mu Omega 2)
    (ℓ' ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletSolutionWithLiftingL hcoeff hcoercive
      (dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ'), ℓ) =
        dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ) := by
  simpa only [liftingOperator_eq] using
    (liftingCoercive hcoeff hcoercive).solutionWithLifting_solutionWithLifting g ℓ' ℓ

/-- Zero boundary lifting recovers the Lax–Milgram solution on `H¹₀`. -/
@[simp]
theorem dirichletSolutionWithLiftingL_zero (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletSolutionWithLiftingL hcoeff hcoercive (0, ℓ) =
      (hcoercive.solutionOfFunctional ℓ : W1p mu Omega 2) := by
  simpa only [liftingOperator_eq, liftingForm_eq, Submodule.subtypeL_apply] using
    (liftingCoercive hcoeff hcoercive).solutionWithLifting_zero ℓ

/-- Every zero-boundary lifting gives the homogeneous-boundary solution. -/
@[simp]
theorem dirichletSolutionWithLiftingL_coe (w : W1p0 mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletSolutionWithLiftingL hcoeff hcoercive ((w : W1p mu Omega 2), ℓ) =
      (hcoercive.solutionOfFunctional ℓ : W1p mu Omega 2) := by
  simpa only [liftingOperator_eq, liftingForm_eq, Submodule.subtypeL_apply] using
    (liftingCoercive hcoeff hcoercive).solutionWithLifting_map w ℓ

/-- With zero lifting and `L²` forcing, the solution is `weakSolutionDirichlet`. -/
theorem dirichletSolutionWithLiftingL_zero_dirichletForcing (f : Lp ℝ 2 (mu.restrict Omega)) :
    dirichletSolutionWithLiftingL hcoeff hcoercive (0, dirichletForcing f) =
      (weakSolutionDirichlet hcoeff hcoercive f : W1p mu Omega 2) := by
  have hweak := isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive f
  exact (dirichletSolutionWithLiftingL_eq_iff hcoeff hcoercive).2
    ⟨by rw [sub_zero]; exact (weakSolutionDirichlet hcoeff hcoercive f).property,
      hweak.energyFormH1_eq_dirichletForcing⟩

/-- **A lifting with vanishing gradient is its own solution.** With no mass term and zero forcing,
a boundary lifting `g` with `∇g = 0`, such as a constant or a function constant on each connected
component of `Ω`, solves the Dirichlet problem with boundary values `g`. No connectedness of `Ω`
is needed. -/
theorem dirichletSolutionWithLiftingL_eq_self_of_gradient_eq_zero
    (hc : c =ᵐ[mu.restrict Omega] 0) {g : W1p mu Omega 2} (hg : W1p.gradient g = 0) :
    dirichletSolutionWithLiftingL hcoeff hcoercive (g, 0) = g :=
  (dirichletSolutionWithLiftingL_eq_iff hcoeff hcoercive).2 ⟨by simp, fun v => by
    rw [energyFormH1_congr_ae .rfl .rfl hc, energyFormH1_eq_zero_of_gradient_eq_zero a b hg,
      zero_apply]⟩

variable {C : ℝ} (hC : 0 < C)
  (hlower : ∀ w : W1p0 mu Omega 2,
    C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) w)

include hC hlower

/-- Quantitative bound for the correction to the boundary lifting. -/
theorem norm_dirichletSolutionWithLiftingL_sub_le (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ‖dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ) - g‖ ≤
      (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C :=
  norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hcoeff hC hlower
    (dirichletSolutionWithLiftingL_sub_mem hcoeff hcoercive g ℓ)
    (energyFormH1_dirichletSolutionWithLiftingL hcoeff hcoercive g ℓ)

/-- The solution norm is bounded in terms of the lifting, forcing, form norm, and coercivity. -/
theorem norm_dirichletSolutionWithLiftingL_apply_le (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ‖dirichletSolutionWithLiftingL hcoeff hcoercive (g, ℓ)‖ ≤
      ‖g‖ + (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C := by
  rw [liftingOperator_eq]
  refine ((liftingCoercive hcoeff hcoercive).norm_solutionWithLifting_apply_le hC
    (fun w => by simpa only [energyFormH1L_apply, Submodule.subtypeL_apply] using hlower w)
    g ℓ).trans ?_
  calc
    _ ≤ ‖g‖ + 1 * ((‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖ * 1) / C) := by
      gcongr <;> exact Submodule.norm_subtypeL_le _
    _ = _ := by ring

/-- Operator-norm bound for the joint boundary-lifting and forcing solution map. -/
theorem norm_dirichletSolutionWithLiftingL_le :
    ‖dirichletSolutionWithLiftingL hcoeff hcoercive‖ ≤
      1 + (1 + ‖energyFormH1L hcoeff‖) / C := by
  rw [liftingOperator_eq]
  refine ((liftingCoercive hcoeff hcoercive).norm_solutionWithLifting_le hC
    (fun w => by
      simpa only [energyFormH1L_apply, Submodule.subtypeL_apply] using hlower w)).trans ?_
  calc
    _ ≤ 1 + 1 * ((1 + ‖energyFormH1L hcoeff‖ * 1) / C) := by
      gcongr <;> exact Submodule.norm_subtypeL_le _
    _ = _ := by ring

end TauCeti.PDE
