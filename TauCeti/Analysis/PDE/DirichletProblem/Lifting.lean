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

For a bounded energy form coercive on `H¹₀(Ω)`, `dirichletLiftingL` sends a pair `(g, ℓ)`
to the weak solution with boundary lifting `g ∈ H¹(Ω)` and forcing `ℓ ∈ H⁻¹(Ω)`.
It is a continuous linear map, with bounds in terms of the coercivity constant and the norm
of the energy form. No boundedness or boundary regularity of the open domain is needed.

The boundary condition is `u - g ∈ H¹₀(Ω)`. In particular, the solution depends only on the
class of the lifting modulo `H¹₀(Ω)`, not on its values in the interior. The characterization
`dirichletLiftingL_eq_iff` allows the operator to be used without unfolding its construction.
For zero forcing its action on liftings is an idempotent projection onto weakly homogeneous
solutions.

The construction uses `IsCoercive.solutionWithLifting`, the Lax–Milgram solution for the
correction `u - g` with forcing `ℓ - B(g, ·)`.

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

private theorem exists_lifting_operator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    ∃ T : (W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2,
      ∀ g ℓ, T (g, ℓ) - g ∈ w1p0Submodule mu Omega 2 ∧
        ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (T (g, ℓ)) v = ℓ v := by
  let S : W1p0 mu Omega 2 →L[ℝ] W1p mu Omega 2 :=
    (w1p0Submodule mu Omega 2).toSubmodule.subtypeL
  -- Identify the two bundled restrictions explicitly, rather than unfolding their instances
  -- while elaborating the abstract lifting theorem on the nested Sobolev subtypes.
  have hB : (energyFormH1L hcoeff).bilinearComp S S = energyFormH1L0 hcoeff := by
    ext u v
    simp [ContinuousLinearMap.bilinearComp_apply, energyFormH1L_apply, energyFormH1L0_apply, S]
  have h : IsCoercive ((energyFormH1L hcoeff).bilinearComp S S) := hB.symm ▸ hcoercive
  refine ⟨h.solutionWithLifting, fun g ℓ ↦ ?_⟩
  obtain ⟨w, hw⟩ := h.solutionWithLifting_sub_mem_range g ℓ
  constructor
  · rw [← hw]
    exact w.2
  · intro v
    rw [← energyFormH1L_apply hcoeff]
    exact h.apply_solutionWithLifting g ℓ v

variable (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hcoercive : IsCoercive (energyFormH1L0 hcoeff))

/-- The bounded linear Dirichlet solution map for an `H¹` boundary lifting and `H⁻¹` forcing.
It is characterized by `dirichletLiftingL_eq_iff`. -/
def dirichletLiftingL :
    (W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2)) →L[ℝ] W1p mu Omega 2 :=
  (exists_lifting_operator hcoeff hcoercive).choose

/-- The solution has the prescribed boundary class modulo the zero-boundary Sobolev space. -/
@[simp]
theorem dirichletLiftingL_sub_mem (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletLiftingL hcoeff hcoercive (g, ℓ) - g ∈ w1p0Submodule mu Omega 2 :=
  ((exists_lifting_operator hcoeff hcoercive).choose_spec g ℓ).1

/-- The Dirichlet solution operator satisfies the weak equation against every `H¹₀` test. -/
@[simp]
theorem energyFormH1_dirichletLiftingL (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) (v : W1p0 mu Omega 2) :
    energyFormH1 a b c (dirichletLiftingL hcoeff hcoercive (g, ℓ)) v = ℓ v :=
  ((exists_lifting_operator hcoeff hcoercive).choose_spec g ℓ).2 v

/-- Characterization of the solution operator by its boundary class and weak equation. -/
theorem dirichletLiftingL_eq_iff {g u : W1p mu Omega 2}
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} :
    dirichletLiftingL hcoeff hcoercive (g, ℓ) = u ↔
      u - g ∈ w1p0Submodule mu Omega 2 ∧
        ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v := by
  constructor
  · rintro rfl
    exact ⟨dirichletLiftingL_sub_mem hcoeff hcoercive g ℓ,
      energyFormH1_dirichletLiftingL hcoeff hcoercive g ℓ⟩
  · intro hu
    exact (existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq hcoeff hcoercive g ℓ).unique
      ⟨dirichletLiftingL_sub_mem hcoeff hcoercive g ℓ,
        energyFormH1_dirichletLiftingL hcoeff hcoercive g ℓ⟩ hu

/-- Two liftings give the same solution for a fixed forcing exactly when they represent the
same boundary class. -/
theorem dirichletLiftingL_eq_iff_sub_mem (g g' : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletLiftingL hcoeff hcoercive (g, ℓ) =
        dirichletLiftingL hcoeff hcoercive (g', ℓ) ↔
      g - g' ∈ w1p0Submodule mu Omega 2 := by
  constructor
  · intro h
    have h₁ := dirichletLiftingL_sub_mem hcoeff hcoercive g ℓ
    have h₂ := dirichletLiftingL_sub_mem hcoeff hcoercive g' ℓ
    rw [h] at h₁
    have heq : g - g' =
        (dirichletLiftingL hcoeff hcoercive (g', ℓ) - g') -
          (dirichletLiftingL hcoeff hcoercive (g', ℓ) - g) := by abel
    rw [heq]
    exact (w1p0Submodule mu Omega 2).sub_mem h₂ h₁
  · intro h
    apply (dirichletLiftingL_eq_iff hcoeff hcoercive).2
    refine ⟨?_, energyFormH1_dirichletLiftingL hcoeff hcoercive g' ℓ⟩
    have heq : dirichletLiftingL hcoeff hcoercive (g', ℓ) - g =
        (dirichletLiftingL hcoeff hcoercive (g', ℓ) - g') - (g - g') := by abel
    rw [heq]
    exact (w1p0Submodule mu Omega 2).sub_mem
      (dirichletLiftingL_sub_mem hcoeff hcoercive g' ℓ) h

/-- Solving the homogeneous equation twice does not change its solution: the zero-forcing
boundary solution map is a projection. -/
@[simp]
theorem dirichletLiftingL_idempotent (g : W1p mu Omega 2) :
    dirichletLiftingL hcoeff hcoercive
      (dirichletLiftingL hcoeff hcoercive (g, 0), 0) =
        dirichletLiftingL hcoeff hcoercive (g, 0) := by
  apply (dirichletLiftingL_eq_iff hcoeff hcoercive).2
  exact ⟨by simp, energyFormH1_dirichletLiftingL hcoeff hcoercive g 0⟩

variable {C : ℝ} (hC : 0 < C)
  (hlower : ∀ w : W1p0 mu Omega 2,
    C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) w)

include hC hlower

/-- Quantitative bound for the correction to the boundary lifting. -/
theorem norm_dirichletLiftingL_sub_le (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ‖dirichletLiftingL hcoeff hcoercive (g, ℓ) - g‖ ≤
      (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C :=
  norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hcoeff hC hlower
    (dirichletLiftingL_sub_mem hcoeff hcoercive g ℓ)
    (energyFormH1_dirichletLiftingL hcoeff hcoercive g ℓ)

/-- The solution norm is bounded in terms of the lifting, forcing, form norm, and coercivity. -/
theorem norm_dirichletLiftingL_le (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ‖dirichletLiftingL hcoeff hcoercive (g, ℓ)‖ ≤
      ‖g‖ + (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C := by
  calc
    _ ≤ ‖dirichletLiftingL hcoeff hcoercive (g, ℓ) - g‖ + ‖g‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith [norm_dirichletLiftingL_sub_le hcoeff hcoercive hC hlower g ℓ]

end TauCeti.PDE
