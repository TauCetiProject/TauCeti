/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Single
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Basic

/-!
# A contraction of the coinduced resolution

After forgetting the action and topology, Mathlib's shifted coinduced resolution
`C(G, X) → C(G, C(G, X)) → ⋯` is homotopy equivalent to `X` concentrated in degree zero.
The inclusion sends a coefficient to the constant function, the projection evaluates at `1`,
and evaluation at `1` in each positive degree gives the contracting homotopy.

This is the splitting needed when tensoring resolutions: homotopy equivalences can be tensored
without any flatness assumption. The contraction is on the underlying modules; evaluation at
`1` is not equivariant and does not contract the complex of invariant cochains.

The construction follows the recursion of `TopRep.d` and the evaluation identity recorded in
`TopRep.d_sum_apply_add_sum_d_apply`.

## References

* L. Evens, A generalization of the transfer map in the cohomology of groups,
  Transactions of the American Mathematical Society 108 (1963), §§2–5, for tensor resolutions.
-/

public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace TopRep

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

/-- The shifted coinduced resolution with its action and topology forgotten. -/
noncomputable abbrev resolutionModuleComplex : CochainComplex (ModuleCat.{max v w} R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (resolutionX X (n + 1)).V)
    (fun n ↦ ModuleCat.ofHom (d X (n + 1)).hom.toLinearMap)
    (fun n ↦ by
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
        ← ContinuousLinearMap.toLinearMap_comp,
        ← ContIntertwiningMap.toContinuousLinearMap_comp, ← hom_comp, d_comp_d]
      rfl)

private abbrev resolutionEval (n : ℕ) :
    ModuleCat.of R (resolutionX X (n + 1)).V ⟶ ModuleCat.of R (resolutionX X n).V :=
  ModuleCat.ofHom (ContinuousMap.evalCLM R (1 : G)).toLinearMap

/-- The augmentation of the underlying shifted resolution, by constant functions. -/
noncomputable def resolutionModuleIncl :
    (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R X.V) ⟶
      resolutionModuleComplex X :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (d X 0).hom.toLinearMap, by
      dsimp [resolutionModuleComplex, CochainComplex.of.d]
      rw [Category.comp_id]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact ConcreteCategory.congr_hom (d_comp_d X 0) x⟩

/-- The projection of the underlying shifted resolution onto its coefficients. -/
noncomputable def resolutionModuleProj :
    resolutionModuleComplex X ⟶
      (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R X.V) :=
  (CochainComplex.toSingle₀Equiv _ _).symm (resolutionEval X 0)

/-- The augmentation in degree zero is the original constant-function map. -/
@[simp] theorem resolutionModuleIncl_f_zero :
    (resolutionModuleIncl X).f 0 = ModuleCat.ofHom (d X 0).hom.toLinearMap :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The projection in degree zero evaluates at the identity. -/
@[simp] theorem resolutionModuleProj_f_zero :
    (resolutionModuleProj X).f 0 =
      ModuleCat.ofHom (ContinuousMap.evalCLM R (1 : G)).toLinearMap :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_zero _

/-- The projection vanishes in every positive degree. -/
@[simp] theorem resolutionModuleProj_f_succ (n : ℕ) :
    (resolutionModuleProj X).f (n + 1) = 0 :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_succ _ n

/-- Evaluation retracts the constant-function augmentation. -/
@[simp] theorem resolutionModuleIncl_comp_proj :
    resolutionModuleIncl X ≫ resolutionModuleProj X = 𝟙 _ := by
  apply to_single_hom_ext
  simp only [comp_f, resolutionModuleIncl_f_zero, resolutionModuleProj_f_zero, id_f]
  rfl

private theorem resolutionModule_contract_zero :
    (𝟙 (resolutionModuleComplex X) - resolutionModuleProj X ≫
      resolutionModuleIncl X).f 0 =
      (resolutionModuleComplex X).d 0 1 ≫ resolutionEval X 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  simp only [sub_f_apply, id_f, comp_f, resolutionModuleIncl_f_zero,
    resolutionModuleProj_f_zero, ModuleCat.hom_sub, ModuleCat.hom_comp, ModuleCat.hom_id,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  exact (hom_d_succ_apply_apply X 0 F 1).symm

private theorem resolutionModule_contract_succ (n : ℕ) :
    (𝟙 (resolutionModuleComplex X) - resolutionModuleProj X ≫
      resolutionModuleIncl X).f (n + 1) =
      resolutionEval X (n + 1) ≫ (resolutionModuleComplex X).d n (n + 1) +
        (resolutionModuleComplex X).d (n + 1) (n + 1 + 1) ≫ resolutionEval X (n + 2) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  simp only [sub_f_apply, id_f, comp_f, resolutionModuleProj_f_succ, zero_comp,
    sub_zero, ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    CochainComplex.of_d, ModuleCat.hom_ofHom]
  dsimp [resolutionEval]
  exact (sub_eq_iff_eq_add'.mp (hom_d_succ_apply_apply X (n + 1) F 1).symm)

/-- Evaluation contracts the identity onto the coefficient summand of the underlying
shifted resolution. -/
noncomputable def resolutionModuleHomotopy :
    Homotopy (𝟙 (resolutionModuleComplex X))
      (resolutionModuleProj X ≫ resolutionModuleIncl X) :=
  { hom := fun i j ↦ if h : j + 1 = i then
      ((resolutionModuleComplex X).XIsoOfEq h.symm).hom ≫ resolutionEval X (j + 1)
      else 0
    zero := fun i j h ↦ by
      simp only [ComplexShape.up_Rel] at h
      exact dite_eq_right h
    comm := fun i ↦ by
      cases i with
      | zero =>
        simp only [id_f, Homotopy.dNext_cochainComplex (P := resolutionModuleComplex X)
          (Q := resolutionModuleComplex X),
          Homotopy.prevD_zero_cochainComplex (P := resolutionModuleComplex X)
            (Q := resolutionModuleComplex X), dite_eq_left rfl,
          XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, add_zero]
        have h := resolutionModule_contract_zero X
        simp only [sub_f_apply, id_f] at h
        exact sub_eq_iff_eq_add.mp h
      | succ n =>
        simp only [id_f, Homotopy.dNext_cochainComplex (P := resolutionModuleComplex X)
          (Q := resolutionModuleComplex X),
          Homotopy.prevD_succ_cochainComplex (P := resolutionModuleComplex X)
            (Q := resolutionModuleComplex X), dite_eq_left rfl,
          XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
        have h := resolutionModule_contract_succ X n
        simp only [sub_f_apply, id_f] at h
        simpa only [add_comm] using sub_eq_iff_eq_add.mp h }

/-- The contracting homotopy in every positive degree evaluates the outermost variable at `1`. -/
@[simp] theorem resolutionModuleHomotopy_hom_succ (n : ℕ) :
    (resolutionModuleHomotopy X).hom (n + 1) n =
      ModuleCat.ofHom (ContinuousMap.evalCLM R (1 : G)).toLinearMap := by
  simp [resolutionModuleHomotopy]

/-- The underlying shifted coinduced resolution is homotopy equivalent to the coefficient
module concentrated in degree zero. No discreteness, compactness or flatness is needed. -/
noncomputable def resolutionModuleHomotopyEquiv :
    HomotopyEquiv ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R X.V))
      (resolutionModuleComplex X) where
  hom := resolutionModuleIncl X
  inv := resolutionModuleProj X
  homotopyHomInvId := Homotopy.ofEq (resolutionModuleIncl_comp_proj X)
  homotopyInvHomId := (resolutionModuleHomotopy X).symm

/-- The forward map of the homotopy equivalence is the constant-function augmentation. -/
@[simp] theorem resolutionModuleHomotopyEquiv_hom :
    (resolutionModuleHomotopyEquiv X).hom = resolutionModuleIncl X := (rfl)

/-- The inverse map of the homotopy equivalence is evaluation in degree zero. -/
@[simp] theorem resolutionModuleHomotopyEquiv_inv :
    (resolutionModuleHomotopyEquiv X).inv = resolutionModuleProj X := (rfl)

end TopRep
