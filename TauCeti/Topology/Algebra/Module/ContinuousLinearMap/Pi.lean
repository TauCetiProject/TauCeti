/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Topology.Instances.Matrix

/-!
# Bounded-convergence continuity and inversion on finite coordinate spaces

On a finite coordinate space `ι → 𝕜`, neither bounded-convergence continuity nor continuous
inversion of linear equivalences requires `CompleteSpace 𝕜`:
* `TauCeti.continuous_pi_clm_iff_apply` equates continuity of `T : Y → (ι → 𝕜) →L[𝕜] G` with
  continuity of the basis evaluations `y ↦ T y (Pi.single i 1)`;
* `ContinuousLinearMap.isInvertible_of_bijective_pi` equips any bijective `(ι → R) →L[R] (κ → R)`
  with `[Finite κ]` over a topological semiring `R` with a continuous inverse;
* `Continuous.pi_clm_inverse` proves continuity of `y ↦ (T y).inverse` via Cramer's rule.
-/

public section

section EvalBasis

variable {𝕜 ι Y G : Type*} [NontriviallyNormedField 𝕜] [Finite ι] [TopologicalSpace Y]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [Module 𝕜 G] [ContinuousSMul 𝕜 G]

/-- A family of continuous linear maps out of `ι → 𝕜` into a topological `𝕜`-module `G` is
continuous if and only if its values on `Pi.single i 1` vary continuously. -/
theorem TauCeti.continuous_pi_clm_iff_apply [DecidableEq ι] {T : Y → (ι → 𝕜) →L[𝕜] G} :
    Continuous T ↔ ∀ i : ι, Continuous fun y ↦ T y (Pi.single i 1) where
  mp hT i := (continuous_eval_const (Pi.single i 1)).comp hT
  mpr hT := by
    have := Fintype.ofFinite ι
    let rankOne (i : ι) : G →L[𝕜] ((ι → 𝕜) →L[𝕜] G) :=
      ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i).precomp G).comp
        ContinuousLinearMap.toSpanSingletonCLE.toContinuousLinearMap
    have h_eq : T = fun y ↦ ∑ i : ι, rankOne i (T y (Pi.single i 1)) := by
      funext y; ext v; rw [sum_apply]
      conv_lhs => rw [pi_eq_sum_univ' v, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ map_smul (T y) (v i) (Pi.single i 1)
    exact h_eq ▸ continuous_finsetSum _ fun i _ ↦ (rankOne i).continuous.comp (hT i)

end EvalBasis

section Inverse

/-- Any bijective continuous linear map into a finite coordinate space over a topological semiring
has a continuous inverse. -/
theorem ContinuousLinearMap.isInvertible_of_bijective_pi {R ι κ : Type*}
    [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [Finite κ]
    {f : (ι → R) →L[R] (κ → R)} (hf : Function.Bijective f) : f.IsInvertible := by
  let e := LinearEquiv.ofBijective f.toLinearMap hf
  exact .of_inverse (g := ⟨e.symm.toLinearMap, LinearMap.continuous_on_pi _⟩)
    (ext e.apply_symm_apply) (ext e.symm_apply_apply)

private theorem continuous_pi_clm_inverse_self {𝕜 ι Y : Type*}
    [NontriviallyNormedField 𝕜] [Finite ι] [TopologicalSpace Y]
    {T : Y → (ι → 𝕜) →L[𝕜] (ι → 𝕜)} (hT : Continuous T) (hbij : ∀ y, Function.Bijective (T y)) :
    Continuous fun y ↦ (T y).inverse := by
  classical
  have := Fintype.ofFinite ι
  let M : Y → Matrix ι ι 𝕜 := fun y ↦ LinearMap.toMatrix' (T y).toLinearMap
  have hM : Continuous M := continuous_matrix fun i j ↦
    (continuous_apply i).comp ((TauCeti.continuous_pi_clm_iff_apply.1 hT) j)
  have hMN (y : Y) : M y * LinearMap.toMatrix' (T y).inverse.toLinearMap = 1 := by
    have hcomp : (T y).toLinearMap.comp (T y).inverse.toLinearMap = LinearMap.id :=
      congrArg ContinuousLinearMap.toLinearMap
        ((T y).isInvertible_of_bijective_pi (hbij y)).self_comp_inverse
    rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id]
  refine TauCeti.continuous_pi_clm_iff_apply.2 fun j ↦ continuous_pi fun i ↦
    continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  have hdet : (M y₀).det ≠ 0 :=
    left_ne_zero_of_mul_eq_one (by rw [← Matrix.det_mul, hMN y₀, Matrix.det_one])
  refine (hM.continuousAt.matrix_inv_apply hdet i j).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [Matrix.inv_eq_right_inv (hMN y), LinearMap.toMatrix'_apply]; rfl

/-- Along a continuous family of pointwise bijective continuous linear maps between finite
coordinate spaces over `𝕜`, `(T y).inverse` varies continuously without `CompleteSpace 𝕜`. -/
theorem Continuous.pi_clm_inverse {𝕜 ι κ Y : Type*} [NontriviallyNormedField 𝕜]
    [Finite ι] [Finite κ] [TopologicalSpace Y] {T : Y → (ι → 𝕜) →L[𝕜] (κ → 𝕜)}
    (hT : Continuous T) (hbij : ∀ y, Function.Bijective (T y)) :
    Continuous fun y ↦ (T y).inverse := by
  by_cases hY : Nonempty Y
  · obtain ⟨y₀⟩ := hY
    have := Fintype.ofFinite ι; have := Fintype.ofFinite κ
    have hcard : Fintype.card ι = Fintype.card κ := by
      simpa only [Module.finrank_fintype_fun_eq_card] using
        (LinearEquiv.ofBijective (T y₀).toLinearMap (hbij y₀)).finrank_eq
    let e : (κ → 𝕜) ≃L[𝕜] (ι → 𝕜) :=
      ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : ι ↦ 𝕜) (Fintype.equivOfCardEq hcard).symm
    have hTe : Continuous fun y ↦ (T y).comp (e : (κ → 𝕜) →L[𝕜] (ι → 𝕜)) :=
      ((e : (κ → 𝕜) →L[𝕜] (ι → 𝕜)).precomp (κ → 𝕜)).continuous.comp hT
    have hinv := continuous_pi_clm_inverse_self hTe fun y ↦ (hbij y).comp e.bijective
    refine ((e : (κ → 𝕜) →L[𝕜] (ι → 𝕜)).postcomp (κ → 𝕜)).continuous.comp hinv |>.congr fun y ↦ ?_
    ext v; simp [ContinuousLinearMap.postcomp_apply, ContinuousLinearMap.inverse_comp_equiv]
  · have : IsEmpty Y := not_nonempty_iff.1 hY
    exact continuous_iff_continuousAt.2 isEmptyElim

end Inverse
