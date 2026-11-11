/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyPotential
public import TauCeti.Analysis.PDE.Parabolic.Holder.DuhamelPotential.Basic
public import TauCeti.Analysis.PDE.Parabolic.Holder.InitialData
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The heat equation as an initial-data isomorphism

The map `u ↦ (∂ₜu - Δu, u(·,0))` is a bounded linear isomorphism from
`C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}` on a finite positive time slab, for
`0 < α < 1`. Its inverse is the sum of the Duhamel potential of the forcing and the
Cauchy potential of the initial datum. This is the starting isomorphism for perturbation
and method-of-continuity arguments for parabolic equations. The theorem
`existsUnique_initialDataL_eq_of_near_heat` applies the quantitative coefficient perturbation
criterion to obtain existence and uniqueness near the heat operator.

The data and solution operators work on finite-dimensional real inner product spaces
with Banach-valued data. The isomorphism is proved for scalar functions on Euclidean space,
using the whole-space comparison theorem for uniqueness. Both endpoint time derivatives
are included in the equation, and no boundary condition at spatial infinity is imposed
beyond the bounded Hölder norm.

The construction uses `TauCeti.heatCauchyPotentialL` and `TauCeti.heatDuhamelPotentialL`;
uniqueness uses `ParabolicC2HolderSpace.eq_of_euclideanParabolicOperatorL_eq`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Corollary 4.2.10.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime ParabolicC2HolderSpace InnerProductSpace Laplacian
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {α T : ℝ≥0} {hT : (0 : ℝ) < T}

/-- A local shortcut for the nested Hessian norm in the coefficient space. -/
private local instance hessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
/-- A local shortcut for scalar operations on that Hessian space. -/
private local instance hessianNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- The heat equation's forcing and initial trace as a bounded linear data operator. -/
def heatInitialDataL (hα : α ≤ 1) (hT : (0 : ℝ) < T) :
    ParabolicC2HolderSpace α E F hT →L[ℝ]
      HolderSpace α (slab (E := E) 0 T) F × CkHolderSpace 2 α E F :=
  initialDataL hα (HolderSpace.const traceL) 0 0

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The first component is `∂ₜu - Δu`, with the recorded one-sided derivatives at endpoints. -/
@[simp]
theorem heatInitialDataL_fst_apply (hα : α ≤ 1) (u : ParabolicC2HolderSpace α E F hT)
    (p : slab (E := E) 0 T) :
    (heatInitialDataL hα hT u).1 p = timeDerivL u p -
      Δ (fun x ↦ u (slabMk x (slabTime p))) (p : ParabolicSpaceTime E).space := by
  simp [heatInitialDataL, laplacian_eq_traceL, u.fderiv_fderiv_eq]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The second component is the initial spatial trace. -/
@[simp]
theorem heatInitialDataL_snd (hα : α ≤ 1) (u : ParabolicC2HolderSpace α E F hT) :
    (heatInitialDataL hα hT u).2 = u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ := by
  simp [heatInitialDataL]

/-- The solution operator for forcing and initial data, in that order: the Duhamel potential
of the forcing plus the Cauchy potential of the initial datum. -/
def heatSolutionL (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T) :
    (HolderSpace α (slab (E := E) 0 T) F × CkHolderSpace 2 α E F) →L[ℝ]
      ParabolicC2HolderSpace α E F hT :=
  (heatDuhamelPotentialL hα₀ hα₁ hT).coprod (heatCauchyPotentialL hT le_rfl)

/-- The solution is the sum of its forcing and initial-data potentials. -/
theorem heatSolutionL_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) (g : CkHolderSpace 2 α E F) :
    heatSolutionL hα₀ hα₁ hT (f, g) =
      heatDuhamelPotentialL hα₀ hα₁ hT f + heatCauchyPotentialL hT le_rfl g := by
  simp [heatSolutionL]

/-- The constructed solution attains both the forcing and the initial datum, on the closed
slab. In particular the equation holds with one-sided endpoint time derivatives. -/
@[simp]
theorem heatInitialDataL_heatSolutionL (hα₀ : 0 < α) (hα₁ : α < 1)
    (d : HolderSpace α (slab (E := E) 0 T) F × CkHolderSpace 2 α E F) :
    heatInitialDataL hα₁.le hT (heatSolutionL hα₀ hα₁ hT d) = d := by
  rcases d with ⟨f, g⟩
  have hD : (heatInitialDataL hα₁.le hT (heatDuhamelPotentialL hα₀ hα₁ hT f)).1 = f := by
    ext p
    rw [heatInitialDataL_fst_apply, timeDerivL_heatDuhamelPotentialL_eq_laplacian_add]
    abel
  have hC : (heatInitialDataL hα₁.le hT (heatCauchyPotentialL hT le_rfl g)).1 = 0 := by
    ext p
    rw [heatInitialDataL_fst_apply, timeDerivL_heatCauchyPotentialL_eq_laplacian]
    simp
  rw [heatSolutionL_apply, map_add]
  apply Prod.ext
  · simp [hD, hC]
  · simp [spatialTrace_heatCauchyPotentialL_left]

section Euclidean

variable {ι : Type*} [Fintype ι]

/-- Shortcut for the Hessian norm in Euclidean coefficient fields. The general shortcut above
cannot infer the spatial and target spaces when they occur only inside the coefficient type. -/
local instance euclideanHessianNormedAddCommGroup :
    NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance
/-- Shortcut for scalar operations on Euclidean Hessians, for the same coefficient elaboration. -/
local instance euclideanHessianNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance

variable [DecidableEq ι] in
/-- The coordinate identity identifies the first data component with the existing Euclidean
parabolic operator having identity diffusion and zero lower-order coefficients. -/
theorem heatInitialDataL_fst_eq_euclideanParabolicOperatorL (hα : α ≤ 1)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    (heatInitialDataL hα hT u).1 = euclideanParabolicOperatorL hα
      (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0 u := by
  classical
  ext p
  rw [heatInitialDataL_fst_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun ι ℝ)]
  simp [euclideanParabolicOperatorL_apply, u.iteratedFDeriv_two_apply,
    EuclideanSpace.basisFun_apply, Matrix.one_apply]

/-- Uniqueness for the heat equation in the bounded order-two Hölder class. -/
theorem heatInitialDataL_injective (hα : α ≤ 1) :
    Function.Injective (heatInitialDataL (E := EuclideanSpace ℝ ι) (F := ℝ) hα hT) := by
  classical
  intro u v huv
  apply eq_of_euclideanParabolicOperatorL_eq hα
    (a := fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) (b := 0) (c := 0)
    (fun p ξ ↦ by
      have hI : (Matrix.of fun i j ↦
          HolderSpace.const (α := α) ((1 : Matrix ι ι ℝ) i j) p) = 1 := by
        ext i j
        simp
      rw [hI, Matrix.toQuadraticForm'_apply, Matrix.one_mulVec]
      exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
  · simpa only [heatInitialDataL_fst_eq_euclideanParabolicOperatorL] using congrArg Prod.fst huv
  · intro x
    have h := congrArg (fun d ↦ d.2 x) huv
    simpa using h

/-- The heat equation's bounded initial-data isomorphism. Its inverse is explicitly the
Duhamel potential of the forcing plus the Cauchy potential of the initial datum. -/
def heatInitialDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ :=
  ContinuousLinearEquiv.equivOfInverse (heatInitialDataL hα₁.le hT) (heatSolutionL hα₀ hα₁ hT)
    (Function.RightInverse.leftInverse_of_injective
      (heatInitialDataL_heatSolutionL (E := EuclideanSpace ℝ ι) (F := ℝ) (hT := hT) hα₀ hα₁)
      (heatInitialDataL_injective hα₁.le))
    (heatInitialDataL_heatSolutionL hα₀ hα₁)

/-- The forward isomorphism is the forcing-and-initial-trace operator. -/
@[simp]
theorem heatInitialDataCLE_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    heatInitialDataCLE (ι := ι) hα₀ hα₁ hT u = heatInitialDataL hα₁.le hT u := by
  rw [heatInitialDataCLE, ContinuousLinearEquiv.equivOfInverse_apply]

/-- The inverse isomorphism is the constructed heat solution operator. -/
@[simp]
theorem heatInitialDataCLE_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    (heatInitialDataCLE (ι := ι) hα₀ hα₁ hT).symm d = heatSolutionL hα₀ hα₁ hT d := by
  apply (heatInitialDataCLE (ι := ι) hα₀ hα₁ hT).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, heatInitialDataCLE_apply,
    heatInitialDataL_heatSolutionL]

/-- The heat initial-data map is invertible for `0 < α < 1`. -/
theorem isInvertible_heatInitialDataL (hα₀ : 0 < α) (hα₁ : α < 1) :
    (heatInitialDataL (E := EuclideanSpace ℝ ι) (F := ℝ) hα₁.le hT).IsInvertible := by
  refine ⟨heatInitialDataCLE hα₀ hα₁ hT, ?_⟩
  ext1 u
  exact heatInitialDataCLE_apply hα₀ hα₁ u

/-- The totalized operator inverse of the heat initial-data map is the heat solution map. -/
@[simp]
theorem inverse_heatInitialDataL (hα₀ : 0 < α) (hα₁ : α < 1) :
    (heatInitialDataL (E := EuclideanSpace ℝ ι) (F := ℝ) hα₁.le hT).inverse =
      heatSolutionL hα₀ hα₁ hT := by
  apply ContinuousLinearMap.ext
  intro d
  apply heatInitialDataL_injective hα₁.le
  rw [(isInvertible_heatInitialDataL hα₀ hα₁).self_apply_inverse,
    heatInitialDataL_heatSolutionL]

/-- **The Cauchy problem near the heat operator.** If the coefficient distance to the heat
operator is small against the heat solution norm, every Hölder forcing and order-two initial
datum has a unique solution in the closed-slab order-two parabolic Hölder space. -/
theorem existsUnique_initialDataL_eq_of_near_heat (hα₀ : 0 < α) (hα₁ : α < 1)
    (A : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T)
      ((EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T)
      ((EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) (ℝ →L[ℝ] ℝ))
    (hsmall : ‖heatSolutionL (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀ hα₁ hT‖ *
      (‖A - HolderSpace.const traceL‖ + 24 * (‖B‖ + ‖C‖)) < 1)
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ∃! u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      initialDataL hα₁.le A B C u = d := by
  have hheat := isInvertible_heatInitialDataL (ι := ι) (hT := hT) hα₀ hα₁
  rw [heatInitialDataL] at hheat
  have hpert := isInvertible_initialDataL_of_mul_norm_sub_lt hα₁.le
    (A := HolderSpace.const traceL) (B := 0) (C := 0) hheat
    (M := ‖heatSolutionL hα₀ hα₁ hT‖)
    (by rw [← heatInitialDataL, inverse_heatInitialDataL hα₀ hα₁])
    (A' := A) (B' := B) (C' := C) (by simpa using hsmall)
  exact ⟨(initialDataL hα₁.le A B C).inverse d, hpert.self_apply_inverse d,
    fun u hu ↦ hpert.injective (hu.trans (hpert.self_apply_inverse d).symm)⟩

end Euclidean

end TauCeti
