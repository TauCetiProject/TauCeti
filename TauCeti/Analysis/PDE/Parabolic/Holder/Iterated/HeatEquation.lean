/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.HeatEquation
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.CauchyPotential
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Const
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.DuhamelPotential
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Operator

/-!
# The heat equation in the parabolic Hölder spaces of every order

For every order `k` and `0 < α < 1`, the map `u ↦ (∂ₜu - Δu, u(·, 0))` is a bounded linear
isomorphism

`C_{par,b}^{(k+2)+α}(ℝⁿ × [0, T]) ≃ C_{par,b}^{k+α}(ℝⁿ × [0, T]) × C_b^{k+2,α}(ℝⁿ)`

(`TauCeti.ParabolicCkHolderSpace.heatInitialDataCLE`), whose inverse is the Duhamel potential of
the forcing plus the Cauchy potential of the initial datum. At `k = 0` this is the isomorphism
`TauCeti.heatInitialDataCLE` on `C_b^{2+α,1+α/2}`. It is the starting point of the method of
continuity for parabolic equations with coefficients in `C_{par,b}^{k+α}`, whose initial-data
operators `TauCeti.ParabolicCkHolderSpace.initialDataL` contain the heat data operator as the one
with coefficients `(const tr, 0, 0)`.

Existence holds on every finite-dimensional real inner product space with Banach-valued data:
the potentials solve the heat equation at every order
(`TauCeti.ParabolicCkHolderSpace.timeDerivL_heatDuhamelPotentialL_eq_laplacian_add`,
`TauCeti.ParabolicCkHolderSpace.timeDerivL_heatCauchyPotentialL_eq_laplacian`). Uniqueness is
proved for scalar functions on Euclidean space by reading a solution of order `k + 2` at order two,
where the whole-space comparison principle applies (`TauCeti.heatInitialDataL_injective`). No
condition at spatial infinity is imposed beyond the bounded Hölder norm, and the time derivatives
are one-sided at the endpoints of the slab.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.heatInitialDataL`: the data operator `u ↦ (∂ₜu - Δu, u(·, 0))`.
* `TauCeti.ParabolicCkHolderSpace.heatSolutionL`: the solution operator, the sum of the Duhamel
  and Cauchy potentials.
* `TauCeti.ParabolicCkHolderSpace.heatInitialDataL_heatSolutionL`: existence.
* `TauCeti.ParabolicCkHolderSpace.heatInitialDataL_injective`: uniqueness.
* `TauCeti.ParabolicCkHolderSpace.heatInitialDataCLE` and
  `TauCeti.ParabolicCkHolderSpace.isInvertible_heatInitialDataL`: the isomorphism.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (the heat equation in parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime InnerProductSpace Laplacian
open scoped NNReal

namespace ParabolicCkHolderSpace

/- The shortcut instances of `TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Differentiation` for
operator-valued fields, with which the coefficient spaces of the parabolic operators are built. -/
attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

/-! ### The data operator -/

section InitialData

variable {k : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α T : ℝ≥0} {hT : (0 : ℝ) < T}

variable (k) in
/-- **The heat equation as a data operator** of order `k`: the map `u ↦ (∂ₜu - Δu, u(·, 0))` from
`C_{par,b}^{(k+2)+α}` to `C_{par,b}^{k+α} × C_b^{k+2,α}` on the slab `E × [0, T]`. It is the
initial-data operator of the parabolic operator with the constant trace functional on Hessians
as second-order coefficient and no lower-order terms. -/
def heatInitialDataL (hα : α ≤ 1) (hT : (0 : ℝ) < T) :
    ParabolicCkHolderSpace (k + 2) α E F hT →L[ℝ]
      ParabolicCkHolderSpace k α E F hT × CkHolderSpace (k + 2) α E F :=
  initialDataL hα (const (traceL (E := E) (F := F))) 0 0

theorem heatInitialDataL_eq_initialDataL (hα : α ≤ 1) :
    heatInitialDataL k (E := E) (F := F) hα hT =
      initialDataL hα (const (traceL (E := E) (F := F))) 0 0 := (rfl)

/-- The first component is `∂ₜu - Δu`, with the one-sided time derivatives at the endpoints. -/
@[simp]
theorem heatInitialDataL_fst_apply (hα : α ≤ 1) (u : ParabolicCkHolderSpace (k + 2) α E F hT)
    (p : slab (E := E) 0 T) :
    (heatInitialDataL k hα hT u).1 p = timeDerivL k α E F hT u p -
      Δ (fun x ↦ u (slabMk x (slabTime p))) (p : ParabolicSpaceTime E).space := by
  obtain ⟨x, t, rfl⟩ : ∃ x t, p = slabMk x t := ⟨_, _, (slabMk_space_slabTime p).symm⟩
  rw [heatInitialDataL, initialDataL_fst, parabolicOperatorL_slabMk, timeDerivL_slabMk]
  simp [laplacian_eq_traceL]

/-- The second component is the initial spatial trace. -/
@[simp]
theorem heatInitialDataL_snd (hα : α ≤ 1) (u : ParabolicCkHolderSpace (k + 2) α E F hT) :
    (heatInitialDataL k hα hT u).2 = u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ := by
  simp [heatInitialDataL]

end InitialData

/-! ### The solution operator -/

section Solution

variable {k : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {α T : ℝ≥0} {hT : (0 : ℝ) < T}

variable (k) in
/-- The solution operator of the heat equation of order `k`, for forcing and initial datum in that
order: the Duhamel potential of the forcing plus the Cauchy potential of the initial datum. -/
def heatSolutionL (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T) :
    (ParabolicCkHolderSpace k α E F hT × CkHolderSpace (k + 2) α E F) →L[ℝ]
      ParabolicCkHolderSpace (k + 2) α E F hT :=
  (heatDuhamelPotentialL hα₀ hα₁ hT).coprod (heatCauchyPotentialL hα₁.le hT le_rfl)

/-- The solution is the sum of its forcing and initial-data potentials. -/
theorem heatSolutionL_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : ParabolicCkHolderSpace k α E F hT) (g : CkHolderSpace (k + 2) α E F) :
    heatSolutionL k hα₀ hα₁ hT (f, g) =
      heatDuhamelPotentialL hα₀ hα₁ hT f + heatCauchyPotentialL hα₁.le hT le_rfl g := by
  simp [heatSolutionL]

/-- **Existence.** The constructed solution attains both the forcing and the initial datum, on the
closed slab. -/
@[simp]
theorem heatInitialDataL_heatSolutionL (hα₀ : 0 < α) (hα₁ : α < 1)
    (d : ParabolicCkHolderSpace k α E F hT × CkHolderSpace (k + 2) α E F) :
    heatInitialDataL k hα₁.le hT (heatSolutionL k hα₀ hα₁ hT d) = d := by
  rcases d with ⟨f, g⟩
  have hD : (heatInitialDataL k hα₁.le hT (heatDuhamelPotentialL hα₀ hα₁ hT f)).1 = f := by
    ext p
    rw [heatInitialDataL_fst_apply, timeDerivL_heatDuhamelPotentialL_eq_laplacian_add]
    abel
  have hC : (heatInitialDataL k hα₁.le hT (heatCauchyPotentialL hα₁.le hT le_rfl g)).1 = 0 := by
    ext p
    rw [heatInitialDataL_fst_apply, timeDerivL_heatCauchyPotentialL_eq_laplacian, sub_self,
      coe_zero, Pi.zero_apply]
  rw [heatSolutionL_apply, map_add]
  apply Prod.ext
  · simp [hD, hC]
  · ext x
    simp [heatCauchyPotential_zero]

end Solution

/-! ### Uniqueness and the isomorphism -/

section Euclidean

variable {k : ℕ} {α T : ℝ≥0} {hT : (0 : ℝ) < T} {ι : Type*} [Fintype ι]

/-- The inclusion of order `k + 2` into order two, as a map; it keeps the underlying function. -/
private def toOrderTwo {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b} (hα : α ≤ 1) :
    (k : ℕ) → ParabolicCkHolderSpace (k + 2) α E F hab → ParabolicCkHolderSpace 2 α E F hab
  | 0 => id
  | k + 1 => fun u ↦ toOrderTwo hα k (inclusionL hα u)

private theorem toOrderTwo_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b} (hα : α ≤ 1) :
    ∀ (k : ℕ) (u : ParabolicCkHolderSpace (k + 2) α E F hab) (p : slab (E := E) a b),
      toOrderTwo hα k u p = u p
  | 0, _, _ => rfl
  | k + 1, u, p => by
    rw [toOrderTwo, toOrderTwo_apply hα k, inclusionL_apply]

/-- The heat equation's forcing of the order-two map with the same values as `u` is the forcing
of `u`. -/
private theorem heatInitialDataL_toOrderTwo_fst {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hα : α ≤ 1) (u : ParabolicCkHolderSpace (k + 2) α E F hT) (p : slab (E := E) 0 T) :
    (TauCeti.heatInitialDataL hα hT (equivParabolicC2HolderSpace (toOrderTwo hα k u))).1 p =
      (heatInitialDataL k hα hT u).1 p := by
  have hval (q : slab (E := E) 0 T) : equivParabolicC2HolderSpace (toOrderTwo hα k u) q = u q := by
    rw [equivParabolicC2HolderSpace_apply, toOrderTwo_apply]
  obtain ⟨x, t, rfl⟩ : ∃ x t, p = slabMk x t := ⟨_, _, (slabMk_space_slabTime p).symm⟩
  rw [TauCeti.heatInitialDataL_fst_apply, heatInitialDataL_fst_apply,
    ← ParabolicC2HolderSpace.derivWithin_eq, timeDerivL_slabMk]
  simp only [ParabolicC2HolderSpace.timeExtension_def, hval]

/-- **Uniqueness for the heat equation** in the bounded Hölder class of order `k + 2`: a solution is
determined by its forcing and its initial trace. -/
theorem heatInitialDataL_injective (hα : α ≤ 1) :
    Function.Injective (heatInitialDataL k (E := EuclideanSpace ℝ ι) (F := ℝ) hα hT) := by
  intro u v huv
  have hval (w : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
      (q : slab (E := EuclideanSpace ℝ ι) 0 T) :
      equivParabolicC2HolderSpace (toOrderTwo hα k w) q = w q := by
    rw [equivParabolicC2HolderSpace_apply, toOrderTwo_apply]
  have h2 : equivParabolicC2HolderSpace (toOrderTwo hα k u) =
      equivParabolicC2HolderSpace (toOrderTwo hα k v) := by
    refine TauCeti.heatInitialDataL_injective hα (Prod.ext (HolderSpace.ext fun p ↦ ?_) ?_)
    · rw [heatInitialDataL_toOrderTwo_fst, heatInitialDataL_toOrderTwo_fst, huv]
    · refine CkHolderSpace.ext fun x ↦ ?_
      have h := congrArg (fun d ↦ d.2 x) huv
      simp only [heatInitialDataL_snd, spatialTrace_apply] at h
      rw [TauCeti.heatInitialDataL_snd, TauCeti.heatInitialDataL_snd,
        ParabolicC2HolderSpace.spatialTrace_apply, ParabolicC2HolderSpace.spatialTrace_apply,
        hval, hval]
      exact h
  refine ParabolicCkHolderSpace.ext fun p ↦ ?_
  rw [← hval u p, h2, hval]

/-- **The heat equation's initial-data isomorphism** of order `k`: for `0 < α < 1`,
`u ↦ (∂ₜu - Δu, u(·, 0))` is an isomorphism from `C_{par,b}^{(k+2)+α}` onto
`C_{par,b}^{k+α} × C_b^{k+2,α}` on the slab `ℝⁿ × [0, T]`. Its inverse is the Duhamel potential
of the forcing plus the Cauchy potential of the initial datum. -/
def heatInitialDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T) :
    ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
        CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ :=
  ContinuousLinearEquiv.ofContinuousLinearMap (heatInitialDataL k hα₁.le hT)
    (heatSolutionL k hα₀ hα₁ hT)
    (ContinuousLinearMap.ext (heatInitialDataL_heatSolutionL hα₀ hα₁))
    (ContinuousLinearMap.ext fun _ ↦ heatInitialDataL_injective hα₁.le
      (heatInitialDataL_heatSolutionL hα₀ hα₁ _))

/-- The forward isomorphism is the heat data operator. -/
@[simp]
theorem heatInitialDataCLE_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    heatInitialDataCLE (k := k) (ι := ι) hα₀ hα₁ hT u = heatInitialDataL k hα₁.le hT u :=
  -- The forward map of `ContinuousLinearEquiv.ofContinuousLinearMap` is the given map.
  (rfl)

/-- The inverse isomorphism is the heat solution operator. -/
@[simp]
theorem heatInitialDataCLE_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (d : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT ×
      CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    (heatInitialDataCLE (ι := ι) hα₀ hα₁ hT).symm d = heatSolutionL k hα₀ hα₁ hT d := by
  apply (heatInitialDataCLE (ι := ι) hα₀ hα₁ hT).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, heatInitialDataCLE_apply,
    heatInitialDataL_heatSolutionL]

/-- The heat data operator of order `k` is invertible for `0 < α < 1`. -/
theorem isInvertible_heatInitialDataL (hα₀ : 0 < α) (hα₁ : α < 1) :
    (heatInitialDataL k (E := EuclideanSpace ℝ ι) (F := ℝ) hα₁.le hT).IsInvertible :=
  ⟨heatInitialDataCLE hα₀ hα₁ hT, ContinuousLinearMap.ext (heatInitialDataCLE_apply hα₀ hα₁)⟩

/-- Solving the heat equation with the data of a function recovers that function. -/
@[simp]
theorem heatSolutionL_heatInitialDataL (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    heatSolutionL k hα₀ hα₁ hT (heatInitialDataL k hα₁.le hT u) = u :=
  heatInitialDataL_injective hα₁.le (heatInitialDataL_heatSolutionL hα₀ hα₁ _)

end Euclidean

end ParabolicCkHolderSpace

end TauCeti
