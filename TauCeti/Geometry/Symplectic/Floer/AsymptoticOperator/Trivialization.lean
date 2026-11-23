/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.FrameTrivialization
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.FrameTrivialization
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Frame trivialization of the Hamiltonian Floer asymptotic and cylinder operators

The Sobolev operators `TauCeti.CircleSobolev.loopOperator` and
`TauCeti.CircleSobolev.cylinderOperator` act on loops and cylinders valued in a fixed complex
Hilbert model `(F, I, Im ⟪·, ·⟫)`, whereas linearized Hamiltonian Floer operators along an orbit in
`(V, ω)` carry time-dependent `J_t` and `S_t = dX_{H_t}(x(t))`. Pulling back along a frame
`Φ : ℝ → F →L[ℝ] V` via `S_Φ(t) = Φ(t)⁻¹ (S(t) Φ(t) - Φ'(t))` (`TauCeti.trivializedCoeff`) reduces
them to `F`, feeding `TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator/Cylinder.lean`
alongside `SymplecticForm.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`
(`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator.lean`): intertwining
`Floer.asymptoticOperator` and `Floer.stationaryCylinderOperator` and preserving infinitesimal
symplecticity on `AddCircle 1`. Adapts `TauCeti.orbitTorusVerticalOperator_frame_apply`
(`TauCeti/Geometry/Symplectic/JHolomorphic/OrbitTorus/Trivialization.lean`).

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2, §2.2.
* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611.
-/

public section

noncomputable section

open ContinuousLinearMap

namespace TauCeti

namespace Floer

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- When `Φ` and `ζ` are differentiable at `t` and invertible `Φ t` intertwines `J₀ t` with `J t`,
`Φ` pulls `asymptoticOperator J S` back to `asymptoticOperator J₀ (trivializedCoeff Φ S)`. This
generalizes `TauCeti.Floer.asymptoticOperator_frame_apply`, whose model structure `J₀` is constant,
to a time-dependent `J₀`. -/
theorem asymptoticOperator_frame_apply_trivializedCoeff {Φ : ℝ → F →L[ℝ] V}
    {J : ℝ → AlmostComplexStructure V} {J₀ : ℝ → AlmostComplexStructure F} {S : ℝ → V →L[ℝ] V}
    {ζ : ℝ → F} {t : ℝ}
    (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible)
    (hJ : ∀ v, J t (Φ t v) = Φ t (J₀ t v)) (hζ : DifferentiableAt ℝ ζ t) :
    asymptoticOperator J S (fun r ↦ Φ r (ζ r)) t =
      Φ t (asymptoticOperator J₀ (trivializedCoeff Φ S) ζ t) := by
  rw [asymptoticOperator_def, deriv_clm_apply_sub_eq_apply_deriv_sub_trivializedCoeff hΦd hΦ hζ,
    hJ, asymptoticOperator_def]

/-- When `Φ` is differentiable at `z.2` with invertible `Φ z.2` intertwining `J₀ z.2` with `J z.2`
and `η` is differentiable at `z`, `Φ` pulls `stationaryCylinderOperator J S` back to
`stationaryCylinderOperator J₀ (trivializedCoeff Φ S)`. -/
theorem stationaryCylinderOperator_frame_apply {Φ : ℝ → F →L[ℝ] V}
    {J : ℝ → AlmostComplexStructure V} {J₀ : ℝ → AlmostComplexStructure F} {S : ℝ → V →L[ℝ] V}
    {η : ℝ × ℝ → F} {z : ℝ × ℝ} (hΦd : DifferentiableAt ℝ Φ z.2) (hΦ : (Φ z.2).IsInvertible)
    (hJ : ∀ v, J z.2 (Φ z.2 v) = Φ z.2 (J₀ z.2 v)) (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderOperator J S (fun w ↦ Φ w.2 (η w)) z =
      Φ z.2 (stationaryCylinderOperator J₀ (trivializedCoeff Φ S) η z) := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ Φ w.2 (η w)) ((Φ z.2).comp (fderiv ℝ η z) +
      ((fderiv ℝ Φ z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).flip (η z)) z :=
    (hΦd.hasFDerivAt.comp z hasFDerivAt_snd).clm_apply hη.hasFDerivAt
  rw [stationaryCylinderOperator_def, hd.fderiv, stationaryCylinderOperator_def]
  simp only [add_apply, coe_comp, Function.comp_apply, flip_apply, coe_snd', stdComplexLineReal_eq,
    stdComplexLineImag_eq, map_zero, zero_apply, add_zero, fderiv_apply_one_eq_deriv, map_add,
    map_sub, trivializedCoeff_apply, hΦ.self_apply_inverse, ← hJ]
  abel

end Floer

namespace SymplecticForm

section SymplecticOrbit

variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Along `x` where each `H t` is `C²` at `x t`, a loop `S` trivializing `dX_{H_t}(x(t))` in a
differentiable invertible symplectic frame `Φ` is infinitesimally symplectic on `AddCircle 1`. -/
theorem im_inner_apply_add_eq_zero_of_trivializedCoeff (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {x : ℝ → V} (hH : ∀ t, ContDiffAt ℝ 2 (H t) (x t)) {Φ : ℝ → F →L[ℝ] V}
    (hΦd : Differentiable ℝ Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im) {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t =
      trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t)
    (θ : AddCircle (1 : ℝ)) (v w : F) :
    (inner ℂ (S θ v) w).im + (inner ℂ v (S θ w)).im = 0 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact hS t ▸ ω.im_inner_trivializedCoeff_add_eq_zero (hΦd t) (hΦ t) hω
    (ω.apply_fderiv_hamiltonianVectorField_add (hH t)) v w

end SymplecticOrbit

end SymplecticForm

end TauCeti
