/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.FrameTrivialization
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.FrameTrivialization
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Geometry.Symplectic.Transport

/-!
# Frame trivialization of the Hamiltonian Floer asymptotic and cylinder operators

The Fourier-series Sobolev operators `TauCeti.CircleSobolev.loopOperator` and
`TauCeti.CircleSobolev.cylinderOperator` act on loops and cylinders valued in a fixed complex
Hilbert model `(F, I, Im ⟪·, ·⟫)`, whereas linearized Hamiltonian Floer operators along an orbit in
`(V, ω)` carry time-dependent almost complex structures `J_t` and real-linear Hamiltonian
linearizations `S_t = dX_{H_t}(x(t))`. Pulling back along a differentiable frame
`Φ : ℝ → F →L[ℝ] V` via `S_Φ(t) = Φ(t)⁻¹ (S(t) Φ(t) - Φ'(t))` (`TauCeti.trivializedCoeff`) reduces
those operators to the model space `F`, feeding the Sobolev stationary-cylinder theory in
`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator/Cylinder.lean`:

* **Pointwise operator intertwining.** When `Φ` intertwines `J₀` on `F` with `J` on `V`, applying
  `Φ` pulls `Floer.asymptoticOperator` and `Floer.stationaryCylinderOperator` back to coefficient
  `S_Φ` (`Floer.asymptoticOperator_frame_apply`, `Floer.stationaryCylinderOperator_frame_apply`).
* **Symplectic and nondegeneracy transport.** Along a Hamiltonian trajectory in a symplectic frame
  pulling `ω` back to `Im ⟪·, ·⟫`, the trivialized loop `S` on `AddCircle 1` is infinitesimally
  symplectic (`SymplecticForm.im_inner_apply_add_eq_zero_of_trivializedCoeff`); along a `1`-periodic
  orbit in a `1`-periodic frame, `CircleSobolev.loopOperator 1 S` is invertible iff `x(0)` is a
  nondegenerate fixed point of the time-one flow
  (`SymplecticForm.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`).

Adapts `TauCeti.orbitTorusVerticalOperator_frame_apply`
(`TauCeti/Geometry/Symplectic/JHolomorphic/OrbitTorus/Trivialization.lean`) and
`TauCeti.SymplecticForm.isInvertible_loopOperator_iff_isNondegenerateFixedPt`
(`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator.lean`).

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2, §2.2.
* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Function Topology
open scoped Manifold NNReal

namespace TauCeti

namespace Floer

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- **Intertwining `asymptoticOperator`:** when `Φ` and `ζ` are differentiable at `t` and `Φ t` is
invertible and intertwines `J₀ t` with `J t`, applying `Φ` pulls `asymptoticOperator J S` back to
`asymptoticOperator J₀ (trivializedCoeff Φ S)`. -/
theorem asymptoticOperator_frame_apply {Φ : ℝ → F →L[ℝ] V} {J : ℝ → AlmostComplexStructure V}
    {J₀ : ℝ → AlmostComplexStructure F} {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ}
    (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible)
    (hJ : ∀ v, J t (Φ t v) = Φ t (J₀ t v)) (hζ : DifferentiableAt ℝ ζ t) :
    asymptoticOperator J S (fun r ↦ Φ r (ζ r)) t =
      Φ t (asymptoticOperator J₀ (trivializedCoeff Φ S) ζ t) := by
  rw [asymptoticOperator_def, deriv_clm_apply_sub_eq_apply_deriv_sub_trivializedCoeff hΦd hΦ hζ,
    hJ, asymptoticOperator_def]

/-- **Intertwining `stationaryCylinderOperator`:** when `Φ` is differentiable at `z.2` with
invertible value `Φ z.2` intertwining `J₀ z.2` with `J z.2` and `η` is differentiable at `z`,
applying `Φ` pulls `stationaryCylinderOperator J S` back to
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

section LoopInvertibility

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **Loop invertibility equivalence in a `1`-periodic frame:** along a `1`-periodic orbit `x` of a
`1`-periodic, jointly `C²` Hamiltonian `H` with globally Lipschitz suspended vector field, for a
differentiable `1`-periodic invertible frame `Φ` trivializing `dX_{H_t}(x(t))` as `S`,
`CircleSobolev.loopOperator 1 S` is invertible iff `x(0)` is a nondegenerate fixed point of the
time-one flow. -/
theorem isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS : ∀ t : ℝ, S t =
      trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    (CircleSobolev.loopOperator 1 S).IsInvertible ↔
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) := by
  obtain ⟨e₀, _⟩ := hΦ 0
  let J₀ : AlmostComplexStructure V :=
    (AlmostComplexStructure.ofComplexModule F).transport e₀.toLinearEquiv
  rw [CircleSobolev.isInvertible_loopOperator_iff,
    ω.isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero hX hH hHp hx hxp
      fun _ ↦ J₀]
  refine ⟨fun hloop ξ hξd hξp hA ↦ ?_, fun hnd ζ hζ ↦ ?_⟩
  · have hΦinv : Differentiable ℝ fun t ↦ (Φ t).inverse := fun t ↦
      (((hΦ t).contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp t (hΦd t)
    set ζ₀ : ℝ → F := fun t ↦ (Φ t).inverse (ξ t)
    have hζ₀d : Differentiable ℝ ζ₀ := hΦinv.clm_apply hξd
    have hζ₀p : Periodic ζ₀ 1 := fun t ↦ by simp only [ζ₀, hΦp t, hξp t]
    let ζ : C(AddCircle (1 : ℝ), F) :=
      ⟨hζ₀p.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hζ₀d.continuous⟩
    have hζeq (t : ℝ) : ζ t = (Φ t).inverse (ξ t) := by simp [ζ, ζ₀]
    have hfun : (fun r ↦ Φ r (ζ₀ r)) = ξ := funext fun r ↦ (hΦ r).self_apply_inverse (ξ r)
    have h0 := hloop ζ fun t ↦ by
      rw [funext hζeq, hS t]
      refine (hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff (hΦd t) (hΦ t) (hζ₀d t)).1 ?_
      simpa only [hfun, ζ₀, (hΦ t).self_apply_inverse] using
        (Floer.asymptoticOperator_eq_zero_iff (hξd t)).1 (hA t)
    funext t
    rw [Pi.zero_apply, ← (hΦ t).self_apply_inverse (ξ t), ← hζeq t, h0, ContinuousMap.zero_apply,
      map_zero]
  · have hζd : Differentiable ℝ fun y : ℝ ↦ ζ y := fun y ↦ (hζ y).differentiableAt
    have hξd : Differentiable ℝ fun t ↦ Φ t (ζ t) := hΦd.clm_apply hζd
    have hξp : Periodic (fun t ↦ Φ t (ζ t)) 1 := fun t ↦ by simp [hΦp t]
    have h0 := hnd (fun t ↦ Φ t (ζ t)) hξd hξp fun t ↦
      (Floer.asymptoticOperator_eq_zero_iff (hξd t)).2 <|
        (hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff (hΦd t) (hΦ t) (hζd t)).2
          (by simpa only [hS t] using hζ t)
    ext θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact (hΦ t).injective (by simpa using congrFun h0 t)

end LoopInvertibility

end SymplecticForm

end TauCeti
