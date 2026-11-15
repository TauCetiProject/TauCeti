/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Geometry.Symplectic.Transport

/-!
# Frame trivialization of the Hamiltonian Floer asymptotic and cylinder operators

For a differentiable path of invertible frames `Φ : ℝ → F →L[ℝ] V`, pulling back `ξ' - S_t ξ` along
`ξ(t) = Φ(t) ζ(t)` replaces `S : ℝ → V →L[ℝ] V` by `S_Φ(t) = Φ(t)⁻¹ (S(t) Φ(t) - Φ'(t))`
(`TauCeti.Floer.trivializedCoeff`):

* **Classical ODE covariance and intertwining.** Application of `Φ` intertwines `ζ ↦ ζ' - S_Φ(t) ζ`
  with `ξ ↦ ξ' - S_t ξ` (`deriv_clm_apply_sub_eq_apply_deriv_sub_trivializedCoeff`,
  `hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff`). When `Φ(t)` intertwines `I` with `J(t)`,
  `asymptoticOperator` and `stationaryCylinderOperator` pull back to `(F, I)` with coefficient `S_Φ`
  (`asymptoticOperator_frame_apply`, `stationaryCylinderOperator_frame_apply`), and subtracting
  `δ • K_t` from `S_t` subtracts `δ • (I • id)` from `S_Φ(t)` (`trivializedCoeff_sub_smul`).
* **Infinitesimal symplecticity.** When `Φ(t)` pulls `ω` back to `Im ⟪·, ·⟫` on `F`, differentiating
  `ω(Φ(t) v, Φ(t) w)` cancels `Φ(t)⁻¹ Φ'(t)`, preserving infinitesimal symplecticity
  (`im_inner_trivializedCoeff_add_eq_zero`, `im_inner_apply_add_eq_zero_of_trivializedCoeff`).
* **Sobolev loop invertibility equivalence.** Along a one-periodic Hamiltonian orbit `x` in a
  one-periodic frame `Φ`, `CircleSobolev.loopOperator 1 S` is invertible iff `x(0)` is a
  nondegenerate fixed point of the time-one flow
  (`isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`,
  `isInvertible_loopOperator_iff_isNondegenerateFixedPt`).

Adapts `TauCeti.frameConnection`, `TauCeti.orbitTorusVerticalOperator_frame_apply`, and
`TauCeti.isSymmetric_frameConnection`
(`TauCeti/Geometry/Symplectic/JHolomorphic/OrbitTorus/Trivialization.lean`), and
`TauCeti.SymplecticForm.isInvertible_loopOperator_of_isNondegenerateFixedPt` and
`TauCeti.SymplecticForm.eventually_isInvertible_loopOperator_sub_smul`
(`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator.lean`).

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2, §2.2.
* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611.
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter Function Topology
open scoped Manifold NNReal

namespace TauCeti

namespace Floer

section Trivialization

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The trivialized loop coefficient `S_Φ(t) = Φ(t)⁻¹ (S(t) Φ(t) - Φ'(t))` obtained by pulling back
`ζ' - S_t ζ` along a path of invertible frames `Φ : ℝ → F →L[ℝ] V`. -/
def trivializedCoeff (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) : F →L[ℝ] F :=
  (Φ t).inverse ∘L (S t ∘L Φ t - deriv Φ t)

/-- Operator-level unfolding of `trivializedCoeff`. -/
theorem trivializedCoeff_def (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) :
    trivializedCoeff Φ S t = (Φ t).inverse ∘L (S t ∘L Φ t - deriv Φ t) := (rfl)

/-- Pointwise evaluation of `trivializedCoeff`. -/
@[simp]
theorem trivializedCoeff_apply (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) (v : F) :
    trivializedCoeff Φ S t v = (Φ t).inverse (S t (Φ t v) - deriv Φ t v) := (rfl)

/-- Trivializing along the constant identity frame leaves the loop coefficient unchanged. -/
@[simp]
theorem trivializedCoeff_const_id (S : ℝ → F →L[ℝ] F) (t : ℝ) :
    trivializedCoeff (fun _ ↦ ContinuousLinearMap.id ℝ F) S t = S t := by
  ext v
  simp [trivializedCoeff_apply]

/-- Trivializing along a constant continuous linear equivalence conjugates `S_t`. -/
@[simp]
theorem trivializedCoeff_const_equiv (e : F ≃L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) :
    trivializedCoeff (fun _ ↦ (e : F →L[ℝ] V)) S t =
      (e.symm : V →L[ℝ] F) ∘L S t ∘L (e : F →L[ℝ] V) := by
  ext v
  simp [trivializedCoeff_apply]

/-- **Pulling back `ζ' - S_t ζ` along a differentiable frame.** -/
theorem deriv_clm_apply_sub_eq_apply_deriv_sub_trivializedCoeff {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t)
    (hΦ : (Φ t).IsInvertible) (hζ : DifferentiableAt ℝ ζ t) :
    deriv (fun r ↦ Φ r (ζ r)) t - S t (Φ t (ζ t)) =
      Φ t (deriv ζ t - trivializedCoeff Φ S t (ζ t)) := by
  have hd : HasDerivAt (fun r ↦ Φ r (ζ r)) (deriv Φ t (ζ t) + Φ t (deriv ζ t)) t := by
    simpa only [add_comm] using hΦd.hasDerivAt.clm_apply hζ.hasDerivAt
  rw [hd.deriv, map_sub, trivializedCoeff_apply, hΦ.self_apply_inverse]
  abel

/-- **Classical ODE correspondence under a frame.** For differentiable `ζ : ℝ → F`, `r ↦ Φ r (ζ r)`
solves `ξ' = S_t ξ` at `t` iff `ζ` solves `ζ' = S_Φ(t) ζ` at `t`. -/
theorem hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t)
    (hΦ : (Φ t).IsInvertible) (hζ : DifferentiableAt ℝ ζ t) :
    HasDerivAt (fun r ↦ Φ r (ζ r)) (S t (Φ t (ζ t))) t ↔
      HasDerivAt ζ (trivializedCoeff Φ S t (ζ t)) t := by
  have hd : HasDerivAt (fun r ↦ Φ r (ζ r)) (deriv Φ t (ζ t) + Φ t (deriv ζ t)) t := by
    simpa only [add_comm] using hΦd.hasDerivAt.clm_apply hζ.hasDerivAt
  refine ⟨fun h ↦ ?_, fun h ↦ (hΦd.hasDerivAt.clm_apply h).congr_deriv ?_⟩
  · have hsub : Φ t (deriv ζ t - trivializedCoeff Φ S t (ζ t)) = 0 := by
      rw [map_sub, trivializedCoeff_apply, hΦ.self_apply_inverse, ← hd.unique h]
      abel
    exact (sub_eq_zero.1 (hΦ.injective (hsub.trans (map_zero (Φ t)).symm))) ▸ hζ.hasDerivAt
  · rw [trivializedCoeff_apply, hΦ.self_apply_inverse]
    abel

/-- If `Φ` is `C¹` with invertible values and `S` is continuous, `trivializedCoeff Φ S` is
continuous. -/
theorem continuous_trivializedCoeff [CompleteSpace F] {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    (hΦ : ContDiff ℝ 1 Φ) (hinv : ∀ t, (Φ t).IsInvertible) (hS : Continuous S) :
    Continuous (trivializedCoeff Φ S) := by
  have hderiv : Continuous (deriv Φ) := contDiff_zero.1 (contDiff_succ_iff_deriv.1 hΦ).2.2
  have hinverse : Continuous fun t ↦ (Φ t).inverse := continuous_iff_continuousAt.2 fun t ↦
    ((hinv t).contDiffAt_map_inverse (n := 0)).continuousAt.comp hΦ.continuous.continuousAt
  exact hinverse.clm_comp ((hS.clm_comp hΦ.continuous).sub hderiv)

/-- Periodicity of `Φ` and `S` passes to `trivializedCoeff Φ S`. -/
theorem periodic_trivializedCoeff {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {T : ℝ}
    (hΦ : Periodic Φ T) (hS : Periodic S T) : Periodic (trivializedCoeff Φ S) T := fun t ↦ by
  simp only [trivializedCoeff_def, hΦ t, hS t, hΦ.deriv t]

end Trivialization

section ComplexFrame

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- **Weight-shift compatibility.** Subtracting `δ • K_t` from `S_t`, where `K_t` intertwines with
`I • ·` through `Φ_t`, subtracts `δ • (I • id)` from `trivializedCoeff Φ S`. -/
theorem trivializedCoeff_sub_smul {Φ : ℝ → F →L[ℝ] V} {S K : ℝ → V →L[ℝ] V} {t : ℝ}
    (hΦ : (Φ t).IsInvertible) (hK : ∀ v, K t (Φ t v) = Φ t (I • v)) (δ : ℝ) :
    trivializedCoeff Φ (fun r ↦ S r - δ • K r) t =
      trivializedCoeff Φ S t - δ • (I • ContinuousLinearMap.id ℝ F) := by
  ext v
  simp only [trivializedCoeff_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply, hK,
    sub_right_comm _ (δ • Φ t (I • v)), map_sub, map_smul, hΦ.inverse_apply_self]

/-- **Intertwining `asymptoticOperator`** along a frame intertwining `I • ·` with `J(t)`. -/
theorem asymptoticOperator_frame_apply {Φ : ℝ → F →L[ℝ] V} {J : ℝ → AlmostComplexStructure V}
    {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t)
    (hΦ : (Φ t).IsInvertible) (hJ : ∀ v, J t (Φ t v) = Φ t (I • v)) (hζ : DifferentiableAt ℝ ζ t) :
    asymptoticOperator J S (fun r ↦ Φ r (ζ r)) t =
      Φ t (asymptoticOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (trivializedCoeff Φ S) ζ t) := by
  rw [asymptoticOperator_def, deriv_clm_apply_sub_eq_apply_deriv_sub_trivializedCoeff hΦd hΦ hζ,
    hJ, asymptoticOperator_def, AlmostComplexStructure.ofComplexModule_apply]

/-- **Intertwining `stationaryCylinderOperator`** along a frame intertwining `I • ·` with
`J(z.2)`. -/
theorem stationaryCylinderOperator_frame_apply {Φ : ℝ → F →L[ℝ] V}
    {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V} {η : ℝ × ℝ → F} {z : ℝ × ℝ}
    (hΦd : DifferentiableAt ℝ Φ z.2) (hΦ : (Φ z.2).IsInvertible)
    (hJ : ∀ v, J z.2 (Φ z.2 v) = Φ z.2 (I • v)) (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderOperator J S (fun w ↦ Φ w.2 (η w)) z =
      Φ z.2 (stationaryCylinderOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (trivializedCoeff Φ S) η z) := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ Φ w.2 (η w)) ((Φ z.2).comp (fderiv ℝ η z) +
      ((fderiv ℝ Φ z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).flip (η z)) z :=
    (hΦd.hasFDerivAt.comp z hasFDerivAt_snd).clm_apply hη.hasFDerivAt
  rw [stationaryCylinderOperator_def, hd.fderiv, stationaryCylinderOperator_def]
  simp only [add_apply, coe_comp, Function.comp_apply, flip_apply, coe_snd', stdComplexLineReal_eq,
    stdComplexLineImag_eq, map_zero, zero_apply, add_zero, fderiv_apply_one_eq_deriv,
    AlmostComplexStructure.ofComplexModule_apply, map_add, map_sub, trivializedCoeff_apply,
    hΦ.self_apply_inverse, ← hJ]
  abel

end ComplexFrame

section SymplecticFrame

variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Preservation of infinitesimal symplecticity.** If `Φ` pulls `ω` back to `Im ⟪·, ·⟫` on `F`,
`trivializedCoeff Φ S t` is infinitesimally symplectic whenever `S t` is for `ω`. -/
theorem im_inner_trivializedCoeff_add_eq_zero (ω : SymplecticForm V) {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible)
    (hω : ∀ r v w, ω (Φ r v) (Φ r w) = (inner ℂ v w).im)
    (hS : ∀ v w, ω (S t v) w + ω v (S t w) = 0) (v w : F) :
    (inner ℂ (trivializedCoeff Φ S t v) w).im + (inner ℂ v (trivializedCoeff Φ S t w)).im = 0 := by
  have hdΦ (u : F) : HasDerivAt (fun r ↦ Φ r u) (deriv Φ t u) t := by
    simpa using hΦd.hasDerivAt.clm_apply (hasDerivAt_const t u)
  have hdω := ω.hasDerivAt_apply_comp (hdΦ v) (hdΦ w)
  rw [funext fun r ↦ hω r v w] at hdω
  have h0 := hdω.unique (hasDerivAt_const t _)
  rw [← hω t (trivializedCoeff Φ S t v) w, ← hω t v (trivializedCoeff Φ S t w),
    trivializedCoeff_apply, trivializedCoeff_apply, hΦ.self_apply_inverse, hΦ.self_apply_inverse]
  simp only [map_sub, LinearMap.sub_apply]
  linarith [hS (Φ t v) (Φ t w)]

end SymplecticFrame

end Floer

namespace SymplecticForm

section SymplecticOrbit

variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Along `x` where each `H t` is `C²` at `x t`, a loop `S` trivializing `dX_{H_t}(x(t))` in a
differentiable symplectic frame `Φ` is infinitesimally symplectic on `AddCircle 1`. -/
theorem im_inner_apply_add_eq_zero_of_trivializedCoeff (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {x : ℝ → V} (hH : ∀ t, ContDiffAt ℝ 2 (H t) (x t)) {Φ : ℝ → F →L[ℝ] V}
    (hΦd : Differentiable ℝ Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im) {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t =
      Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t)
    (θ : AddCircle (1 : ℝ)) (v w : F) :
    (inner ℂ (S θ v) w).im + (inner ℂ v (S θ w)).im = 0 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact hS t ▸ Floer.im_inner_trivializedCoeff_add_eq_zero ω (hΦd t) (hΦ t) hω
    (ω.apply_fderiv_hamiltonianVectorField_add (hH t)) v w

end SymplecticOrbit

section LoopInvertibility

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **Loop invertibility equivalence in a periodic frame.** Along a one-periodic Hamiltonian orbit
`x` in a differentiable one-periodic frame `Φ`, `CircleSobolev.loopOperator 1 S` is invertible iff
`x(0)` is a nondegenerate fixed point of the time-one flow. -/
theorem isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS : ∀ t : ℝ, S t =
      Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
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
      refine (Floer.hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff
        (hΦd t) (hΦ t) (hζ₀d t)).1 ?_
      simpa only [hfun, ζ₀, (hΦ t).self_apply_inverse] using
        (Floer.asymptoticOperator_eq_zero_iff (hξd t)).1 (hA t)
    funext t
    rw [Pi.zero_apply, ← (hΦ t).self_apply_inverse (ξ t), ← hζeq t, h0, ContinuousMap.zero_apply,
      map_zero]
  · have hζd : Differentiable ℝ fun y : ℝ ↦ ζ y := fun y ↦ (hζ y).differentiableAt
    have hξd : Differentiable ℝ fun t ↦ Φ t (ζ t) := hΦd.clm_apply hζd
    have hξp : Periodic (fun t ↦ Φ t (ζ t)) 1 := fun t ↦ by
      simp only [hΦp t, AddCircle.coe_add_period]
    have h0 := hnd (fun t ↦ Φ t (ζ t)) hξd hξp fun t ↦
      (Floer.asymptoticOperator_eq_zero_iff (hξd t)).2 <|
        (Floer.hasDerivAt_clm_apply_iff_hasDerivAt_trivializedCoeff (hΦd t) (hΦ t) (hζd t)).2
          (by simpa only [hS t] using hζ t)
    ext θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact (hΦ t).injective (by simpa using congrFun h0 t)

/-- **Frame-free loop invertibility equivalence** on a finite-dimensional complex normed space `E`
equipped with a symplectic form `ω`. -/
theorem isInvertible_loopOperator_iff_isNondegenerateFixedPt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (ω : SymplecticForm E) {H : ℝ → E → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H)) (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hxp : Periodic x 1) {S : C(AddCircle (1 : ℝ), E →L[ℝ] E)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    (CircleSobolev.loopOperator 1 S).IsInvertible ↔
      IsNondegenerateFixedPt 𝓘(ℝ, E) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ E) hX hH hHp hx hxp (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ E))
    fun t ↦ by simp [hS t]

end LoopInvertibility

end SymplecticForm

end TauCeti
