/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Cylinder
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Geometry.Symplectic.Transport

/-!
# Sobolev invertibility of the stationary cylinder operator at a Hamiltonian orbit

Let `(V, ω)` be a finite-dimensional symplectic vector space, `x` a one-periodic orbit of a
one-periodic, jointly `C²` time-dependent Hamiltonian `H`, and `J_t` a family of almost complex
structures along `x`. At the stationary cylinder `u(s, t) = x(t)`, the linearized Floer operator is
`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` (`TauCeti.Floer.stationaryCylinderOperator`), with
`S_t = dX_{H_t}(x(t))`.

Along a differentiable path of invertible frames `Φ(t) : F →L[ℝ] V` from a complex inner product
space `F` (with complex structure `I` and symplectic form `ω₀(v, w) = Im ⟪v, w⟫`), pulling back
`ξ(s, t) = Φ(t) η(s, t)` replaces `S_t` by the trivialized loop coefficient

`S_Φ(t) = Φ(t)⁻¹ (S_t Φ(t) - Φ'(t))`

(`TauCeti.Floer.trivializedCoeff`). Specifically:

* **Classical intertwining and weight shifts.** When `Φ(t)` intertwines `I` with `J_t`, both the
  asymptotic operator `A` and the stationary cylinder operator `D` pull back to their model
  counterparts on `(F, I)` with coefficient `S_Φ` (`TauCeti.Floer.asymptoticOperator_frame_apply`,
  `TauCeti.Floer.stationaryCylinderOperator_frame_apply`), and replacing `S_t` by `S_t - δ J_t`
  replaces `S_Φ(t)` by `S_Φ(t) - δ I` (`TauCeti.Floer.trivializedCoeff_sub_smul`).
* **Preservation of infinitesimal symplecticity.** When `Φ(t)` pulls `ω` back to `Im ⟪·, ·⟫`, the
  product rule for `t ↦ ω(Φ(t) v, Φ(t) w)` cancels the connection term `Φ(t)⁻¹ Φ'(t)`, so `S_Φ(t)`
  is infinitesimally symplectic for `Im ⟪·, ·⟫` whenever `S_t` is infinitesimally symplectic for
  `ω` (`TauCeti.Floer.im_inner_trivializedCoeff_add_eq_zero`).
* **Sobolev cylinder invertibility and weighted inverses.** Realizing `∂s + I (∂t - S_Φ)` on the
  common-domain Sobolev space `L²(ℝ, H¹) ∩ W^{1,2}(ℝ, H⁰)` via
  `TauCeti.CircleSobolev.cylinderOperator 1 S_Φ`:
  1. `cylinderOperator 1 S_Φ` is unconditionally injective along any one-periodic orbit `x`, even a
     degenerate one (`TauCeti.SymplecticForm.injective_cylinderOperator_of_trivializedCoeff`);
  2. `cylinderOperator 1 S_Φ` is invertible — and equivalently Fredholm — if and only if `x(0)` is
     a nondegenerate fixed point of the time-one Hamiltonian flow
     (`SymplecticForm.isInvertible_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`,
     `SymplecticForm.isFredholm_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`);
  3. at a nondegenerate orbit, the exponentially weighted cylinder operators
     `cylinderOperator 1 (S_Φ - δ • const (I • id))` are invertible with uniformly bounded inverses
     for all sufficiently small weights `|δ| ≤ ε`
     (`SymplecticForm.exists_pos_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff`).

Specializing to the identity frame on `(F, ω)` with `ω(v, w) = Im ⟪v, w⟫` gives the corresponding
frame-free theorems directly in `TauCeti.SymplecticForm`.

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2,
  Section 2.2 (unitary trivializations along periodic orbits and Proposition 2.2).
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
the differential expression `ζ' - S_t ζ` along a path of invertible frames `Φ : ℝ → F →L[ℝ] V`. -/
def trivializedCoeff (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) : F →L[ℝ] F :=
  (Φ t).inverse ∘L (S t ∘L Φ t - deriv Φ t)

/-- Pointwise evaluation of `trivializedCoeff`. -/
@[simp]
theorem trivializedCoeff_apply (Φ : ℝ → F →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) (v : F) :
    trivializedCoeff Φ S t v = (Φ t).inverse (S t (Φ t v) - deriv Φ t v) :=
  (rfl)

/-- Trivializing along the constant identity frame leaves the loop coefficient unchanged. -/
@[simp]
theorem trivializedCoeff_const_id (S : ℝ → F →L[ℝ] F) (t : ℝ) :
    trivializedCoeff (fun _ ↦ ContinuousLinearMap.id ℝ F) S t = S t := by
  ext v
  simp [trivializedCoeff]

/-- Trivializing along a constant continuous linear equivalence conjugates `S_t` by that
equivalence. -/
theorem trivializedCoeff_const_equiv (e : F ≃L[ℝ] V) (S : ℝ → V →L[ℝ] V) (t : ℝ) :
    trivializedCoeff (fun _ ↦ (e : F →L[ℝ] V)) S t =
      (e.symm : V →L[ℝ] F) ∘L S t ∘L (e : F →L[ℝ] V) := by
  ext v
  simp [trivializedCoeff]

/-- **Pulling back `ζ' - S_t ζ` along a differentiable frame.** -/
theorem comp_sub_trivializedCoeff {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ}
    (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible) (hζ : DifferentiableAt ℝ ζ t) :
    deriv (fun r ↦ Φ r (ζ r)) t - S t (Φ t (ζ t)) =
      Φ t (deriv ζ t - trivializedCoeff Φ S t (ζ t)) := by
  have hd : HasDerivAt (fun r ↦ Φ r (ζ r)) (deriv Φ t (ζ t) + Φ t (deriv ζ t)) t := by
    simpa only [add_comm] using hΦd.hasDerivAt.clm_apply hζ.hasDerivAt
  rw [hd.deriv, map_sub, trivializedCoeff_apply, hΦ.self_apply_inverse]
  abel

/-- **Classical ODE correspondence under a frame.** For a differentiable map `ζ : ℝ → F`, `r ↦ Φ r
(ζ r)` solves `ξ' = S_t ξ` at `t` if and only if `ζ` solves `ζ' = S_Φ(t) ζ` at `t`. -/
theorem hasDerivAt_comp_iff_hasDerivAt_trivializedCoeff {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible)
    (hζ : DifferentiableAt ℝ ζ t) :
    HasDerivAt (fun r ↦ Φ r (ζ r)) (S t (Φ t (ζ t))) t ↔
      HasDerivAt ζ (trivializedCoeff Φ S t (ζ t)) t := by
  have hd : HasDerivAt (fun r ↦ Φ r (ζ r)) (deriv Φ t (ζ t) + Φ t (deriv ζ t)) t := by
    simpa only [add_comm] using hΦd.hasDerivAt.clm_apply hζ.hasDerivAt
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have heq := hd.unique h
    have hsub : Φ t (deriv ζ t - trivializedCoeff Φ S t (ζ t)) = 0 := by
      rw [map_sub, trivializedCoeff_apply, hΦ.self_apply_inverse, ← heq]
      abel
    exact (sub_eq_zero.1 (hΦ.injective (hsub.trans (map_zero (Φ t)).symm))) ▸ hζ.hasDerivAt
  · refine (hΦd.hasDerivAt.clm_apply h).congr_deriv ?_
    rw [trivializedCoeff_apply, hΦ.self_apply_inverse]
    abel

/-- If `Φ` is `C¹` with invertible values and `S` is continuous, then `trivializedCoeff Φ S` is
continuous. -/
theorem continuous_trivializedCoeff [CompleteSpace F] {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    (hΦ : ContDiff ℝ 1 Φ) (hinv : ∀ t, (Φ t).IsInvertible) (hS : Continuous S) :
    Continuous (trivializedCoeff Φ S) := by
  have hderiv : Continuous (deriv Φ) := contDiff_zero.1 (contDiff_succ_iff_deriv.1 hΦ).2.2
  have hinverse : Continuous fun t ↦ (Φ t).inverse :=
    continuous_iff_continuousAt.2 fun t ↦
      ((hinv t).contDiffAt_map_inverse (n := 0)).continuousAt.comp hΦ.continuous.continuousAt
  exact hinverse.clm_comp ((hS.clm_comp hΦ.continuous).sub hderiv)

/-- Periodicity of `Φ` and `S` passes to `trivializedCoeff Φ S`. -/
theorem periodic_trivializedCoeff {Φ : ℝ → F →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {T : ℝ}
    (hΦ : Periodic Φ T) (hS : Periodic S T) :
    Periodic (trivializedCoeff Φ S) T := fun t ↦ by
  simp only [trivializedCoeff, hΦ t, hS t, hΦ.deriv t]

end Trivialization

section ComplexFrame

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- **Weight-shift compatibility under a complex-linear frame.** Subtracting `δ • K_t` from `S_t`,
where `K_t` intertwines with multiplication by `I` through `Φ_t`, subtracts `δ • (I • id)` from
`trivializedCoeff Φ S`. -/
theorem trivializedCoeff_sub_smul {Φ : ℝ → F →L[ℝ] V} {S K : ℝ → V →L[ℝ] V} {t : ℝ}
    (hΦ : (Φ t).IsInvertible) (hK : ∀ v, K t (Φ t v) = Φ t (I • v)) (δ : ℝ) :
    trivializedCoeff Φ (fun r ↦ S r - δ • K r) t =
      trivializedCoeff Φ S t - δ • (I • ContinuousLinearMap.id ℝ F) := by
  ext v
  simp only [trivializedCoeff_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply, hK,
    sub_right_comm _ (δ • Φ t (I • v)), map_sub, map_smul, hΦ.inverse_apply_self]

/-- **Intertwining the asymptotic operator.** When `Φ(t)` intertwines multiplication by `I` with
`J(t)`, `asymptoticOperator J S` pulls back along `Φ` to the model asymptotic operator on `F` with
coefficient `trivializedCoeff Φ S`. -/
theorem asymptoticOperator_frame_apply {Φ : ℝ → F →L[ℝ] V} {J : ℝ → AlmostComplexStructure V}
    {S : ℝ → V →L[ℝ] V} {ζ : ℝ → F} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t)
    (hΦ : (Φ t).IsInvertible) (hJ : ∀ v, J t (Φ t v) = Φ t (I • v))
    (hζ : DifferentiableAt ℝ ζ t) :
    asymptoticOperator J S (fun r ↦ Φ r (ζ r)) t =
      Φ t (asymptoticOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (trivializedCoeff Φ S) ζ t) := by
  rw [asymptoticOperator_def, comp_sub_trivializedCoeff hΦd hΦ hζ, hJ, asymptoticOperator_def,
    AlmostComplexStructure.ofComplexModule_apply]

/-- **Intertwining the stationary cylinder operator.** When `Φ(z.2)` intertwines multiplication by
`I` with `J(z.2)`, `stationaryCylinderOperator J S` pulls back along `(s, t) ↦ Φ t (η(s, t))` to the
model stationary cylinder operator on `F` with coefficient `trivializedCoeff Φ S`. -/
theorem stationaryCylinderOperator_frame_apply {Φ : ℝ → F →L[ℝ] V}
    {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V} {η : ℝ × ℝ → F} {z : ℝ × ℝ}
    (hΦd : DifferentiableAt ℝ Φ z.2) (hΦ : (Φ z.2).IsInvertible)
    (hJ : ∀ v, J z.2 (Φ z.2 v) = Φ z.2 (I • v)) (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderOperator J S (fun w ↦ Φ w.2 (η w)) z =
      Φ z.2 (stationaryCylinderOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (trivializedCoeff Φ S) η z) := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ Φ w.2 (η w))
      ((Φ z.2).comp (fderiv ℝ η z) +
        ((fderiv ℝ Φ z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).flip (η z)) z :=
    (hΦd.hasFDerivAt.comp z hasFDerivAt_snd).clm_apply hη.hasFDerivAt
  rw [stationaryCylinderOperator_def, hd.fderiv, stationaryCylinderOperator_def]
  simp only [add_apply, coe_comp, Function.comp_apply, flip_apply, coe_snd',
    stdComplexLineReal_eq, stdComplexLineImag_eq]
  simp only [map_zero, zero_apply, add_zero, fderiv_apply_one_eq_deriv,
    AlmostComplexStructure.ofComplexModule_apply, map_add, map_sub, trivializedCoeff_apply,
    hΦ.self_apply_inverse, ← hJ]
  abel

end ComplexFrame

section SymplecticFrame

variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Preservation of infinitesimal symplecticity under a symplectic frame.** If `Φ` pulls a
symplectic form `ω` on `V` back to `Im ⟪·, ·⟫` on `F`, then `trivializedCoeff Φ S t` is
infinitesimally symplectic for `Im ⟪·, ·⟫` whenever `S t` is infinitesimally symplectic for `ω`. -/
theorem im_inner_trivializedCoeff_add_eq_zero (ω : SymplecticForm V) {Φ : ℝ → F →L[ℝ] V}
    {S : ℝ → V →L[ℝ] V} {t : ℝ} (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible)
    (hω : ∀ r v w, ω (Φ r v) (Φ r w) = (inner ℂ v w).im)
    (hS : ∀ v w, ω (S t v) w + ω v (S t w) = 0) (v w : F) :
    (inner ℂ (trivializedCoeff Φ S t v) w).im +
      (inner ℂ v (trivializedCoeff Φ S t w)).im = 0 := by
  have hdΦ (u : F) : HasDerivAt (fun r ↦ Φ r u) (deriv Φ t u) t := by
    simpa using hΦd.hasDerivAt.clm_apply (hasDerivAt_const t u)
  have hdω := ω.hasDerivAt_apply_comp (hdΦ v) (hdΦ w)
  rw [funext fun r ↦ hω r v w] at hdω
  have h0 : ω (deriv Φ t v) (Φ t w) + ω (Φ t v) (deriv Φ t w) = 0 :=
    hdω.unique (hasDerivAt_const t _)
  rw [← hω t (trivializedCoeff Φ S t v) w, ← hω t v (trivializedCoeff Φ S t w),
    trivializedCoeff_apply, trivializedCoeff_apply, hΦ.self_apply_inverse, hΦ.self_apply_inverse]
  simp only [map_sub, LinearMap.sub_apply]
  linarith [hS (Φ t v) (Φ t w)]

end SymplecticFrame

end Floer

namespace SymplecticForm

section TrivializedOrbit

variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Along a Hamiltonian orbit `x`, the loop `S_Φ` trivializing `dX_{H_t}(x(t))` in a symplectic
frame `Φ` is infinitesimally symplectic at every point of `AddCircle 1`. -/
theorem im_inner_trivializedCoeff_hamiltonian_add_eq_zero (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V} {Φ : ℝ → F →L[ℝ] V}
    (hΦd : Differentiable ℝ Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t)
    (θ : AddCircle (1 : ℝ)) (v w : F) :
    (inner ℂ (S θ v) w).im + (inner ℂ v (S θ w)).im = 0 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [hS t]
  exact Floer.im_inner_trivializedCoeff_add_eq_zero ω (hΦd t) (hΦ t) hω
    (ω.apply_fderiv_hamiltonianVectorField_add (hH.comp (contDiff_prodMk_right t)).contDiffAt) v w

variable [FiniteDimensional ℂ F]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **Unconditional injectivity of the Sobolev cylinder operator along a periodic orbit.** Even when
the orbit `x` is degenerate, `CircleSobolev.cylinderOperator 1 S` has trivial kernel on
`L²(ℝ, H¹) ∩ W^{1,2}(ℝ, H⁰)`. -/
theorem injective_cylinderOperator_of_trivializedCoeff (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V} {Φ : ℝ → F →L[ℝ] V}
    (hΦd : Differentiable ℝ Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    Function.Injective (CircleSobolev.cylinderOperator 1 S) :=
  CircleSobolev.injective_cylinderOperator 1
    (ω.im_inner_trivializedCoeff_hamiltonian_add_eq_zero hH hΦd hΦ hω hS)

/-- **Loop invertibility equivalence in a periodic frame.** Along a one-periodic Hamiltonian orbit
`x` trivialized by a differentiable one-periodic frame `Φ`, `CircleSobolev.loopOperator 1 S` is
invertible if and only if `x(0)` is a nondegenerate fixed point of the time-one flow. -/
theorem isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
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
    have hζeq (t : ℝ) : ζ t = (Φ t).inverse (ξ t) := rfl
    have hfun : (fun r ↦ Φ r (ζ₀ r)) = ξ :=
      funext fun r ↦ (hΦ r).self_apply_inverse (ξ r)
    have h0 := hloop ζ fun t ↦ by
      rw [funext hζeq, hS t]
      refine (Floer.hasDerivAt_comp_iff_hasDerivAt_trivializedCoeff (hΦd t) (hΦ t) (hζ₀d t)).1 ?_
      have hξ' := (Floer.asymptoticOperator_eq_zero_iff (hξd t)).1 (hA t)
      simpa only [hfun, ζ₀, (hΦ t).self_apply_inverse] using hξ'
    funext t
    rw [Pi.zero_apply, ← (hΦ t).self_apply_inverse (ξ t), ← hζeq t, h0,
      ContinuousMap.zero_apply, map_zero]
  · have hζd : Differentiable ℝ fun y : ℝ ↦ ζ y := fun y ↦ (hζ y).differentiableAt
    have hξd : Differentiable ℝ fun t ↦ Φ t (ζ t) := hΦd.clm_apply hζd
    have hξp : Periodic (fun t ↦ Φ t (ζ t)) 1 := fun t ↦ by
      simp only [hΦp t, AddCircle.coe_add_period]
    have h0 := hnd (fun t ↦ Φ t (ζ t)) hξd hξp fun t ↦ by
      refine (Floer.asymptoticOperator_eq_zero_iff (hξd t)).2 ?_
      refine (Floer.hasDerivAt_comp_iff_hasDerivAt_trivializedCoeff
        (S := fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r))
        (hΦd t) (hΦ t) (hζd t)).2 ?_
      simpa only [hS t] using hζ t
    ext θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact (hΦ t).injective (by simpa using congrFun h0 t)

/-- **Stationary cylinder invertibility equivalence in a unitary frame.** Along a one-periodic
Hamiltonian orbit `x` trivialized by a differentiable one-periodic symplectic frame `Φ`, the
Sobolev stationary cylinder operator `CircleSobolev.cylinderOperator 1 S` is invertible if and only
if `x(0)` is a nondegenerate fixed point of the time-one Hamiltonian flow. -/
theorem isInvertible_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    (CircleSobolev.cylinderOperator 1 S).IsInvertible ↔
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  (CircleSobolev.isInvertible_cylinderOperator_iff_isInvertible_loopOperator 1
    (ω.im_inner_trivializedCoeff_hamiltonian_add_eq_zero hH hΦd hΦ hω hS)).trans
    (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff hX hH hHp hx hxp
      hΦd hΦp hΦ hS)

/-- **Stationary cylinder Fredholm equivalence in a unitary frame.** Along a one-periodic
Hamiltonian orbit `x` trivialized by a differentiable one-periodic symplectic frame `Φ`, the
Sobolev stationary cylinder operator is Fredholm if and only if `x(0)` is a nondegenerate fixed
point of the time-one Hamiltonian flow. -/
theorem isFredholm_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    (CircleSobolev.cylinderOperator 1 S).IsFredholm ↔
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  (CircleSobolev.isFredholm_cylinderOperator_iff_isInvertible_loopOperator 1
    (ω.im_inner_trivializedCoeff_hamiltonian_add_eq_zero hH hΦd hΦ hω hS)).trans
    (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff hX hH hHp hx hxp
      hΦd hΦp hΦ hS)

/-- **Uniform weighted cylinder inverses at a nondegenerate orbit.** At a nondegenerate one-periodic
orbit `x` trivialized by a differentiable one-periodic symplectic frame `Φ`, there exist `ε > 0`
and `C ≥ 0` such that for every exponential weight `|δ| ≤ ε`, the shifted cylinder operator
`CircleSobolev.cylinderOperator 1 (S - δ • const (I • id))` is invertible with inverse norm at most
`C`. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ δ : ℝ, |δ| ≤ ε →
      (CircleSobolev.cylinderOperator 1
          (S - δ • ContinuousMap.const (AddCircle (1 : ℝ))
            (I • ContinuousLinearMap.id ℝ F))).IsInvertible ∧
        ‖(CircleSobolev.cylinderOperator 1
            (S - δ • ContinuousMap.const (AddCircle (1 : ℝ))
              (I • ContinuousLinearMap.id ℝ F))).inverse‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, h⟩ :=
    CircleSobolev.exists_pos_isInvertible_cylinderOperator_sub_smul_of_isInvertible_loopOperator 1
      (isCompact_singleton (x := ())) (fun _ ↦ S)
      (fun _ ↦ ContinuousMap.const (AddCircle (1 : ℝ)) (I • ContinuousLinearMap.id ℝ F))
      continuousOn_const continuousOn_const
      (fun _ _ ↦ ω.im_inner_trivializedCoeff_hamiltonian_add_eq_zero hH hΦd hΦ hω hS)
      (fun _ _ ↦ (ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
        hX hH hHp hx hxp hΦd hΦp hΦ hS).2 hnd)
  exact ⟨ε, hε, C, hC, fun δ hδ ↦ h () rfl δ hδ⟩

/-- Filter form of `exists_pos_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff`: for all
weights `δ` in a neighborhood of `0`, the weighted cylinder operator is invertible. -/
theorem eventually_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {Φ : ℝ → F →L[ℝ] V} (hΦd : Differentiable ℝ Φ) (hΦp : Periodic Φ 1)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ,
      S t = Floer.trivializedCoeff Φ (fun r ↦ fderiv ℝ (ω.hamiltonianVectorField (H r)) (x r)) t) :
    ∀ᶠ δ in 𝓝 (0 : ℝ),
      (CircleSobolev.cylinderOperator 1
        (S - δ • ContinuousMap.const (AddCircle (1 : ℝ))
          (I • ContinuousLinearMap.id ℝ F))).IsInvertible := by
  obtain ⟨ε, hε, _, _, h⟩ :=
    ω.exists_pos_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff hX hH hHp hx hxp hnd
      hΦd hΦp hΦ hω hS
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hε] with δ hδ
  exact (h δ (by simpa [Real.dist_eq] using hδ)).1

end TrivializedOrbit

section ComplexInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Frame-free unconditional injectivity of `CircleSobolev.cylinderOperator 1 S` along any
Hamiltonian orbit on `(F, ω)` with `ω(v, w) = Im ⟪v, w⟫`. -/
theorem injective_cylinderOperator (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} (hH : ContDiff ℝ 2 (uncurry H))
    {x : ℝ → F} {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    Function.Injective (CircleSobolev.cylinderOperator 1 S) :=
  ω.injective_cylinderOperator_of_trivializedCoeff (x := x)
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hH (differentiable_const _)
    (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω) fun t ↦ by
      simp [hS t]

/-- **Frame-free stationary cylinder invertibility equivalence.** On a finite-dimensional complex
inner product space `F` with symplectic form `ω(v, w) = Im ⟪v, w⟫`, the Sobolev stationary cylinder
operator along a one-periodic orbit `x` is invertible if and only if `x(0)` is a nondegenerate fixed
point of the time-one Hamiltonian flow. -/
theorem isInvertible_cylinderOperator_iff_isNondegenerateFixedPt (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    (CircleSobolev.cylinderOperator 1 S).IsInvertible ↔
      IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  ω.isInvertible_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hX hH hHp hx hxp (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω)
    fun t ↦ by simp [hS t]

/-- **Frame-free stationary cylinder Fredholm equivalence.** On `(F, ω)` with
`ω(v, w) = Im ⟪v, w⟫`, the Sobolev stationary cylinder operator along a one-periodic orbit `x` is
Fredholm if and only if `x(0)` is a nondegenerate fixed point of the time-one Hamiltonian flow. -/
theorem isFredholm_cylinderOperator_iff_isNondegenerateFixedPt (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    (CircleSobolev.cylinderOperator 1 S).IsFredholm ↔
      IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) :=
  ω.isFredholm_cylinderOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hX hH hHp hx hxp (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω)
    fun t ↦ by simp [hS t]

/-- **Frame-free uniform weighted cylinder inverses at a nondegenerate orbit.** -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_of_isNondegenerateFixedPt
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ δ : ℝ, |δ| ≤ ε →
      (CircleSobolev.cylinderOperator 1
          (S - δ • ContinuousMap.const (AddCircle (1 : ℝ))
            (I • ContinuousLinearMap.id ℝ F))).IsInvertible ∧
        ‖(CircleSobolev.cylinderOperator 1
            (S - δ • ContinuousMap.const (AddCircle (1 : ℝ))
              (I • ContinuousLinearMap.id ℝ F))).inverse‖ ≤ C :=
  ω.exists_pos_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hX hH hHp hx hxp hnd (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω)
    fun t ↦ by simp [hS t]

/-- Filter form of `exists_pos_isInvertible_cylinderOperator_sub_smul_of_isNondegenerateFixedPt`. -/
theorem eventually_isInvertible_cylinderOperator_sub_smul (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)}
    (hS : ∀ t : ℝ, S t = fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) :
    ∀ᶠ δ in 𝓝 (0 : ℝ),
      (CircleSobolev.cylinderOperator 1
        (S - δ • ContinuousMap.const (AddCircle (1 : ℝ))
          (I • ContinuousLinearMap.id ℝ F))).IsInvertible :=
  ω.eventually_isInvertible_cylinderOperator_sub_smul_of_trivializedCoeff
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) hX hH hHp hx hxp hnd (differentiable_const _)
    (fun _ ↦ rfl) (fun _ ↦ isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ F)) (fun _ ↦ hω)
    fun t ↦ by simp [hS t]

end ComplexInnerProductSpace

end SymplecticForm

end TauCeti
