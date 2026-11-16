/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# The covariant derivative of a twisted section on a flat space

Let `E` be a real normed space, `b` a real one-form on `E` and `a = i b` the corresponding
imaginary connection form on a trivial Hermitian line. For a section `α : E → F` of the trivial
bundle whose fibre `F` is a complex vector space, for instance a section of the line (`F = ℂ`) or a
spinor field twisted by the line (`F` a Clifford module), the covariant derivative is

`∇_a α = dα + i b α`     (`TauCeti.SeibergWitten.covariantDeriv`).

This file collects its basic API: evaluation, linearity, differentiability, the commutation with
complex-linear endomorphisms of a finite-dimensional fibre, and the **Ricci identity**: the
curvature of `∇ = d + i b` is `i db`, so the second covariant derivative
`∇²_{v, w} ψ = ∇_v (∇ψ)(w)` satisfies `∇²_{v, w} ψ - ∇²_{w, v} ψ = i db(v, w) ψ`.

## Main definitions

* `TauCeti.SeibergWitten.covariantDeriv b α`: the covariant derivative `dα + i b α`.

## Main results

* `TauCeti.SeibergWitten.covariantDeriv_apply_eq_add_smul`,
  `TauCeti.SeibergWitten.covariantDeriv_apply`: evaluation of the covariant derivative on a vector.
* `TauCeti.SeibergWitten.covariantDeriv_add`, `TauCeti.SeibergWitten.covariantDeriv_const_smul`,
  `TauCeti.SeibergWitten.covariantDeriv_fun_sum`,
  `TauCeti.SeibergWitten.covariantDeriv_apply_apply`,
  `TauCeti.SeibergWitten.differentiableAt_covariantDeriv`: linearity, evaluation and
  differentiability of covariant derivatives of vector-valued sections.
* `TauCeti.SeibergWitten.covariantDeriv_covariantDeriv_sub`: the Ricci identity
  `∇²_{v, w} ψ - ∇²_{w, v} ψ = i db(v, w) ψ`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {x : E}

/-- The covariant derivative `∇_a α = dα + i b α` of a section `α` of the trivial bundle with
fibre a complex vector space `F`, for the imaginary connection form `a = i b`. For `F = ℂ` this is
a section of the trivial line; for `F` a Clifford module it is a spinor field twisted by the line.
-/
def covariantDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → F) (x : E) : E →L[ℝ] F :=
  fderiv ℝ α x + ((ofSubsingletonLIE (0 : Fin 1)).symm (b x)).smulRight (I • α x)

/-- The covariant derivative of a vector-valued section evaluated on a vector. -/
theorem covariantDeriv_apply_eq_add_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → F) (x v : E) :
    covariantDeriv b α x v = fderiv ℝ α x v + b x (fun _ ↦ v) • I • α x := by
  simp [covariantDeriv, ofSubsingletonLIE_symm_apply]

/-- The covariant derivative evaluated on a vector. -/
@[simp]
theorem covariantDeriv_apply (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x v : E) :
    covariantDeriv b α x v = fderiv ℝ α x v + I * b x (fun _ ↦ v) * α x := by
  simp [covariantDeriv_apply_eq_add_smul]
  ring

/-- The covariant derivative of a `C¹` section for a continuous connection form is
continuous. -/
theorem continuous_covariantDeriv (hα : ContDiff ℝ 1 α) (hb : Continuous b) :
    Continuous (covariantDeriv b α) := by
  unfold covariantDeriv
  fun_prop

section VectorValued

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {ψ φ : E → W} {κ : Type*}
  [Fintype κ]

/-- The covariant derivative of the zero section vanishes. -/
@[simp]
theorem covariantDeriv_zero : covariantDeriv b (0 : E → W) x = 0 := by
  ext v
  simp [covariantDeriv_apply_eq_add_smul]

/-- The covariant derivative of a sum of differentiable sections is the sum of their covariant
derivatives. -/
theorem covariantDeriv_add (hψ : DifferentiableAt ℝ ψ x) (hφ : DifferentiableAt ℝ φ x) :
    covariantDeriv b (ψ + φ) x = covariantDeriv b ψ x + covariantDeriv b φ x := by
  ext v
  simp only [_root_.add_apply, covariantDeriv_apply_eq_add_smul, fderiv_add hψ hφ,
    Pi.add_apply, smul_add]
  abel

/-- The covariant derivative commutes with multiplication of a differentiable section by a
complex constant. -/
theorem covariantDeriv_const_smul (c : ℂ) (hψ : DifferentiableAt ℝ ψ x) :
    covariantDeriv b (c • ψ) x = c • covariantDeriv b ψ x := by
  ext v
  simp only [_root_.smul_apply, covariantDeriv_apply_eq_add_smul,
    fderiv_const_smul hψ c, Pi.smul_apply, smul_add, smul_comm c]

/-- The covariant derivative of a finite sum of differentiable sections is the sum of their
covariant derivatives. -/
theorem covariantDeriv_fun_sum {f : κ → E → W} (hf : ∀ k, DifferentiableAt ℝ (f k) x) :
    covariantDeriv b (fun y ↦ ∑ k, f k y) x = ∑ k, covariantDeriv b (f k) x := by
  ext v
  simp only [_root_.sum_apply, covariantDeriv_apply_eq_add_smul,
    Finset.sum_add_distrib, Finset.smul_sum]
  rw [fderiv_fun_sum fun k _ ↦ hf k]
  simp

/-- The covariant derivative of a section of `Hom(E, W)` evaluated at a fixed vector `w` is the
covariant derivative of the section `y ↦ G y w` of `W`. -/
theorem covariantDeriv_apply_apply {G : E → E →L[ℝ] W} (hG : DifferentiableAt ℝ G x)
    (v w : E) : covariantDeriv b G x v w = covariantDeriv b (fun y ↦ G y w) x v := by
  have hd : fderiv ℝ (fun y ↦ G y w) x = (ContinuousLinearMap.apply ℝ W w).comp (fderiv ℝ G x) :=
    ((ContinuousLinearMap.apply ℝ W w).hasFDerivAt.comp x hG.hasFDerivAt).fderiv
  simp [covariantDeriv_apply_eq_add_smul, hd]

/-- The covariant derivative of a section `ψ` is differentiable at `x` when `ψ`, its derivative
`dψ` and the connection form `b` are differentiable at `x`. -/
theorem differentiableAt_covariantDeriv (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) x)
    (hψ' : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) :
    DifferentiableAt ℝ (covariantDeriv b ψ) x := by
  -- `∇ψ(y) = dψ(y) + (b y) ⊗ i ψ(y)`, a sum of differentiable maps.
  have heq : covariantDeriv b ψ = fun y ↦ fderiv ℝ ψ y +
      ContinuousLinearMap.smulRightL ℝ E W
        ((ofSubsingletonLIE (0 : Fin 1)).symm (b y)) (I • ψ y) := by
    ext y v
    simp [covariantDeriv_apply_eq_add_smul, ofSubsingletonLIE_symm_apply]
  rw [heq]
  refine hψ.add ?_
  have h₁ : DifferentiableAt ℝ (fun y ↦ (ofSubsingletonLIE (0 : Fin 1)).symm (b y)) x := by
    fun_prop
  have h₂ : DifferentiableAt ℝ (fun y ↦ I • ψ y) x := hψ'.const_smul I
  exact ((ContinuousLinearMap.smulRightL ℝ E W).differentiableAt.comp x h₁).clm_apply h₂

/-- The second covariant derivative `∇²_{v, w} ψ = ∇_v (∇ψ)(w)`, expanded. -/
theorem covariantDeriv_covariantDeriv_apply (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) x)
    (hψ' : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) (v w : E) :
    covariantDeriv b (covariantDeriv b ψ) x v w =
      fderiv ℝ (fderiv ℝ ψ) x v w + b x (fun _ ↦ w) • I • fderiv ℝ ψ x v +
        fderiv ℝ (fun y ↦ b y (fun _ ↦ w)) x v • I • ψ x +
        b x (fun _ ↦ v) • I • (fderiv ℝ ψ x w + b x (fun _ ↦ w) • I • ψ x) := by
  have hfun : (fun y ↦ covariantDeriv b ψ y w) =
      fun y ↦ fderiv ℝ ψ y w + b y (fun _ ↦ w) • I • ψ y :=
    funext fun y ↦ covariantDeriv_apply_eq_add_smul b ψ y w
  rw [covariantDeriv_apply_apply (differentiableAt_covariantDeriv hψ hψ' hb),
    covariantDeriv_apply_eq_add_smul, hfun, covariantDeriv_apply_eq_add_smul]
  have hbw : DifferentiableAt ℝ (fun y ↦ b y (fun _ ↦ w)) x :=
    hb.continuousAlternatingMap_apply_const _
  have hfw : DifferentiableAt ℝ (fun y ↦ fderiv ℝ ψ y w) x :=
    (ContinuousLinearMap.apply ℝ W w).differentiableAt.comp x hψ
  have h₁ : fderiv ℝ (fun y ↦ fderiv ℝ ψ y w) x v = fderiv ℝ (fderiv ℝ ψ) x v w := by
    rw [fderiv_clm_apply hψ (differentiableAt_const w)]
    simp
  have hd : HasFDerivAt (fun y ↦ fderiv ℝ ψ y w + b y (fun _ ↦ w) • I • ψ y) _ x :=
    hfw.hasFDerivAt.add (hbw.hasFDerivAt.smul (hψ'.hasFDerivAt.const_smul I))
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, h₁]
  abel

/-- **The Ricci identity** for the twisted connection on flat space: the curvature of
`∇ = d + i b` is `i db`, so `∇²_{v, w} ψ - ∇²_{w, v} ψ = db(v, w) i ψ`. -/
theorem covariantDeriv_covariantDeriv_sub (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) (v w : E) :
    covariantDeriv b (covariantDeriv b ψ) x v w - covariantDeriv b (covariantDeriv b ψ) x w v =
      extDeriv b x ![v, w] • I • ψ x := by
  have hψ₁ : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hψ' : DifferentiableAt ℝ ψ x := hψ.differentiableAt two_ne_zero
  have hsymm : fderiv ℝ (fderiv ℝ ψ) x v w = fderiv ℝ (fderiv ℝ ψ) x w v :=
    hψ.isSymmSndFDerivAt (by simp) v w
  rw [covariantDeriv_covariantDeriv_apply hψ₁ hψ' hb,
    covariantDeriv_covariantDeriv_apply hψ₁ hψ' hb, extDeriv_apply_pair_of_differentiableAt hb,
    hsymm, sub_smul]
  simp only [smul_add, smul_comm (b x (fun _ ↦ v)) I, smul_comm (b x (fun _ ↦ w)) I,
    smul_smul (b x (fun _ ↦ v)), smul_smul (b x (fun _ ↦ w)), mul_comm (b x (fun _ ↦ w))]
  abel

/-- The covariant derivative commutes with a complex-linear endomorphism of a finite-dimensional
fibre: `∇ (T ψ) = T (∇ ψ)`. -/
theorem covariantDeriv_comp_apply [FiniteDimensional ℂ W] (T : Module.End ℂ W)
    (hψ : DifferentiableAt ℝ ψ x) (v : E) :
    covariantDeriv b (fun y ↦ T (ψ y)) x v = T (covariantDeriv b ψ x v) := by
  set L := (LinearMap.toContinuousLinearMap T).restrictScalars ℝ
  have hd : fderiv ℝ (fun y ↦ T (ψ y)) x = L.comp (fderiv ℝ ψ x) :=
    (L.hasFDerivAt.comp x hψ.hasFDerivAt).fderiv
  simp [covariantDeriv_apply_eq_add_smul, hd, L, LinearMap.map_smul_of_tower]

end VectorValued

end TauCeti.SeibergWitten
