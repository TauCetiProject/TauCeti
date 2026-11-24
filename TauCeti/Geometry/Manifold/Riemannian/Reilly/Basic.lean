/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Bochner.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormSq

/-!
# Reilly's vector field

For a smooth function `f` on a Riemannian manifold, Reilly's formula is the divergence theorem for
the vector field

`X = Δf ∇f − ½ ∇|∇f|² = Δf ∇f − ∇_{∇f} ∇f`.

By the Bochner formula its divergence is `(Δf)² − |Hess f|² − Ric(∇f, ∇f)`, and its component
along a vector `w` is `Δf df(w) − Hess f(∇f, w)`. Both identities are pointwise and hold on
manifolds with boundary.

## Main results

* `TauCeti.Manifold.reillyField`: the vector field `Δf ∇f − ½ ∇|∇f|²`.
* `TauCeti.Manifold.inner_reillyField`: `⟪X, w⟫ = Δf df(w) − Hess f(∇f, w)`.
* `TauCeti.Manifold.divergence_reillyField`: `div X = (Δf)² − |Hess f|² − Ric(∇f, ∇f)`.

## References

* R. C. Reilly, *Applications of the Hessian operator in a Riemannian manifold*, Indiana Univ.
  Math. J. 26 (1977), 459–472.
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Field

variable [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M}

variable (I) in
/-- **Reilly's vector field** `Δf ∇f − ½ ∇|∇f|²` of a function `f`. -/
def reillyField (f : M → ℝ) (x : M) : TangentSpace I x :=
  laplaceBeltrami I f x • mgradient I f x -
    (1 / 2 : ℝ) • mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2) x

/-- The defining formula for Reilly’s vector field. -/
theorem reillyField_def (f : M → ℝ) (x : M) :
    reillyField I f x = laplaceBeltrami I f x • mgradient I f x -
      (1 / 2 : ℝ) • mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2) x := by
  rw [reillyField]

/-- Reilly's vector field is `Δf ∇f − ∇_{∇f} ∇f`. -/
theorem reillyField_eq (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    reillyField I f x = laplaceBeltrami I f x • mgradient I f x -
      leviCivitaConnection I M (mgradient I f) x (mgradient I f x) := by
  rw [reillyField_def, mgradient_norm_sq_mgradient hf, smul_smul]
  norm_num

/-- The component of Reilly's vector field along `w` is `Δf df(w) − Hess f(∇f, w)`. -/
theorem inner_reillyField (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (w : TangentSpace I x) :
    ⟪reillyField I f x, w⟫_ℝ =
      laplaceBeltrami I f x * mvfderiv I f x w - hessian I f x (mgradient I f x) w := by
  rw [reillyField_eq hf, inner_sub_left, real_inner_smul_left, inner_mgradient, hessian_def]

end Field

section Divergence

variable [T2Space M] [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ}

omit [T2Space M] in
/-- Reilly's vector field of a smooth function is smooth. -/
theorem contMDiff_reillyField (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    CMDiff ∞ (T% (reillyField I f)) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff ∞ (T% (mgradient I f)) := contMDiff_mgradient hf
  have hL : ContMDiff I 𝓘(ℝ) ∞ (laplaceBeltrami I f) :=
    contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp) hf
  have hN := contMDiff_norm_sq_mgradient (n := ∞) hf
  have hGN : CMDiff ∞ (T% (mgradient I (fun x ↦ ‖mgradient I f x‖ ^ 2))) := contMDiff_mgradient hN
  exact (hL.smul_section hG).sub_section (contMDiff_const.smul_section hGN)

/-- **The divergence of Reilly's vector field**: for a smooth function `f` and every orthonormal
basis `eᵢ` of the tangent space at `x`,
`div (Δf ∇f − ½ ∇|∇f|²) = (Δf)² − ∑ᵢⱼ Hess f(eᵢ, eⱼ)² − Ric(∇f, ∇f)`. -/
theorem divergence_reillyField (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    divergence I (reillyField I f) x =
      laplaceBeltrami I f x ^ 2 - ∑ i, ∑ j, hessian I f x (b i) (b j) ^ 2 -
        (leviCivitaConnection I M).ricciTensor x (mgradient I f x) (mgradient I f x) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff ∞ (T% (mgradient I f)) := contMDiff_mgradient hf
  have hL : ContMDiff I 𝓘(ℝ) ∞ (laplaceBeltrami I f) :=
    contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp) hf
  have hN := contMDiff_norm_sq_mgradient (n := ∞) hf
  have hGN : CMDiff ∞ (T% (mgradient I (fun x ↦ ‖mgradient I f x‖ ^ 2))) := contMDiff_mgradient hN
  have hGd : MDiffAt (T% (mgradient I f)) x := hG.mdifferentiable (by simp) x
  have hGNd : MDiffAt (T% (mgradient I (fun x ↦ ‖mgradient I f x‖ ^ 2))) x :=
    hGN.mdifferentiable (by simp) x
  have hLd : MDifferentiableAt I 𝓘(ℝ) (laplaceBeltrami I f) x := hL.mdifferentiable (by simp) x
  have hX : reillyField I f = laplaceBeltrami I f • mgradient I f +
      (-(1 / 2 : ℝ)) • mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2) := by
    funext y
    simp only [reillyField_def, Pi.add_apply, Pi.smul_apply', neg_smul]
    exact sub_eq_add_neg _ _
  have hA : MDiffAt (T% (laplaceBeltrami I f • mgradient I f)) x :=
    (hL.smul_section hG).mdifferentiable (by simp) x
  have hB : MDiffAt
      (T% ((-(1 / 2 : ℝ)) • mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2))) x :=
    (contMDiff_const.smul_section hGN).mdifferentiable (by simp) x
  rw [hX, divergence_add I _ _ x hA hB, divergence_smul_function I _ _ x hLd hGd,
    divergence_smul I _ _ x hGNd, ← laplaceBeltrami_def, ← laplaceBeltrami_def,
    laplaceBeltrami_norm_sq_mgradient hf x b]
  ring

end Divergence

end TauCeti.Manifold
