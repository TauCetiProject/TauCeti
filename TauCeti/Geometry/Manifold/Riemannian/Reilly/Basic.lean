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
  rw [reillyField_eq hf, inner_sub_left, real_inner_smul_left, inner_mgradient,
    I.hessian_eq_inner_leviCivitaConnection_mgradient]

end Field

section Regularity

variable {n : ℕ∞ω} [IsManifold I 2 M] [IsManifold I (n + 1) M]
  [IsManifold I (n + 1 + 1) M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (n + 1) E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ}

private theorem contMDiff_laplaceBeltrami_smul_mgradient
    (hf : ContMDiff I 𝓘(ℝ) (n + 2) f) :
    CMDiff n (T% (laplaceBeltrami I f • mgradient I f)) := by
  let _ : IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := n + 1) (by simp)
  exact (contMDiff_laplaceBeltrami (m := n + 1 + 1) (k := n + 1)
    (by simp [add_assoc, one_add_one_eq_two]) le_rfl hf).smul_section
    (contMDiff_mgradient (hf.of_le (by gcongr; norm_num)))

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
private theorem contMDiff_const_smul_mgradient_norm_sq_mgradient
    (hf : ContMDiff I 𝓘(ℝ) (n + 2) f) (c : ℝ) :
    CMDiff n (T% (c • mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2))) := by
  let _ : IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := n + 1) (by simp)
  have hN : ContMDiff I 𝓘(ℝ) (n + 1) (fun y ↦ ‖mgradient I f y‖ ^ 2) :=
    contMDiff_norm_sq_mgradient (by simpa only [add_assoc, one_add_one_eq_two] using hf)
  exact (contMDiff_mgradient hN).const_smul_section

end Regularity

/-- On a `C^m` manifold with a `C^k` metric, Reilly's vector field of a `C^(n + 2)` function
is `C^n` when `n + 2 ≤ m` and `n + 1 ≤ k`. -/
theorem contMDiff_reillyField {n m k : ℕ∞ω} [IsManifold I 2 M] [IsManifold I m M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]
    (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) (n + 2) f) : CMDiff n (T% (reillyField I f)) := by
  let _ : IsManifold I (n + 1 + 1) M := IsManifold.of_le (n := m) (by
    simpa only [add_assoc, one_add_one_eq_two] using hm)
  let _ : IsManifold I (n + 1) M := IsManifold.of_le (n := n + 1 + 1) (by simp)
  let _ : IsContMDiffRiemannianBundle I (n + 1) E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k) hk
  exact (contMDiff_laplaceBeltrami_smul_mgradient hf).sub_section
    (contMDiff_const_smul_mgradient_norm_sq_mgradient hf (1 / 2))

section Divergence

variable [T2Space M] [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ}

/-- **The divergence of Reilly's vector field**: for a smooth function `f` and every orthonormal
basis `eᵢ` of the tangent space at `x`,
`div (Δf ∇f − ½ ∇|∇f|²) = (Δf)² − ∑ᵢⱼ Hess f(eᵢ, eⱼ)² − Ric(∇f, ∇f)`. -/
theorem divergence_reillyField (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    divergence I (reillyField I f) x =
      laplaceBeltrami I f x ^ 2 - ∑ i, ∑ j, hessian I f x (b i) (b j) ^ 2 -
        (leviCivitaConnection I M).ricciTensor x (mgradient I f x) (mgradient I f x) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let _ : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let _ : IsContMDiffRiemannianBundle I (∞ + 1) E (fun x : M ↦ TangentSpace I x) := by
    simpa using (inferInstance : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x))
  have hGd : MDiffAt (T% (mgradient I f)) x :=
    mdifferentiable_mgradient (hf.of_le (by simp)) x
  have hGNd : MDiffAt (T% (mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2))) x := by
    simpa only [one_smul] using
      (contMDiff_const_smul_mgradient_norm_sq_mgradient (n := ∞) hf 1).mdifferentiable
        (by simp) x
  have hLd : MDifferentiableAt I 𝓘(ℝ) (laplaceBeltrami I f) x :=
    (contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞)
      (by simp) (by simp) hf).mdifferentiable (by simp) x
  have hX : reillyField I f = laplaceBeltrami I f • mgradient I f +
      (-(1 / 2 : ℝ)) • mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2) := by
    funext y
    simp only [reillyField_def, Pi.add_apply, Pi.smul_apply', neg_smul]
    exact sub_eq_add_neg _ _
  have hA : MDiffAt (T% (laplaceBeltrami I f • mgradient I f)) x :=
    (contMDiff_laplaceBeltrami_smul_mgradient (n := ∞) hf).mdifferentiable (by simp) x
  have hB : MDiffAt
      (T% ((-(1 / 2 : ℝ)) • mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2))) x :=
    (contMDiff_const_smul_mgradient_norm_sq_mgradient (n := ∞) hf (-(1 / 2))).mdifferentiable
      (by simp) x
  rw [hX, divergence_add I _ _ x hA hB, divergence_smul_function I _ _ x hLd hGd,
    divergence_smul I _ _ x hGNd, ← laplaceBeltrami_def, ← laplaceBeltrami_def,
    laplaceBeltrami_norm_sq_mgradient hf x b]
  ring

end Divergence

end TauCeti.Manifold
