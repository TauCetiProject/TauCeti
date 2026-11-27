/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Inner products of curve velocities with tangent fields

For a pair of tangent fields `s = (s₀, s₁)` and a curve `γ` in a Riemannian manifold, the complex
number `⟪s₀, γ'⟫ + i ⟪s₁, γ'⟫` packages the two inner products with the velocity `γ'(t)`
(`TauCeti.Manifold.frameVelocityCoordinates`). When the span of `s` at `γ t` contains the
velocity, it vanishes exactly where the velocity does; if `s` is moreover orthonormal at `γ t`, it
determines the velocity, `γ' = Re z • s₀ + Im z • s₁`, and has the norm of the velocity. It is
periodic along a periodic curve, continuous along a `C¹` curve for a continuous metric and tangent
fields continuous on a set containing the curve, and `C^k` along a `C^(k+1)` curve for a `C^k`
metric and tangent fields `C^k` on such a set.

For velocity inner products `z` continuous and nonzero on `[0, 1]` with equal normalized endpoints,
normalized coordinates `z / ‖z‖` form a loop in the unit circle `Circle`
by applying `ContinuousMap.exists_path_eq_div_norm` to the restriction of `z`. When the pair is
orthonormal along the curve and its span contains the velocity, this is the unit tangent read
in the pair: if `θ` is a continuous angle of this loop, the unit tangent is
`T = cos θ s₀ + sin θ s₁`.

## Main results

* `TauCeti.Manifold.curveVelocity_eq_frameVelocityCoordinates`: reconstruction of the velocity.
* `TauCeti.Manifold.norm_frameVelocityCoordinates`: in a pair orthonormal at the evaluation point
  whose span contains the velocity, the coordinates have the norm of the velocity.
* `TauCeti.Manifold.frameVelocityCoordinates_eq_zero_iff`: the coordinates vanish exactly at
  stationary points when the span of the pair at the evaluation point contains the velocity.
* `TauCeti.Manifold.periodic_frameVelocityCoordinates`: periodicity along periodic curves.
* `TauCeti.Manifold.continuous_frameVelocityCoordinates`: continuity along `C¹` curves.
* `TauCeti.Manifold.contDiff_frameVelocityCoordinates`: `C^k` regularity along `C^(k+1)` curves.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 9.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The pair of inner products `⟪s₀, γ'⟫ + i ⟪s₁, γ'⟫` with the velocity of `γ` at `t`,
where the tangent fields `s = (s₀, s₁)` are evaluated at `γ t`. For an orthonormal pair whose
span contains the velocity, these are its reconstruction coefficients. -/
def frameVelocityCoordinates (s : Fin 2 → Π x : M, TangentSpace I x) (γ : ℝ → M) (t : ℝ) : ℂ :=
  ⟨inner ℝ (s 0 (γ t)) (curveVelocity I γ t), inner ℝ (s 1 (γ t)) (curveVelocity I γ t)⟩

/-- The real part of the frame coordinates is the inner product with the first field. -/
@[simp]
theorem frameVelocityCoordinates_re (s : Fin 2 → Π x : M, TangentSpace I x) (γ : ℝ → M)
    (t : ℝ) : (frameVelocityCoordinates s γ t).re = inner ℝ (s 0 (γ t)) (curveVelocity I γ t) :=
  (rfl)

/-- The imaginary part of the frame coordinates is the inner product with the second field. -/
@[simp]
theorem frameVelocityCoordinates_im (s : Fin 2 → Π x : M, TangentSpace I x) (γ : ℝ → M)
    (t : ℝ) : (frameVelocityCoordinates s γ t).im = inner ℝ (s 1 (γ t)) (curveVelocity I γ t) :=
  (rfl)

/-- A pair orthonormal at `γ t` whose span contains the velocity recovers the velocity from its
complex coordinates: `γ' = Re z • s₀ + Im z • s₁`. For a local frame, the span condition follows
from `IsLocalFrameOn.generating`. -/
theorem curveVelocity_eq_frameVelocityCoordinates {s : Fin 2 → Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t : ℝ} (ho : Orthonormal ℝ (fun i ↦ s i (γ t)))
    (hsp : curveVelocity I γ t ∈ Submodule.span ℝ (range fun i ↦ s i (γ t))) :
    curveVelocity I γ t = (frameVelocityCoordinates s γ t).re • s 0 (γ t) +
      (frameVelocityCoordinates s γ t).im • s 1 (γ t) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hsp
  have hc' (i : Fin 2) : inner ℝ (s i (γ t)) (curveVelocity I γ t) = c i := by
    rw [← hc, ho.inner_right_fintype]
  rw [frameVelocityCoordinates_re, frameVelocityCoordinates_im, hc' 0, hc' 1, ← hc,
    Fin.sum_univ_two]

/-- Zero velocity has zero complex coordinates in any pair of tangent fields. -/
@[simp]
theorem frameVelocityCoordinates_eq_zero_of_curveVelocity_eq_zero
    {s : Fin 2 → Π x : M, TangentSpace I x} {γ : ℝ → M} {t : ℝ}
    (hv : curveVelocity I γ t = 0) : frameVelocityCoordinates s γ t = 0 := by
  apply Complex.ext <;> simp [frameVelocityCoordinates, hv]

/-- In a pair orthonormal at `γ t` whose span contains the velocity, the complex coordinates of
the velocity have the norm of the velocity. -/
theorem norm_frameVelocityCoordinates {s : Fin 2 → Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t : ℝ} (ho : Orthonormal ℝ (fun i ↦ s i (γ t)))
    (hsp : curveVelocity I γ t ∈ Submodule.span ℝ (range fun i ↦ s i (γ t))) :
    ‖frameVelocityCoordinates s γ t‖ = ‖curveVelocity I γ t‖ := by
  have h := congrArg (fun w ↦ inner ℝ w (curveVelocity I γ t))
    (curveVelocity_eq_frameVelocityCoordinates ho hsp)
  simp only [inner_add_left, real_inner_smul_left, ← frameVelocityCoordinates_re,
    ← frameVelocityCoordinates_im, real_inner_self_eq_norm_sq] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h]

/-- In a pair whose span at `γ t` contains the velocity, the complex coordinates of the velocity
vanish exactly where the velocity does. -/
@[simp]
theorem frameVelocityCoordinates_eq_zero_iff {s : Fin 2 → Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t : ℝ}
    (hsp : curveVelocity I γ t ∈ Submodule.span ℝ (range fun i ↦ s i (γ t))) :
    frameVelocityCoordinates s γ t = 0 ↔ curveVelocity I γ t = 0 := by
  refine ⟨fun h ↦ ?_, frameVelocityCoordinates_eq_zero_of_curveVelocity_eq_zero⟩
  have hker : Submodule.span ℝ (range fun i ↦ s i (γ t)) ≤
      (innerSL ℝ (curveVelocity I γ t)).toLinearMap.ker := by
    refine Submodule.span_le.mpr (range_subset_iff.mpr fun i ↦ ?_)
    rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    fin_cases i
    · simpa [real_inner_comm] using congrArg Complex.re h
    · simpa [real_inner_comm] using congrArg Complex.im h
  have hself := hker hsp
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hself
  exact inner_self_eq_zero.mp hself

/-- Along an `a`-periodic curve, the frame coordinates of the velocity are `a`-periodic. -/
theorem periodic_frameVelocityCoordinates (s : Fin 2 → Π x : M, TangentSpace I x) {γ : ℝ → M}
    {a : ℝ} (hp : Function.Periodic γ a) :
    Function.Periodic (frameVelocityCoordinates s γ) a := by
  intro t
  unfold frameVelocityCoordinates
  rw [hp.curveVelocity_add (I := I), hp t]

section Continuous

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

/-- For continuous tangent fields on a set and a continuous metric, the frame coordinates of
the velocity of a `C¹` curve in that set are continuous. -/
theorem continuous_frameVelocityCoordinates {s : Fin 2 → Π x : M, TangentSpace I x}
    {u : Set M} (hs : ∀ i, ContinuousOn (fun x ↦ TotalSpace.mk' E x (s i x)) u) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (hγu : ∀ t, γ t ∈ u) :
    Continuous (frameVelocityCoordinates s γ) := by
  have hv : Continuous (fun t ↦ TotalSpace.mk' E (γ t) (curveVelocity I γ t)) :=
    (ContMDiff.continuous_curveVelocityLift hγ).congr fun t ↦ curveVelocityLift_apply γ t
  have hframe (i : Fin 2) : Continuous (fun t ↦ TotalSpace.mk' E (γ t) (s i (γ t))) :=
    (hs i).comp_continuous hγ.continuous hγu
  have hi (i : Fin 2) : Continuous (fun t ↦ inner ℝ (s i (γ t)) (curveVelocity I γ t)) :=
    Continuous.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (v := fun t ↦ s i (γ t)) (w := fun t ↦ curveVelocity I γ t) (hframe i) hv
  have h : Continuous (fun t ↦
      (inner ℝ (s 0 (γ t)) (curveVelocity I γ t) : ℂ) +
        (inner ℝ (s 1 (γ t)) (curveVelocity I γ t) : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp (hi 0)).add
      ((Complex.continuous_ofReal.comp (hi 1)).mul continuous_const)
  convert h using 1
  funext t
  exact (Complex.re_add_im (frameVelocityCoordinates s γ t)).symm

end Continuous

variable {k : ℕ∞ω} [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I k E (TangentSpace I : M → Type _)]

/-- For `C^k` tangent fields on a set and a `C^k` metric, the frame coordinates of the
velocity of a `C^(k+1)` curve in that set are `C^k`. -/
theorem contDiff_frameVelocityCoordinates {s : Fin 2 → Π x : M, TangentSpace I x}
    {u : Set M} (hs : ∀ i, ContMDiffOn I I.tangent k (fun x ↦ TotalSpace.mk' E x (s i x)) u)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I (k + 1) γ) (hγu : ∀ t, γ t ∈ u) :
    ContDiff ℝ k (frameVelocityCoordinates s γ) := by
  have hw := ContMDiffOn.contMDiffOn_curveVelocityLiftWithin hγ.contMDiffOn
    (m := k) le_rfl uniqueMDiffOn_univ
  rw [curveVelocityLiftWithin_univ] at hw
  have hv : ContMDiff 𝓘(ℝ) I.tangent k
      (fun t ↦ TotalSpace.mk' E (γ t) (curveVelocity I γ t)) :=
    (contMDiffOn_univ.mp hw).congr fun t ↦ (curveVelocityLift_apply γ t).symm
  have hframe (i : Fin 2) : ContMDiff 𝓘(ℝ) I.tangent k
      (fun t ↦ TotalSpace.mk' E (γ t) (s i (γ t))) :=
    (hs i).comp_contMDiff (hγ.of_le le_self_add) hγu
  have hi (i : Fin 2) : ContDiff ℝ k (fun t ↦ inner ℝ (s i (γ t)) (curveVelocity I γ t)) := by
    have hh := @ContMDiff.inner_bundle E _ _ H _ I k M _ _ E _ _
      (fun x : M ↦ TangentSpace I x) _
      (fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x)))
      (fun x ↦ inferInstanceAs (InnerProductSpace ℝ (TangentSpace I x))) _ _
      ℝ _ _ ℝ _ 𝓘(ℝ) ℝ _ _
      (inferInstance : IsContMDiffRiemannianBundle I k E (TangentSpace I))
      γ (fun t ↦ s i (γ t)) (fun t ↦ curveVelocity I γ t) (hframe i) hv
    exact contMDiff_iff_contDiff.mp hh
  have h : ContDiff ℝ k (fun t ↦
      (inner ℝ (s 0 (γ t)) (curveVelocity I γ t) : ℂ) +
        (inner ℝ (s 1 (γ t)) (curveVelocity I γ t) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp (hi 0)).add
      ((Complex.ofRealCLM.contDiff.comp (hi 1)).mul contDiff_const)
  convert h using 1
  funext t
  exact (Complex.re_add_im (frameVelocityCoordinates s γ t)).symm

end TauCeti.Manifold
