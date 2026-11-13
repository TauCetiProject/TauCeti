/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame.Orthonormal
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Path

/-!
# Velocities of curves in an orthonormal frame of a surface

For a pair of tangent fields `s = (s₀, s₁)` and a curve `γ` in a Riemannian manifold, the complex
number `⟪s₀, γ'⟫ + i ⟪s₁, γ'⟫` is the coordinate of the velocity `γ'(t)` in the frame
(`TauCeti.Manifold.frameVelocityCoordinates`). When `s` is a local frame of a surface, orthonormal
at `γ t`, it determines the velocity, `γ' = Re z • s₀ + Im z • s₁`, and has the same norm, so it
vanishes only where the velocity does. It is periodic along a periodic curve, continuous along a
`C¹` curve for a continuous metric, and `C¹` along a `C²` curve for a `C¹` frame and metric.

For a regular periodic `C¹` curve inside the domain of a frame orthonormal along it, the unit
coordinates `z / ‖z‖` form a loop in the unit circle `Circle`, the unit tangent read in the frame
(`TauCeti.Manifold.exists_path_eq_frameVelocityCoordinates_div_norm`). If `θ` is a continuous
angle of this loop, the unit tangent is `T = cos θ s₀ + sin θ s₁`.

## Main results

* `TauCeti.Manifold.curveVelocity_eq_frameVelocityCoordinates`: reconstruction of the velocity.
* `TauCeti.Manifold.norm_frameVelocityCoordinates`: the coordinates have the norm of the velocity.
* `TauCeti.Manifold.periodic_frameVelocityCoordinates`: periodicity along periodic curves.
* `TauCeti.Manifold.continuous_frameVelocityCoordinates`: continuity along `C¹` curves.
* `TauCeti.Manifold.contDiff_frameVelocityCoordinates`: `C¹` regularity along `C²` curves.
* `TauCeti.Manifold.exists_path_eq_frameVelocityCoordinates_div_norm`: the unit tangent loop in
  the frame.

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

/-- The complex coordinates `⟪s₀, γ'⟫ + i ⟪s₁, γ'⟫` of the velocity of a curve `γ` at `t` in a
pair of tangent fields `s = (s₀, s₁)`, evaluated at `γ t`. -/
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

section Frame

variable [IsManifold I 1 M] {n : ℕ∞ω} {s : Fin 2 → Π x : M, TangentSpace I x} {u : Set M}
  {γ : ℝ → M} {t : ℝ}

/-- An orthonormal frame at `γ t` recovers the velocity from its complex coordinates:
`γ' = Re z • s₀ + Im z • s₁`. -/
theorem curveVelocity_eq_frameVelocityCoordinates (hs : IsLocalFrameOn I E n s u)
    (ht : γ t ∈ u) (ho : Orthonormal ℝ (fun i ↦ s i (γ t))) :
    curveVelocity I γ t = (frameVelocityCoordinates s γ t).re • s 0 (γ t) +
      (frameVelocityCoordinates s γ t).im • s 1 (γ t) := by
  simpa only [Fin.sum_univ_two, frameVelocityCoordinates_re, frameVelocityCoordinates_im] using
    (hs.sum_inner_smul_eq ht ho (curveVelocity I γ t)).symm

/-- In a frame orthonormal at `γ t`, the complex coordinates of the velocity have the norm of the
velocity. -/
theorem norm_frameVelocityCoordinates (hs : IsLocalFrameOn I E n s u) (ht : γ t ∈ u)
    (ho : Orthonormal ℝ (fun i ↦ s i (γ t))) :
    ‖frameVelocityCoordinates s γ t‖ = ‖curveVelocity I γ t‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simpa only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs,
    frameVelocityCoordinates_re, frameVelocityCoordinates_im, ← pow_two] using
    hs.sum_sq_norm_inner ht ho (curveVelocity I γ t)

/-- In a frame orthonormal at `γ t`, the complex coordinates of a nonzero velocity are nonzero. -/
theorem frameVelocityCoordinates_ne_zero (hs : IsLocalFrameOn I E n s u) (ht : γ t ∈ u)
    (ho : Orthonormal ℝ (fun i ↦ s i (γ t))) (hv : curveVelocity I γ t ≠ 0) :
    frameVelocityCoordinates s γ t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_frameVelocityCoordinates hs ht ho]
  exact norm_ne_zero_iff.mpr hv

end Frame

/-- Along a differentiable `a`-periodic curve, the frame coordinates of the velocity are
`a`-periodic. -/
theorem periodic_frameVelocityCoordinates (s : Fin 2 → Π x : M, TangentSpace I x) {γ : ℝ → M}
    {a : ℝ} (hp : Function.Periodic γ a) (hγ : MDifferentiable 𝓘(ℝ) I γ) :
    Function.Periodic (frameVelocityCoordinates s γ) a := by
  intro t
  have hv := hp.curveVelocity_add (hγ (t + a))
  unfold frameVelocityCoordinates
  rw [hv, hp t]

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

/-- **The unit tangent loop in an orthonormal frame.** For a regular `1`-periodic `C¹` curve `γ`
in the domain `u` of a local frame orthonormal along `γ`, the normalized frame coordinates
`z / ‖z‖` of the velocity form a loop in the unit circle. -/
theorem exists_path_eq_frameVelocityCoordinates_div_norm {n : ℕ∞ω}
    {s : Fin 2 → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E n s u)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (hγu : ∀ t, γ t ∈ u)
    (ho : ∀ t, Orthonormal ℝ (fun i ↦ s i (γ t))) (hp : Function.Periodic γ 1)
    (hne : ∀ t, curveVelocity I γ t ≠ 0) :
    ∃ v : Circle, ∃ p : Path v v, ∀ t : unitInterval,
      (p t : ℂ) = frameVelocityCoordinates s γ t / (‖frameVelocityCoordinates s γ t‖ : ℂ) := by
  let z := frameVelocityCoordinates s γ
  have hz : Continuous z :=
    continuous_frameVelocityCoordinates (fun i ↦ (hs.contMDiffOn i).continuousOn) hγ hγu
  have hz0 (t : ℝ) : z t ≠ 0 :=
    frameVelocityCoordinates_ne_zero hs (hγu t) (ho t) (hne t)
  let U (t : ℝ) : Circle := ⟨z t / (‖z t‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr (hz0 t))⟩
  have hU : Continuous U :=
    (hz.div (Complex.continuous_ofReal.comp hz.norm) fun t ↦
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz0 t))).subtype_mk _
  have hclosed : U 1 = U 0 := by
    have hper : z 1 = z 0 := by
      simpa only [zero_add] using
        periodic_frameVelocityCoordinates s hp (hγ.mdifferentiable one_ne_zero) 0
    exact Circle.ext (by simp only [U, hper])
  exact ⟨U 0, ⟨⟨fun t ↦ U t, hU.comp continuous_subtype_val⟩, rfl, hclosed⟩, fun t ↦ rfl⟩

end Continuous

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- For `C¹` tangent fields on an open set and a `C¹` metric, the frame coordinates of the
velocity of a `C²` curve in that set are `C¹`. -/
theorem contDiff_frameVelocityCoordinates {s : Fin 2 → Π x : M, TangentSpace I x}
    {u : Set M} (hs : ∀ i, ContMDiffOn I I.tangent 1 (fun x ↦ TotalSpace.mk' E x (s i x)) u)
    (hu : IsOpen u) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ) I 2 γ) (hγu : ∀ t, γ t ∈ u) :
    ContDiff ℝ 1 (frameVelocityCoordinates s γ) := by
  have hw := ContMDiffOn.contMDiffOn_curveVelocityLiftWithin hγ.contMDiffOn
    (m := 1) (by norm_num) uniqueMDiffOn_univ
  rw [curveVelocityLiftWithin_univ] at hw
  have hv : ContMDiff 𝓘(ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (curveVelocity I γ t)) :=
    (contMDiffOn_univ.mp hw).congr fun t ↦ (curveVelocityLift_apply γ t).symm
  have hframe (i : Fin 2) : ContMDiff 𝓘(ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (s i (γ t))) := fun t ↦
    ((hs i).contMDiffAt (hu.mem_nhds (hγu t))).comp t ((hγ.of_le one_le_two) t)
  have hi (i : Fin 2) : ContDiff ℝ 1 (fun t ↦ inner ℝ (s i (γ t)) (curveVelocity I γ t)) := by
    have hh := @ContMDiff.inner_bundle E _ _ H _ I 1 M _ _ E _ _
      (fun x : M ↦ TangentSpace I x) _
      (fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x)))
      (fun x ↦ inferInstanceAs (InnerProductSpace ℝ (TangentSpace I x))) _ _
      ℝ _ _ ℝ _ 𝓘(ℝ) ℝ _ _
      (inferInstance : IsContMDiffRiemannianBundle I 1 E (TangentSpace I))
      γ (fun t ↦ s i (γ t)) (fun t ↦ curveVelocity I γ t) (hframe i) hv
    exact contMDiff_iff_contDiff.mp hh
  have h : ContDiff ℝ 1 (fun t ↦
      (inner ℝ (s 0 (γ t)) (curveVelocity I γ t) : ℂ) +
        (inner ℝ (s 1 (γ t)) (curveVelocity I γ t) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp (hi 0)).add
      ((Complex.ofRealCLM.contDiff.comp (hi 1)).mul contDiff_const)
  convert h using 1
  funext t
  exact (Complex.re_add_im (frameVelocityCoordinates s γ t)).symm

end TauCeti.Manifold
