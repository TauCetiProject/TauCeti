/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.LeviForm
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.Complex.Pseudoconvex.Strong
import TauCeti.Topology.Algebra.Order.Field

/-!
# Smooth positive multipliers for strictly plurisubharmonic functions

If `p` is strictly plurisubharmonic and vanishes to first order on a closed set `S`,
`TauCeti.exists_pos_contMDiff_add_mul_isManifoldStrictlyPlurisubharmonicAt` makes `r + μ * p`
strictly plurisubharmonic on a neighbourhood of `S` for any real `C²` function `r`.
The multiplier `μ` is positive and smooth. This is the multiplier step in Grauert's
construction of strictly plurisubharmonic tubes.

The Levi product rule gives `manifoldLeviForm_mul_of_eq_zero_of_mvfderiv_eq_zero` at a
first-order zero. The open second-jet test gives
`isOpen_setOf_isManifoldStrictlyPlurisubharmonicAt` for real `C²` functions.
The pointwise bound `IsManifoldStrictlyPlurisubharmonicAt.eventually_atTop_add_smul`
gives locally admissible constants for Mathlib's smooth selection theorem
`exists_contMDiffMap_forall_mem_convex_of_local_const`.

## References

* H. Grauert, *On Levi's problem and the imbedding of real-analytic manifolds*,
  Annals of Mathematics 68 (1958), §3, Propositions 6–7.
-/

public section

open Complex Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] {p r : M → ℝ} {x : M}

/-- At a point where `p` is strictly plurisubharmonic, adding a sufficiently large constant
multiple of `p` to a `C²` function makes the sum strictly plurisubharmonic. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.eventually_atTop_add_smul
    [FiniteDimensional ℂ E] (h : IsManifoldStrictlyPlurisubharmonicAt E p x)
    (hp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 p x) (hr : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 r x) :
    ∀ᶠ c : ℝ in atTop, IsManifoldStrictlyPlurisubharmonicAt E (r + c • p) x := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  rw [isManifoldStrictlyPlurisubharmonicAt_iff] at h
  have hcont (f : M → ℝ) : Continuous fun v : E ↦ (manifoldLeviForm E f x v v).re := by
    simp only [re_manifoldLeviForm_apply]
    let B : E →L[ℝ] E →L[ℝ] ℝ := criticalHessian 𝓘(ℝ, E) f x
    have hB : Continuous fun v : E ↦ B v v := (B.continuous.clm_apply continuous_id)
    exact (hB.add (hB.comp (continuous_const_smul I))).div_const 4
  have hunit (v : E) (hv : v ∈ Metric.sphere (0 : E) 1) :
      0 < (manifoldLeviForm E p x v v).re :=
    h v (ne_zero_of_mem_sphere one_ne_zero ⟨v, hv⟩)
  have hlarge := (isCompact_sphere (0 : E) 1).eventually_forall_mul_add_pos
    (hcont p).continuousOn (hcont r).continuousOn
    (fun v hv ↦ (hunit v hv).le) (fun v hv hz ↦ ((hunit v hv).ne' hz).elim)
  filter_upwards [hlarge] with c hc
  rw [isManifoldStrictlyPlurisubharmonicAt_iff]
  intro v hv
  let u : E := (‖v‖⁻¹ : ℂ) • v
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  -- Normalize the tangent vector so that the compact-sphere estimate applies.
  have hu : u ∈ Metric.sphere (0 : E) 1 := by
    have hnorm : ‖(‖v‖ : ℂ)‖ = ‖v‖ :=
      (Complex.norm_real _).trans (Real.norm_of_nonneg (norm_nonneg _))
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, hnorm, inv_mul_cancel₀ hvnorm]
  have hvu : (‖v‖ : ℂ) • u = v := by
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hvnorm), one_smul]
  rw [← hvu, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]
  simp only [Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul]
  have hdiag := hc u hu
  have hcp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 (c • p) x :=
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) c).contMDiffAt.comp x hp
  rw [manifoldLeviForm_add hr hcp, manifoldLeviForm_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Complex.add_re, smul_eq_mul,
    Complex.re_ofReal_mul]
  exact mul_pos (norm_pos_iff.mpr hv) (mul_pos (norm_pos_iff.mpr hv)
    (by simpa only [add_comm] using hdiag))

variable [FiniteDimensional ℂ E]

/-- Let `p` and `r` be real `C²` functions on a finite-dimensional complex manifold. If `p`
vanishes with its differential and is strictly plurisubharmonic on a closed subset `S`,
then `r + μ * p` is strictly plurisubharmonic on an open neighbourhood of `S` for some
everywhere positive smooth function `μ`. -/
theorem exists_pos_contMDiff_add_mul_isManifoldStrictlyPlurisubharmonicAt
    [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M] [SigmaCompactSpace M]
    {S : Set M} (hS : IsClosed S)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 p) (hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 r)
    (h₀ : ∀ x ∈ S, p x = 0) (h₁ : ∀ x ∈ S, mvfderiv 𝓘(ℝ, E) p x = 0)
    (hpos : ∀ x ∈ S, IsManifoldStrictlyPlurisubharmonicAt E p x) :
    ∃ μ : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ μ ∧ (∀ x, 0 < μ x) ∧
      ∃ U : Set M, IsOpen U ∧ S ⊆ U ∧
        ∀ x ∈ U, IsManifoldStrictlyPlurisubharmonicAt E (r + μ * p) x := by
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars ℝ
    (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  let A (x : M) : Set ℝ := {c | 0 < c ∧
    (x ∈ S → IsManifoldStrictlyPlurisubharmonicAt E (r + c • p) x)}
  have hsmul (c : ℝ) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 (c • p) :=
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) c).comp hp
  -- Larger coefficients preserve positivity on `S`, so the admissible sets are convex.
  have hupper (x : M) : IsUpperSet (A x) := by
    intro c d hcd hc
    refine ⟨hc.1.trans_le hcd, fun hx ↦ ?_⟩
    have hcv := isManifoldStrictlyPlurisubharmonicAt_iff.1 (hc.2 hx)
    refine isManifoldStrictlyPlurisubharmonicAt_iff.2 fun v hv ↦ (hcv v hv).trans_le ?_
    simp only [manifoldLeviForm_add hr.contMDiffAt (hsmul _).contMDiffAt, manifoldLeviForm_smul,
      LinearMap.add_apply, LinearMap.smul_apply, Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
    gcongr
    exact (isManifoldStrictlyPlurisubharmonicAt_iff.1 (hpos x hx) v hv).le
  have hlocal (x : M) : ∃ c, ∀ᶠ y in 𝓝 x, c ∈ A y := by
    by_cases hx : x ∈ S
    · obtain ⟨c, hcx, hc⟩ :=
        ((hpos x hx).eventually_atTop_add_smul hp.contMDiffAt hr.contMDiffAt |>.and
          (eventually_gt_atTop (0 : ℝ))).exists
      refine ⟨c, ?_⟩
      have hU := isOpen_setOf_isManifoldStrictlyPlurisubharmonicAt (hr.add (hsmul c))
      have he : ∀ᶠ y in 𝓝 x, IsManifoldStrictlyPlurisubharmonicAt E (r + c • p) y :=
        hU.mem_nhds hcx
      exact he.mono fun _ hy ↦ ⟨hc, fun _ ↦ hy⟩
    · have he : ∀ᶠ y in 𝓝 x, y ∉ S := hS.isOpen_compl.mem_nhds hx
      exact ⟨1, he.mono fun _ hy ↦ ⟨one_pos, fun hyS ↦ (hy hyS).elim⟩⟩
  obtain ⟨μ, hμ⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
    (n := ⊤) 𝓘(ℝ, E) (fun x ↦ (hupper x).ordConnected.convex) hlocal
  have hμ₂ := μ.contMDiff.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hU := isOpen_setOf_isManifoldStrictlyPlurisubharmonicAt (hr.add (hμ₂.mul hp))
  refine ⟨μ, μ.contMDiff, fun x ↦ (hμ x).1, _, hU, fun x hx ↦ ?_, fun _ hx ↦ hx⟩
  have hmul := manifoldLeviForm_mul_of_eq_zero_of_mvfderiv_eq_zero
    hμ₂.contMDiffAt hp.contMDiffAt (h₀ x hx) (h₁ x hx)
  -- At a first-order zero the Levi form only sees the value of the multiplier.
  have hLevi : manifoldLeviForm E (r + (μ : M → ℝ) * p) x = manifoldLeviForm E (r + μ x • p) x := by
    rw [manifoldLeviForm_add hr.contMDiffAt (hμ₂.mul hp).contMDiffAt, hmul]
    rw [manifoldLeviForm_add hr.contMDiffAt (hsmul (μ x)).contMDiffAt, manifoldLeviForm_smul]
  have hpos' := isManifoldStrictlyPlurisubharmonicAt_iff.1 ((hμ x).2 hx)
  exact isManifoldStrictlyPlurisubharmonicAt_iff.2 (hLevi.symm ▸ hpos')

end TauCeti
