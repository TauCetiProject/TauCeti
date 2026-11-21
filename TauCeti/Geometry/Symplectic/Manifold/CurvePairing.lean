/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

import TauCeti.Geometry.Manifold.DeRham.Map
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.TwoForm.Closed
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Orientation

/-!
# Pairings of two-forms with pseudoholomorphic curves

Let `u : (C, j) → (X, J)` be a smooth pseudoholomorphic map from a surface, oriented so that the
frames `(e, j e)` are positive, and let `θ` and `σ` be two-forms on `X`. Pulled back along `u`, a
two-form is determined on each tangent plane of `C` by its value on one frame `(e, j e)`, and by
the Cauchy–Riemann equation `du (j e) = J (du e)` that value is `θ(du e, J (du e))`. Hence:

* if `θ(v, J v) ≥ 0` for every tangent vector `v` along `u`, then `u^* θ` is a nonnegative top
  form and `∫_C u^* θ ≥ 0` (`TauCeti.integralTopForm_mpullback_nonneg`, from the pointwise
  `TauCeti.SmoothAlmostComplexStructure.apply_basis_nonneg_of_forall_nonneg`);
* if `|θ(v, J v)| ≤ K σ(v, J v)` along `u`, then for compact `C`,
  `|∫_C u^* θ| ≤ K ∫_C u^* σ` (`TauCeti.abs_integralTopForm_mpullback_le`).

When `σ` is a symplectic form compatible with `J` and `g = σ(·, J ·)` is the associated metric,
the vectors `v` and `J v` are `g`-orthogonal of equal length, so `σ(v, J v) = |v|²` while
`|θ(v, J v)| ≤ ‖θ_x‖ |v| |J v| = ‖θ_x‖ |v|²` for the comass `‖θ_x‖` of `θ` at `x`
(`ContinuousAlternatingMap.le_opNorm`, with the operator norm identified with the comass by
`ContinuousAlternatingMap.opNorm_le_iff_le_mul_norm_ιMulti`). On a compact `X` the second hypothesis
therefore holds with `K` the maximal comass of `θ`: the integral `∫_C u^* θ` over a closed
pseudoholomorphic curve is bounded by the comass of `θ` times the symplectic area `∫_C u^* σ`.

The intended application bounds, for a basis of closed two-forms, every real pairing of the
homology class of a curve of bounded area, and then uses
`TauCeti.IsComassBounded.finite_setOf_area_le`, with injectivity from
`TauCeti.liftBaseChange_pi_injective_of_span_eq_top`, to leave only finitely many possible
classes. That step depends on identifying `∫_C u^* θ` with
the pairing of `[θ]` with the class of the curve, a de Rham comparison not provided here.

If `θ` tames `J` strictly along `u`, that is `θ(v, J v) > 0` for every nonzero tangent vector `v`
at a point of the image, the pairing also detects whether `u` is constant: the integrand
`θ(du e, J du e)` is positive wherever `du` is nonzero, so `∫_C u^* θ = 0` forces `du = 0`
(`TauCeti.mfderiv_eq_zero_of_integralTopForm_mpullback_eq_zero`). When `C` is closed and connected
and `u^* θ` is exact, Stokes' theorem gives `∫_C u^* θ = 0`, so `u` is constant
(`TauCeti.apply_eq_of_mpullback_mem_exactForms`). This applies when `θ` itself is exact
(`TauCeti.apply_eq_of_mem_exactForms`), and so, by the Poincaré lemma, to every closed taming form
on a real normed space (`TauCeti.apply_eq_of_mem_closedForms_normedSpace`). In particular a closed
connected curve that is pseudoholomorphic for a constant linear complex structure `J₀` on a normed
space, tamed by an alternating bilinear form, is constant
(`TauCeti.apply_eq_of_isPseudoholomorphicAt_const`). This is motivated by curves contained in one
normal fibre of an embedded pseudoholomorphic curve: the normal linearization
`TauCeti.normalLinearization` acts on vertical vectors `(0, n)` by the constant block
`J_NN(z, 0)`, a linear complex structure when `J(z, 0)` preserves `E × {0}`. Applying the constant
case to such a vertical curve needs that reduction, which is not formalized here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347, §1.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893, §2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (energy of closed curves for exact forms).
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C]
  {J : SmoothAlmostComplexStructure I X} {j : SmoothAlmostComplexStructure I' C}
  {o : Manifold.Orientation I' C (Fin 2)} {u : C → X}

/-- **Nonnegativity of the pairing with a pseudoholomorphic curve.** Let `u` be a smooth
pseudoholomorphic map from a surface `C`, oriented so that the frames `(e, j e)` are positive. If
`θ(v, J v) ≥ 0` for every tangent vector `v` along `u`, then `∫_C u^* θ ≥ 0`. -/
theorem integralTopForm_mpullback_nonneg (hu : ContMDiff I' I ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {θ : SmoothTwoForm I X}
    (hθ : ∀ c (v : TangentSpace I (u c)), 0 ≤ SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)) :
    0 ≤ integralTopForm o (SmoothForm.mpullback u hu θ).val :=
  integralTopForm_nonneg o fun c b hb ↦
    j.apply_basis_nonneg_of_forall_nonneg (ho c) (fun e ↦ by
      rw [← SmoothBundleForm.eval₂_apply, SmoothForm.eval₂_mpullback,
        (hhol c).mfderiv_apply_commute]
      exact hθ c _) b hb

/-- **Pairings with a pseudoholomorphic curve are bounded by area.** Let `u` be a smooth
pseudoholomorphic map from a compact surface `C`, oriented so that the frames `(e, j e)` are
positive. If `|θ(v, J v)| ≤ K σ(v, J v)` for every tangent vector `v` along `u`, then
`|∫_C u^* θ| ≤ K ∫_C u^* σ`. For a symplectic form `σ` compatible with `J`, the hypothesis holds
with `K` any bound for the comass of `θ` in the metric `σ(·, J ·)`. -/
theorem abs_integralTopForm_mpullback_le [CompactSpace C] (hu : ContMDiff I' I ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {θ σ : SmoothTwoForm I X} {K : ℝ}
    (hK : ∀ c (v : TangentSpace I (u c)),
      |SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)| ≤
        K * SmoothBundleForm.eval₂ σ (u c) v (J (u c) v)) :
    |integralTopForm o (SmoothForm.mpullback u hu θ).val| ≤
      K * integralTopForm o (SmoothForm.mpullback u hu σ).val := by
  -- `K • σ + s • θ` is nonnegative on the complex lines along `u` whenever `|s| ≤ 1`.
  have key (s : ℝ) (hs : |s| ≤ 1) :
      0 ≤ K * integralTopForm o (SmoothForm.mpullback u hu σ).val +
        s * integralTopForm o (SmoothForm.mpullback u hu θ).val := by
    have hpt (c : C) (v : TangentSpace I (u c)) :
        0 ≤ SmoothBundleForm.eval₂ (K • σ + s • θ) (u c) v (J (u c) v) := by
      have hs' : |s * SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)| ≤
          |SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) hs
      rw [SmoothBundleForm.eval₂_add, SmoothForm.eval₂_smul, SmoothForm.eval₂_smul, smul_eq_mul,
        smul_eq_mul]
      linarith [neg_abs_le (s * SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)), hK c v]
    have hσ : IsSmoothForm I' 0 (SmoothForm.mpullback u hu σ).val :=
      (SmoothForm.isSmoothForm _).of_le (by simp)
    have hθ : IsSmoothForm I' 0 (SmoothForm.mpullback u hu θ).val :=
      (SmoothForm.isSmoothForm _).of_le (by simp)
    simpa only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul,
      integralTopForm_add_of_compactSpace o (hσ.smul K) (hθ.smul s), integralTopForm_smul]
      using integralTopForm_mpullback_nonneg hu ho hhol hpt
  have h₁ := key 1 (by simp)
  have h₂ := key (-1) (by simp)
  rw [abs_le]
  constructor <;> linarith

/-! ### Closed curves with exact pairing are constant -/

/-- **A taming form with vanishing pairing kills the differential.** Let `u` be a smooth
pseudoholomorphic map from a compact surface `C`, oriented so that the frames `(e, j e)` are
positive, and let `θ` tame `J` along `u`: `θ(v, J v) > 0` for every nonzero tangent vector `v` at a
point of the image. If `∫_C u^* θ = 0`, then the differential of `u` vanishes everywhere. -/
theorem mfderiv_eq_zero_of_integralTopForm_mpullback_eq_zero [CompactSpace C]
    (hu : ContMDiff I' I ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {θ : SmoothTwoForm I X}
    (hθ : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ θ (u c) v (J (u c) v))
    (h : integralTopForm o (SmoothForm.mpullback u hu θ).val = 0) (c : C) :
    mfderiv I' I u c = 0 := by
  -- On a frame `(e, j e)` the pullback is `θ(du e, J du e)`.
  have hframe (c' : C) (e : TangentSpace I' c') :
      (SmoothForm.mpullback u hu θ).val c' ![e, j c' e] =
        SmoothBundleForm.eval₂ θ (u c') (mfderiv I' I u c' e)
          (J (u c') (mfderiv I' I u c' e)) := by
    rw [← SmoothBundleForm.eval₂_apply, SmoothForm.eval₂_mpullback,
      (hhol c').mfderiv_apply_commute]
  have hnn (c' : C) (e : TangentSpace I' c') :
      0 ≤ (SmoothForm.mpullback u hu θ).val c' ![e, j c' e] := by
    rw [hframe]
    rcases eq_or_ne (mfderiv I' I u c' e) 0 with he | he
    · rw [he, SmoothBundleForm.eval₂_zero_left]
    · exact (hθ c' _ he).le
  refine ContinuousLinearMap.ext (σ₁₂ := RingHom.id ℝ) fun e ↦ ?_
  by_contra he
  have hpos : 0 < (SmoothForm.mpullback u hu θ).val c ![e, j c e] := by
    rw [hframe]
    exact hθ c _ he
  refine (j.integralTopForm_pos_of_forall_nonneg ho
    ((SmoothForm.isSmoothForm _).of_le (by simp))
    (isClosed_tsupport _).isCompact hnn hpos).ne' h

variable [BoundarylessManifold I' C] [T2Space C] [CompactSpace C] [PreconnectedSpace C]

/-- **Closed pseudoholomorphic curves with exact pairing are constant.** Let `u` be a smooth
pseudoholomorphic map from a closed connected surface `C`, oriented so that the frames `(e, j e)`
are positive, and let `θ` tame `J` along `u`. If the pullback `u^* θ` is exact, then `u` is
constant: by Stokes' theorem `∫_C u^* θ = 0`, while the integrand is positive wherever the
differential of `u` is nonzero. -/
theorem apply_eq_of_mpullback_mem_exactForms (hu : ContMDiff I' I ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {θ : SmoothTwoForm I X}
    (hθ : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ θ (u c) v (J (u c) v))
    (hex : SmoothForm.mpullback u hu θ ∈ exactForms I' C 2) (c c' : C) : u c = u c' := by
  obtain ⟨α, hα⟩ := (exactForms_succ I' (M := C) 1).le hex
  have hint : integralTopForm o (SmoothForm.mpullback u hu θ).val = 0 := by
    rw [← hα, mextDerivₗ_apply]
    exact integralTopForm_mextDeriv_eq_zero o ((SmoothForm.isSmoothForm α).of_le (by simp))
      (isClosed_tsupport _).isCompact
  exact hu.mdifferentiable (by simp) |>.apply_eq_of_mfderiv_eq_zero
    (mfderiv_eq_zero_of_integralTopForm_mpullback_eq_zero hu ho hhol hθ hint) c c'

/-- **Pseudoholomorphic curves are constant for exact taming forms.** A smooth pseudoholomorphic
map from a closed connected surface into an almost complex manifold tamed along the map by an
exact two-form is constant. -/
theorem apply_eq_of_mem_exactForms (hu : ContMDiff I' I ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {θ : SmoothTwoForm I X}
    (hθ : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ θ (u c) v (J (u c) v))
    (hex : θ ∈ exactForms I X 2) (c c' : C) : u c = u c' := by
  refine apply_eq_of_mpullback_mem_exactForms hu ho hhol hθ ?_ c c'
  simpa using closedForms.mpullback_mem_exactForms u hu 2 ⟨θ, exactForms_le_closedForms I 2 hex⟩ hex

/-- **Closed pseudoholomorphic curves in a normed space are constant.** On a real normed space `V`
with an almost complex structure tamed along the map by a closed two-form, every smooth
pseudoholomorphic map from a closed connected surface is constant. By the Poincaré lemma the
taming form is exact. -/
theorem apply_eq_of_mem_closedForms_normedSpace {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {u : C → V}
    (hu : ContMDiff I' 𝓘(ℝ, V) ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {θ : SmoothTwoForm 𝓘(ℝ, V) V}
    (hθ : ∀ c (v : TangentSpace 𝓘(ℝ, V) (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ θ (u c) v (J (u c) v))
    (hcl : θ ∈ closedForms 𝓘(ℝ, V) V 2) (c c' : C) : u c = u c' :=
  apply_eq_of_mem_exactForms hu ho hhol hθ
    ((exactForms_succ_eq_closedForms_normedSpace V 1).ge hcl) c c'

/-- **Closed pseudoholomorphic curves for a tamed constant complex structure are constant.** Let
`Jc` be a linear complex structure on a real normed space `V`, tamed by an alternating bilinear
form `B`: `B v (Jc v) > 0` for `v ≠ 0`. Every smooth map from a closed connected surface that is
pseudoholomorphic for the constant structure `Jc` is constant.

This is motivated by vertical curves along an embedded pseudoholomorphic curve: the normal
linearization `TauCeti.normalLinearization` acts on vertical vectors `(0, n)` by the constant block
`J_NN(z, 0)`, which is a linear complex structure when `J(z, 0)` preserves `E × {0}`. Applying
this theorem to a curve in one normal fibre needs that reduction, which is not formalized here. -/
theorem apply_eq_of_isPseudoholomorphicAt_const {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {Jc : V →L[ℝ] V} (hJc : ∀ v, Jc (Jc v) = -v) {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hB : ∀ v, B v v = 0) (hBJ : ∀ v, v ≠ 0 → 0 < B v (Jc v)) {u : C → V}
    (hu : ContMDiff I' 𝓘(ℝ, V) ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.const Jc hJc) u c)
    (c c' : C) : u c = u c' := by
  refine apply_eq_of_mem_closedForms_normedSpace hu ho hhol (θ := SmoothTwoForm.const B)
    (fun c v hv ↦ ?_) ?_ c c'
  · rw [SmoothTwoForm.const_apply B hB]
    simp only [SmoothAlmostComplexStructure.const_toEndomorphism_apply]
    -- `NormedSpace.fromTangentSpace` is Mathlib's identification of `TangentSpace 𝓘(ℝ, V) x`
    -- with `V`, which is the identity map.
    exact hBJ v hv
  · exact (mem_closedForms _ _).mpr
      ((SmoothForm.isClosed_def _).mp (SmoothTwoForm.isClosed_const B))

end TauCeti
