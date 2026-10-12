/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Kernel
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Sobolev functions above the graph of a `C¹` function, and their trace

Let `φ : E → ℝ` be continuous. In the Euclidean product `ℝ × E`, the region above its graph is
the open set

`TauCeti.normalEpigraph φ = {x | φ x.snd < x.fst}`, the strict epigraph of `φ`,

whose boundary is the graph `{(φ y, y) | y ∈ E}`. These regions are the local models of domains
with `C¹` (or Lipschitz) boundary: near each boundary point such a domain is, after a rotation,
the region above the graph of a function. The half-space `TauCeti.normalHalfSpace 0` is the case
`φ = 0`.

The **shear** `TauCeti.normalShear φ : (t, y) ↦ (t + φ y, y)` is a measure-preserving homeomorphism
of `ℝ × E` carrying the half-space `{0 < t}` onto the region above the graph, and its inverse is
the shear by `-φ`. If `φ` is of class `C¹` with `‖fderiv ℝ φ‖ ≤ L`, the shear is `C¹` with
derivative of norm at most `1 + L`, so by `TauCeti.W1p.compMeasurePreservingL` precomposition
with the two shears is a pair of mutually inverse bounded operators between `W^{1,p}` of the
region and `W^{1,p}` of the half-space (`TauCeti.W1p.normalEpigraphEquivL`), and for `p < ∞`
both preserve zero boundary values.

Composing with the half-space trace `TauCeti.W1p.halfSpaceTrace` gives the trace on the graph,
`TauCeti.W1p.normalEpigraphTrace φ : H¹(normalEpigraph φ) →L[ℝ] L²(E)`, a bounded operator. The
graph is parametrized by `y ↦ (φ y, y)`, the image under the shear of the boundary point `(0, y)`
of the half-space, and the trace is measured by Lebesgue measure on `E` rather than by surface
measure on the graph. Its kernel is exactly `H¹₀` of the region
(`TauCeti.W1p.ker_normalEpigraphTrace`), the characterization of the homogeneous Dirichlet
condition by the trace.

## Main declarations

* `TauCeti.normalShear`, `TauCeti.measurePreserving_normalShear`,
  `TauCeti.norm_fderiv_normalShear_le`: the shear.
* `TauCeti.normalEpigraph`: the region above the graph.
* `TauCeti.W1p.normalEpigraphEquivL`: `W^{1,p}` of the region is isomorphic to `W^{1,p}` of the
  half-space, with `TauCeti.W1p.normalEpigraphEquivL_mem_w1p0Submodule_iff`.
* `TauCeti.W1p.normalEpigraphTrace`: the trace on the graph, with
  `TauCeti.W1p.norm_normalEpigraphTrace_le` and `TauCeti.W1p.ker_normalEpigraphTrace`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 1 (the trace theorem is
  proved by flattening the boundary locally).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.3
  (flattening `C¹` boundaries) and Lemma 9.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The shear -/

/-- The **shear** `(t, y) ↦ (t + φ y, y)` of the Euclidean product `ℝ × E` by a continuous
function `φ : E → ℝ`. It carries the half-space `{0 < t}` onto the region above the graph of
`φ`. -/
def normalShear (φ : C(E, ℝ)) : WithLp 2 (ℝ × E) ≃ₜ WithLp 2 (ℝ × E) where
  toFun x := WithLp.toLp 2 (x.fst + φ x.snd, x.snd)
  invFun x := WithLp.toLp 2 (x.fst - φ x.snd, x.snd)
  left_inv x := (WithLp.ext_iff 2).2 (by simp; rfl)
  right_inv x := (WithLp.ext_iff 2).2 (by simp; rfl)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [InnerProductSpace ℝ E] in
@[simp]
theorem normalShear_apply (φ : C(E, ℝ)) (x : WithLp 2 (ℝ × E)) :
    normalShear φ x = WithLp.toLp 2 (x.fst + φ x.snd, x.snd) :=
  (rfl)

omit [InnerProductSpace ℝ E] in
/-- The inverse of the shear by `φ` is the shear by `-φ`. -/
@[simp]
theorem normalShear_symm (φ : C(E, ℝ)) : (normalShear φ).symm = normalShear (-φ) := by
  ext x : 1
  exact (WithLp.ext_iff 2).2 (by simp [normalShear, sub_eq_add_neg])

/-- The embedding `t ↦ (t, 0)` of the normal line, of norm at most one. -/
private def normalLineL (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ℝ →L[ℝ] WithLp 2 (ℝ × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ ℝ E)

private theorem norm_normalLineL_le : ‖normalLineL E‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by simp [normalLineL]

private theorem normalShear_eq_add (φ : C(E, ℝ)) :
    ⇑(normalShear φ) = fun x => x + normalLineL E (φ (WithLp.sndL 2 ℝ ℝ E x)) := by
  funext x
  exact (WithLp.ext_iff 2).2 (Prod.ext (by simp [normalLineL]) (by simp [normalLineL]))

/-- If `φ` is differentiable, so is the shear, with derivative
`(s, z) ↦ (s + fderiv ℝ φ y z, z)` at `(t, y)`. -/
private theorem hasFDerivAt_normalShear {φ : C(E, ℝ)} {x : WithLp 2 (ℝ × E)}
    (hφ : DifferentiableAt ℝ φ x.snd) :
    HasFDerivAt (normalShear φ) (ContinuousLinearMap.id ℝ _ + (normalLineL E).comp
      ((fderiv ℝ φ x.snd).comp (WithLp.sndL 2 ℝ ℝ E))) x := by
  rw [normalShear_eq_add]
  exact (hasFDerivAt_id x).add ((normalLineL E).hasFDerivAt.comp x
    (hφ.hasFDerivAt.comp x (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt))

/-- The shear by a `C^n` function is `C^n`. -/
theorem contDiff_normalShear {φ : C(E, ℝ)} {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (normalShear φ) := by
  rw [normalShear_eq_add]
  exact contDiff_id.add ((normalLineL E).contDiff.comp (hφ.comp (WithLp.sndL 2 ℝ ℝ E).contDiff))

/-- The derivative of the shear by `φ` exceeds the identity by at most `‖fderiv ℝ φ‖`. -/
theorem norm_fderiv_normalShear_le {φ : C(E, ℝ)} {x : WithLp 2 (ℝ × E)}
    (hφ : DifferentiableAt ℝ φ x.snd) :
    ‖fderiv ℝ (normalShear φ) x‖ ≤ 1 + ‖fderiv ℝ φ x.snd‖ := by
  have hsnd : ‖WithLp.sndL 2 ℝ ℝ E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa using WithLp.norm_snd_le ℝ x
  rw [(hasFDerivAt_normalShear hφ).fderiv]
  have hcomp : ‖(normalLineL E).comp ((fderiv ℝ φ x.snd).comp (WithLp.sndL 2 ℝ ℝ E))‖ ≤
      ‖normalLineL E‖ * (‖fderiv ℝ φ x.snd‖ * ‖WithLp.sndL 2 ℝ ℝ E‖) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
  calc _ ≤ ‖ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E))‖ +
        ‖normalLineL E‖ * (‖fderiv ℝ φ x.snd‖ * ‖WithLp.sndL 2 ℝ ℝ E‖) :=
        (norm_add_le (E := WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) _ _).trans
          (add_le_add_right hcomp _)
    _ ≤ 1 + 1 * (‖fderiv ℝ φ x.snd‖ * 1) :=
        add_le_add ContinuousLinearMap.norm_id_le (mul_le_mul norm_normalLineL_le
          (mul_le_mul_of_nonneg_left hsnd (norm_nonneg _)) (by positivity) zero_le_one)
    _ = 1 + ‖fderiv ℝ φ x.snd‖ := by ring

/-! ### The region above a graph -/

omit [InnerProductSpace ℝ E] in
/-- The open region `{x | φ x.snd < x.fst}` above the graph of a continuous function
`φ : E → ℝ` in the Euclidean product `ℝ × E`. -/
def normalEpigraph (φ : C(E, ℝ)) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | φ x.snd < x.fst}, isOpen_lt (by fun_prop) (by fun_prop)⟩

omit [InnerProductSpace ℝ E] in
@[simp]
theorem mem_normalEpigraph (φ : C(E, ℝ)) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalEpigraph φ ↔ φ x.snd < x.fst :=
  Iff.rfl

omit [InnerProductSpace ℝ E] in
/-- The region above the graph of `0` is the half-space `{0 < t}`. -/
theorem normalEpigraph_zero : normalEpigraph (0 : C(E, ℝ)) = normalHalfSpace 0 := by
  ext x
  simp

omit [InnerProductSpace ℝ E] in
/-- The shear by `φ` carries the half-space `{0 < t}` onto the region above the graph of `φ`. -/
theorem preimage_normalShear_normalEpigraph (φ : C(E, ℝ)) :
    normalShear φ ⁻¹' normalEpigraph φ = normalHalfSpace (E := E) 0 := by
  ext x
  simp

/-- The derivative bound `‖fderiv ℝ (normalShear ψ)‖ ≤ 1 + L` for a `C¹` function `ψ` whose
derivative is bounded by `L`. -/
private theorem norm_fderiv_normalShear_le_of_forall {L : ℝ} {ψ : C(E, ℝ)} (hψ : ContDiff ℝ 1 ψ)
    (hL : ∀ y, ‖fderiv ℝ ψ y‖ ≤ L) (x : WithLp 2 (ℝ × E)) :
    ‖fderiv ℝ (normalShear ψ) x‖ ≤ 1 + L :=
  (norm_fderiv_normalShear_le (hψ.differentiable one_ne_zero _)).trans (by linarith [hL x.snd])

private theorem contDiff_neg_of_contDiff {φ : C(E, ℝ)} (hφ : ContDiff ℝ 1 φ) :
    ContDiff ℝ 1 (-φ : C(E, ℝ)) := by
  rw [ContinuousMap.coe_neg]
  exact hφ.neg

private theorem norm_fderiv_neg_le {φ : C(E, ℝ)} {L : ℝ} (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (y : E) :
    ‖fderiv ℝ (-φ : C(E, ℝ)) y‖ ≤ L := by
  simpa [fderiv_neg] using hL y

private theorem one_le_one_add {φ : C(E, ℝ)} {L : ℝ} (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    (1 : ℝ) ≤ 1 + L := by
  linarith [norm_nonneg (fderiv ℝ φ 0), hL 0]

omit [InnerProductSpace ℝ E] in
private theorem preimage_normalShear_neg_normalHalfSpace (φ : C(E, ℝ)) :
    normalShear (-φ) ⁻¹' normalHalfSpace (E := E) 0 = normalEpigraph φ := by
  ext x
  simp [sub_pos, ← sub_eq_add_neg]

omit [InnerProductSpace ℝ E] in
private theorem normalShear_normalShear_neg (φ : C(E, ℝ)) (x : WithLp 2 (ℝ × E)) :
    normalShear φ (normalShear (-φ) x) = x := by
  rw [← normalShear_symm, Homeomorph.apply_symm_apply]

omit [InnerProductSpace ℝ E] in
private theorem normalShear_neg_normalShear (φ : C(E, ℝ)) (x : WithLp 2 (ℝ × E)) :
    normalShear (-φ) (normalShear φ x) = x := by
  rw [← normalShear_symm, Homeomorph.symm_apply_apply]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The shear preserves Lebesgue measure: on each normal line it is a translation. -/
theorem measurePreserving_normalShear (φ : C(E, ℝ)) : MeasurePreserving (normalShear φ) := by
  -- On `E × ℝ`, the map `(y, t) ↦ (y, t + φ y)` is a skew product of translations.
  have hskew : MeasurePreserving (fun w : E × ℝ => (w.1, w.2 + φ w.1)) :=
    (MeasurePreserving.id volume).skew_product (g := fun y t => t + φ y) (by fun_prop)
      (Filter.Eventually.of_forall fun y => map_add_right_eq_self volume (φ y))
  have hswap : MeasurePreserving (Prod.swap : ℝ × E → E × ℝ) := Measure.measurePreserving_swap
  have hswap' : MeasurePreserving (Prod.swap : E × ℝ → ℝ × E) := Measure.measurePreserving_swap
  convert (WithLp.volume_preserving_toLp ℝ E).comp (hswap'.comp
    (hskew.comp (hswap.comp (WithLp.volume_preserving_ofLp ℝ E)))) using 1
  funext x
  rfl

/-! ### Flattening `W^{1,p}` of the region above a `C¹` graph -/

section Flatten

variable {φ : C(E, ℝ)} {L : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Precomposition with the shear by `φ`, from the region above the graph to the half-space. -/
private def flattenL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    W1p volume (normalEpigraph φ) p →L[ℝ] W1p volume (normalHalfSpace (E := E) 0) p :=
  W1p.compMeasurePreservingL (measurePreserving_normalShear φ)
    (preimage_normalShear_normalEpigraph φ).symm (contDiff_normalShear hφ).contDiffOn
    fun x _ => norm_fderiv_normalShear_le_of_forall hφ hL x

/-- Precomposition with the shear by `-φ`, from the half-space to the region above the graph. -/
private def unflattenL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    W1p volume (normalHalfSpace (E := E) 0) p →L[ℝ] W1p volume (normalEpigraph φ) p :=
  W1p.compMeasurePreservingL (measurePreserving_normalShear (-φ))
    (preimage_normalShear_neg_normalHalfSpace φ).symm
    (contDiff_normalShear (contDiff_neg_of_contDiff hφ)).contDiffOn
    fun x _ => norm_fderiv_normalShear_le_of_forall (contDiff_neg_of_contDiff hφ)
      (norm_fderiv_neg_le hL) x

private theorem norm_flattenL_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    ‖(flattenL hφ hL : W1p volume (normalEpigraph φ) p →L[ℝ] _)‖ ≤ 1 + L :=
  (W1p.norm_compMeasurePreservingL_le _ _ _ _).trans_eq (max_eq_right (one_le_one_add hL))

private theorem norm_unflattenL_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    ‖(unflattenL hφ hL : W1p volume (normalHalfSpace (E := E) 0) p →L[ℝ] _)‖ ≤ 1 + L :=
  (W1p.norm_compMeasurePreservingL_le _ _ _ _).trans_eq (max_eq_right (one_le_one_add hL))

private theorem unflattenL_flattenL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    Function.LeftInverse (unflattenL (p := p) hφ hL) (flattenL hφ hL) := fun u =>
  W1p.compMeasurePreservingL_compMeasurePreservingL _ _ _ _ _ _ _ _
    (normalShear_normalShear_neg φ) u

private theorem flattenL_unflattenL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    Function.RightInverse (unflattenL (p := p) hφ hL) (flattenL hφ hL) := fun v =>
  W1p.compMeasurePreservingL_compMeasurePreservingL _ _ _ _ _ _ _ _
    (normalShear_neg_normalShear φ) v

/-- **Flattening the region above a `C¹` graph.** If `φ` is of class `C¹` with
`‖fderiv ℝ φ‖ ≤ L`, precomposition with the shear by `φ` is an isomorphism from `W^{1,p}` of the
region above the graph of `φ` onto `W^{1,p}` of the half-space `{0 < t}`, with inverse the
precomposition with the shear by `-φ`. Both directions have norm at most `1 + L`
(`TauCeti.W1p.norm_normalEpigraphEquivL_le`). -/
def W1p.normalEpigraphEquivL (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    W1p volume (normalEpigraph φ) p ≃L[ℝ] W1p volume (normalHalfSpace (E := E) 0) p :=
  ContinuousLinearEquiv.equivOfInverse (flattenL hφ hL) (unflattenL hφ hL)
    (unflattenL_flattenL hφ hL) (flattenL_unflattenL hφ hL)

private theorem normalEpigraphEquivL_apply_eq (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) p) :
    W1p.normalEpigraphEquivL hφ hL u = flattenL hφ hL u :=
  ContinuousLinearEquiv.equivOfInverse_apply _ _ _ _ u

private theorem normalEpigraphEquivL_symm_apply_eq (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (v : W1p volume (normalHalfSpace (E := E) 0) p) :
    (W1p.normalEpigraphEquivL hφ hL).symm v = unflattenL hφ hL v := by
  rw [W1p.normalEpigraphEquivL, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply]

/-- Flattening multiplies the `W^{1,p}` norm by at most `1 + L`. -/
theorem W1p.norm_normalEpigraphEquivL_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L)
    (u : W1p volume (normalEpigraph φ) p) :
    ‖W1p.normalEpigraphEquivL hφ hL u‖ ≤ (1 + L) * ‖u‖ := by
  rw [normalEpigraphEquivL_apply_eq]
  have h1 := (flattenL hφ hL).le_opNorm u
  have h2 := norm_flattenL_le (p := p) hφ hL
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- The inverse of flattening multiplies the `W^{1,p}` norm by at most `1 + L`. -/
theorem W1p.norm_normalEpigraphEquivL_symm_le (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (v : W1p volume (normalHalfSpace (E := E) 0) p) :
    ‖(W1p.normalEpigraphEquivL hφ hL).symm v‖ ≤ (1 + L) * ‖v‖ := by
  rw [normalEpigraphEquivL_symm_apply_eq]
  have h1 := (unflattenL hφ hL).le_opNorm v
  have h2 := norm_unflattenL_le (p := p) hφ hL
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- The flattened function is `u ∘ normalShear φ`. -/
theorem W1p.value_normalEpigraphEquivL_ae (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) p) :
    W1p.value (W1p.normalEpigraphEquivL hφ hL u) =ᵐ[volume.restrict (normalHalfSpace (E := E) 0)]
      fun x => W1p.value u (normalShear φ x) := by
  rw [normalEpigraphEquivL_apply_eq]
  exact W1p.value_compMeasurePreservingL_ae _ _ _ _ u

/-- The weak gradient of the flattened function is given by the chain rule. -/
theorem W1p.gradient_normalEpigraphEquivL_ae (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) p) :
    W1p.gradient (W1p.normalEpigraphEquivL hφ hL u) =ᵐ[volume.restrict (normalHalfSpace (E := E) 0)]
      fun x => ContinuousLinearMap.adjoint (fderiv ℝ (normalShear φ) x)
        (W1p.gradient u (normalShear φ x)) := by
  rw [normalEpigraphEquivL_apply_eq]
  exact W1p.gradient_compMeasurePreservingL_ae _ _ _ _ u

/-- The inverse of flattening is `v ∘ normalShear (-φ)`. -/
theorem W1p.value_normalEpigraphEquivL_symm_ae (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (v : W1p volume (normalHalfSpace (E := E) 0) p) :
    W1p.value ((W1p.normalEpigraphEquivL hφ hL).symm v) =ᵐ[volume.restrict (normalEpigraph φ)]
      fun x => W1p.value v (normalShear (-φ) x) := by
  rw [normalEpigraphEquivL_symm_apply_eq]
  exact W1p.value_compMeasurePreservingL_ae _ _ _ _ v

/-- Flattening and its inverse preserve zero boundary values. -/
theorem W1p.normalEpigraphEquivL_mem_w1p0Submodule_iff (hp : p ≠ ∞) (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) p) :
    W1p.normalEpigraphEquivL hφ hL u ∈ w1p0Submodule volume (normalHalfSpace 0) p ↔
      u ∈ w1p0Submodule volume (normalEpigraph φ) p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← (W1p.normalEpigraphEquivL hφ hL).symm_apply_apply u, normalEpigraphEquivL_symm_apply_eq]
    exact W1p.compMeasurePreservingL_mem_w1p0Submodule hp _ _ _ _ h
  · rw [normalEpigraphEquivL_apply_eq]
    exact W1p.compMeasurePreservingL_mem_w1p0Submodule hp _ _ _ _ h

end Flatten

/-! ### The trace on the graph -/

section Trace

variable {φ : C(E, ℝ)} {L : ℝ}

/-- **The trace on the graph of a `C¹` function.** For `φ` of class `C¹` with
`‖fderiv ℝ φ‖ ≤ L`, the trace of `u ∈ H¹` of the region `{φ y < t}` above the graph is the
half-space trace of the flattened function `u ∘ normalShear φ`. It is an element of `L²(E)`: the
graph is parametrized by `y ↦ (φ y, y)`, the image under the shear of the boundary point
`(0, y)` of the half-space. -/
def W1p.normalEpigraphTrace (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    W1p volume (normalEpigraph φ) 2 →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  (W1p.halfSpaceTrace 0).comp (W1p.normalEpigraphEquivL hφ hL).toContinuousLinearMap

theorem W1p.normalEpigraphTrace_apply (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L)
    (u : W1p volume (normalEpigraph φ) 2) :
    W1p.normalEpigraphTrace hφ hL u = W1p.halfSpaceTrace 0 (W1p.normalEpigraphEquivL hφ hL u) :=
  (rfl)

/-- **The trace inequality on a graph domain**: `‖Tu‖_{L²} ≤ (1 + L) ‖u‖_{H¹}`. -/
theorem W1p.norm_normalEpigraphTrace_le (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L)
    (u : W1p volume (normalEpigraph φ) 2) :
    ‖W1p.normalEpigraphTrace hφ hL u‖ ≤ (1 + L) * ‖u‖ :=
  (W1p.norm_halfSpaceTrace_le 0 _).trans (W1p.norm_normalEpigraphEquivL_le hφ hL u)

/-- **The functions of zero trace on a graph domain are those of `H¹₀`.** -/
theorem W1p.mem_w1p0Submodule_iff_normalEpigraphTrace_eq_zero (hφ : ContDiff ℝ 1 φ)
    (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) (u : W1p volume (normalEpigraph φ) 2) :
    u ∈ w1p0Submodule volume (normalEpigraph φ) 2 ↔ W1p.normalEpigraphTrace hφ hL u = 0 := by
  rw [W1p.normalEpigraphTrace_apply, ← W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero,
    W1p.normalEpigraphEquivL_mem_w1p0Submodule_iff (p := 2) ENNReal.ofNat_ne_top]

/-- **The kernel of the trace on a graph domain is `H¹₀`.** On the region above the graph of a
`C¹` function with bounded derivative, the trace `H¹ → L²(E)` vanishes exactly on the closure
of the test functions. -/
theorem W1p.ker_normalEpigraphTrace (hφ : ContDiff ℝ 1 φ) (hL : ∀ y, ‖fderiv ℝ φ y‖ ≤ L) :
    LinearMap.ker (W1p.normalEpigraphTrace hφ hL).toLinearMap =
      (w1p0Submodule volume (normalEpigraph φ) 2).toSubmodule := by
  ext u
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ClosedSubmodule.mem_toSubmodule_iff,
    W1p.mem_w1p0Submodule_iff_normalEpigraphTrace_eq_zero hφ hL]

end Trace

end TauCeti
