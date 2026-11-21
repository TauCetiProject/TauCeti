/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
public import TauCeti.Analysis.PDE.Vortex.Symmetry
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Complex.Isometry
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Complex.RigidMotion
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.CompLp
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rigid motions of the plane and the `H¹` realization of the vortex operator

The orientation-preserving isometries `z ↦ u z + a` of the plane, `u` on the unit circle, act on
plane vortex fields by `rotateField u ∘ translateField a`
(`TauCeti.Analysis.PDE.Vortex.Symmetry`), and the gauge-fixed operator `L_x = d₀* ⊕ d₁`
intertwines this action with `rotateTarget u ∘ translateField a` on its target `ℝ ⊕ ℝ ⊕ ℂ`. This
file proves the same law for the bounded realization

`TauCeti.Vortex.sobolevGaugeFixedOperator c : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`

of `L_x` with `L∞` coefficient `c`, on which the Fredholm theory of plane vortices is built. The
motion `Circle.rigidMotion u a` acts

* by the linear isometry equivalence `TauCeti.Vortex.coefficientMotion u a` on the `L∞` classes
  of fields,
* by the continuous linear equivalence `TauCeti.Vortex.variationMotion u a` on `H¹(ℂ)⁴`, and
* by the linear isometry equivalence `TauCeti.Vortex.targetMotion u a` on `L²(ℂ; ℝ⁴)`,

each composing with the motion and rotating the values by `fieldRotation u` or `targetRotation u`
(`TauCeti.Vortex.coeFn_coefficientMotion`, `TauCeti.Vortex.value_variationMotion_ae`,
`TauCeti.Vortex.coeFn_targetMotion`); the weak gradients of a moved variation are rotated by `u⁻¹`
as well (`TauCeti.Vortex.gradient_variationMotion_ae`). The two isometries are built from the
measure-preserving pullback `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv` and the pointwise
isometry `LinearIsometryEquiv.compLpₗᵢ`. Each action is trivial at the identity, composes as
the motions do, and has as inverse the motion by the inverse isometry `z ↦ u⁻¹ z - u⁻¹ a`.

The realization at the moved coefficient is the conjugate of the realization at `c`:
`L_{g·c} (g·y) = g·(L_c y)`
(`TauCeti.Vortex.sobolevGaugeFixedOperator_coefficientMotion_apply`). Consequently the kernel at
the moved coefficient is the moved kernel, and surjectivity, the Fredholm property and the index
are unchanged. The moved class of a field `x` is the class of `rotateField u (translateField a x)`
(`TauCeti.Vortex.coeFn_coefficientMotion_of_ae_eq`), so these laws transport the Fredholm theory
of the realization at a vortex to all of its translates and rotations.

## Main definitions

* `TauCeti.Vortex.coefficientMotion`, `TauCeti.Vortex.variationMotion`,
  `TauCeti.Vortex.targetMotion`: the motion `z ↦ u z + a` on coefficients, variations and targets.

## Main results

* `TauCeti.Vortex.coefficientMotion_coefficientMotion`,
  `TauCeti.Vortex.variationMotion_variationMotion`, `TauCeti.Vortex.targetMotion_targetMotion`
  and the `_one_zero` and `_symm` lemmas: the group laws of the three actions.
* `TauCeti.Vortex.sobolevGaugeFixedOperator_coefficientMotion_apply`,
  `TauCeti.Vortex.sobolevGaugeFixedOperator_coefficientMotion`: the intertwining law.
* `TauCeti.Vortex.ker_sobolevGaugeFixedOperator_coefficientMotion`,
  `TauCeti.Vortex.sobolevGaugeFixedOperator_coefficientMotion_surjective_iff`,
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_coefficientMotion_iff`,
  `TauCeti.Vortex.index_sobolevGaugeFixedOperator_coefficientMotion`: its consequences.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal ComplexConjugate

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

private theorem measurePreserving_top (g : ℂ ≃ᵃⁱ[ℝ] ℂ) : MeasurePreserving g μ⊤ μ⊤ := by
  simpa using g.measurePreserving

private theorem comp_symm_ae_eq_id (g : ℂ ≃ᵃⁱ[ℝ] ℂ) : g ∘ g.symm =ᵐ[μ⊤] id :=
  Filter.Eventually.of_forall g.apply_symm_apply

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Precomposition with an affine isometry `g` followed by the pointwise isometry `R`, on `Lᵖ`
for the measure `μ⊤` that `sobolevGaugeFixedOperator` uses. Its laws below are instances of the
identity, composition, inverse and commutation laws of `Lp.compMeasurePreservingₗᵢEquiv` and
`LinearIsometryEquiv.compLpₗᵢ`. -/
private def lpMotion (p : ℝ≥0∞) [Fact (1 ≤ p)] (R : E ≃ₗᵢ[ℝ] E) (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    Lp E p μ⊤ ≃ₗᵢ[ℝ] Lp E p μ⊤ :=
  (Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_top g) (measurePreserving_top g.symm)
    (comp_symm_ae_eq_id g)).trans (R.compLpₗᵢ p μ⊤)

private theorem coeFn_lpMotion (R : E ≃ₗᵢ[ℝ] E) (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (f : Lp E p μ⊤) :
    ⇑(lpMotion p R g f) =ᵐ[μ⊤] fun z ↦ R (f (g z)) := by
  filter_upwards [R.coeFn_compLpₗᵢ (Lp.compMeasurePreservingₗᵢEquiv ℝ
      (measurePreserving_top g) (measurePreserving_top g.symm) (comp_symm_ae_eq_id g) f),
    Lp.coeFn_compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_top g)
      (measurePreserving_top g.symm) (comp_symm_ae_eq_id g) f] with z h₁ h₂
  rw [lpMotion, LinearIsometryEquiv.trans_apply, h₁, h₂, Function.comp_apply]

private theorem lpMotion_refl :
    lpMotion (E := E) p (.refl ℝ E) (.refl ℝ ℂ) = .refl ℝ _ := by
  rw [lpMotion, LinearIsometryEquiv.compLpₗᵢ_refl, LinearIsometryEquiv.trans_refl,
    Lp.compMeasurePreservingₗᵢEquiv_eq_refl ℝ _ _ _ (.of_eq AffineIsometryEquiv.coe_refl)]

/-- Successive motions compose. -/
private theorem lpMotion_lpMotion (R R' : E ≃ₗᵢ[ℝ] E) (g g' : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    (lpMotion p R' g').trans (lpMotion p R g) = lpMotion p (R'.trans R) (g.trans g') := by
  rw [lpMotion, lpMotion, lpMotion, ← LinearIsometryEquiv.trans_assoc _ (R'.compLpₗᵢ p μ⊤),
    LinearIsometryEquiv.trans_assoc (R'.compLpₗᵢ p μ⊤),
    ← Lp.compMeasurePreservingₗᵢEquiv_trans_compLpₗᵢ,
    ← LinearIsometryEquiv.trans_assoc _ (R'.compLpₗᵢ p μ⊤), LinearIsometryEquiv.trans_assoc,
    Lp.compMeasurePreservingₗᵢEquiv_trans ℝ _ _ _ _ _ _ (measurePreserving_top (g.trans g'))
      (measurePreserving_top (g.trans g').symm) (comp_symm_ae_eq_id (g.trans g'))
      (.of_eq (AffineIsometryEquiv.coe_trans g g')),
    ← LinearIsometryEquiv.compLpₗᵢ_trans]

private theorem lpMotion_symm (R : E ≃ₗᵢ[ℝ] E) (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    (lpMotion p R g).symm = lpMotion p R.symm g.symm := by
  rw [lpMotion, lpMotion, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.compLpₗᵢ_symm,
    Lp.compMeasurePreservingₗᵢEquiv_symm ℝ _ _ _ (measurePreserving_top g.symm)
      (measurePreserving_top g.symm.symm) (comp_symm_ae_eq_id g.symm) .rfl,
    Lp.compMeasurePreservingₗᵢEquiv_trans_compLpₗᵢ]

/-- Precomposition of the four coordinates with an affine isometry `g` followed by the pointwise
isometry `R`, on `H¹(ℂ)⁴`. -/
private def w1pMotion (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  ContinuousLinearMap.pi fun i ↦ ∑ k, R (EuclideanSpace.single k 1) i •
    (W1p.compAffineIsometryEquivL g rfl).comp (ContinuousLinearMap.proj k)

private theorem w1pMotion_apply (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (i : Fin 4) :
    w1pMotion R g y i =
      ∑ k, R (EuclideanSpace.single k 1) i • W1p.compAffineIsometryEquivL g rfl (y k) := by
  simp [w1pMotion]

private theorem value_w1pMotion_ae (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z ∂μ⊤, (WithLp.toLp 2 fun i ↦ W1p.value (w1pMotion R g y i) z :
      EuclideanSpace ℝ (Fin 4)) = R (WithLp.toLp 2 fun k ↦ W1p.value (y k) (g z)) := by
  -- The coordinates of `R v` in terms of the images of the standard basis.
  have hR (v : EuclideanSpace ℝ (Fin 4)) (i : Fin 4) :
      R v i = ∑ k, R (EuclideanSpace.single k 1) i * v k := by
    have hv : v = ∑ k, v k • EuclideanSpace.single k (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp [mul_comm]
  have hs (i : Fin 4) := W1p.value_finsetSum_ae (mu := volume) (Omega := ⊤) (p := 2) Finset.univ
    fun k ↦ R (EuclideanSpace.single k 1) i • W1p.compAffineIsometryEquivL g rfl (y k)
  have hc (i k : Fin 4) := W1p.value_smul_ae (R (EuclideanSpace.single k 1) i)
    (W1p.compAffineIsometryEquivL g (U := ⊤) (V := ⊤) (p := 2) rfl (y k))
  filter_upwards [ae_all_iff.2 hs, ae_all_iff.2 fun i ↦ ae_all_iff.2 (hc i),
    ae_all_iff.2 fun k ↦ W1p.value_compAffineIsometryEquivL_ae g rfl (y k)] with z h₁ h₂ h₃
  ext i
  rw [hR, PiLp.toLp_apply, w1pMotion_apply, h₁ i]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [h₂ i k, Pi.smul_apply, h₃ k, smul_eq_mul]

private theorem gradient_w1pMotion_ae
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z ∂μ⊤, ∀ i, W1p.gradient (w1pMotion R g y i) z =
      ∑ k, R (EuclideanSpace.single k 1) i •
        g.linearIsometryEquiv.symm (W1p.gradient (y k) (g z)) := by
  have hs (i : Fin 4) := Lp.coeFn_fun_finsetSum (μ := μ⊤) Finset.univ fun k ↦
    R (EuclideanSpace.single k 1) i •
      W1p.gradient (W1p.compAffineIsometryEquivL g (U := ⊤) (V := ⊤) (p := 2) rfl (y k))
  have hc (i k : Fin 4) := Lp.coeFn_smul (R (EuclideanSpace.single k 1) i)
    (W1p.gradient (W1p.compAffineIsometryEquivL g (U := ⊤) (V := ⊤) (p := 2) rfl (y k)))
  filter_upwards [ae_all_iff.2 hs, ae_all_iff.2 fun i ↦ ae_all_iff.2 (hc i),
    ae_all_iff.2 fun k ↦ W1p.gradient_compAffineIsometryEquivL_ae g rfl (y k)] with z h₁ h₂ h₃ i
  rw [w1pMotion_apply, W1p.gradient_sum]
  simp only [W1p.gradient_smul]
  rw [h₁ i]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [h₂ i k, Pi.smul_apply, h₃ k]

private theorem w1pMotion_refl (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    w1pMotion (.refl ℝ _) (.refl ℝ ℂ) y = y := by
  funext i
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_w1pMotion_ae (.refl ℝ _) (.refl ℝ ℂ) y] with z hz
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v i) hz

/-- Successive motions compose. -/
private theorem w1pMotion_w1pMotion
    (R R' : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g g' : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    w1pMotion R g (w1pMotion R' g' y) = w1pMotion (R'.trans R) (g.trans g') y := by
  funext i
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_w1pMotion_ae R g (w1pMotion R' g' y),
    (measurePreserving_top g).quasiMeasurePreserving.ae (value_w1pMotion_ae R' g' y),
    value_w1pMotion_ae (R'.trans R) (g.trans g') y] with z h₁ h₂ h₃
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v i)
    (h₁.trans ((congrArg R h₂).trans h₃.symm))

private theorem w1pMotion_symm_w1pMotion
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    w1pMotion R.symm g.symm (w1pMotion R g y) = y := by
  rw [w1pMotion_w1pMotion, LinearIsometryEquiv.self_trans_symm,
    AffineIsometryEquiv.symm_trans_self, w1pMotion_refl]

private theorem w1pMotion_w1pMotion_symm
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    w1pMotion R g (w1pMotion R.symm g.symm y) = y := by
  rw [w1pMotion_w1pMotion, LinearIsometryEquiv.symm_trans_self,
    AffineIsometryEquiv.self_trans_symm, w1pMotion_refl]

/-- `w1pMotion R g` as a continuous linear equivalence. -/
private def w1pMotionEquiv (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) ≃L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  .ofContinuousLinearMap (w1pMotion R g) (w1pMotion R.symm g.symm)
    (ContinuousLinearMap.ext (w1pMotion_w1pMotion_symm R g))
    (ContinuousLinearMap.ext (w1pMotion_symm_w1pMotion R g))

private theorem w1pMotionEquiv_apply
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) : w1pMotionEquiv R g y = w1pMotion R g y := (rfl)

/-! ### The rigid motions of the plane on the Sobolev realization -/

/-- **The rigid motion `z ↦ u z + a` on the `L∞` classes of fields.** It sends the class of a
field `x` to the class of `rotateField u (translateField a x)`, the pullback of `x` by the motion
(`coeFn_coefficientMotion`). These are the coefficients of `sobolevGaugeFixedOperator`. -/
def coefficientMotion (u : Circle) (a : ℂ) :
    Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ ≃ₗᵢ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ :=
  lpMotion ∞ (fieldRotation u) (u.rigidMotion a)

/-- **The rigid motion `z ↦ u z + a` on the `L²` targets of `sobolevGaugeFixedOperator`.** It
sends the class of `η` to the class of `rotateTarget u (translateField a η)`
(`coeFn_targetMotion`). -/
def targetMotion (u : Circle) (a : ℂ) :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ≃ₗᵢ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  lpMotion 2 (targetRotation u) (u.rigidMotion a)

/-- **The rigid motion `z ↦ u z + a` on `H¹` variations.** It acts on the four coordinates in
`H¹(ℂ) = W^{1,2}(ℂ)` as `rotateField u ∘ translateField a` acts on their values
(`value_variationMotion_ae`): each coordinate is composed with the motion, and the connection
coordinates are mixed by `fieldRotation u`. -/
def variationMotion (u : Circle) (a : ℂ) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) ≃L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  w1pMotionEquiv (fieldRotation u) (u.rigidMotion a)

/-- The coefficient moved by `z ↦ u z + a` is the rotated translate of the coefficient. -/
theorem coeFn_coefficientMotion (u : Circle) (a : ℂ) (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    ⇑(coefficientMotion u a c) =ᵐ[μ⊤] rotateField u (translateField a c) := by
  filter_upwards [coeFn_lpMotion (fieldRotation u) (u.rigidMotion a) c] with z hz
  rw [coefficientMotion, hz, rotateField_apply_eq_fieldRotation, translateField_apply,
    Circle.rigidMotion_apply]

/-- If the coefficient `c` is the class of a field `x`, the moved coefficient is the class of
`rotateField u (translateField a x)`. -/
theorem coeFn_coefficientMotion_of_ae_eq {c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hcx : c =ᵐ[μ⊤] x) (u : Circle) (a : ℂ) :
    ⇑(coefficientMotion u a c) =ᵐ[μ⊤] rotateField u (translateField a x) := by
  filter_upwards [coeFn_coefficientMotion u a c,
    (measurePreserving_top (u.rigidMotion a)).quasiMeasurePreserving.ae hcx] with z h₁ h₂
  rw [h₁, rotateField_apply_eq_fieldRotation, rotateField_apply_eq_fieldRotation,
    translateField_apply, translateField_apply, ← Circle.rigidMotion_apply, h₂]

/-- The target moved by `z ↦ u z + a` is the rotated translate of the target. -/
theorem coeFn_targetMotion (u : Circle) (a : ℂ) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    ⇑(targetMotion u a f) =ᵐ[μ⊤] rotateTarget u (translateField a f) := by
  filter_upwards [coeFn_lpMotion (targetRotation u) (u.rigidMotion a) f] with z hz
  rw [targetMotion, hz, rotateTarget_apply_eq_targetRotation, translateField_apply,
    Circle.rigidMotion_apply]

/-- The values of a variation moved by `z ↦ u z + a` are the rotated translates of its values. -/
theorem value_variationMotion_ae (u : Circle) (a : ℂ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z ∂μ⊤, (WithLp.toLp 2 fun j ↦ W1p.value (variationMotion u a y j) z :
      EuclideanSpace ℝ (Fin 4)) =
        rotateField u (translateField a fun w ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) w) z := by
  filter_upwards [value_w1pMotion_ae (fieldRotation u) (u.rigidMotion a) y] with z hz
  rw [variationMotion, w1pMotionEquiv_apply, hz, rotateField_apply_eq_fieldRotation,
    translateField_apply, Circle.rigidMotion_apply]

/-- The weak gradients of a variation moved by `z ↦ u z + a`: the gradients of the coordinates
are taken at `u z + a` and multiplied by `u⁻¹ = conj u`, and the coordinates are mixed by
`fieldRotation u`. -/
theorem gradient_variationMotion_ae (u : Circle) (a : ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z ∂μ⊤, ∀ i, W1p.gradient (variationMotion u a y i) z =
      ∑ k, fieldRotation u (EuclideanSpace.single k 1) i •
        (conj (u : ℂ) * W1p.gradient (y k) ((u : ℂ) * z + a)) := by
  filter_upwards [gradient_w1pMotion_ae (fieldRotation u) (u.rigidMotion a) y] with z hz i
  rw [variationMotion, w1pMotionEquiv_apply, hz i]
  simp only [Circle.linearIsometryEquiv_rigidMotion_symm_apply, Circle.rigidMotion_apply]

@[simp]
theorem coefficientMotion_one_zero : coefficientMotion 1 0 = LinearIsometryEquiv.refl ℝ _ :=
  by rw [coefficientMotion, fieldRotation_one, Circle.rigidMotion_one_zero, lpMotion_refl]

@[simp]
theorem targetMotion_one_zero : targetMotion 1 0 = LinearIsometryEquiv.refl ℝ _ :=
  by rw [targetMotion, targetRotation_one, Circle.rigidMotion_one_zero, lpMotion_refl]

@[simp]
theorem variationMotion_one_zero : variationMotion 1 0 = ContinuousLinearEquiv.refl ℝ _ :=
  ContinuousLinearEquiv.ext <| funext fun y ↦ by
    rw [variationMotion, w1pMotionEquiv_apply, fieldRotation_one, Circle.rigidMotion_one_zero,
      w1pMotion_refl, ContinuousLinearEquiv.refl_apply]

/-- Moving by `z ↦ v z + b` and then by `z ↦ u z + a` is moving by the composite
`z ↦ v (u z + a) + b`. Not a simp lemma: the type of the classes mentions the measure
`volume.restrict ↑⊤`, which simp rewrites to `volume.restrict Set.univ`. -/
theorem coefficientMotion_coefficientMotion (u v : Circle) (a b : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    coefficientMotion u a (coefficientMotion v b c) = coefficientMotion (u * v) (v * a + b) c := by
  rw [coefficientMotion, coefficientMotion, coefficientMotion, ← LinearIsometryEquiv.trans_apply,
    lpMotion_lpMotion, Circle.rigidMotion_trans_rigidMotion, fieldRotation_trans_fieldRotation]

/-- Moving by `z ↦ v z + b` and then by `z ↦ u z + a` is moving by the composite
`z ↦ v (u z + a) + b`. Not a simp lemma: the type of the classes mentions the measure
`volume.restrict ↑⊤`, which simp rewrites to `volume.restrict Set.univ`. -/
theorem targetMotion_targetMotion (u v : Circle) (a b : ℂ)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    targetMotion u a (targetMotion v b f) = targetMotion (u * v) (v * a + b) f := by
  rw [targetMotion, targetMotion, targetMotion, ← LinearIsometryEquiv.trans_apply,
    lpMotion_lpMotion, Circle.rigidMotion_trans_rigidMotion, targetRotation_trans_targetRotation]

/-- Moving by `z ↦ v z + b` and then by `z ↦ u z + a` is moving by the composite
`z ↦ v (u z + a) + b`. -/
@[simp]
theorem variationMotion_variationMotion (u v : Circle) (a b : ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    variationMotion u a (variationMotion v b y) = variationMotion (u * v) (v * a + b) y := by
  rw [variationMotion, variationMotion, variationMotion, w1pMotionEquiv_apply,
    w1pMotionEquiv_apply, w1pMotionEquiv_apply, w1pMotion_w1pMotion,
    Circle.rigidMotion_trans_rigidMotion, fieldRotation_trans_fieldRotation]

private theorem w1pMotionEquiv_symm
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    (w1pMotionEquiv R g).symm = w1pMotionEquiv R.symm g.symm := by
  refine ContinuousLinearEquiv.ext (funext fun y ↦ ?_)
  rw [w1pMotionEquiv_apply, w1pMotionEquiv, ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap]

/-- The inverse of the motion `z ↦ u z + a` on coefficients is the motion by the inverse
isometry `z ↦ u⁻¹ z - u⁻¹ a`. -/
@[simp]
theorem coefficientMotion_symm (u : Circle) (a : ℂ) :
    (coefficientMotion u a).symm = coefficientMotion u⁻¹ (-((u : ℂ)⁻¹ * a)) := by
  rw [coefficientMotion, coefficientMotion, lpMotion_symm, fieldRotation_symm,
    Circle.rigidMotion_symm]

/-- The inverse of the motion `z ↦ u z + a` on targets is the motion by the inverse isometry
`z ↦ u⁻¹ z - u⁻¹ a`. -/
@[simp]
theorem targetMotion_symm (u : Circle) (a : ℂ) :
    (targetMotion u a).symm = targetMotion u⁻¹ (-((u : ℂ)⁻¹ * a)) := by
  rw [targetMotion, targetMotion, lpMotion_symm, targetRotation_symm, Circle.rigidMotion_symm]

/-- The inverse of the motion `z ↦ u z + a` on variations is the motion by the inverse isometry
`z ↦ u⁻¹ z - u⁻¹ a`. -/
@[simp]
theorem variationMotion_symm (u : Circle) (a : ℂ) :
    (variationMotion u a).symm = variationMotion u⁻¹ (-((u : ℂ)⁻¹ * a)) := by
  rw [variationMotion, variationMotion, w1pMotionEquiv_symm, fieldRotation_symm,
    Circle.rigidMotion_symm]

/-- **Rigid motions intertwine the `H¹` realization of `L_x`.** Moving the coefficient and the
variation by `z ↦ u z + a` moves the image: `L_{g·c} (g·y) = g·(L_c y)`, where the motion acts on
coefficients by `coefficientMotion`, on variations by `variationMotion` and on targets by
`targetMotion`. -/
theorem sobolevGaugeFixedOperator_coefficientMotion_apply (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevGaugeFixedOperator (coefficientMotion u a c) (variationMotion u a y) =
      targetMotion u a (sobolevGaugeFixedOperator c y) := by
  refine Lp.ext ?_
  rw [coefficientMotion, variationMotion, targetMotion, w1pMotionEquiv_apply]
  filter_upwards [sobolevGaugeFixedOperator_apply_ae
      (lpMotion ∞ (fieldRotation u) (u.rigidMotion a) c)
      (w1pMotion (fieldRotation u) (u.rigidMotion a) y),
    coeFn_lpMotion (fieldRotation u) (u.rigidMotion a) c,
    coeFn_lpMotion (targetRotation u) (u.rigidMotion a) (sobolevGaugeFixedOperator c y),
    (measurePreserving_top (u.rigidMotion a)).quasiMeasurePreserving.ae
      (sobolevGaugeFixedOperator_apply_ae c y),
    value_w1pMotion_ae (fieldRotation u) (u.rigidMotion a) y,
    gradient_w1pMotion_ae (fieldRotation u) (u.rigidMotion a) y] with z h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, h₃, h₄, h₅, map_add, ← gaugeFixedZerothOrder_fieldRotation]
  refine congrArg (· + _) ((congrArg gaugeFixedFirstOrder (funext fun i ↦ ?_)).trans
    (gaugeFixedFirstOrder_fieldRotation u fun k ↦ W1p.gradient (y k) (u.rigidMotion a z)))
  rw [h₆ i]
  simp only [Circle.linearIsometryEquiv_rigidMotion_symm_apply]

/-- **Rigid motions conjugate the `H¹` realization of `L_x`.** The realization at the coefficient
moved by `z ↦ u z + a` is the realization at `c` conjugated by the motions of variations and
targets. -/
theorem sobolevGaugeFixedOperator_coefficientMotion (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    sobolevGaugeFixedOperator (coefficientMotion u a c) =
      (((targetMotion u a).toContinuousLinearEquiv :
          Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] _).comp
        (sobolevGaugeFixedOperator c)).comp
          ((variationMotion u a).symm : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) := by
  ext1 y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [← sobolevGaugeFixedOperator_coefficientMotion_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The kernel of the realization at a moved coefficient is the moved kernel. -/
theorem ker_sobolevGaugeFixedOperator_coefficientMotion (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (sobolevGaugeFixedOperator (coefficientMotion u a c)).ker =
      (sobolevGaugeFixedOperator c).ker.map ((variationMotion u a :
        (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
          (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →ₗ[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, sobolevGaugeFixedOperator_coefficientMotion,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.map_eq_zero_iff]
  refine ⟨fun h ↦ ⟨(variationMotion u a).symm y, h, (variationMotion u a).apply_symm_apply y⟩, ?_⟩
  rintro ⟨y₀, hy₀, rfl⟩
  rwa [ContinuousLinearEquiv.symm_apply_apply]

/-- The realization at a moved coefficient is onto exactly when the realization at `c` is. -/
theorem sobolevGaugeFixedOperator_coefficientMotion_surjective_iff (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    Function.Surjective (sobolevGaugeFixedOperator (coefficientMotion u a c)) ↔
      Function.Surjective (sobolevGaugeFixedOperator c) := by
  rw [sobolevGaugeFixedOperator_coefficientMotion]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    EquivLike.comp_surjective, EquivLike.surjective_comp]

/-- The realization at a moved coefficient is Fredholm exactly when the realization at `c` is. -/
theorem isFredholm_sobolevGaugeFixedOperator_coefficientMotion_iff (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (sobolevGaugeFixedOperator (coefficientMotion u a c)).IsFredholm ↔
      (sobolevGaugeFixedOperator c).IsFredholm := by
  rw [sobolevGaugeFixedOperator_coefficientMotion]
  simp

/-- Rigid motions preserve the index of the realization. -/
theorem index_sobolevGaugeFixedOperator_coefficientMotion (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (sobolevGaugeFixedOperator (coefficientMotion u a c)).index =
      (sobolevGaugeFixedOperator c).index := by
  rw [sobolevGaugeFixedOperator_coefficientMotion]
  simp

end TauCeti.Vortex
