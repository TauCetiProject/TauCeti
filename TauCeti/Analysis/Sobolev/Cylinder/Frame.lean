/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Analysis.Sobolev.Strip.Frame
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import TauCeti.Analysis.ODE.FrameTrivialization
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Changes of frame on the Sobolev space of the cylinder

Let `Φ : ℝ × ℝ → L(V, W)` be a frame on the cylinder `ℝ × S¹`: a `C²` family of linear maps of
period one in `t`, bounded together with its derivative. Reading sections of the trivial bundle
with fibre `V` in the frame, `ξ ↦ (w ↦ Φ w (ξ w))`, acts on jets through the coefficient field
`TauCeti.StripSobolev.frameJetCoeff Φ`, and this file shows that it acts on the Sobolev space
`W^{1,2}(ℝ × S¹)`:

* it maps `W^{1,2}(ℝ × S¹, V)` into `W^{1,2}(ℝ × S¹, W)`
  (`TauCeti.CylinderSobolev.jetOperator_frameJetCoeff_mem_H1`), giving the bounded operator
  `TauCeti.CylinderSobolev.frameL`;
* if `Ψ z` is a two-sided inverse of `Φ z` and `Ψ` is a frame as well, the two operators are
  mutually inverse (`TauCeti.CylinderSobolev.frameL_comp_frameL_of_comp_eq_id`), so reading in a
  frame is an isomorphism of Sobolev spaces (`TauCeti.CylinderSobolev.frameEquiv`).

Consequently Fredholmness and the index of first-order operators on the cylinder do not depend on
the frame in which they are written. If `D : W^{1,2}(ℝ × S¹, W) → L²(ℝ × S¹, U)` has coefficient
field `M`, then `D` composed with the change of frame is the operator of the coefficient field
`M ∘ frameJetCoeff Φ`, which is Fredholm exactly when `D` is, with the same index
(`TauCeti.CylinderSobolev.isFredholm_jetOperator_comp_frameJetCoeff_iff`,
`TauCeti.CylinderSobolev.index_jetOperator_comp_frameJetCoeff`). For operators `∂s + A ∂t + C`
(`TauCeti.firstOrderJetCoeff`), reading in the frame `Φ` and applying `Ψ = Φ⁻¹` gives the operator
`∂s + (Ψ A Φ) ∂t + Ψ (C Φ + ∂s Φ + A ∂t Φ)` of the same form
(`TauCeti.StripSobolev.comp_firstOrderJetCoeff_comp_frameJetCoeff`), and the two are Fredholm
together, with equal indices
(`TauCeti.CylinderSobolev.isFredholm_jetOperator_firstOrderJetCoeff_frame_iff`,
`TauCeti.CylinderSobolev.index_jetOperator_firstOrderJetCoeff_frame`). The multiplication by `Ψ` on
`L²` used for the target is invertible by
`MeasureTheory.Lp.isInvertible_operatorMultiplication_of_comp_eq_id`.

For a linearized Floer operator `∂s + J ∂t + C` written in a trivialization along a cylinder, this
says that its Fredholm property and index do not depend on the trivialization. For a loop of
frames `Φ_t` that does not depend on `s` and intertwines `J₀_t` with `J_t`, the operator
`∂s + J_t (∂t - S(s, t))` becomes `∂s + J₀_t (∂t - S_Φ(s, t))` with
`S_Φ(s, ·) = Φ⁻¹ (S(s, ·) Φ - Φ')` the trivialized coefficient (`TauCeti.trivializedCoeff`), and the
two operators are Fredholm together, with equal indices
(`TauCeti.CylinderSobolev.isFredholm_jetOperator_firstOrderJetCoeff_trivializedCoeff_iff`,
`TauCeti.CylinderSobolev.index_jetOperator_firstOrderJetCoeff_trivializedCoeff`). The ends
`∂s + J (∂t - S_±)` are trivialized along the same loop, so when two trivializations differ by a
loop `g` of symplectic maps the Conley–Zehnder indices of both ends shift by the same amount
`2 μ(g)` (`TauCeti.SymplecticForm.conleyZehnderIndex_frameChange`), while the index of the cylinder
operator does not change.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix C, on real Cauchy–Riemann operators in trivializations and their Fredholm theory.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

open MeasureTheory Filter Function
open scoped ENNReal

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U]

/-! ### Reading sections in a frame -/

section Frame

variable {Φ : ℝ × ℝ → V →L[ℝ] W}

/-- Reading a test section in a `C²` frame of period one in `t` gives a test section. -/
theorem frame_mem_testSection (hΦ : ContDiff ℝ 2 Φ) (hΦp : ∀ s t, Φ (s, t + 1) = Φ (s, t))
    {ξ : ℝ × ℝ → V} (hξ : ξ ∈ testSection V) : (fun w ↦ Φ w (ξ w)) ∈ testSection W := by
  obtain ⟨hξ2, hξp, R, hR⟩ := mem_testSection_iff.1 hξ
  exact mem_testSection_iff.2 ⟨hΦ.clm_apply hξ2, fun s t ↦ by simp only [hΦp, hξp],
    R, fun s t hs ↦ by simp only [hR s t hs, map_zero]⟩

variable {B : ℝ} (hΦ : ContDiff ℝ 2 Φ) (hΦp : ∀ s t, Φ (s, t + 1) = Φ (s, t))
  (hΦB : ∀ z, ‖Φ z‖ ≤ B) (hΦ'B : ∀ z, ‖fderiv ℝ Φ z‖ ≤ B)

include hΦ hΦB hΦ'B in
/-- On the `L²` jet of a test section `ξ`, the change of frame gives the `L²` jet of the test
section `w ↦ Φ w (ξ w)`. -/
theorem jetOperator_frameJetCoeff_jetLp (ξ : testSection V) :
    jetOperator stripMeasure (frameJetCoeff Φ) (jetLp (testSection V) ξ) =
      jetLp (testSection W) ⟨_, frame_mem_testSection hΦ hΦp ξ.property⟩ := by
  have hξd : Differentiable ℝ (ξ : ℝ × ℝ → V) :=
    (mem_testSection_iff.1 ξ.property).1.differentiable (by norm_num)
  refine Lp.ext ?_
  filter_upwards [jetOperator_jetLp_ae_eq (memLp_frameJetCoeff (hΦ.of_le one_le_two) hΦB hΦ'B) ξ,
    coeFn_jetLp (S := testSection W) ⟨_, frame_mem_testSection hΦ hΦp ξ.property⟩]
    with z h₁ h₂
  rw [h₁, h₂, jet_frame_eq_frameJetCoeff ((hΦ.differentiable (by norm_num)) z) (hξd z)]

include hΦ hΦp hΦB hΦ'B in
/-- **Changes of frame preserve `W^{1,2}`.** For a `C²` frame `Φ` of period one in `t` with `Φ`
and `dΦ` bounded, the operator of the coefficient field `frameJetCoeff Φ`, which reads a section in
the frame `Φ`, maps `H1 V` into `H1 W`. -/
theorem jetOperator_frameJetCoeff_mem_H1 {f : Lp (V × V × V) 2 stripMeasure} (hf : f ∈ H1 V) :
    jetOperator stripMeasure (frameJetCoeff Φ) f ∈ H1 W := by
  refine jetClosure_subset_of_isClosed
    (s := jetOperator stripMeasure (frameJetCoeff Φ) ⁻¹'
      (H1 W : Set (Lp (W × W × W) 2 stripMeasure)))
    ((isClosed_jetClosure _).preimage (jetOperator stripMeasure _).continuous) ?_ hf
  rintro _ ⟨ξ, rfl⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, jetOperator_frameJetCoeff_jetLp hΦ hΦp hΦB hΦ'B ξ]
  exact jetLp_mem_jetClosure _

/-- Reading sections in a `C²` frame `Φ` of period one in `t`, with `Φ` and `dΦ` bounded, as an
operator `H1 V →L[ℝ] H1 W`: the operator of the coefficient field `frameJetCoeff Φ`, restricted to
`H1 V` (`TauCeti.CylinderSobolev.coe_frameL`). -/
def frameL : H1 V →L[ℝ] H1 W :=
  ((jetOperator stripMeasure (frameJetCoeff Φ)).comp (H1 V).subtypeL).codRestrict (H1 W) fun x ↦
    jetOperator_frameJetCoeff_mem_H1 hΦ hΦp hΦB hΦ'B x.property

/-- As an `L²` jet, `frameL` is the operator of the coefficient field `frameJetCoeff Φ`. -/
@[simp]
theorem coe_frameL (x : H1 V) :
    (frameL hΦ hΦp hΦB hΦ'B x : Lp (W × W × W) 2 stripMeasure) =
      jetOperator stripMeasure (frameJetCoeff Φ) (x : Lp (V × V × V) 2 stripMeasure) :=
  (rfl)

/-- **First-order operators in a frame.** A first-order operator with coefficient field `M`,
composed with the change of frame by `Φ`, is the first-order operator with coefficient field
`M ∘ frameJetCoeff Φ`. -/
theorem jetOperator_comp_subtypeL_comp_frameL {M : ℝ × ℝ → W × W × W →L[ℝ] U}
    (hM : MemLp M ∞ stripMeasure) :
    ((jetOperator stripMeasure M).comp (H1 W).subtypeL).comp (frameL hΦ hΦp hΦB hΦ'B) =
      (jetOperator stripMeasure fun z ↦ (M z).comp (frameJetCoeff Φ z)).comp (H1 V).subtypeL := by
  ext1 x
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, coe_frameL,
    ← jetOperator_comp_jetOperator hM (memLp_frameJetCoeff (hΦ.of_le one_le_two) hΦB hΦ'B)]

end Frame

/-! ### Inverse frames -/

section Inverse

variable {Φ : ℝ × ℝ → V →L[ℝ] W} {Ψ : ℝ × ℝ → W →L[ℝ] V} {B : ℝ}
  (hΦ : ContDiff ℝ 2 Φ) (hΦp : ∀ s t, Φ (s, t + 1) = Φ (s, t))
  (hΦB : ∀ z, ‖Φ z‖ ≤ B) (hΦ'B : ∀ z, ‖fderiv ℝ Φ z‖ ≤ B)
  (hΨ : ContDiff ℝ 2 Ψ) (hΨp : ∀ s t, Ψ (s, t + 1) = Ψ (s, t))
  (hΨB : ∀ z, ‖Ψ z‖ ≤ B) (hΨ'B : ∀ z, ‖fderiv ℝ Ψ z‖ ≤ B)

include hΦ hΨ in
/-- **Inverse frames give inverse operators.** If `Ψ z` is a left inverse of `Φ z` for every `z`,
reading in the frame `Φ` and then in the frame `Ψ` is the identity of `H1 V`. -/
theorem frameL_comp_frameL_of_comp_eq_id
    (hΨΦ : ∀ z, (Ψ z).comp (Φ z) = ContinuousLinearMap.id ℝ V) :
    (frameL hΨ hΨp hΨB hΨ'B).comp (frameL hΦ hΦp hΦB hΦ'B) = ContinuousLinearMap.id ℝ (H1 V) := by
  -- The composite coefficient field is the change of frame by the identity frame.
  have hcoeff : (fun z ↦ (frameJetCoeff Ψ z).comp (frameJetCoeff Φ z)) =
      fun _ ↦ ContinuousLinearMap.id ℝ (V × V × V) := by
    funext z
    rw [frameJetCoeff_comp_frameJetCoeff ((hΨ.differentiable (by norm_num)) z)
      ((hΦ.differentiable (by norm_num)) z), funext hΨΦ, frameJetCoeff_const_id]
  ext1 x
  refine Subtype.ext ?_
  simp only [ContinuousLinearMap.comp_apply, coe_frameL, ContinuousLinearMap.id_apply]
  rw [← ContinuousLinearMap.comp_apply,
    jetOperator_comp_jetOperator (memLp_frameJetCoeff (hΨ.of_le one_le_two) hΨB hΨ'B)
      (memLp_frameJetCoeff (hΦ.of_le one_le_two) hΦB hΦ'B), hcoeff, jetOperator_id,
    ContinuousLinearMap.id_apply]

/-- **Reading in a frame is an isomorphism of Sobolev spaces.** For a `C²` frame `Φ` of period one
in `t` whose pointwise inverse `Ψ` is also a `C²` frame of period one in `t`, both bounded together
with their derivatives, reading sections in the frame `Φ` is an isomorphism
`W^{1,2}(ℝ × S¹, V) ≃ W^{1,2}(ℝ × S¹, W)`, with inverse reading them in the frame `Ψ`. -/
def frameEquiv (hΨΦ : ∀ z, (Ψ z).comp (Φ z) = ContinuousLinearMap.id ℝ V)
    (hΦΨ : ∀ z, (Φ z).comp (Ψ z) = ContinuousLinearMap.id ℝ W) : H1 V ≃L[ℝ] H1 W :=
  .ofContinuousLinearMap (frameL hΦ hΦp hΦB hΦ'B) (frameL hΨ hΨp hΨB hΨ'B)
    (frameL_comp_frameL_of_comp_eq_id hΨ hΨp hΨB hΨ'B hΦ hΦp hΦB hΦ'B hΦΨ)
    (frameL_comp_frameL_of_comp_eq_id hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ)

/-- The isomorphism `frameEquiv` is reading sections in the frame `Φ`. -/
@[simp]
theorem coe_frameEquiv (hΨΦ : ∀ z, (Ψ z).comp (Φ z) = ContinuousLinearMap.id ℝ V)
    (hΦΨ : ∀ z, (Φ z).comp (Ψ z) = ContinuousLinearMap.id ℝ W) :
    (frameEquiv hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ : H1 V →L[ℝ] H1 W) =
      frameL hΦ hΦp hΦB hΦ'B :=
  (rfl)

/-- The inverse of `frameEquiv` is reading sections in the inverse frame `Ψ`. -/
@[simp]
theorem coe_frameEquiv_symm (hΨΦ : ∀ z, (Ψ z).comp (Φ z) = ContinuousLinearMap.id ℝ V)
    (hΦΨ : ∀ z, (Φ z).comp (Ψ z) = ContinuousLinearMap.id ℝ W) :
    ((frameEquiv hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ).symm : H1 W →L[ℝ] H1 V) =
      frameL hΨ hΨp hΨB hΨ'B :=
  (rfl)

end Inverse

/-! ### Fredholm operators in a frame -/

section Fredholm

variable {Φ : ℝ × ℝ → V →L[ℝ] W} {Ψ : ℝ × ℝ → W →L[ℝ] V} {B : ℝ}
  (hΦ : ContDiff ℝ 2 Φ) (hΦp : ∀ s t, Φ (s, t + 1) = Φ (s, t))
  (hΦB : ∀ z, ‖Φ z‖ ≤ B) (hΦ'B : ∀ z, ‖fderiv ℝ Φ z‖ ≤ B)
  (hΨ : ContDiff ℝ 2 Ψ) (hΨp : ∀ s t, Ψ (s, t + 1) = Ψ (s, t))
  (hΨB : ∀ z, ‖Ψ z‖ ≤ B) (hΨ'B : ∀ z, ‖fderiv ℝ Ψ z‖ ≤ B)
  (hΨΦ : ∀ z, (Ψ z).comp (Φ z) = ContinuousLinearMap.id ℝ V)
  (hΦΨ : ∀ z, (Φ z).comp (Ψ z) = ContinuousLinearMap.id ℝ W)
  {M : ℝ × ℝ → W × W × W →L[ℝ] U} (hM : MemLp M ∞ stripMeasure)

include hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ hM in
/-- **Fredholmness does not depend on the frame.** A first-order operator with coefficient field
`M` on `W^{1,2}(ℝ × S¹, W)` is Fredholm exactly when the operator with coefficient field
`M ∘ frameJetCoeff Φ` on `W^{1,2}(ℝ × S¹, V)`, its reading in the frame `Φ`, is Fredholm. -/
theorem isFredholm_jetOperator_comp_frameJetCoeff_iff :
    ((jetOperator stripMeasure fun z ↦ (M z).comp (frameJetCoeff Φ z)).comp
        (H1 V).subtypeL).IsFredholm ↔
      ((jetOperator stripMeasure M).comp (H1 W).subtypeL).IsFredholm := by
  rw [← jetOperator_comp_subtypeL_comp_frameL hΦ hΦp hΦB hΦ'B hM,
    ← coe_frameEquiv hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ,
    ContinuousLinearMap.isFredholm_comp_equiv]

include hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ hM in
/-- **The index does not depend on the frame.** A first-order operator with coefficient field `M`
on `W^{1,2}(ℝ × S¹, W)` and its reading in the frame `Φ`, the operator with coefficient field
`M ∘ frameJetCoeff Φ` on `W^{1,2}(ℝ × S¹, V)`, have the same index. -/
theorem index_jetOperator_comp_frameJetCoeff :
    ((jetOperator stripMeasure fun z ↦ (M z).comp (frameJetCoeff Φ z)).comp (H1 V).subtypeL).index =
      ((jetOperator stripMeasure M).comp (H1 W).subtypeL).index := by
  rw [← jetOperator_comp_subtypeL_comp_frameL hΦ hΦp hΦB hΦ'B hM,
    ← coe_frameEquiv hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ,
    ContinuousLinearMap.index_comp_equiv]

end Fredholm

/-! ### Operators `∂s + A ∂t + C` in a frame -/

section FirstOrder

variable {Φ : ℝ × ℝ → V →L[ℝ] W} {Ψ : ℝ × ℝ → W →L[ℝ] V} {B : ℝ}
  (hΦ : ContDiff ℝ 2 Φ) (hΦp : ∀ s t, Φ (s, t + 1) = Φ (s, t))
  (hΦB : ∀ z, ‖Φ z‖ ≤ B) (hΦ'B : ∀ z, ‖fderiv ℝ Φ z‖ ≤ B)
  (hΨ : ContDiff ℝ 2 Ψ) (hΨp : ∀ s t, Ψ (s, t + 1) = Ψ (s, t))
  (hΨB : ∀ z, ‖Ψ z‖ ≤ B) (hΨ'B : ∀ z, ‖fderiv ℝ Ψ z‖ ≤ B)
  (hΨΦ : ∀ z, (Ψ z).comp (Φ z) = ContinuousLinearMap.id ℝ V)
  (hΦΨ : ∀ z, (Φ z).comp (Ψ z) = ContinuousLinearMap.id ℝ W)
  {A C : ℝ × ℝ → W →L[ℝ] W}
  (hAC : MemLp (fun z ↦ firstOrderJetCoeff (A z) (C z)) ∞ stripMeasure)

include hΨΦ hAC in
/-- The operator `∂s + A ∂t + C` read in the frame `Φ`, with `Ψ` applied to its values, factors as
multiplication by `Ψ` after `∂s + A ∂t + C` after the change of frame. -/
private theorem jetOperator_firstOrderJetCoeff_frame_eq (hΨL : MemLp Ψ ∞ stripMeasure) :
    (jetOperator stripMeasure fun z ↦ firstOrderJetCoeff ((Ψ z).comp ((A z).comp (Φ z)))
        ((Ψ z).comp ((C z).comp (Φ z) + fderiv ℝ Φ z (1, 0) +
          (A z).comp (fderiv ℝ Φ z (0, 1))))).comp (H1 V).subtypeL =
      (Lp.operatorMultiplication 2 (hΨL.toLp Ψ)).comp
        (((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (A z) (C z)).comp
          (H1 W).subtypeL).comp (frameL hΦ hΦp hΦB hΦ'B)) := by
  rw [jetOperator_comp_subtypeL_comp_frameL hΦ hΦp hΦB hΦ'B hAC, ← ContinuousLinearMap.comp_assoc,
    ← jetOperator_comp_eq_operatorMultiplication_comp hΨL
      (hAC.clm_comp ∞ (memLp_frameJetCoeff (hΦ.of_le one_le_two) hΦB hΦ'B))]
  congr 2
  funext z
  rw [← comp_firstOrderJetCoeff_comp_frameJetCoeff (hΨΦ z)]
  exact ContinuousLinearMap.comp_assoc _ _ _

include hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ hAC in
/-- The operator `∂s + A ∂t + C` read in the frame `Φ` is `∂s + A ∂t + C` composed with
isomorphisms on both sides. -/
private theorem exists_jetOperator_firstOrderJetCoeff_frame_eq_comp :
    ∃ (e : Lp W 2 stripMeasure ≃L[ℝ] Lp V 2 stripMeasure) (e' : H1 V ≃L[ℝ] H1 W),
      (jetOperator stripMeasure fun z ↦ firstOrderJetCoeff ((Ψ z).comp ((A z).comp (Φ z)))
          ((Ψ z).comp ((C z).comp (Φ z) + fderiv ℝ Φ z (1, 0) +
            (A z).comp (fderiv ℝ Φ z (0, 1))))).comp (H1 V).subtypeL =
        (e : Lp W 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure).comp
          (((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (A z) (C z)).comp
            (H1 W).subtypeL).comp (e' : H1 V →L[ℝ] H1 W)) := by
  have hΦL : MemLp Φ ∞ stripMeasure :=
    memLp_top_of_bound hΦ.continuous.aestronglyMeasurable B (ae_of_all _ hΦB)
  have hΨL : MemLp Ψ ∞ stripMeasure :=
    memLp_top_of_bound hΨ.continuous.aestronglyMeasurable B (ae_of_all _ hΨB)
  obtain ⟨e, he⟩ := Lp.isInvertible_operatorMultiplication_of_comp_eq_id (p := 2) hΨL hΦL
    (ae_of_all _ hΦΨ) (ae_of_all _ hΨΦ)
  refine ⟨e, frameEquiv hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ, ?_⟩
  rw [jetOperator_firstOrderJetCoeff_frame_eq hΦ hΦp hΦB hΦ'B hΨΦ hAC hΨL, he, coe_frameEquiv]

include hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ hAC in
/-- **Fredholmness of `∂s + A ∂t + C` does not depend on the frame.** For a frame `Φ` with inverse
frame `Ψ`, the operator `∂s + A ∂t + C` on `W^{1,2}(ℝ × S¹, W)` is Fredholm exactly when its
reading in the frame, `∂s + (Ψ A Φ) ∂t + Ψ (C Φ + ∂s Φ + A ∂t Φ)` on `W^{1,2}(ℝ × S¹, V)`, is. -/
theorem isFredholm_jetOperator_firstOrderJetCoeff_frame_iff :
    ((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff ((Ψ z).comp ((A z).comp (Φ z)))
        ((Ψ z).comp ((C z).comp (Φ z) + fderiv ℝ Φ z (1, 0) +
          (A z).comp (fderiv ℝ Φ z (0, 1))))).comp (H1 V).subtypeL).IsFredholm ↔
      ((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (A z) (C z)).comp
        (H1 W).subtypeL).IsFredholm := by
  obtain ⟨e, e', h⟩ := exists_jetOperator_firstOrderJetCoeff_frame_eq_comp hΦ hΦp hΦB hΦ'B hΨ hΨp
    hΨB hΨ'B hΨΦ hΦΨ hAC
  rw [h, ContinuousLinearMap.isFredholm_equiv_comp, ContinuousLinearMap.isFredholm_comp_equiv]

include hΦ hΦp hΦB hΦ'B hΨ hΨp hΨB hΨ'B hΨΦ hΦΨ hAC in
/-- **The index of `∂s + A ∂t + C` does not depend on the frame.** For a frame `Φ` with inverse
frame `Ψ`, the operator `∂s + A ∂t + C` on `W^{1,2}(ℝ × S¹, W)` and its reading in the frame,
`∂s + (Ψ A Φ) ∂t + Ψ (C Φ + ∂s Φ + A ∂t Φ)` on `W^{1,2}(ℝ × S¹, V)`, have the same index. -/
theorem index_jetOperator_firstOrderJetCoeff_frame :
    ((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff ((Ψ z).comp ((A z).comp (Φ z)))
        ((Ψ z).comp ((C z).comp (Φ z) + fderiv ℝ Φ z (1, 0) +
          (A z).comp (fderiv ℝ Φ z (0, 1))))).comp (H1 V).subtypeL).index =
      ((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (A z) (C z)).comp
        (H1 W).subtypeL).index := by
  obtain ⟨e, e', h⟩ := exists_jetOperator_firstOrderJetCoeff_frame_eq_comp hΦ hΦp hΦB hΦ'B hΨ hΨp
    hΨB hΨ'B hΨΦ hΦΨ hAC
  rw [h, ContinuousLinearMap.index_equiv_comp, ContinuousLinearMap.index_comp_equiv]

end FirstOrder

/-! ### Loops of frames -/

section Loop

variable [CompleteSpace V] {Φ : ℝ → V →L[ℝ] W} (hΦ : ContDiff ℝ 2 Φ) (hΦp : Periodic Φ 1)
  (hΦi : ∀ t, (Φ t).IsInvertible) {J : ℝ → W →L[ℝ] W} {J₀ : ℝ → V →L[ℝ] V}
  (hJ : ∀ t, (J t).comp (Φ t) = (Φ t).comp (J₀ t)) {S : ℝ × ℝ → W →L[ℝ] W}

omit [CompleteSpace V] in
include hΦ hΦi hJ in
/-- Reading `∂s + J_t (∂t - S)` in a loop of frames `Φ_t` intertwining `J₀_t` with `J_t` gives
`∂s + J₀_t (∂t - S_Φ)`, with `S_Φ = Φ⁻¹ (S Φ - Φ')` the trivialized coefficient. -/
private theorem firstOrderJetCoeff_frame_loop_eq (z : ℝ × ℝ) :
    firstOrderJetCoeff ((Φ z.2).inverse.comp ((J z.2).comp (Φ z.2)))
        ((Φ z.2).inverse.comp ((-(J z.2).comp (S z)).comp (Φ z.2) +
          fderiv ℝ (fun w : ℝ × ℝ ↦ Φ w.2) z (1, 0) +
          (J z.2).comp (fderiv ℝ (fun w : ℝ × ℝ ↦ Φ w.2) z (0, 1)))) =
      firstOrderJetCoeff (J₀ z.2)
        (-(J₀ z.2).comp (trivializedCoeff Φ (fun t ↦ S (z.1, t)) z.2)) := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ Φ w.2)
      ((fderiv ℝ Φ z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    ((hΦ.differentiable (by norm_num)) z.2).hasFDerivAt.comp z hasFDerivAt_snd
  have hinv (v : V) : (Φ z.2).inverse (Φ z.2 v) = v := (hΦi z.2).inverse_apply_self v
  -- `Φ⁻¹ J = J₀ Φ⁻¹`, from `J Φ = Φ J₀`.
  have hJ' (w : W) : (Φ z.2).inverse (J z.2 w) = J₀ z.2 ((Φ z.2).inverse w) := by
    conv_lhs => rw [← (hΦi z.2).self_apply_inverse w]
    rw [← ContinuousLinearMap.comp_apply (J z.2), hJ, ContinuousLinearMap.comp_apply, hinv]
  rw [hd.fderiv]
  congr 1 <;> refine ContinuousLinearMap.ext fun v ↦ ?_
  · simp [hJ', hinv]
  · simp only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', fderiv_eq_smul_deriv, zero_smul, add_zero, one_smul,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_neg, add_apply, neg_apply, hJ',
      trivializedCoeff_apply, Prod.mk.eta, map_sub, neg_sub]
    abel

include hΦ hΦp hΦi hJ in
/-- In a loop of frames, `∂s + J₀_t (∂t - S_Φ)` is `∂s + J_t (∂t - S)` composed with isomorphisms
on both sides. -/
private theorem exists_jetOperator_firstOrderJetCoeff_trivializedCoeff_eq_comp
    (hM : MemLp (fun z ↦ firstOrderJetCoeff (J z.2) (-(J z.2).comp (S z))) ∞ stripMeasure) :
    ∃ (e : Lp W 2 stripMeasure ≃L[ℝ] Lp V 2 stripMeasure) (e' : H1 V ≃L[ℝ] H1 W),
      (jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (J₀ z.2)
          (-(J₀ z.2).comp (trivializedCoeff Φ (fun t ↦ S (z.1, t)) z.2))).comp (H1 V).subtypeL =
        (e : Lp W 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure).comp
          (((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (J z.2) (-(J z.2).comp (S z))).comp
            (H1 W).subtypeL).comp (e' : H1 V →L[ℝ] H1 W)) := by
  have hΨ : ContDiff ℝ 2 fun t ↦ (Φ t).inverse := hΦ.clm_inverse hΦi
  have hΨp : Periodic (fun t ↦ (Φ t).inverse) 1 := fun t ↦ by simp only [hΦp t]
  obtain ⟨B₁, hB₁⟩ :=
    hΦp.exists_forall_norm_le_comp_snd (E := ℝ) one_ne_zero (hΦ.of_le one_le_two)
  obtain ⟨B₂, hB₂⟩ :=
    hΨp.exists_forall_norm_le_comp_snd (E := ℝ) one_ne_zero (hΨ.of_le one_le_two)
  rw [← funext (firstOrderJetCoeff_frame_loop_eq hΦ hΦi hJ (S := S))]
  exact exists_jetOperator_firstOrderJetCoeff_frame_eq_comp (B := max B₁ B₂)
    (hΦ.comp contDiff_snd) (fun _ t ↦ hΦp t) (fun z ↦ (hB₁ z).1.trans (le_max_left _ _))
    (fun z ↦ (hB₁ z).2.trans (le_max_left _ _)) (hΨ.comp contDiff_snd) (fun _ t ↦ hΨp t)
    (fun z ↦ (hB₂ z).1.trans (le_max_right _ _)) (fun z ↦ (hB₂ z).2.trans (le_max_right _ _))
    (fun z ↦ (hΦi z.2).inverse_comp_self) (fun z ↦ (hΦi z.2).self_comp_inverse) hM

include hΦ hΦp hΦi hJ in
/-- **Fredholmness of cylinder operators in a loop of frames.** Let `Φ_t` be a `C²` loop of
invertible maps `V → W` of period one, intertwining loops of operators `J₀_t` on `V` and `J_t` on
`W`. The operator `∂s + J_t (∂t - S(s, t))` on `W^{1,2}(ℝ × S¹, W)` is Fredholm exactly when the
operator `∂s + J₀_t (∂t - S_Φ(s, t))` on `W^{1,2}(ℝ × S¹, V)` is, where
`S_Φ(s, ·) = Φ⁻¹ (S(s, ·) Φ - Φ')` is the trivialization of `S(s, ·)` along `Φ`
(`TauCeti.trivializedCoeff`). -/
theorem isFredholm_jetOperator_firstOrderJetCoeff_trivializedCoeff_iff
    (hM : MemLp (fun z ↦ firstOrderJetCoeff (J z.2) (-(J z.2).comp (S z))) ∞ stripMeasure) :
    ((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (J₀ z.2)
        (-(J₀ z.2).comp (trivializedCoeff Φ (fun t ↦ S (z.1, t)) z.2))).comp
          (H1 V).subtypeL).IsFredholm ↔
      ((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (J z.2) (-(J z.2).comp (S z))).comp
        (H1 W).subtypeL).IsFredholm := by
  obtain ⟨e, e', h⟩ :=
    exists_jetOperator_firstOrderJetCoeff_trivializedCoeff_eq_comp hΦ hΦp hΦi hJ hM
  rw [h, ContinuousLinearMap.isFredholm_equiv_comp, ContinuousLinearMap.isFredholm_comp_equiv]

include hΦ hΦp hΦi hJ in
/-- **The index of cylinder operators in a loop of frames.** Let `Φ_t` be a `C²` loop of
invertible maps `V → W` of period one, intertwining loops of operators `J₀_t` on `V` and `J_t` on
`W`. The operator `∂s + J_t (∂t - S(s, t))` on `W^{1,2}(ℝ × S¹, W)` and the operator
`∂s + J₀_t (∂t - S_Φ(s, t))` on `W^{1,2}(ℝ × S¹, V)`, where `S_Φ(s, ·) = Φ⁻¹ (S(s, ·) Φ - Φ')` is
the trivialization of `S(s, ·)` along `Φ` (`TauCeti.trivializedCoeff`), have the same index. -/
theorem index_jetOperator_firstOrderJetCoeff_trivializedCoeff
    (hM : MemLp (fun z ↦ firstOrderJetCoeff (J z.2) (-(J z.2).comp (S z))) ∞ stripMeasure) :
    ((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (J₀ z.2)
        (-(J₀ z.2).comp (trivializedCoeff Φ (fun t ↦ S (z.1, t)) z.2))).comp
          (H1 V).subtypeL).index =
      ((jetOperator stripMeasure fun z ↦ firstOrderJetCoeff (J z.2) (-(J z.2).comp (S z))).comp
        (H1 W).subtypeL).index := by
  obtain ⟨e, e', h⟩ :=
    exists_jetOperator_firstOrderJetCoeff_trivializedCoeff_eq_comp hΦ hΦp hΦi hJ hM
  rw [h, ContinuousLinearMap.index_equiv_comp, ContinuousLinearMap.index_comp_equiv]

end Loop

end TauCeti.CylinderSobolev
