/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UnitDisc.PuncturedManifold
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# The local coordinate at a cusp

For a positive width `w`, the usual local coordinate
`z ↦ exp (2 π i z / w)` maps the upper half-plane onto the punctured unit disc. Its fibres
are exactly the orbits of the translation subgroup `w ℤ`. Consequently it identifies the orbit
quotient of the upper half-plane by these translations with the punctured unit disc.

The construction reuses Mathlib's `Function.Periodic.qParam`; in particular, the normalization
of `2 π i / w` agrees with the local parameter used for modular-form q-expansions.

## Main declarations

* `TauCeti.UpperHalfPlane.qParamPuncturedUnitDisc`: the width-`w` q-parameter with its range
  bundled.
* `TauCeti.UpperHalfPlane.invQParamUpperHalfPlane`: a chosen logarithmic lift/right inverse,
  valued in the upper half-plane.
* `TauCeti.UpperHalfPlane.qParamPuncturedUnitDisc_eq_iff`: two lifts have the same q-parameter
  exactly when they differ by an integral multiple of the width.
* `TauCeti.UpperHalfPlane.cuspTranslationQuotientHomeomorph`: the resulting homeomorphism from
  the translation-orbit quotient to the punctured unit disc.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Complex Filter Function MulAction UpperHalfPlane
open scoped Complex.UnitDisc Manifold Real Topology

namespace TauCeti.UpperHalfPlane

local notation "𝔢" => Function.Periodic.qParam

/-- The q-parameter of positive width, regarded as a map from the upper half-plane to the
punctured unit disc. -/
def qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) (z : ℍ) : {q : 𝔻 // q ≠ 0} :=
  ⟨Complex.UnitDisc.mk (𝔢 w z) (Function.Periodic.norm_qParam_lt_one hw z.im_pos),
    fun h ↦ Function.Periodic.qParam_ne_zero (h := w) z <| by
      simpa using congrArg ((↑) : 𝔻 → ℂ) h⟩

@[simp]
theorem coe_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) (z : ℍ) :
    (((qParamPuncturedUnitDisc w hw z : {q : 𝔻 // q ≠ 0}) : 𝔻) : ℂ) = 𝔢 w z :=
  (rfl)

/-- The logarithmic lift of a point of the punctured unit disc to the upper half-plane. -/
def invQParamUpperHalfPlane (w : ℝ) (hw : 0 < w) (q : {q : 𝔻 // q ≠ 0}) : ℍ :=
  ⟨Function.Periodic.invQParam w q,
    Function.Periodic.im_invQParam_pos_of_norm_lt_one hw q.1.norm_lt_one <|
      fun h ↦ q.2 (Complex.UnitDisc.coe_injective h)⟩

@[simp]
theorem coe_invQParamUpperHalfPlane (w : ℝ) (hw : 0 < w) (q : {q : 𝔻 // q ≠ 0}) :
    (invQParamUpperHalfPlane w hw q : ℂ) = Function.Periodic.invQParam w q :=
  (rfl)

@[simp]
theorem qParamPuncturedUnitDisc_invQParamUpperHalfPlane (w : ℝ) (hw : 0 < w)
    (q : {q : 𝔻 // q ≠ 0}) :
    qParamPuncturedUnitDisc w hw (invQParamUpperHalfPlane w hw q) = q := by
  apply Subtype.ext
  apply Complex.UnitDisc.coe_injective
  rw [coe_qParamPuncturedUnitDisc, coe_invQParamUpperHalfPlane]
  exact Function.Periodic.qParam_right_inv hw.ne' fun h ↦
    q.2 (Complex.UnitDisc.coe_injective h)

/-- Every nonzero point of the unit disc has a logarithmic lift to the upper half-plane. -/
theorem qParamPuncturedUnitDisc_surjective (w : ℝ) (hw : 0 < w) :
    Function.Surjective (qParamPuncturedUnitDisc w hw) := fun q ↦
  ⟨invQParamUpperHalfPlane w hw q, qParamPuncturedUnitDisc_invQParamUpperHalfPlane w hw q⟩

private theorem continuous_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    Continuous (qParamPuncturedUnitDisc w hw) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact ((Function.Periodic.continuous_qParam (h := w)).comp continuous_coe).congr
    (fun z ↦ (coe_qParamPuncturedUnitDisc w hw z).symm)

/-- The q-parameter is holomorphic as a map into the punctured unit disc. -/
theorem mdifferentiable_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qParamPuncturedUnitDisc w hw) := by
  have h : MDiff (fun z : ℍ ↦ 𝔢 w z) :=
    Function.Periodic.differentiable_qParam.mdifferentiable.comp
    UpperHalfPlane.mdifferentiable_coe
  intro z
  apply mdifferentiableAt_iff_target.mpr
  constructor
  · exact (continuous_qParamPuncturedUnitDisc w hw).continuousAt
  · simpa only [TauCeti.Complex.UnitDisc.extChartAt_coe_punctured,
      Function.comp_def, coe_qParamPuncturedUnitDisc] using h z

/-- A horodisc is the inverse image of the punctured disc of the corresponding radius. -/
theorem norm_qParamPuncturedUnitDisc_lt_iff (w : ℝ) (hw : 0 < w) (A : ℝ) (z : ℍ) :
    ‖((qParamPuncturedUnitDisc w hw z : 𝔻) : ℂ)‖ < Real.exp (-2 * Real.pi * A / w) ↔
      A < z.im := by
  rw [coe_qParamPuncturedUnitDisc]
  exact Function.Periodic.norm_qParam_lt_iff hw A z

/-- The image of a horodisc is the punctured disc of the corresponding exponential radius. -/
theorem image_qParamPuncturedUnitDisc_setOf_lt_im (w : ℝ) (hw : 0 < w) (A : ℝ) :
    qParamPuncturedUnitDisc w hw '' {z : ℍ | A < z.im} =
      {q : {q : 𝔻 // q ≠ 0} | ‖((q : 𝔻) : ℂ)‖ < Real.exp (-2 * Real.pi * A / w)} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (norm_qParamPuncturedUnitDisc_lt_iff w hw A z).mpr hz
  · intro hq
    obtain ⟨z, rfl⟩ := qParamPuncturedUnitDisc_surjective w hw q
    exact ⟨z, (norm_qParamPuncturedUnitDisc_lt_iff w hw A z).mp hq, rfl⟩

/-- The q-parameter tends to zero through nonzero values as the height tends to infinity. -/
theorem tendsto_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    Tendsto (fun z : ℍ ↦ ((qParamPuncturedUnitDisc w hw z : 𝔻) : ℂ))
      atImInfty (𝓝[≠] 0) := by
  simp only [coe_qParamPuncturedUnitDisc]
  exact (Function.Periodic.qParam_tendsto hw).comp
    (tendsto_comap_iff.mpr tendsto_comap)

/-- Multiplying by the `k`th integer power of the q-parameter cancels the opposing exponential
comparison and gives a function bounded at `i∞`. For positive width, nonnegative `k` controls
growth, while negative `k` controls decay. -/
theorem isBoundedAtImInfty_qParam_zpow_mul_of_isBigO (w : ℝ) (k : ℤ) {f : ℍ → ℂ}
    (hf : f =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / w)) :
    IsBoundedAtImInfty fun z ↦ Function.Periodic.qParam w z ^ k * f z := by
  have hq : (fun z : ℍ ↦ Function.Periodic.qParam w z ^ k) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * (k : ℝ) * z.im / w) := by
    apply Asymptotics.isBigO_of_le
    intro z
    simp only [norm_zpow, Function.Periodic.norm_qParam, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [← Real.rpow_intCast, ← Real.exp_mul]
    apply le_of_eq
    congr 1
    simp only [UpperHalfPlane.coe_im]
    ring
  rw [IsBoundedAtImInfty, BoundedAtFilter]
  refine (hq.mul hf).congr_right fun z ↦ ?_
  simp only [Pi.one_apply, ← Real.exp_add]
  convert Real.exp_zero using 1
  ring_nf

/-- Two points of the upper half-plane have the same width-`w` q-parameter exactly when one is
an integral-width translate of the other. -/
theorem qParamPuncturedUnitDisc_eq_iff (w : ℝ) (hw : 0 < w) (z z' : ℍ) :
    qParamPuncturedUnitDisc w hw z = qParamPuncturedUnitDisc w hw z' ↔
      ∃ n : ℤ, z = ((n : ℝ) * w) +ᵥ z' := by
  constructor
  · intro h
    have hq : 𝔢 w z = 𝔢 w z' := by
      simpa only [← coe_qParamPuncturedUnitDisc w hw] using
        congrArg (fun q : {q : 𝔻 // q ≠ 0} ↦ (((q : 𝔻) : ℂ))) h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp <| by
      simpa only [Function.Periodic.qParam] using hq
    refine ⟨n, UpperHalfPlane.coe_injective ?_⟩
    rw [UpperHalfPlane.coe_vadd]
    push_cast at hn ⊢
    field_simp [hw.ne'] at hn ⊢
    linear_combination hn
  · rintro ⟨n, rfl⟩
    apply Subtype.ext
    apply Complex.UnitDisc.coe_injective
    rw [coe_qParamPuncturedUnitDisc, coe_qParamPuncturedUnitDisc,
      Function.Periodic.qParam]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨n, ?_⟩
    rw [UpperHalfPlane.coe_vadd]
    push_cast
    field_simp [hw.ne']
    ring_nf

/-- The orbit quotient of the upper half-plane by translations through integral multiples of a
positive width. -/
abbrev CuspTranslationQuotient (w : ℝ) :=
  AddAction.orbitRel.Quotient (AddSubgroup.zmultiples w) ℍ

/-- The orbit relation for integral-width translations is exactly equality of q-parameters. -/
theorem cuspTranslationOrbitRel_iff_qParam_eq (w : ℝ) (hw : 0 < w) (z z' : ℍ) :
    AddAction.orbitRel (AddSubgroup.zmultiples w) ℍ z z' ↔
      qParamPuncturedUnitDisc w hw z = qParamPuncturedUnitDisc w hw z' := by
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff,
    qParamPuncturedUnitDisc_eq_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
    exact ⟨n, by simp [zsmul_eq_mul]⟩
  · rintro ⟨n, rfl⟩
    refine ⟨⟨(n : ℝ) * w, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp [zsmul_eq_mul]⟩⟩, ?_⟩
    rfl

private theorem isOpenMap_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    IsOpenMap (qParamPuncturedUnitDisc w hw) := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I / w) ≠ 0 :=
    div_ne_zero Complex.two_pi_I_ne_zero (Complex.ofReal_ne_zero.mpr hw.ne')
  have hlinear : IsOpenMap (fun z : ℂ ↦ (2 * (Real.pi : ℂ) * Complex.I / w) * z) :=
    (Homeomorph.mulLeft₀ _ hc).isOpenMap
  have hq : IsOpenMap (𝔢 w) := by
    convert Complex.isOpenMap_exp.comp hlinear using 1
    ext z
    simp only [Function.comp_apply, Function.Periodic.qParam]
    ring_nf
  have hqℍ : IsOpenMap (fun z : ℍ ↦ 𝔢 w z) :=
    hq.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
  exact (hqℍ.subtype_mk _).subtype_mk _

/-- The q-parameter from the upper half-plane to the punctured unit disc is an open quotient
map. -/
theorem isOpenQuotientMap_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    IsOpenQuotientMap (qParamPuncturedUnitDisc w hw) :=
  ⟨qParamPuncturedUnitDisc_surjective w hw, continuous_qParamPuncturedUnitDisc w hw,
    isOpenMap_qParamPuncturedUnitDisc w hw⟩

/-- The q-parameter descended to the width-translation quotient. -/
def cuspTranslationQuotientMap (w : ℝ) (hw : 0 < w) :
    CuspTranslationQuotient w → {q : 𝔻 // q ≠ 0} :=
  Quotient.lift (qParamPuncturedUnitDisc w hw) fun z z' h ↦
    (cuspTranslationOrbitRel_iff_qParam_eq w hw z z').mp h

@[simp]
theorem cuspTranslationQuotientMap_mk (w : ℝ) (hw : 0 < w) (z : ℍ) :
    cuspTranslationQuotientMap w hw (Quotient.mk'' z) = qParamPuncturedUnitDisc w hw z :=
  (rfl)

/-- The descended q-parameter is a homeomorphism. -/
theorem isHomeomorph_cuspTranslationQuotientMap (w : ℝ) (hw : 0 < w) :
    IsHomeomorph (cuspTranslationQuotientMap w hw) := by
  have hcomp : (cuspTranslationQuotientMap w hw) ∘
      (Quotient.mk (AddAction.orbitRel (AddSubgroup.zmultiples w) ℍ) :
        ℍ → CuspTranslationQuotient w) = qParamPuncturedUnitDisc w hw := by
    funext z
    exact cuspTranslationQuotientMap_mk w hw z
  have hquot : Topology.IsQuotientMap (cuspTranslationQuotientMap w hw) :=
    isQuotientMap_quotient_mk'.of_comp_isQuotientMap <| hcomp.symm ▸
      (isOpenQuotientMap_qParamPuncturedUnitDisc w hw).isQuotientMap
  apply isHomeomorph_iff_isQuotientMap_injective.mpr
  refine ⟨hquot, fun x y hxy ↦ ?_⟩
  induction x, y using Quotient.inductionOn₂ with
  | _ z z' =>
    apply Quotient.sound
    exact (cuspTranslationOrbitRel_iff_qParam_eq w hw z z').mpr hxy

/-- The q-parameter identifies the width-translation quotient of the upper half-plane
homeomorphically with the punctured unit disc. -/
noncomputable def cuspTranslationQuotientHomeomorph (w : ℝ) (hw : 0 < w) :
    CuspTranslationQuotient w ≃ₜ {q : 𝔻 // q ≠ 0} :=
  (isHomeomorph_cuspTranslationQuotientMap w hw).homeomorph _

@[simp]
theorem cuspTranslationQuotientHomeomorph_mk (w : ℝ) (hw : 0 < w) (z : ℍ) :
    cuspTranslationQuotientHomeomorph w hw (Quotient.mk'' z) =
      qParamPuncturedUnitDisc w hw z := by
  rw [cuspTranslationQuotientHomeomorph]
  rfl

@[simp]
theorem cuspTranslationQuotientHomeomorph_symm_apply (w : ℝ) (hw : 0 < w)
    (q : {q : 𝔻 // q ≠ 0}) :
    (cuspTranslationQuotientHomeomorph w hw).symm q =
      Quotient.mk'' (invQParamUpperHalfPlane w hw q) := by
  apply (cuspTranslationQuotientHomeomorph w hw).injective
  simp

end TauCeti.UpperHalfPlane
