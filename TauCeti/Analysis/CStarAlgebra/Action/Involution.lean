/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import TauCeti.MeasureTheory.Group.ModularCharacter
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The twisted involution on compactly supported coefficient functions

For a point-norm continuous action `α` on a possibly nonunital C⋆-algebra, the twisted
involution sends `f` to `s ↦ c(s) • α s (star (f s⁻¹))`, where `c` is Mathlib's modular
character. It preserves continuity and compact support, is conjugate-linear, and squares
to the identity. Its support is exactly the inverse of the original support.

The operation is named rather than installed as a `Star` instance: compactly supported
continuous maps already carry a different, pointwise star operation. These functions and
this involution are the dense coefficient space for crossed-product convolution algebras.
Compatibility with twisted convolution is proved in
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.Algebra`; this file says nothing about the
`L¹` norm.

The convention follows Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2:
Mathlib's `c(s)` is Williams's `Δ(s)⁻¹`.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal Pointwise CompactlySupported

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [NonUnitalCStarAlgebra A]

/-- The twisted, conjugate-linear involution on compactly supported coefficient functions. -/
def twistedInvolution (α : CStarAction G A) : C_c(G, A) →ₗ⋆[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s := ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹))
      continuous_toFun :=
        (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
          continuous_modularCharacter)).smul
            (α.continuous_apply continuous_id (f.continuous.comp continuous_inv).star)
      hasCompactSupport' :=
        (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mono (by
          intro s hs
          have hz : f s⁻¹ ≠ 0 := by
            intro hz
            exact hs (by simp [hz])
          exact hz) }
  map_add' f g := by
    ext s
    simp [map_add, smul_add]
  map_smul' z f := by
    ext s
    simp only [CompactlySupportedContinuousMap.smul_apply, star_smul, map_smul,
      starRingEnd_apply]
    exact smul_comm _ _ _

/-- The pointwise formula, using the inverse of Williams's modular function. -/
@[simp]
theorem twistedInvolution_apply (α : CStarAction G A) (f : C_c(G, A)) (s : G) :
    α.twistedInvolution f s = ((Measure.modularCharacter s : ℝ) : ℂ) •
      α s (star (f s⁻¹)) :=
  (rfl)

/-- Applying the twisted involution twice recovers the original coefficient function. -/
@[simp]
theorem twistedInvolution_twistedInvolution (α : CStarAction G A) (f : C_c(G, A)) :
    α.twistedInvolution (α.twistedInvolution f) = f := by
  ext s
  have hc : Measure.modularCharacter s * Measure.modularCharacter s⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hc' : ((Measure.modularCharacter s : ℝ) : ℂ) *
      ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hc
  simp only [twistedInvolution_apply, inv_inv, star_smul, map_star, star_star,
    map_smul, Complex.star_def, Complex.conj_ofReal,
    apply_inv_apply, smul_smul, hc', one_smul]

/-- The norm of an involuted coefficient includes precisely the modular weight. -/
@[simp↓]
theorem norm_twistedInvolution_apply (α : CStarAction G A) (f : C_c(G, A)) (s : G) :
    ‖α.twistedInvolution f s‖ = (Measure.modularCharacter s : ℝ) * ‖f s⁻¹‖ := by
  simp [norm_smul, StarAlgEquiv.norm_map]

/-- Involution vanishes at `s` exactly when the original function vanishes at `s⁻¹`. -/
@[simp↓]
theorem twistedInvolution_apply_eq_zero_iff (α : CStarAction G A) (f : C_c(G, A)) (s : G) :
    α.twistedInvolution f s = 0 ↔ f s⁻¹ = 0 := by
  rw [← norm_eq_zero, norm_twistedInvolution_apply]
  have hc : (Measure.modularCharacter s : ℝ) ≠ 0 := by
    rw [modularCharacter_apply]
    exact NNReal.coe_ne_zero.mpr (Measure.modularCharacterFun_pos s).ne'
  simp [hc]

/-- The support of the twisted involution is the inverse support. -/
@[simp]
theorem support_twistedInvolution (α : CStarAction G A) (f : C_c(G, A)) :
    Function.support (α.twistedInvolution f) = (Function.support f)⁻¹ := by
  ext s
  exact not_congr (α.twistedInvolution_apply_eq_zero_iff f s)

/-- The topological support of the twisted involution is the inverse topological support. -/
@[simp]
theorem tsupport_twistedInvolution (α : CStarAction G A) (f : C_c(G, A)) :
    tsupport (α.twistedInvolution f) = (tsupport f)⁻¹ := by
  simp only [tsupport, support_twistedInvolution, ← inv_closure]

end TauCeti.CStarAction
