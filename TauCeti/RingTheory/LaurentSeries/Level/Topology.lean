/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.KaehlerDifferential

/-!
# Topology and continuous trace of ramified-level one-forms

The ramified level `L = K⸨u⸩`, with `t = u ^ d`, carries the valuation topology in the
variable `u`. Its continuous one-forms carry the same topology through `g du ↦ g`.
This file puts these topologies on the level carriers and proves continuity of the
pullback and trace of one-forms. In particular the residue identity for trace can be
used together with valuation limits, not just as an algebraic identity.

The coefficient trace is continuous in every characteristic: it is `d` times the
exponent-congruence projection `contract d · 0`. For the trace of one-forms we assume
that `d` is nonzero in `K`, exactly the separability condition for the level extension.
Neither construction uses a topology on the coefficient field.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968).
-/

public section

open Topology
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

variable {K : Type*} [Field K] {d : ℕ+}

/-- The valuation topology of the level, read in its Laurent variable `u`. -/
noncomputable instance : TopologicalSpace (Level K d) :=
  .induced (ringEquivLaurentSeries K d) inferInstance

/-- The topology of a level is induced by its Laurent-series coordinate. -/
theorem isInducing_ringEquivLaurentSeries : IsInducing (ringEquivLaurentSeries K d) :=
  .induced _

variable (K d) in
/-- Reading a ramified level in its Laurent variable is a homeomorphism. -/
noncomputable def homeomorphLaurentSeries : Level K d ≃ₜ K⸨X⸩ :=
  (ringEquivLaurentSeries K d).toEquiv.toHomeomorphOfIsInducing
    isInducing_ringEquivLaurentSeries

@[simp]
theorem homeomorphLaurentSeries_apply (x : Level K d) :
    homeomorphLaurentSeries K d x = ringEquivLaurentSeries K d x := (rfl)

@[simp]
theorem homeomorphLaurentSeries_symm_apply (f : K⸨X⸩) :
    (homeomorphLaurentSeries K d).symm f = (ringEquivLaurentSeries K d).symm f := (rfl)

instance : T2Space (Level K d) := (homeomorphLaurentSeries K d).isEmbedding.t2Space

instance : IsTopologicalRing (Level K d) := by
  let := isInducing_ringEquivLaurentSeries.isTopologicalAddGroup
    (ringEquivLaurentSeries K d).toAddMonoidHom
  let := isInducing_ringEquivLaurentSeries.continuousMul (ringEquivLaurentSeries K d)
  exact
    { toContinuousAdd := inferInstance
      toContinuousMul := inferInstance
      toContinuousNeg := inferInstance }

/-- The inclusion of the base field into a ramified level is continuous. -/
theorem continuous_algebraMap : Continuous (Algebra.algebraMap K⸨X⸩ (Level K d)) := by
  apply isInducing_ringEquivLaurentSeries.continuous_iff.mpr
  simpa only [Function.comp_def, algebraMap_apply,
    ← TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand] using
    (TauCeti.LaurentSeries.continuous_substAlgHom (K := K)
      (φ := PowerSeries.X ^ (d : ℕ)) (by simp) (pow_ne_zero _ PowerSeries.X_ne_zero))

instance : ContinuousSMul K⸨X⸩ (Level K d) :=
  continuousSMul_of_algebraMap _ _ continuous_algebraMap

/-- The coefficient trace of a ramified level is continuous, also in inseparable degrees. -/
theorem continuous_trace : Continuous (Algebra.trace K⸨X⸩ (Level K d)) := by
  exact (((_root_.LaurentSeries.continuous_contract (K := K) d 0).comp
    (homeomorphLaurentSeries K d).continuous).nsmul (d : ℕ)).congr
      fun x ↦ (trace_eq_nsmul_contract d x).symm

namespace ContinuousKaehlerDifferential

/-- One-forms of a level have the valuation topology of their coefficient in `du`. -/
noncomputable instance : TopologicalSpace (Level.ContinuousKaehlerDifferential K d) :=
  .induced (equivLevel K d) inferInstance

/-- The coefficient in `du` induces the topology on level one-forms. -/
theorem isInducing_equivLevel : IsInducing (equivLevel K d) := .induced _

variable (K d) in
/-- The valuation coordinate `g du ↦ g` is a continuous linear equivalence. -/
noncomputable def continuousEquivLevel : Level.ContinuousKaehlerDifferential K d ≃L[Level K d]
    Level K d where
  toLinearEquiv := equivLevel K d
  continuous_toFun := isInducing_equivLevel.continuous
  continuous_invFun := ((equivLevel K d).toEquiv.toHomeomorphOfIsInducing
    isInducing_equivLevel).symm.continuous

@[simp]
theorem continuousEquivLevel_apply (ω : Level.ContinuousKaehlerDifferential K d) :
    continuousEquivLevel K d ω = equivLevel K d ω := (rfl)

@[simp]
theorem continuousEquivLevel_symm_apply (x : Level K d) :
    (continuousEquivLevel K d).symm x = (equivLevel K d).symm x := (rfl)

/-- The transported valuation topology is the module topology over the level field. -/
instance : IsModuleTopology (Level K d) (Level.ContinuousKaehlerDifferential K d) :=
  IsModuleTopology.iso (continuousEquivLevel K d).symm

instance : T2Space (Level.ContinuousKaehlerDifferential K d) :=
  (continuousEquivLevel K d).toHomeomorph.isEmbedding.t2Space

instance : IsTopologicalAddGroup (Level.ContinuousKaehlerDifferential K d) :=
  IsModuleTopology.isTopologicalAddGroup (Level K d) _

variable (K d) in
/-- Reading level one-forms as ordinary continuous Laurent one-forms is a homeomorphism. -/
noncomputable def homeomorphForm : Level.ContinuousKaehlerDifferential K d ≃ₜ
    TauCeti.ContinuousKaehlerDifferential K :=
  (continuousEquivLevel K d).toHomeomorph.trans <|
    (homeomorphLaurentSeries K d).trans
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toHomeomorph.symm

@[simp]
theorem homeomorphForm_apply (ω : Level.ContinuousKaehlerDifferential K d) :
    homeomorphForm K d ω = addEquivContinuousKaehlerDifferential K d ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  simp [homeomorphForm]

/-- Reading an ordinary continuous Laurent one-form in the level variable inverts
`homeomorphForm`. -/
@[simp]
theorem homeomorphForm_symm_apply (ω : TauCeti.ContinuousKaehlerDifferential K) :
    (homeomorphForm K d).symm ω =
      (addEquivContinuousKaehlerDifferential K d).symm ω := by
  apply (homeomorphForm K d).injective
  simp

/-- Pulling back one-forms along `t = u ^ d` is continuous, in every characteristic. -/
theorem continuous_map : Continuous (map K d) := by
  apply (homeomorphForm K d).comp_continuous_iff.mp
  simpa only [Function.comp_def, homeomorphForm_apply,
    addEquivContinuousKaehlerDifferential_map] using
    (TauCeti.ContinuousKaehlerDifferential.continuous_subst (K := K)
      (φ := PowerSeries.X ^ (d : ℕ)) (by simp) (pow_ne_zero _ PowerSeries.X_ne_zero))

section Separable

variable [NeZero ((d : ℕ) : K)]

/-- The trace of continuous one-forms of a finite separable ramified level is continuous. -/
theorem continuous_trace : Continuous (trace K d) := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries
    K).toHomeomorph.comp_continuous_iff.mp
  exact (Level.continuous_trace.comp
    ((continuousEquivLevel K d).continuous.mul (continuous_const (y :=
      ((ringEquivLaurentSeries K d).symm
        (_root_.LaurentSeries.derivative K (HahnSeries.single (d : ℤ) 1)))⁻¹)))).congr
          fun ω ↦ by
            simpa only [Function.comp_apply, Pi.mul_apply, continuousEquivLevel_apply,
              ContinuousLinearEquiv.coe_toHomeomorph, div_eq_mul_inv] using
              (equivLaurentSeries_trace ω).symm

end Separable

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Level
