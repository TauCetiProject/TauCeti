/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegralClosure

/-!
# Separability of completed number-field extensions

The canonical extension of completions at finite places is finite and has a characteristic-zero
base. It is therefore separable. This supplies the separability hypothesis needed to apply local
different and monogenicity results to the completed integer rings.
-/

public section

open scoped AdicCompletionExtension NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]
  {L : Type*} [Field L] [NumberField L] [Algebra K L]

/-- The canonical extension `L_w / K_v` of completions of number fields is separable. -/
theorem adicCompletion_isSeparable (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) := by
  let hchar : CharZero (v.adicCompletion K) := adicCompletion_charZero v
  refine ⟨fun x ↦ ?_⟩
  have hx : IsIntegral (v.adicCompletion K) x := IsIntegral.of_finite _ x
  exact @_root_.Irreducible.separable _ inferInstance hchar _ (minpoly.irreducible hx)

end IsDedekindDomain.HeightOneSpectrum

end
