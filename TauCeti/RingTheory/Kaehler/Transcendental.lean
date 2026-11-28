/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Algebraic.Defs
import TauCeti.FieldTheory.RatFunc.Kaehler
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.RingTheory.Kaehler.BaseChange
import TauCeti.RingTheory.Kaehler.Separable
import TauCeti.RingTheory.Smooth.Field
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Detecting transcendence by derivations

In a characteristic-zero extension of fields, a transcendental element can be assigned
derivative one. Its differential is already nonzero in the rational function subfield it
generates, and formal smoothness makes the map on differentials into the ambient field
injective. This applies also to extensions of infinite transcendence degree.

## Main results

* `TauCeti.D_eq_zero_iff_isAlgebraic`: vanishing of the universal differential characterizes
  algebraicity in characteristic zero.
* `Transcendental.exists_derivation_apply_eq_one`: a transcendental element admits a
  field-valued derivation sending it to one.
-/

public section

open KaehlerDifferential

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero k] {x : F}

/-- An element of a field extension in characteristic zero has vanishing universal
differential exactly when it is algebraic over the base. -/
theorem TauCeti.D_eq_zero_iff_isAlgebraic : D k F x = 0 ↔ IsAlgebraic k x := by
  constructor
  · contrapose!
    intro hx
    let _ := TauCeti.ratFuncAlgebraOfTranscendental hx
    let _ := TauCeti.isScalarTower_ratFuncAlgebraOfTranscendental hx
    have hinj := TauCeti.injective_kaehlerDifferential_map_of_subsingleton_h1Cotangent
      k (RatFunc k) F
    simpa only [map_D, TauCeti.algebraMap_ratFuncAlgebraOfTranscendental_X hx] using
      ((map_ne_zero_iff _ hinj).mpr (RatFunc.D_X_ne_zero k))
  · intro hx
    exact of_not_not fun h ↦ TauCeti.transcendental_of_D_ne_zero h hx

/-- In characteristic zero a transcendental element admits a field-valued derivation
sending it to one. -/
theorem Transcendental.exists_derivation_apply_eq_one (hx : Transcendental k x) :
    ∃ δ : Derivation k F F, δ x = 1 := by
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one F
    (TauCeti.D_eq_zero_iff_isAlgebraic.not.mpr hx)
  exact ⟨ℓ.compDer (D k F), hℓ⟩
