/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Frobenius
public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.WittVector.AdicTopology

/-!
# Integral p-adic scalars in Witt vectors

The canonical map `ℤ_p → W(R)` for a characteristic-`p` ring `R` comes from Mathlib's
`WittVector.fromPadicInt` and functoriality of Witt vectors. It is continuous for the
`(p, [ϖ])`-adic topology, even though its image of `(p)` need not be an ideal of definition.
-/

public section

namespace WittVector

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]

/-- The canonical scalar map from `ℤ_p` to `W(R)`, via `W(𝔽_p)`. -/
noncomputable def padicIntToWitt : ℤ_[p] →+* WittVector p R :=
  (WittVector.map (ZMod.castHom dvd_rfl R)).comp (fromPadicInt p)

variable {p R}

/-- The scalar map is obtained by applying `W` to the prime-field map. -/
theorem padicIntToWitt_def : padicIntToWitt p R =
    (WittVector.map (ZMod.castHom dvd_rfl R)).comp (fromPadicInt p) :=
  (rfl)

/-- The map from `ℤ_p` is continuous for the `(p, [ϖ])`-adic topology on `W(R)`. -/
theorem continuous_padicIntToWitt [TopologicalSpace (WittVector p R)] {ϖ : R}
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) :
    Continuous (padicIntToWitt p R) := by
  have h : IsAdic (Ideal.span {(p : ℤ_[p])}) := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact TauCeti.Huber.PadicInt.isAdic_maximalIdeal
  refine h.continuous_of_map_le_radical hI (Submodule.fg_span_singleton _) ?_
  rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_le_iff_mem]
  exact Ideal.le_radical (Ideal.subset_span (by simp))

/-- Witt-vector Frobenius fixes integral p-adic scalars. -/
@[simp]
theorem frobenius_padicIntToWitt (a : ℤ_[p]) :
    frobenius (padicIntToWitt p R a) = padicIntToWitt p R a := by
  ext n
  simp only [padicIntToWitt_def, RingHom.comp_apply, coeff_frobenius_charP, map_coeff,
    ← map_pow, ZMod.pow_card]

end WittVector
