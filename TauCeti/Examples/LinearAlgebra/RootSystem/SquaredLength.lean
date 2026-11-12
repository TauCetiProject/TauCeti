/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.SquaredLength
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.UniqueScale
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Squared root lengths in the rational root systems of small type

The rational root systems of types `A₂`, `B₂` and `G₂` exercise the squared-length theorem: for a
positive-definite invariant form, every root of `A₂` has one squared length, while `B₂` has two, in
ratio `2`, and `G₂` has two, in ratio `3`. The canonical root form is such a form, so the
hypotheses are met.
-/

public section

namespace TauCeti.DynkinType

/-- The canonical root form of the rational root system of `G₂` is a positive-definite invariant
form. -/
example : (G2.rationalRootSystem valid_G2).toInvariantForm.form.toQuadraticMap.PosDef :=
  RootPairing.rootForm_posDef _

/-- All roots of `A₂` have the same squared length. -/
example (F : ((A 2).rationalRootSystem (by simp)).InvariantForm)
    (hF : F.form.toQuadraticMap.PosDef) :
    ∃ s : ℚ, 0 < s ∧ Set.range (fun k ↦ F.form (((A 2).rationalRootSystem (by simp)).root k)
      (((A 2).rationalRootSystem (by simp)).root k)) = {s} := by
  simpa [Set.eq_singleton_iff_unique_mem] using F.exists_pos_range_apply_root_root_eq hF
    ((A 2).hasCartanType_rationalRootSystem (by simp)) (by simp)

/-- The roots of `B₂` have squared lengths in ratio `2`. -/
example (F : ((B 2).rationalRootSystem (by simp)).InvariantForm)
    (hF : F.form.toQuadraticMap.PosDef) :
    ∃ s : ℚ, 0 < s ∧ Set.range (fun k ↦ F.form (((B 2).rationalRootSystem (by simp)).root k)
      (((B 2).rationalRootSystem (by simp)).root k)) = {s, 2 * s} := by
  simpa using F.exists_pos_range_apply_root_root_eq hF
    ((B 2).hasCartanType_rationalRootSystem (by simp)) (by simp)

/-- The roots of `G₂` have squared lengths in ratio `3`. -/
example (F : (G2.rationalRootSystem valid_G2).InvariantForm)
    (hF : F.form.toQuadraticMap.PosDef) :
    ∃ s : ℚ, 0 < s ∧ Set.range (fun k ↦ F.form ((G2.rationalRootSystem valid_G2).root k)
      ((G2.rationalRootSystem valid_G2).root k)) = {s, 3 * s} := by
  simpa using F.exists_pos_range_apply_root_root_eq hF
    (G2.hasCartanType_rationalRootSystem valid_G2) valid_G2

end TauCeti.DynkinType
