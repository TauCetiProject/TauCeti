/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeilOperator
public import TauCeti.Geometry.Symplectic.Complex.Complexification

/-!
# Weight-one Hodge structures from almost complex structures

An almost complex structure `J` on a real vector space determines an effective pure Hodge
structure of weight one on its complexification. The Hodge components are the `i`- and
`-i`-eigenspaces of the complex-linear extension of `J`; complex conjugation exchanges them.

This file constructs that Hodge structure, computes its filtration and components, and proves
that its Weil operator is the scalar extension of `J`. Together with the construction of a real
almost complex structure from an effective weight-one Hodge structure, this identifies the two
linear-algebraic descriptions of weight-one Hodge structures.

## Main declarations

* `TauCeti.AlmostComplexStructure.hodgeStructure`: the effective weight-one Hodge structure
  associated with an almost complex structure.
* `TauCeti.AlmostComplexStructure.hodgeStructure_piece_one` and
  `TauCeti.AlmostComplexStructure.hodgeStructure_piece_zero`: its two Hodge components.
* `TauCeti.AlmostComplexStructure.hodgeStructure_weilOperator`: its Weil operator is the
  complexification of the original almost complex structure.

The construction follows the standard weight-one correspondence described in Voisin,
*Hodge Theory and Complex Algebraic Geometry I*, §6, and Peters--Steenbrink,
*Mixed Hodge Structures*, §2.
-/

public section

namespace TauCeti

open scoped TensorProduct

universe u

namespace AlmostComplexStructure

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The effective pure Hodge structure of weight one associated with a real almost complex
structure. Its `F¹` is the `i`-eigenspace of the complexified endomorphism. -/
noncomputable def hodgeStructure (J : AlmostComplexStructure V) :
    Hodge.HodgeStructureOn (ℂ ⊗[ℝ] V) (Hodge.complexificationConjugation V) 1 where
  F p := if p ≤ 0 then ⊤ else if p = 1 then
    Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I else ⊥
  F_antitone p q hpq := by
    -- Expose the piecewise filtration stored in the structure field so its integer cases can be
    -- reduced directly; no rewrite theorem exists until `hodgeStructure` has been defined.
    change (if q ≤ 0 then ⊤ else if q = 1 then
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I else ⊥) ≤
        if p ≤ 0 then ⊤ else if p = 1 then
          Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I else ⊥
    by_cases hp : p ≤ 0
    · rw [ite_eq_left hp]
      exact le_top
    have hq : ¬q ≤ 0 := by omega
    rw [ite_eq_right hp, ite_eq_right hq]
    by_cases hq_one : q = 1
    · have hp_one : p = 1 := by omega
      subst p
      subst q
      exact le_rfl
    rw [ite_eq_right hq_one]
    exact bot_le
  F_top := ⟨0, by simp⟩
  opposed p := by
    by_cases hp : p ≤ 0
    · have hother : ¬ 1 + 1 - p ≤ 0 := by omega
      have hotherone : 1 + 1 - p ≠ 1 := by omega
      rw [ite_eq_left hp, ite_eq_right hother, ite_eq_right hotherone, Submodule.map_bot]
      exact isCompl_top_bot
    · by_cases hpone : p = 1
      · subst p
        norm_num
        exact J.isCompl_eigenspace_baseChange_I_neg_I
      · have hpge : 2 ≤ p := by omega
        have hother : 1 + 1 - p ≤ 0 := by omega
        have hmaptop : (⊤ : Submodule ℂ (ℂ ⊗[ℝ] V)).map
            (Hodge.complexificationConjugation V).toEquiv.toLinearMap = ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top]
          exact (Hodge.complexificationConjugation V).toEquiv.surjective
        rw [ite_eq_right hp, ite_eq_right hpone, ite_eq_left hother, hmaptop]
        exact isCompl_bot_top

/-- The filtration of the Hodge structure associated with `J` is top in nonpositive degrees,
the `i`-eigenspace in degree one, and bottom above degree one. -/
@[simp]
theorem hodgeStructure_F (J : AlmostComplexStructure V) (p : ℤ) :
    J.hodgeStructure.F p =
      if p ≤ 0 then ⊤ else if p = 1 then
        Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I else ⊥ :=
  (rfl)

/-- The Hodge structure associated with an almost complex structure is effective. -/
theorem isEffective_hodgeStructure (J : AlmostComplexStructure V) :
    J.hodgeStructure.IsEffective := by
  simp [Hodge.HodgeStructureOn.isEffective_iff]

/-- The `H^{1,0}` component associated with `J` is the `i`-eigenspace of its complexification. -/
@[simp]
theorem hodgeStructure_piece_one (J : AlmostComplexStructure V) :
    J.hodgeStructure.piece 1 =
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I := by
  rw [Hodge.HodgeStructureOn.piece_def, Hodge.HodgeStructureOn.conjF_def]
  norm_num [hodgeStructure_F]

/-- The `H^{0,1}` component associated with `J` is the `-i`-eigenspace of its complexification. -/
@[simp]
theorem hodgeStructure_piece_zero (J : AlmostComplexStructure V) :
    J.hodgeStructure.piece 0 =
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) := by
  rw [Hodge.HodgeStructureOn.piece_def, Hodge.HodgeStructureOn.conjF_def]
  norm_num [hodgeStructure_F]

/-- Every Hodge component of the structure associated with `J` other than `H^{1,0}` and
`H^{0,1}` vanishes. -/
theorem hodgeStructure_piece_eq_bot (J : AlmostComplexStructure V) {p : ℤ}
    (hpzero : p ≠ 0) (hpone : p ≠ 1) : J.hodgeStructure.piece p = ⊥ := by
  by_cases hp : p < 0
  · exact J.isEffective_hodgeStructure.piece_eq_bot_of_neg hp
  · exact J.isEffective_hodgeStructure.piece_eq_bot_of_weight_lt (by omega)

/-- The Weil operator of the Hodge structure associated with `J` is the complex-linear scalar
extension of `J`. Thus the construction recovers the original almost complex structure after
complexification. -/
theorem hodgeStructure_weilOperator (J : AlmostComplexStructure V) :
    J.hodgeStructure.weilOperator = J.toLinearMap.baseChange ℂ := by
  symm
  apply J.hodgeStructure.weilOperator_unique
  intro p x hx
  by_cases hpone : p = 1
  · subst p
    rw [J.hodgeStructure_piece_one, Module.End.mem_eigenspace_iff] at hx
    norm_num
    exact hx
  by_cases hpzero : p = 0
  · subst p
    rw [J.hodgeStructure_piece_zero, Module.End.mem_eigenspace_iff] at hx
    norm_num
    simpa only [neg_smul] using hx
  rw [J.hodgeStructure_piece_eq_bot hpzero hpone, Submodule.mem_bot] at hx
  subst x
  simp

end AlmostComplexStructure

end TauCeti
