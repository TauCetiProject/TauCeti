/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import TauCeti.SetTheory.Descriptive.GenericErgodicity
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.Topology.Baire.Perfect

/-!
# The Vitali relation

The **Vitali relation** on `ℝ` relates `x` and `y` when `y - x` is rational. It is the relation of
lying in the same coset of the subgroup `ℚ` of `ℝ`, that is, `QuotientAddGroup.leftRel` of the
image of `Rat.castHom ℝ`.

Like `E₀` on Cantor space, it is a Borel equivalence relation with countable classes that is not
smooth:

* its graph is Borel, a countable union of translates of the diagonal, and its classes `x + ℚ`
  are countable;
* it is **generically ergodic**: a set with the Baire property that is invariant under every
  rational translation is meagre or comeagre, because `ℚ` is a countable dense subgroup of `ℝ`;
* hence its quotient, with Mathlib's quotient σ-algebra, is not countably separated: no countable
  family of invariant Borel sets separates its classes, since its classes are countable, hence
  meagre;
* it has continuum many classes, since `ℝ` is the union of the classes and each class is
  countable.

## Main definitions

* `TauCeti.vitaliRel`: the Vitali relation on `ℝ`.

## Main results

* `TauCeti.measurableSet_vitaliRel`: the graph of the Vitali relation is Borel.
* `TauCeti.countable_setOf_vitaliRel`: every class is countable.
* `TauCeti.isMeagre_or_mem_residual_of_vitaliRel_invariant`: generic ergodicity.
* `TauCeti.not_countablySeparated_quotient_vitaliRel`: no countable family of invariant Borel sets
  separates the classes, so the Vitali relation is not smooth.
* `TauCeti.mk_quotient_vitaliRel`: the Vitali relation has continuum many classes.

## References

* G. Vitali, *Sul problema della misura dei gruppi di punti di una retta*, Bologna, 1905.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Section 8.J (generic ergodicity).
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Section 6.1 (non-smooth
  equivalence relations).
-/

public section

open Cardinal MeasurableSpace Set Topology

namespace TauCeti

/-- The **Vitali relation** on `ℝ`: `x` and `y` are related when `y - x` is rational. It is the
relation of lying in the same coset of the image of `Rat.castHom ℝ`. It is named `vitaliRel`, as
`TauCeti.vitali` is Vitali's convergence theorem for holomorphic maps. -/
noncomputable def vitaliRel : Setoid ℝ :=
  QuotientAddGroup.leftRel (Rat.castHom ℝ).toAddMonoidHom.range

variable {x y : ℝ} {B : Set ℝ}

/-- Two reals are related by the Vitali relation iff their difference is rational. -/
theorem vitaliRel_iff : vitaliRel x y ↔ ∃ q : ℚ, (q : ℝ) = y - x := by
  rw [vitaliRel, QuotientAddGroup.leftRel_apply, AddMonoidHom.mem_range, neg_add_eq_sub]
  simp

/-- The graph of the Vitali relation is Borel: it is the countable union over `q : ℚ` of the
translates `{(x, y) | y - x = q}` of the diagonal. -/
theorem measurableSet_vitaliRel : MeasurableSet {p : ℝ × ℝ | vitaliRel p.1 p.2} := by
  simp only [vitaliRel_iff, ofPred_exists]
  exact .iUnion fun q => measurableSet_eq_fun measurable_const (measurable_snd.sub measurable_fst)

/-- Every class of the Vitali relation is countable: the class of `x` is `x + ℚ`. -/
theorem countable_setOf_vitaliRel (x : ℝ) : {y | vitaliRel x y}.Countable := by
  refine (countable_range fun q : ℚ => x + q).mono fun y hy => ?_
  obtain ⟨q, hq⟩ := vitaliRel_iff.1 hy
  exact ⟨q, by simp only [hq, add_sub_cancel]⟩

/-- **Generic ergodicity of the Vitali relation.** A set with the Baire property that is invariant
under the Vitali relation is meagre or comeagre. -/
theorem isMeagre_or_mem_residual_of_vitaliRel_invariant (hB : BaireMeasurableSet B)
    (hinv : Quotient.mk vitaliRel ⁻¹' (Quotient.mk vitaliRel '' B) = B) :
    IsMeagre B ∨ B ∈ residual ℝ := by
  have : Countable (Rat.castHom ℝ).toAddMonoidHom.range :=
    Set.Countable.to_subtype (s := ((Rat.castHom ℝ).toAddMonoidHom.range : Set ℝ))
      (by rw [AddMonoidHom.coe_range]; exact countable_range _)
  refine QuotientAddGroup.isMeagre_or_mem_residual_of_leftRel_invariant ?_ hB hinv
  rw [AddMonoidHom.coe_range]
  exact Rat.denseRange_cast

/-- No countable family of invariant Borel sets separates the classes of the Vitali relation: the
quotient `Quotient vitaliRel`, with Mathlib's quotient σ-algebra, is not countably separated. This
is the non-smoothness of the Vitali relation. -/
theorem not_countablySeparated_quotient_vitaliRel : ¬ CountablySeparated (Quotient vitaliRel) :=
  vitaliRel.not_countablySeparated_quotient_of_isMeagre_or_mem_residual
    (fun x => (countable_setOf_vitaliRel x).isMeagre) fun s hs =>
      isMeagre_or_mem_residual_of_vitaliRel_invariant
        (measurableSet_quotient.1 hs).baireMeasurableSet
        (by rw [image_preimage_eq s Quotient.mk_surjective])

/-- The Vitali relation has exactly continuum many classes. -/
theorem mk_quotient_vitaliRel : #(Quotient vitaliRel) = 𝔠 := by
  refine le_antisymm (mk_quotient_le.trans_eq mk_real) ?_
  -- `ℝ` is the union of countably many points over each class.
  have h : 𝔠 ≤ #(Quotient vitaliRel) * ℵ₀ := by
    rw [← mk_real]
    refine mk_le_mk_mul_of_mk_preimage_le (Quotient.mk vitaliRel) fun c => ?_
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective c
    have : Quotient.mk vitaliRel ⁻¹' {Quotient.mk vitaliRel x} = {y | vitaliRel x y} :=
      ext fun y => ⟨fun hy => Quotient.exact hy.symm, fun hy => (Quotient.sound hy).symm⟩
    rw [this]
    exact (countable_setOf_vitaliRel x).le_aleph0
  by_contra hlt
  exact absurd (h.trans (mul_le_max _ _)) <| not_le.2 <|
    max_lt (max_lt (not_le.1 hlt) aleph0_lt_continuum) aleph0_lt_continuum

end TauCeti
