/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.ProperSubgraph
import Mathlib.Tactic.Linarith

/-!
# The four-leaf star in a numerical type

Five components of self-intersection `-2w`, one meeting the other four, exhaust a numerical
type. All five weights agree, the leaves are disjoint, and the centre has twice the
multiplicity of each leaf. Thus a vertex of degree at least four in a minimal numerical type
of genus one forces the entire affine `D₄` configuration, rather than just a subgraph.

The classification is expressed by an equivalence from `Option (Fin 4)`, with `none` the
centre and `some i` the leaves. It records the whole intersection matrix and multiplicity
vector, allowing the configuration to be used without choosing an ordering of the components.

## References

* [Stacks Project, Lemma 55.6.2, case (22), Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T).
* The proof uses the three-leaf classification
  `TauCeti.NumericalType.exists_weight_intersection_star_four_eq` and the exclusion of a
  proper four-leaf star `TauCeti.NumericalType.intersection_eq_zero_of_star_five`.
-/

public section

namespace TauCeti.NumericalType

open Finset

universe u

variable {T : NumericalType.{u}}

/-- Four distinct leaves of self-intersection `-2w` meeting a centre of self-intersection `-2w`
exhaust the numerical type. No hypothesis on its other components or on its genus is needed. -/
private lemma card_eq_five_of_fourLeafStar {c : T.Component} {l : Fin 4 → T.Component}
    (hl : Function.Injective l) (hc : ∀ i, c ≠ l i)
    (hself : T.intersection c c = -(2 * (T.weight c : ℤ)))
    (hlself : ∀ i, T.intersection (l i) (l i) = -(2 * (T.weight (l i) : ℤ)))
    (hadj : ∀ i, 0 < T.intersection c (l i)) : Fintype.card T.Component = 5 := by
  have hinj : Function.Injective (fun v : Option (Fin 4) ↦ v.elim c l) :=
    Option.injective_iff.mpr ⟨hl, by rintro ⟨i, hi⟩; exact hc i hi.symm⟩
  have hge := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_option, Fintype.card_fin] at hge
  by_contra hne
  have hz := T.intersection_eq_zero_of_star_five (by omega) hself
    (hlself 0) (hlself 1) (hlself 2) (hlself 3) (hc 3)
    (hl.ne (by decide : (0 : Fin 4) ≠ 1)) (hl.ne (by decide : (0 : Fin 4) ≠ 2))
    (hl.ne (by decide : (0 : Fin 4) ≠ 3)) (hl.ne (by decide : (1 : Fin 4) ≠ 2))
    (hl.ne (by decide : (1 : Fin 4) ≠ 3)) (hl.ne (by decide : (2 : Fin 4) ≠ 3))
    (hadj 0) (hadj 1) (hadj 2)
  exact (hadj 3).ne' hz

/-- The weights and intersections of four leaves meeting a centre are the simply laced star.
Three leaves at a time form a proper subgraph, so the existing three-leaf classification applies.
-/
private lemma fourLeafStar_weights_intersections {c : T.Component} {l : Fin 4 → T.Component}
    (hl : Function.Injective l) (hcard : 4 < Fintype.card T.Component)
    (hself : T.intersection c c = -(2 * (T.weight c : ℤ)))
    (hlself : ∀ i, T.intersection (l i) (l i) = -(2 * (T.weight (l i) : ℤ)))
    (hadj : ∀ i, 0 < T.intersection c (l i)) :
    (∀ i, T.weight (l i) = T.weight c) ∧
      (∀ i, T.intersection c (l i) = T.weight c) ∧
      (∀ i j, i ≠ j → T.intersection (l i) (l j) = 0) := by
  have triple (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :=
    T.exists_weight_intersection_star_four_eq hcard hself (hlself i) (hlself j) (hlself k)
      (hl.ne hij) (hl.ne hik) (hl.ne hjk) (hadj i) (hadj j) (hadj k)
  obtain ⟨w, hw, hw₀, hw₁, hw₂, ha₀, ha₁, ha₂, hz₀₁, hz₀₂, hz₁₂⟩ :=
    triple 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨w', hw', -, -, hw₃, -, -, ha₃, -, hz₀₃, hz₁₃⟩ :=
    triple 0 1 3 (by decide) (by decide) (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hz₂₃⟩ :=
    triple 0 2 3 (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact_mod_cast hw₀.trans hw.symm
    · exact_mod_cast hw₁.trans hw.symm
    · exact_mod_cast hw₂.trans hw.symm
    · exact_mod_cast hw₃.trans hw'.symm
  · intro i
    fin_cases i
    · exact ha₀.trans hw.symm
    · exact ha₁.trans hw.symm
    · exact ha₂.trans hw.symm
    · exact ha₃.trans hw'.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> grind [T.intersection_comm]

/-- **The four-leaf star classification.** A centre and four distinct leaves, all of
self-intersection `-2w`, that meet as displayed force the whole numerical type to be the
simply laced affine `D₄` configuration. The equivalence preserves the given leaf labels.
The centre has twice the common leaf multiplicity; all weights agree. -/
theorem exists_equiv_fourLeafStar (c : T.Component) (l : Fin 4 → T.Component)
    (hl : Function.Injective l)
    (hself : T.intersection c c = -(2 * (T.weight c : ℤ)))
    (hlself : ∀ i, T.intersection (l i) (l i) = -(2 * (T.weight (l i) : ℤ)))
    (hadj : ∀ i, T.Adj c (l i)) :
    ∃ e : Option (Fin 4) ≃ T.Component, e none = c ∧ (∀ i, e (some i) = l i) ∧
      (∀ v, T.weight (e v) = T.weight c) ∧
      (∀ v, (T.multiplicity (e v) : ℤ) =
        if v = none then 2 * (T.multiplicity (l 0) : ℤ) else T.multiplicity (l 0)) ∧
      (∀ v w, T.intersection (e v) (e w) =
        if v = w then -(2 * (T.weight c : ℤ))
        else if v = none ∨ w = none then T.weight c else 0) := by
  classical
  have hc := fun i ↦ (T.adj_iff.mp (hadj i)).1
  have hpos := fun i ↦ (T.adj_iff.mp (hadj i)).2
  have hcard := card_eq_five_of_fourLeafStar hl hc hself hlself hpos
  have hinj : Function.Injective (fun v : Option (Fin 4) ↦ v.elim c l) :=
    Option.injective_iff.mpr ⟨hl, by rintro ⟨i, hi⟩; exact hc i hi.symm⟩
  have hsurj : Function.Surjective (fun v : Option (Fin 4) ↦ v.elim c l) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simpa using hcard.symm⟩ |>.2
  let e := Equiv.ofBijective (fun v : Option (Fin 4) ↦ v.elim c l) ⟨hinj, hsurj⟩
  obtain ⟨hw, ha, hz⟩ := fourLeafStar_weights_intersections hl (by omega) hself hlself hpos
  have he_none : e none = c := rfl
  have he_some : ∀ i, e (some i) = l i := fun _ ↦ rfl
  have hmult (i : Fin 4) : (T.multiplicity c : ℤ) = 2 * T.multiplicity (l i) := by
    have h := T.fiber_relation (l i)
    rw [← e.sum_comp] at h
    simp only [Fintype.sum_option, he_none, he_some, T.intersection_comm (l i) c, ha] at h
    have hsum : (∑ j, (T.multiplicity (l j) : ℤ) * T.intersection (l i) (l j)) =
        (T.multiplicity (l i) : ℤ) * (-(2 * (T.weight c : ℤ))) := by
      rw [Finset.sum_eq_single i]
      · rw [hlself, hw]
      · intro j _ hji
        rw [hz i j hji.symm, mul_zero]
      · simp
    rw [hsum] at h
    have heq : (T.weight c : ℤ) * ((T.multiplicity c : ℤ) -
        2 * T.multiplicity (l i)) = 0 := by linarith [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (by simp))
  refine ⟨e, he_none, he_some, ?_, ?_, ?_⟩
  · intro v
    cases v <;> simp [he_none, he_some, hw]
  · intro v
    cases v with
    | none => simpa [he_none] using hmult 0
    | some i => simp only [he_some, Option.some_ne_none, ↓reduceIte]; linarith [hmult i, hmult 0]
  · intro v w
    cases v <;> cases w
    · simp [he_none, hself]
    · simp [he_none, he_some, ha]
    · simp [he_none, he_some, T.intersection_comm, ha]
    · simp only [he_some, Option.some.injEq, Option.some_ne_none, false_or, ↓reduceIte]
      split_ifs with h
      · subst h
        rw [hlself, hw]
      · exact hz _ _ h

/-- **The high-degree case of the genus-one classification.** If a component of a minimal
numerical type of genus one has at least four neighbours, the whole type is the five-component
four-leaf star, with weight `w`, multiplicities `(2m; m, m, m, m)`, and zero component genera.
This is case (22) of Stacks, Tag 0C8T. No component count or tree hypothesis is assumed. -/
theorem IsMinimal.exists_equiv_fourLeafStar_of_four_le_ncard_neighborSet (hT : T.IsMinimal)
    (hg : T.arithmeticGenus = 1) (c : T.Component)
    (hdeg : 4 ≤ (T.intersectionGraph.neighborSet c).ncard) :
    ∃ e : Option (Fin 4) ≃ T.Component, e none = c ∧
      (∀ v, T.genus (e v) = 0) ∧ (∀ v, T.weight (e v) = T.weight c) ∧
      (∀ v, (T.multiplicity (e v) : ℤ) =
        if v = none then 2 * (T.multiplicity (e (some 0)) : ℤ)
        else T.multiplicity (e (some 0))) ∧
      (∀ v w, T.intersection (e v) (e w) =
        if v = w then -(2 * (T.weight c : ℤ))
        else if v = none ∨ w = none then T.weight c else 0) := by
  classical
  have hcard : 1 < Fintype.card T.Component := by
    have hd := T.intersectionGraph.degree_lt_card_verts c
    rw [T.intersectionGraph.ncard_neighborSet] at hdeg
    omega
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff hcard).mp ⟨hT, hg⟩
  obtain ⟨f⟩ : Nonempty (Fin 4 ↪ T.intersectionGraph.neighborSet c) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_fin, Set.fintypeCard_eq_ncard]
      exact hdeg)
  let l : Fin 4 → T.Component := fun i ↦ (f i).val
  have hl : Function.Injective l := Subtype.val_injective.comp f.injective
  have hadj : ∀ i, T.Adj c (l i) :=
    fun i ↦ T.intersectionGraph_adj_iff.mp (f i).property
  obtain ⟨e, he, hel, hw, hm, ha⟩ := T.exists_equiv_fourLeafStar c l hl
    (T.isMinusTwoIndex_iff.mp (h₂ c)).2
    (fun i ↦ (T.isMinusTwoIndex_iff.mp (h₂ (l i))).2) hadj
  refine ⟨e, he, fun v ↦ (T.isMinusTwoIndex_iff.mp (h₂ (e v))).1, hw, ?_, ha⟩
  simpa only [hel] using hm

/-- Every vertex of a minimal genus-one numerical type has at most four neighbours. -/
theorem IsMinimal.ncard_neighborSet_le_four (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    (c : T.Component) : (T.intersectionGraph.neighborSet c).ncard ≤ 4 := by
  classical
  by_cases hd : 4 ≤ (T.intersectionGraph.neighborSet c).ncard
  · obtain ⟨e, -⟩ := hT.exists_equiv_fourLeafStar_of_four_le_ncard_neighborSet hg c hd
    have hcard : Fintype.card T.Component = 5 := by
      simpa using (Fintype.card_congr e).symm
    have := T.intersectionGraph.degree_lt_card_verts c
    rw [T.intersectionGraph.ncard_neighborSet]
    omega
  · omega

/-- Away from the five-component case, the genus-one classification only needs graphs of
maximum degree three: a vertex of degree four would force the entire four-leaf star. -/
theorem IsMinimal.ncard_neighborSet_le_three_of_card_ne_five (hT : T.IsMinimal)
    (hg : T.arithmeticGenus = 1) (hcard : Fintype.card T.Component ≠ 5) (c : T.Component) :
    (T.intersectionGraph.neighborSet c).ncard ≤ 3 := by
  by_contra hd
  obtain ⟨e, -⟩ := hT.exists_equiv_fourLeafStar_of_four_le_ncard_neighborSet hg c (by omega)
  exact hcard (by simpa using (Fintype.card_congr e).symm)

end TauCeti.NumericalType
