/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

/-!
# Evaluating polynomials at the fractions of a rational subset

For numerators `t₁, …, tₖ` drawn from `T`, the evaluation `Xᵢ ↦ tᵢ/s` of *polynomials* lands in
the localisation `Aₛ = A⟨T/s⟩` itself, not in its completion: a polynomial in the fractions is a
finite sum, so no convergence is involved. That is what makes this map one the completion functor
can be applied to, and it is why this material sits below
`TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation` rather than beside the completed
evaluation defined there — nothing here needs completion theory.

The three properties together present `Aₛ` as an open quotient of a polynomial ring. They need
different hypotheses, and the distinction matters:

* surjectivity asks the numerators *together with `s`* to generate the unit ideal, which is what
  makes the fractions generate `Aₛ` over `A`;
* openness asks that every fraction `t/s` with `t ∈ T` — and these are what the neighbourhoods
  of `Aₛ` are built from — already occurs among the `tᵢ/s`. It is the *fractions* that must be
  matched, not the numerators: distinct `t` may have the same image in `Aₛ`;
* continuity asks that each fraction `tᵢ/s` lie in the ring of definition `D` of `Aₛ`. That is
  weaker than either of the others and is implied by `tᵢ ∈ T`, via
  `TauCeti.Huber.PairOfDefinition.divBy_mem_locSubring`; it is stated in this form so that a
  caller whose fractions lie in `D` for another reason need not exhibit them as elements of `T`.

None of the three implies another, so the bundled result carries all three hypotheses.

## Main results

* `TauCeti.Huber.polyEvalHom`, with
  `TauCeti.Huber.polyEvalHom_weightedPolynomialsEquiv_apply` as its characteristic
  equation, and `TauCeti.Huber.PairOfDefinition.isOpenQuotientMap_polyEvalHom` bundling the three
  properties above.
* `TauCeti.Huber.PairOfDefinition.exists_aeval_eq_of_mem_locIdealImage`: every element of the
  `n`-th neighbourhood of `Aₛ` is the value of a polynomial whose coefficients lie in `Iⁿ`. This
  direction is what makes the evaluation open; it is an existence statement, not a
  characterisation.
* the two directions of that characterisation in the `Fin k` indexing the evaluation uses,
  `TauCeti.Huber.PairOfDefinition.exists_polynomial_coeff_mem_idealImage` and
  `TauCeti.Huber.PairOfDefinition.aeval_mem_locIdealImage_of_coeff_mem`. Openness is proved from
  the first and continuity from the second, and a consumer wanting either half of the
  correspondence between neighbourhoods and coefficient conditions should use these.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 6.28 and
  Example 6.38, for which this is the downstairs half. Example 6.38 is what Proposition 8.30
  cites by name; the proposition's own conclusion is flatness of restriction maps, so this file
  is upstream of it and is not part of its statement.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

section PolynomialEvaluation

variable (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]

/-- **The evaluation of polynomials at the fractions**, `Xᵢ ↦ tᵢ/s`, read on the subring of
polynomials inside `A⟨X₁, …, Xₖ⟩`.

Unlike `TauCeti.Huber.PairOfDefinition.rationalEvalHom` this lands in `Aₛ` itself, not its
completion: a *polynomial* in the fractions is a finite sum, so no convergence is involved. That
is what makes it a map to which the completion functor can be applied. -/
noncomputable def polyEvalHom {k : ℕ} (t : Fin k → A) :
    weightedPolynomials (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+* S :=
  (MvPolynomial.aeval fun i ↦ (divBy (t i) s : S)).toRingHom.comp
    (weightedPolynomialsEquiv isWeightFamily_one_weight).symm.toRingHom

/-- **The polynomial evaluation is onto `Aₛ`** when the numerators together with the denominator
`s` generate the unit ideal: its range is the `A`-subalgebra the fractions generate, which is
everything by `TauCeti.Localization.adjoin_divBy_eq_top`.

Including `s` among the generators is the weaker hypothesis, and the one a rational subset
supplies. -/
theorem polyEvalHom_surjective {k : ℕ} (t : Fin k → A)
    (hspan : Ideal.span (insert s (Set.range t)) = ⊤) :
    Function.Surjective (polyEvalHom s (S := S) t) := by
  have hrange : (Set.range fun x : (Set.range t) ↦ (divBy (x : A) s : S))
      = Set.range fun i ↦ (divBy (t i) s : S) := by
    ext y
    constructor
    · rintro ⟨⟨_, i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨⟨t i, i, rfl⟩, rfl⟩
  have haeval : Function.Surjective
      (MvPolynomial.aeval (R := A) fun i ↦ (divBy (t i) s : S)) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, ← hrange]
    exact adjoin_divBy_eq_top s hspan
  exact haeval.comp (weightedPolynomialsEquiv isWeightFamily_one_weight).symm.surjective

/-- **How `TauCeti.Huber.polyEvalHom` acts**: on the copy of a polynomial inside
`A⟨X⟩` it is evaluation of that polynomial at the fractions. This is the characteristic equation;
consumers should use it rather than unfolding the definition. -/
@[simp]
theorem polyEvalHom_weightedPolynomialsEquiv_apply {k : ℕ} (t : Fin k → A)
    (p : MvPolynomial (Fin k) A) :
    polyEvalHom s (S := S) t (weightedPolynomialsEquiv isWeightFamily_one_weight p)
      = MvPolynomial.aeval (fun i ↦ (divBy (t i) s : S)) p := by
  simp [polyEvalHom]

end PolynomialEvaluation

namespace PairOfDefinition

variable (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*)
  [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)

omit [NonarchimedeanRing A] hden in
/-- Every element of `D` is the value of a polynomial over `A₀` at the fractions. -/
private theorem exists_aeval_eq_of_mem_locSubring {d : S} (hd : d ∈ locSubring P T s S) :
    ∃ q : MvPolynomial ↥T ↥P.ringOfDefinition,
      MvPolynomial.aeval (fun y : T ↦ (divBy (y : A) s : S)) q = d := by
  rw [locSubring_eq_adjoin, Subalgebra.mem_toSubring,
    Algebra.adjoin_range_eq_range_aeval] at hd
  exact hd

omit [NonarchimedeanRing A] in
/-- **Every element of the `n`-th neighbourhood of `Aₛ` is the value of a polynomial with
coefficients in `Iⁿ`.** Only this direction is proved here; the converse, that every such value
lies in the neighbourhood, is `TauCeti.Huber.PairOfDefinition.aeval_mem_locIdealImage_of_coeff_mem`
in the `Fin k` indexing. This direction is what makes the polynomial evaluation an open map. -/
theorem exists_aeval_eq_of_mem_locIdealImage (n : ℕ) {x : S}
    (hx : x ∈ locIdealImage P T s S n) :
    ∃ q ∈ Ideal.map (MvPolynomial.C (σ := ↥T)) (P.idealOfDefinition ^ n),
      MvPolynomial.aeval (fun y : T ↦ (divBy (y : A) s : S)) q = x := by
  classical
  rw [mem_locIdealImage_iff] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  -- the elements of `D` with the stated property form an ideal
  set Q : Ideal (locSubring P T s S) :=
    { carrier := {d | ∃ q ∈ Ideal.map (MvPolynomial.C (σ := ↥T)) (P.idealOfDefinition ^ n),
        MvPolynomial.aeval (fun y : T ↦ (divBy (y : A) s : S)) q = (d : S)}
      zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
      add_mem' := by
        rintro a b ⟨qa, hqa, ha⟩ ⟨qb, hqb, hb⟩
        exact ⟨qa + qb, Submodule.add_mem _ hqa hqb, by
          rw [map_add, ha, hb]; push_cast; ring⟩
      smul_mem' := by
        rintro c a ⟨qa, hqa, ha⟩
        obtain ⟨qc, hqc⟩ := exists_aeval_eq_of_mem_locSubring P T s S c.2
        refine ⟨qc * qa, Ideal.mul_mem_left _ _ hqa, ?_⟩
        rw [map_mul, hqc, ha, smul_eq_mul]
        norm_cast } with hQ
  have hQle : locIdeal P T s S ^ n ≤ Q := by
    rw [locIdeal_def, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro c hc
    refine ⟨MvPolynomial.C c, Ideal.mem_map_of_mem _ hc, ?_⟩
    rw [MvPolynomial.aeval_C, toLocSubring_apply]
    rfl
  exact hQle hd

/-! ### The polynomial evaluation is open -/

omit [NonarchimedeanRing A] in
/-- **Every element of the `n`-th neighbourhood of `Aₛ` is the value at the fractions of a
polynomial over `A` whose coefficients all lie in the image of `Iⁿ`.**

This is the `Fin k`-indexed form over `A` of
`TauCeti.Huber.PairOfDefinition.exists_aeval_eq_of_mem_locIdealImage`, which is indexed by `T`
and has coefficients in `A₀`. -/
theorem exists_polynomial_coeff_mem_idealImage {k : ℕ} (t : Fin k → A)
    (hTt : Set.range (fun y : ↥T ↦ (divBy (y : A) s : S))
      ⊆ Set.range fun i ↦ (divBy (t i) s : S)) (n : ℕ) {x : S} (hx : x ∈ locIdealImage P T s S n) :
    ∃ p : MvPolynomial (Fin k) A, (∀ m, p.coeff m ∈ P.idealImage n) ∧
      MvPolynomial.aeval (fun i ↦ (divBy (t i) s : S)) p = x := by
  classical
  obtain ⟨q, hq, hqx⟩ := exists_aeval_eq_of_mem_locIdealImage P T s S n hx
  choose σ hσ using fun y : ↥T ↦ hTt ⟨y, rfl⟩
  have hC : (MvPolynomial.rename σ (R := ↥P.ringOfDefinition)).toRingHom.comp MvPolynomial.C
      = MvPolynomial.C := RingHom.ext fun a ↦ by simp
  have hren : MvPolynomial.rename σ q ∈
      Ideal.map (MvPolynomial.C (σ := Fin k)) (P.idealOfDefinition ^ n) := by
    rw [← hC, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hq
  refine ⟨MvPolynomial.map (algebraMap ↥P.ringOfDefinition A) (MvPolynomial.rename σ q),
    fun m ↦ ?_, ?_⟩
  · rw [MvPolynomial.coeff_map]
    exact (P.mem_idealImage n).mpr ⟨_, MvPolynomial.mem_map_C_iff.mp hren m, rfl⟩
  · -- `aeval_rename` leaves the composite `(fun i ↦ tᵢ/s) ∘ σ`; `hσ` says `σ` picks an index
    -- whose fraction equals that of each element of `T`, so the composite is the `T`-indexed
    -- family. The equality is named rather than inlined because `funext` supplies it.
    have hcomp : (fun i ↦ (divBy (t i) s : S)) ∘ σ = fun y : ↥T ↦ (divBy (y : A) s : S) :=
      funext hσ
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq,
      ← MvPolynomial.aeval_def, MvPolynomial.aeval_rename, hcomp]
    exact hqx

/-- **The polynomial evaluation `Xᵢ ↦ tᵢ/s` is an open map**, when the fractions of `T` all
occur among the `tᵢ/s`.

This asserts openness only. Surjectivity is a separate statement with a separate hypothesis —
`TauCeti.Huber.polyEvalHom_surjective`, which asks the numerators together with `s`
to generate the unit ideal.

Together with `TauCeti.Huber.polyEvalHom_surjective` and
`TauCeti.Huber.PairOfDefinition.continuous_polyEvalHom` — the three bundled as
`TauCeti.Huber.PairOfDefinition.isOpenQuotientMap_polyEvalHom` — this presents `Aₛ` as an
open quotient of a polynomial ring. That is exactly the input `AddMonoidHom.surjective_completion`
and `AddMonoidHom.isOpenMap_completion` take, so it is what carries the presentation to the
completions `A⟨X₁, …, Xₖ⟩ → A⟨T/s⟩`, exhibiting `A⟨T/s⟩` as strictly topologically of finite
type over `A` — Wedhorn's Definition 6.28 at Example 6.38 — and through it the strong
noetherianity of a rational localisation. That strong noetherianity is what Proposition 8.30
consumes; the proposition itself concludes flatness of restriction maps and is not proved here.

Openness is the half of the presentation that does not come for free. Surjectivity is a
statement about generation, whereas openness compares two topologies that were defined
independently: `Aₛ` carries the localisation topology, not a quotient topology transported
from the polynomials.

`hTt` asks that every fraction generating a neighbourhood of `Aₛ` already occurs among the
`tᵢ/s`. It is stated on fractions rather than on numerators — `↑T ⊆ Set.range t` would do, and
is what a caller usually has, but the argument only ever compares images in `Aₛ`. It neither
implies nor is implied by the unit-ideal condition surjectivity needs. -/
theorem isOpenMap_polyEvalHom {k : ℕ} (t : Fin k → A)
    (hTt : Set.range (fun y : ↥T ↦ (divBy (y : A) s : S))
      ⊆ Set.range fun i ↦ (divBy (t i) s : S)) :
    letI := locTopology P T s S hden
    IsOpenMap (polyEvalHom s (S := S) t) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero, Filter.le_map_iff]
  intro V hV
  obtain ⟨W, hW, hWV⟩ := (mem_nhds_subtype _ _ _).mp hV
  obtain ⟨U, -, hUW⟩ :=
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).mem_iff.mp hW
  obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp (U.isOpen.mem_nhds U.zero_mem)
  refine Filter.mem_of_superset
    ((isOpen_locIdealImage P T s S hden n).mem_nhds (locIdealImage P T s S n).zero_mem)
    fun x hx ↦ ?_
  obtain ⟨p, hp, hpx⟩ := exists_polynomial_coeff_mem_idealImage P T s S t hTt n hx
  refine ⟨weightedPolynomialsEquiv isWeightFamily_one_weight p, hWV (hUW ?_), ?_⟩
  · rw [SetLike.mem_coe, mem_weightedNhd]
    intro ν
    rw [weightMul_one_weight, coe_weightedPolynomialsEquiv, coe_weightedPolynomialHom,
      MvPolynomial.coeff_coe]
    exact hn (hp ν)
  · simpa only [polyEvalHom_weightedPolynomialsEquiv_apply] using hpx

/-! ### The polynomial evaluation is continuous -/

omit [NonarchimedeanRing A] in
/-- **A polynomial whose coefficients all lie in the image of `Iⁿ` takes its value at the fractions
inside the `n`-th neighbourhood of `Aₛ`.**

This is the converse direction to
`TauCeti.Huber.PairOfDefinition.exists_polynomial_coeff_mem_idealImage`, and it is what makes the
polynomial evaluation continuous. -/
theorem aeval_mem_locIdealImage_of_coeff_mem {k : ℕ} (t : Fin k → A)
    (hmem : ∀ i, (divBy (t i) s : S) ∈ locSubring P T s S)
    (n : ℕ) {p : MvPolynomial (Fin k) A} (hp : ∀ m, p.coeff m ∈ P.idealImage n) :
    MvPolynomial.aeval (fun i ↦ (divBy (t i) s : S)) p ∈ locIdealImage P T s S n := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine sum_mem fun d _ ↦ ?_
  obtain ⟨y, hy, hyd⟩ := (P.mem_idealImage n).mp (hp d)
  refine locIdealImage_mul_locSubring_subset P T s S n (Set.mul_mem_mul ?_ ?_)
  · exact hyd ▸ algebraMap_mem_locIdealImage P T s S hy
  · exact prod_mem fun i _ ↦ pow_mem (hmem i) _

/-- **The polynomial evaluation is continuous.** -/
theorem continuous_polyEvalHom {k : ℕ} (t : Fin k → A)
    (hmem : ∀ i, (divBy (t i) s : S) ∈ locSubring P T s S) :
    letI := locTopology P T s S hden
    Continuous (polyEvalHom s (S := S) t) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  refine continuous_of_continuousAt_zero (polyEvalHom s (S := S) t) ?_
  rw [ContinuousAt, map_zero, (hasBasis_nhds_zero_locTopology P T s S hden).tendsto_right_iff]
  intro n _
  have hnhd : ∀ᶠ x : weightedPolynomials (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight in nhds 0,
      (x : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
        ∈ weightedNhd (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
          (P.idealImage n) :=
    ((isOpen_weightedNhd (k := k) isWeightFamily_one_weight
      (P.isOpen_idealImage n)).preimage continuous_subtype_val).mem_nhds
      (by simp)
  filter_upwards [hnhd] with x hx
  obtain ⟨p, rfl⟩ : ∃ p, weightedPolynomialsEquiv isWeightFamily_one_weight p = x :=
    ⟨(weightedPolynomialsEquiv isWeightFamily_one_weight).symm x, by simp⟩
  have hcoeff : ∀ m, p.coeff m ∈ P.idealImage n := by
    intro m
    have hx' := (mem_weightedNhd).mp hx m
    rwa [weightMul_one_weight, coe_weightedPolynomialsEquiv, coe_weightedPolynomialHom,
      MvPolynomial.coeff_coe] at hx'
  simpa only [polyEvalHom_weightedPolynomialsEquiv_apply, SetLike.mem_coe] using
    aeval_mem_locIdealImage_of_coeff_mem P T s S t hmem n hcoeff

/-- **The polynomial evaluation is an open quotient map onto `Aₛ`.** It is continuous, open and
surjective, which is the bundled form a consumer of the completion needs: this is what
`AddMonoidHom.surjective_completion` and `AddMonoidHom.isOpenMap_completion` take in order to
conclude the same for `A⟨X₁, …, Xₖ⟩ → A⟨T/s⟩`.

The three hypotheses are independent: surjectivity needs the numerators together with `s` to
generate the unit ideal, openness needs the fractions of `T` to occur among theirs, and
continuity needs each fraction
`tᵢ/s` to lie in the ring of definition. A caller holding `tᵢ ∈ T` gets the last from
`TauCeti.Huber.PairOfDefinition.divBy_mem_locSubring`. -/
theorem isOpenQuotientMap_polyEvalHom {k : ℕ} (t : Fin k → A)
    (hmem : ∀ i, (divBy (t i) s : S) ∈ locSubring P T s S)
    (hspan : Ideal.span (insert s (Set.range t)) = ⊤)
    (hTt : Set.range (fun y : ↥T ↦ (divBy (y : A) s : S))
      ⊆ Set.range fun i ↦ (divBy (t i) s : S)) :
    letI := locTopology P T s S hden
    IsOpenQuotientMap (polyEvalHom s (S := S) t) :=
  letI := locTopology P T s S hden
  ⟨polyEvalHom_surjective s S t hspan, continuous_polyEvalHom P T s S hden t hmem,
    isOpenMap_polyEvalHom P T s S hden t hTt⟩

end PairOfDefinition

end TauCeti.Huber

end
