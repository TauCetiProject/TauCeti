/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Coordinate projections of finite product measures

This file records measure-preserving coordinate projections and refreshes for finite product
measures.

**Projecting along an embedding.** If `e : ι ↪ κ`, restriction of a product-distributed
assignment on `κ` to the coordinates in the image of `e` has the corresponding product law on
`ι`. This is the finite-family form of the fact that a subfamily of independent coordinates is
still independent.

**Currying.** A product measure over the pairs `⟨i, j⟩` of a sigma type is the product over `i`
of the product measures over `j`: `MeasurableEquiv.piCurry` carries one to the other. Mathlib has
this for products of probability measures (`MeasureTheory.Measure.infinitePi_map_piCurry`); here
the factors are σ-finite. It regroups the coordinates of a product of products, for instance when
an orthonormal basis is chosen in each factor of a Euclidean product.

**Reading off a pair of coordinates.** The evaluation map `x ↦ (x a, x b)` at two distinct indices
pushes `Measure.pi μ` forward to `μ a ⊗ μ b`: distinct coordinates of a product measure are
independent, and each single coordinate has law `μ a` (Mathlib's `measurePreserving_eval`). This
is the two-variable companion of `measurePreserving_eval`, and is what transports an
almost-everywhere statement about a pair back to the product space.

**Splitting off one coordinate.** Mathlib's `Equiv.piSplitAt` pushes `Measure.pi μ` forward to
`μ i₀ ⊗ Measure.pi fun j : {i // i ≠ i₀} ↦ μ j`. Mathlib splits a product measure along a
predicate and leaves both halves as products over subtypes; a construction that singles out one
index wants the one-element half collapsed to the factor itself.

**Refreshing a pair of coordinates.** Overwriting two *distinct*
probability coordinates by an independent pair samples the same law: the map

`(z, s, t) ↦ Function.update (Function.update z a s) b t`

pushes `(Measure.pi μ) ⊗ (μ a ⊗ μ b)` forward to `Measure.pi μ`. The two overwritten coordinates
carry the fresh samples and the remaining coordinates keep the ones they had, which is the product
law again.

For `a = b` the pair degenerates to a single refresh because the second update overwrites the
first. The distinctness hypothesis records the two-slot factorisation needed by consumers of this
construction.

**Three and four coordinates.** Mathlib identifies `Fin 2 → β` with `β × β`
(`MeasurableEquiv.finTwoArrow`, `measurePreserving_finTwoArrow`). `finThreeArrow`
and `finFourArrow` are the next two cases, identifying `Fin 3 → β` and `Fin 4 → β`
with the right-nested products `β × β × β` and `β × β × β × β`; under them the product measure
`Measure.pi fun _ => μ` becomes the iterated product of `μ`. The paired version,
`finFourArrowPairPair`, groups alternate coordinates as `((x 0, x 2), (x 1, x 3))` and carries
the product measure to `(μ ⊗ μ) ⊗ (μ ⊗ μ)`.

**Extensionality from boxes.** A finite measure on a finite product space, which need not be a
product measure, is determined by its values on measurable boxes `Set.univ.pi s`, because boxes
form a π-system generating the product σ-algebra and contain the whole space. The same holds on
`γ × (∀ i, α i)` for the products `S ×ˢ Set.univ.pi s`. These are the box analogues of Mathlib's
`MeasureTheory.Measure.ext_prod`; Mathlib's `MeasureTheory.Measure.pi_eq` covers only the case
where one side is a product measure.

**Integrating over fibres.** Splitting the coordinates along a predicate `p` with Mathlib's
`MeasurableEquiv.piEquivPiSubtypeProd`, the product measure of a measurable set is the integral,
over the coordinates outside `p`, of the product measures of its fibres. This is the
finite-product form of `MeasureTheory.Measure.prod_apply_symm`.

## Main statements

* `TauCeti.measurePreserving_pi_comp_embedding` — restricting a product assignment along an
  embedding is measure preserving;
* `TauCeti.measurePreserving_piCurry` — currying a product measure over a sigma type is measure
  preserving;
* `TauCeti.measurePreserving_eval_pair` — reading off two distinct coordinates is measure
  preserving;
* `TauCeti.measurePreserving_piSplitAt` — separating the coordinate `i₀` from the rest is
  measure preserving;
* `TauCeti.measurePreserving_update_update` — the two-coordinate refresh is measure
  preserving;
* `TauCeti.finThreeArrow` and `TauCeti.finFourArrow`, with
  `TauCeti.measurePreserving_finThreeArrow` and `TauCeti.measurePreserving_finFourArrow` — functions
  on `Fin 3` and `Fin 4` as iterated products, carrying `Measure.pi` to the iterated product
  measure;
* `TauCeti.finFourArrowPairPair` and `TauCeti.measurePreserving_finFourArrowPairPair` — functions
  on `Fin 4` as two pairs of alternate coordinates, carrying `Measure.pi` to a product of two
  product measures.
* `MeasureTheory.Measure.ext_pi` — two finite measures on a finite product that agree on
  measurable boxes are equal;
* `MeasureTheory.Measure.ext_prod_pi` — two finite measures on `γ × (∀ i, α i)` that agree
  on products of a measurable set and a measurable box are equal;
* `MeasureTheory.Measure.pi_apply_eq_lintegral_piEquivPiSubtypeProd_symm` — the product measure
  of a set is the integral of the measures of its fibres over the coordinates satisfying a
  predicate.

## Implementation

`measurePreserving_eval_pair` reads the pair law off Mathlib's independence of the coordinates of a
product measure, `ProbabilityTheory.iIndepFun_pi`, through
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`.

The proof of `measurePreserving_update_update` splits the product into the coordinates `{a, b}`
and their complement using Mathlib's measure-preserving product equivalences. The fresh pair
replaces the selected coordinates, while the complementary coordinates are projected from the
original assignment; recombining the two parts is pointwise the double update.
-/

public section

open Function MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

open ProbabilityTheory

/-- Restricting a finite product-distributed assignment along an embedding of index types is
measure preserving. The target product uses exactly the marginals selected by the embedding. -/
theorem measurePreserving_pi_comp_embedding {ι κ : Type*} [Fintype ι] [Fintype κ]
    {α : κ → Type*} [∀ j, MeasurableSpace (α j)] (μ : ∀ j, Measure (α j))
    [∀ j, IsProbabilityMeasure (μ j)] (e : ι ↪ κ) :
    MeasurePreserving (fun x : ∀ j, α j => fun i => x (e i))
      (Measure.pi μ) (Measure.pi fun i => μ (e i)) := by
  refine ⟨measurable_pi_iff.mpr fun i => measurable_pi_apply (e i), ?_⟩
  have hindep : iIndepFun (fun i (x : ∀ j, α j) => x (e i)) (Measure.pi μ) :=
    (iIndepFun_pi (μ := μ) fun _ => aemeasurable_id).precomp e.injective
  rw [hindep.map_fun_eq_pi_map fun i => (measurable_pi_apply (e i)).aemeasurable]
  congr 1
  funext i
  exact (measurePreserving_eval μ (e i)).map_eq

/-- **Currying a finite product measure.** A product measure indexed by the pairs `⟨i, j⟩` with
`j : κ i` is carried by `MeasurableEquiv.piCurry` to the product over `i` of the product measures
over `j`.

Mathlib's `MeasureTheory.Measure.infinitePi_map_piCurry` is the corresponding statement for
products of probability measures; here the factors are only σ-finite. -/
theorem measurePreserving_piCurry {ι : Type*} {κ : ι → Type*} [Fintype ι] [∀ i, Fintype (κ i)]
    {X : ∀ i, κ i → Type*} [∀ i j, MeasurableSpace (X i j)] (μ : ∀ i j, Measure (X i j))
    [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2) (Measure.pi fun i => Measure.pi (μ i)) := by
  refine MeasurePreserving.symm _ ⟨(MeasurableEquiv.piCurry X).symm.measurable,
    (Measure.pi_eq fun s _ => ?_).symm⟩
  have hpre : Sigma.uncurry ⁻¹' univ.pi s = univ.pi fun i => univ.pi fun j => s ⟨i, j⟩ := by
    simpa using uncurry_preimage_sigma_pi univ (fun _ => univ) s
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_piCurry_symm, hpre, Measure.pi_pi,
    ← Finset.univ_sigma_univ, Finset.prod_sigma]
  exact Finset.prod_congr rfl fun i _ => Measure.pi_pi _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]

omit [DecidableEq ι] in
/-- **Two distinct coordinates of a product measure carry the product of their laws.** Reading off
the coordinates `a ≠ b` of a product-distributed assignment pushes `Measure.pi μ` forward to
`μ a ⊗ μ b`.

The one-coordinate statement is Mathlib's `MeasureTheory.measurePreserving_eval`; distinctness is
what makes the pair independent, and hence its law a product. -/
theorem measurePreserving_eval_pair (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] {a b : ι} (hab : a ≠ b) :
    MeasurePreserving (fun x : ∀ i, α i => (x a, x b)) (Measure.pi μ) ((μ a).prod (μ b)) := by
  refine ⟨(measurable_pi_apply a).prodMk (measurable_pi_apply b), ?_⟩
  have hindep : (fun x : ∀ i, α i => x a) ⟂ᵢ[Measure.pi μ] fun x : ∀ i, α i => x b :=
    (iIndepFun_pi (X := fun i => (id : α i → α i)) fun _ => aemeasurable_id).indepFun hab
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply a).aemeasurable
    (measurable_pi_apply b).aemeasurable] at hindep
  rw [hindep, (measurePreserving_eval μ a).map_eq, (measurePreserving_eval μ b).map_eq]

/-- **Splitting off one coordinate of a finite product measure.** Mathlib's `Equiv.piSplitAt`,
which reads a product-distributed assignment as its value at `i₀` paired with its values at the
remaining indices, pushes `Measure.pi μ` forward to
`μ i₀ ⊗ Measure.pi fun j : {i // i ≠ i₀} => μ j`.

This is Mathlib's `MeasureTheory.measurePreserving_piEquivPiSubtypeProd` for the predicate
`(· = i₀)`, with the one-element factor collapsed to `μ i₀`. -/
theorem measurePreserving_piSplitAt (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (i₀ : ι) :
    MeasurePreserving (Equiv.piSplitAt i₀ α)
      (Measure.pi μ) ((μ i₀).prod (Measure.pi fun j : {i // i ≠ i₀} => μ j)) := by
  let _ : Unique {i : ι // i = i₀} := ⟨⟨⟨i₀, rfl⟩⟩, fun x => Subtype.ext x.2⟩
  let _ : Fintype {i : ι // i = i₀} := Subtype.fintype _
  -- Composing the split at `(· = i₀)` with the collapse of its one-element factor evaluates,
  -- coordinate by coordinate, to the pair above.  The application lemmas below reduce both
  -- measurable equivalences to their underlying maps; what is left is that the unique element of
  -- `{i // i = i₀}` is `i₀` and that `i ≠ i₀` is by definition `¬ i = i₀`.
  have hfun : Prod.map (MeasurableEquiv.piUnique fun i : {i : ι // i = i₀} => α i)
        (id : (∀ j : {i : ι // i ≠ i₀}, α j) → ∀ j : {i : ι // i ≠ i₀}, α j) ∘
      MeasurableEquiv.piEquivPiSubtypeProd α (· = i₀)
      = ⇑(Equiv.piSplitAt i₀ α) := by
    funext w
    simp only [Function.comp_apply, MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.coe_mk,
      Equiv.piEquivPiSubtypeProd_apply, Prod.map_apply, id_eq, MeasurableEquiv.piUnique,
      Equiv.piUnique_apply, Equiv.piSplitAt_apply]
    rfl
  rw [← hfun]
  exact ((measurePreserving_piUnique fun i : {i : ι // i = i₀} => μ i).prod
    (MeasurePreserving.id (Measure.pi fun j : {i : ι // i ≠ i₀} => μ j))).comp
    (measurePreserving_piEquivPiSubtypeProd μ (· = i₀))

/-- Overwriting the two distinct coordinates `a` and `b` of a product-distributed assignment by an
independent pair leaves the product law unchanged. -/
theorem measurePreserving_update_update (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] {a b : ι} [IsProbabilityMeasure (μ a)]
    [IsProbabilityMeasure (μ b)] (hab : a ≠ b) :
    MeasurePreserving
      (fun w : (∀ i, α i) × α a × α b => update (update w.1 a w.2.1) b w.2.2)
      ((Measure.pi μ).prod ((μ a).prod (μ b))) (Measure.pi μ) := by
  let s : Finset ι := {a}
  let t : Finset ι := {b}
  have hdis : Disjoint s t := by simp [s, t, hab]
  let p : ι → Prop := fun i => i ∈ s ∪ t
  let splitEquiv := MeasurableEquiv.piEquivPiSubtypeProd α p
  let unionEquiv := MeasurableEquiv.piFinsetUnion α hdis
  let singleA := (MeasurableEquiv.piUnique fun i : s => α i).symm
  let singleB := (MeasurableEquiv.piUnique fun i : t => α i).symm
  have singleA_apply (u : α a) : singleA u ⟨a, by simp [s]⟩ = u := by
    simp only [singleA, MeasurableEquiv.piUnique_symm_apply]
    unfold uniqueElim
    rfl
  have singleB_apply (v : α b) : singleB v ⟨b, by simp [t]⟩ = v := by
    simp only [singleB, MeasurableEquiv.piUnique_symm_apply]
    unfold uniqueElim
    rfl
  -- `MeasurableEquiv.piFinsetUnion` is by definition `Equiv.piFinsetUnion` carrying the
  -- measurability proofs, and Mathlib states the componentwise lemmas
  -- `Equiv.piFinsetUnion_left`/`_right` only for the bare equivalence. Bridge the two once here,
  -- so that neither case below unfolds the measurable-equivalence wrapper again.
  have unionEquiv_coe (w : ((i : s) → α i) × ((i : t) → α i)) :
      unionEquiv w = Equiv.piFinsetUnion α hdis w := rfl
  have unionEquiv_a (u : α a) (v : α b) (ha : a ∈ s ∪ t) :
      unionEquiv (singleA u, singleB v) ⟨a, ha⟩ = u := by
    rw [unionEquiv_coe, Equiv.piFinsetUnion_left α hdis (by simp [s]) ha]
    exact singleA_apply u
  have unionEquiv_b (u : α a) (v : α b) (hb : b ∈ s ∪ t) :
      unionEquiv (singleA u, singleB v) ⟨b, hb⟩ = v := by
    rw [unionEquiv_coe, Equiv.piFinsetUnion_right α hdis (by simp [t]) hb]
    exact singleB_apply v
  have splitEquiv_symm_apply (x : ∀ i : Subtype p, α i)
      (y : ∀ i : {i // ¬p i}, α i) (i : ι) :
      splitEquiv.symm (x, y) i = if hi : p i then x ⟨i, hi⟩ else y ⟨i, hi⟩ :=
    Equiv.piEquivPiSubtypeProd_symm_apply p α (x, y) i
  have splitEquiv_snd_apply (z : ∀ i, α i) (i : ι) (hi : ¬p i) :
      (splitEquiv z).2 ⟨i, hi⟩ = z i := rfl
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ p
  have hsingleA : MeasurePreserving singleA (μ a) (Measure.pi fun i : s => μ i) := by
    simpa [singleA, s] using MeasurePreserving.symm
      (MeasurableEquiv.piUnique fun i : s => α i)
      (measurePreserving_piUnique fun i : s => μ i)
  have hsingleB : MeasurePreserving singleB (μ b) (Measure.pi fun i : t => μ i) := by
    simpa [singleB, t] using MeasurePreserving.symm
      (MeasurableEquiv.piUnique fun i : t => α i)
      (measurePreserving_piUnique fun i : t => μ i)
  have hselected := (measurePreserving_piFinsetUnion hdis μ).comp (hsingleA.prod hsingleB)
  have hpi : (@Measure.pi (Subtype p) (fun i => α i)
      (Finset.Subtype.fintype (s ∪ t)) (fun i => inferInstance) fun i => μ i) =
      @Measure.pi (Subtype p) (fun i => α i) (Subtype.fintype p)
        (fun i => inferInstance) fun i => μ i := by
    congr 1
    exact Subsingleton.elim _ _
  let _ : IsProbabilityMeasure (@Measure.pi (Subtype p) (fun i => α i) (Subtype.fintype p)
      (fun i => inferInstance) fun i => μ i) := by
    rw [← hpi, ← hselected.map_eq]
    infer_instance
  have hrest := measurePreserving_snd.comp hsplit
  have hcombine := (hselected.prod hrest).comp
    (Measure.measurePreserving_swap (μ := Measure.pi μ) (ν := (μ a).prod (μ b)))
  have hcombine' : MeasurePreserving
      (Prod.map ((MeasurableEquiv.piFinsetUnion α hdis) ∘ Prod.map singleA singleB)
        (Prod.snd ∘ MeasurableEquiv.piEquivPiSubtypeProd α p) ∘ Prod.swap)
      ((Measure.pi μ).prod ((μ a).prod (μ b)))
      ((@Measure.pi (Subtype p) (fun i => α i) (Subtype.fintype p)
          (fun i => inferInstance) fun i => μ i).prod
        (Measure.pi fun i : {i // ¬p i} => μ i)) := by
    refine ⟨hcombine.measurable, ?_⟩
    exact hcombine.map_eq.trans
      (congrArg (fun m => m.prod (Measure.pi fun i : {i // ¬p i} => μ i)) hpi)
  have hrefresh := (MeasurePreserving.symm splitEquiv hsplit).comp hcombine'
  refine hrefresh.congr (by fun_prop) (ae_of_all _ fun w => ?_)
  funext i
  -- `MeasurePreserving.comp` stores this composite function definitionally; expose it once, then
  -- use the application lemmas above for all measurable-equivalence wrappers.
  change splitEquiv.symm
      (unionEquiv (singleA w.2.1, singleB w.2.2), (splitEquiv w.1).2) i =
    update (update w.1 a w.2.1) b w.2.2 i
  rw [splitEquiv_symm_apply]
  by_cases hia : i = a
  · subst i
    simp only [p, s, t, Finset.mem_union, Finset.mem_singleton, true_or, dite_true]
    rw [unionEquiv_a]
    simp [hab]
  · by_cases hib : i = b
    · subst i
      rw [update_self]
      simp only [p, s, t, Finset.mem_union, Finset.mem_singleton, or_true, dite_true]
      rw [unionEquiv_b]
    · simp only [p, s, t, Finset.mem_union, Finset.mem_singleton, hia, hib, false_or,
        dite_false]
      rw [splitEquiv_snd_apply]
      rw [update_of_ne hib, update_of_ne hia]

section FinArrow

variable {β : Type*} [MeasurableSpace β]

/-- Functions on `Fin 3` are triples, reading off the three coordinates. Mathlib has the
two-coordinate version, `MeasurableEquiv.finTwoArrow`. -/
def finThreeArrow : (Fin 3 → β) ≃ᵐ β × β × β :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => β) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl β) MeasurableEquiv.finTwoArrow)

/-- `finThreeArrow` reads off the three coordinates. -/
@[simp]
theorem finThreeArrow_apply (x : Fin 3 → β) :
    finThreeArrow x = (x 0, x 1, x 2) := (rfl)

/-- The inverse of `finThreeArrow` sends a triple to the corresponding vector. -/
@[simp]
theorem finThreeArrow_symm_apply (p : β × β × β) :
    finThreeArrow.symm p = ![p.1, p.2.1, p.2.2] :=
  finThreeArrow.symm_apply_eq.2 (by simp)

/-- Under `finThreeArrow` the product measure on `Fin 3 → β` is the iterated
product `μ ⊗ (μ ⊗ μ)`. -/
theorem measurePreserving_finThreeArrow (μ : Measure β) [SigmaFinite μ] :
    MeasurePreserving (finThreeArrow (β := β)) (Measure.pi fun _ : Fin 3 => μ)
      (μ.prod (μ.prod μ)) :=
  ((MeasurePreserving.id μ).prod (measurePreserving_finTwoArrow μ)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0)

/-- Functions on `Fin 4` are quadruples, reading off the four coordinates. -/
def finFourArrow : (Fin 4 → β) ≃ᵐ β × β × β × β :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => β) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl β) finThreeArrow)

/-- `finFourArrow` reads off the four coordinates. -/
@[simp]
theorem finFourArrow_apply (x : Fin 4 → β) :
    finFourArrow x = (x 0, x 1, x 2, x 3) := (rfl)

/-- The inverse of `finFourArrow` sends a quadruple to the corresponding
vector. -/
@[simp]
theorem finFourArrow_symm_apply (p : β × β × β × β) :
    finFourArrow.symm p = ![p.1, p.2.1, p.2.2.1, p.2.2.2] :=
  finFourArrow.symm_apply_eq.2 (by simp)

/-- Under `finFourArrow` the product measure on `Fin 4 → β` is the iterated
product `μ ⊗ (μ ⊗ (μ ⊗ μ))`. -/
theorem measurePreserving_finFourArrow (μ : Measure β) [SigmaFinite μ] :
    MeasurePreserving (finFourArrow (β := β)) (Measure.pi fun _ : Fin 4 => μ)
      (μ.prod (μ.prod (μ.prod μ))) :=
  ((MeasurePreserving.id μ).prod (measurePreserving_finThreeArrow μ)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 4 => μ) 0)

/-- Functions on `Fin 4` are two pairs of alternate coordinates. -/
def finFourArrowPairPair : (Fin 4 → β) ≃ᵐ (β × β) × (β × β) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => β) (Equiv.swap 1 2)).trans
    finFourArrow).trans MeasurableEquiv.prodAssoc.symm

/-- `finFourArrowPairPair` groups the zeroth and second coordinates, then the first and third. -/
@[simp]
theorem finFourArrowPairPair_apply (x : Fin 4 → β) :
    finFourArrowPairPair x = ((x 0, x 2), (x 1, x 3)) := by
  simp [finFourArrowPairPair, finFourArrow_apply, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply, Equiv.swap_apply_def]

/-- The inverse of `finFourArrowPairPair` interleaves the two pairs. -/
@[simp]
theorem finFourArrowPairPair_symm_apply (p : (β × β) × (β × β)) :
    finFourArrowPairPair.symm p = ![p.1.1, p.2.1, p.1.2, p.2.2] :=
  finFourArrowPairPair.symm_apply_eq.2 (by simp)

/-- Under `finFourArrowPairPair` the product measure on `Fin 4 → β` is
`(μ ⊗ μ) ⊗ (μ ⊗ μ)`. -/
theorem measurePreserving_finFourArrowPairPair (μ : Measure β) [SigmaFinite μ] :
    MeasurePreserving (finFourArrowPairPair (β := β)) (Measure.pi fun _ : Fin 4 => μ)
      ((μ.prod μ).prod (μ.prod μ)) :=
  (measurePreserving_prodAssoc μ μ (μ.prod μ)).symm.comp
    ((measurePreserving_finFourArrow μ).comp
      (measurePreserving_piCongrLeft (fun _ : Fin 4 => μ) (Equiv.swap 1 2)))

end FinArrow

end TauCeti

namespace MeasureTheory.Measure

variable {ι : Type*} [Finite ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- **Finite measures on a finite product are determined by boxes.** Two measures on
`∀ i, α i` agreeing on every measurable box `Set.univ.pi s` are equal, provided the first is finite;
the box `Set.univ` then makes the second finite too. -/
theorem ext_pi {μ ν : Measure (∀ i, α i)} [IsFiniteMeasure μ]
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) → μ (univ.pi s) = ν (univ.pi s)) :
    μ = ν := by
  refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact h s fun i ↦ hs i (mem_univ i)
  · simpa using h (fun _ ↦ univ) fun _ ↦ .univ

/-- **Finite measures on `γ × (∀ i, α i)` are determined by box rectangles.** Two measures agreeing
on every product `S ×ˢ Set.univ.pi s` of a measurable set and a measurable box are equal, provided
the first is finite. -/
theorem ext_prod_pi {γ : Type*} [MeasurableSpace γ] {μ ν : Measure (γ × ∀ i, α i)}
    [IsFiniteMeasure μ]
    (h : ∀ S : Set γ, MeasurableSet S → ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) →
      μ (S ×ˢ univ.pi s) = ν (S ×ˢ univ.pi s)) :
    μ = ν := by
  refine ext_of_generate_finite (image2 (· ×ˢ ·) {S : Set γ | MeasurableSet S}
    (univ.pi '' univ.pi fun i ↦ {s : Set (α i) | MeasurableSet s})) ?_ ?_ ?_ ?_
  · exact (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      isCountablySpanning_measurableSet
      (IsCountablySpanning.pi fun _ ↦ isCountablySpanning_measurableSet)).symm
  · exact MeasurableSpace.isPiSystem_measurableSet.prod isPiSystem_pi
  · rintro _ ⟨S, hS, _, ⟨s, hs, rfl⟩, rfl⟩
    exact h S hS s fun i ↦ hs i (mem_univ i)
  · simpa using h univ .univ (fun _ ↦ univ) fun _ ↦ .univ

/-- **Fibres over a set of coordinates.** The measure of a set under a finite product measure is
the integral, over the coordinates outside `p`, of the product measures of its fibres over the
coordinates in `p`. This is `MeasureTheory.Measure.prod_apply_symm` transported along Mathlib's
splitting `MeasurableEquiv.piEquivPiSubtypeProd` of the coordinates. -/
theorem pi_apply_eq_lintegral_piEquivPiSubtypeProd_symm {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (p : ι → Prop) [DecidablePred p] {s : Set (∀ i, α i)} (hs : MeasurableSet s) :
    Measure.pi μ s = ∫⁻ z, Measure.pi (fun i : {i // p i} ↦ μ i)
      {y | (MeasurableEquiv.piEquivPiSubtypeProd α p).symm (y, z) ∈ s}
        ∂Measure.pi fun i : {i // ¬p i} ↦ μ i := by
  rw [← (measurePreserving_piEquivPiSubtypeProd μ p).symm.measure_preimage hs.nullMeasurableSet,
    Measure.prod_apply_symm ((MeasurableEquiv.piEquivPiSubtypeProd α p).symm.measurable hs)]
  rfl

end MeasureTheory.Measure
