/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.FiberwiseBasis
public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.MayerVietoris
public import TauCeti.Topology.Category.TopCat.Trivialization

/-!
# The Leray–Hirsch theorem over a base with a finite trivializing cover

Let `k` be a commutative ring, `p : E ⟶ B` a continuous map and `e d : ι d → Hᵈ(E; k)` families of
global classes, with Leray–Hirsch map
`⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ Hⁿ(E; k)`, `(a_{d,i}) ↦ ∑ p^* a_{d,i} ⌣ e_{d,i}`
(`TopCat.lerayHirsch`).

This file proves the Leray–Hirsch theorem when `B` has a finite cover by base sets of
trivializations of `p`, by induction over the cover from the trivial case.

* **Induction over a finite open cover** (`TopCat.lerayHirsch_bijective_of_finite_cover`): if the
  Leray–Hirsch maps over all open subsets of each member of a finite open cover of `B` are
  bijective in degrees `m ≤ n`, so is that of `p`. For an open `W`, the set
  `W ∩ (U ∪ ⋃_{i ∈ t} U i)` is the union of `W ∩ U` and `W ∩ ⋃_{i ∈ t} U i`, whose intersection is
  `(W ∩ U) ∩ ⋃_{i ∈ t} U i`; the Mayer–Vietoris gluing step
  `TopCat.lerayHirschRestrict_union_bijective` and induction over `t`, for all `W` at once, conclude
  (`TopCat.lerayHirschRestrict_inter_biUnion_bijective`).
* **The trivial case** (`TopCat.lerayHirschRestrict_bijective_of_trivialization`): over a subset `S`
  of the base set of a trivialization `t`, the homeomorphism `p⁻¹ S ≃ S × F` of `t` identifies the
  restriction of `p` with the projection `S × F ⟶ S`, and
  `TopCat.lerayHirsch_fst_bijective_of_fiberwise_basis` applies when the classes restrict to a
  basis of the cohomology of every fibre, read through the fibre inclusions `f ↦ t⁻¹(x, f)`
  (`Bundle.Trivialization.fiberInclusion`).

## Main results

* `TopCat.lerayHirsch_bijective_of_finite_cover`: the induction over a finite open cover.
* `TopCat.lerayHirschRestrict_bijective_of_trivialization`: the Leray–Hirsch map over a
  trivializing set.
* `TopCat.lerayHirsch_bijective_of_trivializations`: **the Leray–Hirsch theorem** for a map with
  finitely many trivializations covering the base.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch) and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology
open scoped DirectSum

universe w u

namespace TopCat

variable {k : Type w} [CommRing k]

section Induction

variable {E B : TopCat.{w}} (p : E ⟶ B) {ι : ℕ → Type u} [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- The induction over a finite family of open sets behind
`TopCat.lerayHirsch_bijective_of_finite_cover`: if the Leray–Hirsch maps over all open subsets of
each `U i`, `i ∈ s`, are bijective in degrees `m ≤ n`, then so are those over `W ∩ ⋃_{i ∈ s} U i`
for every open `W`. -/
theorem lerayHirschRestrict_inter_biUnion_bijective {κ : Type*} (U : κ → Set B) (n : ℕ)
    (s : Finset κ) (hU : ∀ i ∈ s, IsOpen (U i))
    (hloc : ∀ i ∈ s, ∀ S : Set B, IsOpen S → S ⊆ U i →
      ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e S m))
    {W : Set B} (hW : IsOpen W) :
    ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e (W ∩ ⋃ i ∈ s, U i) m) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    intro m _
    rw [show W ∩ ⋃ i ∈ (∅ : Finset κ), U i = ∅ by simp]
    exact lerayHirschRestrict_empty_bijective p e m
  | insert j t _ ih =>
    have hU' : ∀ i ∈ t, IsOpen (U i) := fun i hi ↦ hU i (Finset.mem_insert_of_mem hi)
    have hloc' := fun i hi ↦ hloc i (Finset.mem_insert_of_mem hi)
    have hWj : IsOpen (W ∩ U j) := hW.inter (hU j (Finset.mem_insert_self j t))
    have hT : IsOpen (⋃ i ∈ t, U i) := isOpen_biUnion hU'
    rw [show W ∩ ⋃ i ∈ insert j t, U i = (W ∩ U j) ∪ (W ∩ ⋃ i ∈ t, U i) by
      rw [Finset.set_biUnion_insert, Set.inter_union_distrib_left]]
    refine lerayHirschRestrict_union_bijective p e (hWj.preimage continuous_subtypeVal)
      ((hW.inter hT).preimage continuous_subtypeVal) n
      (hloc j (Finset.mem_insert_self j t) _ hWj Set.inter_subset_right) (ih hU' hloc' hW) ?_
    rw [show W ∩ U j ∩ (W ∩ ⋃ i ∈ t, U i) = (W ∩ U j) ∩ ⋃ i ∈ t, U i by
      rw [← Set.inter_assoc, Set.inter_right_comm W (U j) W, Set.inter_self]]
    exact ih hU' hloc' hWj

/-- **The Leray–Hirsch map over a finite open cover.** Let `U i`, `i ∈ s`, be finitely many open
sets covering `B`. If for each `i` the Leray–Hirsch maps of the restrictions of `p` over all open
subsets of `U i`, with the restricted classes, are bijective in degrees `m ≤ n`, then so is the
Leray–Hirsch map of `p`. -/
theorem lerayHirsch_bijective_of_finite_cover {κ : Type*} (U : κ → Set B) (n : ℕ)
    (s : Finset κ) (hU : ∀ i ∈ s, IsOpen (U i)) (hcover : ⋃ i ∈ s, U i = Set.univ)
    (hloc : ∀ i ∈ s, ∀ S : Set B, IsOpen S → S ⊆ U i →
      ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e S m)) :
    ∀ m ≤ n, Function.Bijective (lerayHirsch p m e) := by
  intro m hm
  have h := lerayHirschRestrict_inter_biUnion_bijective p e U n s hU hloc isOpen_univ m hm
  rw [hcover, Set.univ_inter] at h
  exact (lerayHirschRestrict_univ_bijective_iff p e m).1 h

end Induction

section Trivialization

variable {E B F : TopCat.{w}} {p : E ⟶ B}

variable {ι : ℕ → Type u} [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)
  [∀ d, Projective (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
    (𝟙_ (ModuleCat.{w} k))).obj F)]

/-- **The Leray–Hirsch map over a trivializing set.** Let `t` be a trivialization of `p` with
model fibre `F`, whose homology `H_d(F; k)` is projective, and finitely generated for `d ≤ n`, and
let `S` be contained in the base set of `t`. Suppose that for every point `x` of `S` and every
`d ≤ n` the classes `e d i` restrict along the fibre inclusion `f ↦ t⁻¹(x, f)` to a basis of
`Hᵈ(F; k)`. Then the Leray–Hirsch map of the restriction of `p` over `S` is bijective in
degree `n`. -/
theorem lerayHirschRestrict_bijective_of_trivialization (t : Bundle.Trivialization F p) {S : Set B}
    (hS : S ⊆ t.baseSet) (n : ℕ)
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hc : ∀ x (hx : x ∈ S), ∀ d ≤ n,
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap
        (t.fiberInclusion (hS hx)) d (e d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦
        TopCat.singularCohomologyMap (t.fiberInclusion (hS hx)) d (e d i))) :
    Function.Bijective (lerayHirschRestrict p e S n) := by
  refine (lerayHirsch_bijective_iff_of_isIso (t.preimageIso hS).hom (𝟙 _)
    (by rw [t.preimageIso_hom_comp, Category.comp_id]) (fun _ _ _ ↦ rfl)).1
    (lerayHirsch_fst_bijective_of_fiberwise_basis (of S) n _ hF fun x d hd ↦ ?_)
  simp only [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    t.prodFiberInclusion_comp_preimageIso_hom]
  exact hc x x.property d hd

/-- **The Leray–Hirsch theorem over a base with a finite trivializing cover.** Let `p : E ⟶ B` have
finitely many trivializations `t i`, `i ∈ s`, with model fibre `F`, whose base sets cover `B`;
let the homology `H_d(F; k)` be projective, and finitely generated for `d ≤ n`. Suppose that for
every `i ∈ s`, every point `x` of the base set of `t i` and every `d ≤ n`, the classes `e d i'`
restrict along the fibre inclusion `f ↦ (t i)⁻¹(x, f)` to a basis of `Hᵈ(F; k)`. Then the
Leray–Hirsch map
`⨁_{d + q = m} ⨁_{i' : ι d} H^q(B; k) ⟶ Hᵐ(E; k)`, `(a_{d,i'}) ↦ ∑ p^* a_{d,i'} ⌣ e_{d,i'}`,
is bijective in every degree `m ≤ n`. -/
theorem lerayHirsch_bijective_of_trivializations {κ : Type*} (s : Finset κ)
    (t : κ → Bundle.Trivialization F p) (hcover : ⋃ i ∈ s, (t i).baseSet = Set.univ) (n : ℕ)
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hc : ∀ i ∈ s, ∀ x (hx : x ∈ (t i).baseSet), ∀ d ≤ n,
      LinearIndependent k (fun i' ↦ TopCat.singularCohomologyMap
        ((t i).fiberInclusion hx) d (e d i')) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i' ↦
        TopCat.singularCohomologyMap ((t i).fiberInclusion hx) d (e d i'))) :
    ∀ m ≤ n, Function.Bijective (lerayHirsch p m e) :=
  lerayHirsch_bijective_of_finite_cover p e (fun i ↦ (t i).baseSet) n s
    (fun i _ ↦ (t i).open_baseSet) hcover fun i hi _ _ hS m hm ↦
      lerayHirschRestrict_bijective_of_trivialization e (t i) hS m
        (fun d hd ↦ hF d (hd.trans hm)) fun x hx d hd ↦ hc i hi x (hS hx) d (hd.trans hm)

end Trivialization

end TopCat
