/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.Defs
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.Topology.Category.TopCat.Monoidal

/-!
# Restrictions of the Leray–Hirsch map

Let `k` be a commutative ring, `p : E ⟶ B` a continuous map, and `e d : ι d → Hᵈ(E; k)` a family
of global classes on `E`. This file restricts the Leray–Hirsch map `TopCat.lerayHirsch` of `p`
over subsets of the base and to fibres.

Over a subset `S` of `B`, the restriction `p⁻¹ S ⟶ S` of `p` with the restricted classes has its own
Leray–Hirsch map (`TopCat.lerayHirschRestrict`), natural in `S`. It is bijective over the empty set
(`TopCat.lerayHirschRestrict_empty_bijective`, from `TopCat.lerayHirsch_bijective_of_isEmpty`), and
over all of `B` it is bijective exactly when the Leray–Hirsch map of `p` is
(`TopCat.lerayHirschRestrict_univ_bijective_iff`). These are the endpoints of an induction over
open covers of `B`.

On a fibre, restricting the image of `g` along a map `f : F ⟶ E` into the fibre over `x` gives the
combination of the restricted classes `f^* e` with coefficients the values at `x` of the
base-degree-zero components of `g` (`TopCat.singularCohomologyMap_lerayHirsch_of_comp_eq_const`),
since positive-degree classes of the base pull back to zero on a point. For the product
`X × F ⟶ X` and the fibre inclusion `f ↦ (x, f)` this is
`TopCat.singularCohomologyMap_prodFiberInclusion_lerayHirsch`.

## Main definitions and results

* `TopCat.lerayHirsch_bijective_of_isEmpty`: the Leray–Hirsch map over an empty base.
* `TopCat.lerayHirschRestrict`: the Leray–Hirsch map of the restriction of `p` over a subset of
  `B`, natural in the subset (`TopCat.lerayHirschRestrict_lof_inclusion`,
  `TopCat.lerayHirschRestrict_lof_subtypeVal`,
  `TopCat.lerayHirschRestrict_restrictPreimage_bijective_iff`).
* `TopCat.lerayHirschRestrict_empty_bijective`, `TopCat.lerayHirschRestrict_univ_bijective_iff`:
  the Leray–Hirsch map over the empty set and over all of `B`.
* `TopCat.singularCohomologyMap_lerayHirsch_of_comp_eq_const`,
  `TopCat.singularCohomologyMap_prodFiberInclusion_lerayHirsch`: the restriction to a fibre.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped DirectSum

universe w u

namespace TopCat

variable {k : Type w} [CommRing k]

section Empty

variable {E B : TopCat.{w}} (p : E ⟶ B) (n : ℕ) {ι : ℕ → Type u} [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- The Leray–Hirsch map over an empty base is bijective: its source and target vanish. -/
lemma lerayHirsch_bijective_of_isEmpty [IsEmpty B] : Function.Bijective (lerayHirsch p n e) := by
  have : IsEmpty E := Function.isEmpty p
  have := ModuleCat.subsingleton_of_isZero
    (TauCeti.isZero_singularCohomology_of_isEmpty (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) E n)
  have (j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1) :=
    ModuleCat.subsingleton_of_isZero
      (TauCeti.isZero_singularCohomology_of_isEmpty (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) B j.1.val.2)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end Empty

section Restrict

variable {E B : TopCat.{w}} (p : E ⟶ B) {ι : ℕ → Type u} [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- The Leray–Hirsch map in degree `n` of the restriction `p⁻¹ S ⟶ S` of `p` over a subset `S` of
`B`, with the restrictions of the classes `e` to `p⁻¹ S`. -/
abbrev lerayHirschRestrict (S : Set B) (n : ℕ) :=
  lerayHirsch (ofHom (p.hom.restrictPreimage S)) n
    (fun d i ↦ TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (p ⁻¹' S))) d (e d i))

/-- The Leray–Hirsch map over a smaller subset `S ⊆ T` of `B` sends the restriction of a class to
the restriction of its image under the Leray–Hirsch map over `T`. -/
lemma lerayHirschRestrict_lof_inclusion {S T : Set B} (hST : S ⊆ T) (m d q : ℕ) (h : d + q = m)
    (i : ι d) (a : (of T).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirschRestrict p e S m (DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = m}, ι pq.val.1 ↦
          (of S).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
        ⟨⟨(d, q), h⟩, i⟩
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion hST)) q a)) =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion (Set.preimage_mono hST))) m
        (lerayHirschRestrict p e T m (DirectSum.lof k _
          (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = m}, ι pq.val.1 ↦
            (of T).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
          ⟨⟨(d, q), h⟩, i⟩ a)) :=
  lerayHirsch_lof_naturality _ _ (by ext; rfl) d q h i (by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp]
    -- The inclusion `p⁻¹ S ⟶ p⁻¹ T` followed by `p⁻¹ T ⟶ E` is `p⁻¹ S ⟶ E`, pointwise by `rfl`.
    congr 2) a

/-- The Leray–Hirsch map over a subset `S` of `B` sends the restriction of a class of `B` to the
restriction of its image under the Leray–Hirsch map of `p`. -/
lemma lerayHirschRestrict_lof_subtypeVal (S : Set B) (m d q : ℕ) (h : d + q = m) (i : ι d)
    (a : B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirschRestrict p e S m (DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = m}, ι pq.val.1 ↦
          (of S).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
        ⟨⟨(d, q), h⟩, i⟩
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal S)) q a)) =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (p ⁻¹' S))) m
        (lerayHirsch p m e (DirectSum.lof k _
          (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = m}, ι pq.val.1 ↦
            B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
          ⟨⟨(d, q), h⟩, i⟩ a)) :=
  lerayHirsch_lof_naturality _ _ (by ext; rfl) d q h i rfl a

/-- Restricting first over `W` and then over the preimage of `S ⊆ W` in `W` is restricting over
`S`, up to homeomorphisms over homeomorphisms; so the two Leray–Hirsch maps are bijective
together. -/
lemma lerayHirschRestrict_restrictPreimage_bijective_iff {W S : Set B} (hSW : S ⊆ W) (m : ℕ) :
    Function.Bijective (lerayHirschRestrict (ofHom (p.hom.restrictPreimage W))
      (fun d i ↦ TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (p ⁻¹' W))) d
        (e d i)) ((↑) ⁻¹' S : Set ↥W) m) ↔
      Function.Bijective (lerayHirschRestrict p e S m) := by
  have hS : S ⊆ Set.range ((↑) : W → B) := by rwa [Subtype.range_coe]
  have hpS : p ⁻¹' S ⊆ Set.range ((↑) : p ⁻¹' W → E) := by
    rw [Subtype.range_coe]
    exact Set.preimage_mono hSW
  exact lerayHirsch_bijective_iff_of_isIso
    (isoOfHomeo (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hpS)).hom
    (isoOfHomeo (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hS)).hom
    (by ext; rfl) fun d _ i ↦ by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_comp]
    -- Both composites are the inclusion `p⁻¹ S ⟶ E`, pointwise by `rfl`.
    congr 2

/-- The Leray–Hirsch map over all of `B` is bijective if and only if the Leray–Hirsch map of `p`
is. -/
lemma lerayHirschRestrict_univ_bijective_iff (m : ℕ) :
    Function.Bijective (lerayHirschRestrict p e Set.univ m) ↔
      Function.Bijective (lerayHirsch p m e) := by
  -- The inclusions of `p⁻¹ B` into `E` and of `B` into itself are homeomorphisms.
  have : IsIso (ofHom (ContinuousMap.subtypeVal (p ⁻¹' Set.univ))) :=
    (isIso_iff_isHomeomorph _).2
      ((Homeomorph.setCongr (Set.preimage_univ (f := ⇑p))).trans
        (Homeomorph.Set.univ E)).isHomeomorph
  have : IsIso (ofHom (ContinuousMap.subtypeVal (Set.univ : Set B))) :=
    (isIso_iff_isHomeomorph _).2 (Homeomorph.Set.univ B).isHomeomorph
  exact lerayHirsch_bijective_iff_of_isIso (ofHom (ContinuousMap.subtypeVal _))
    (ofHom (ContinuousMap.subtypeVal _)) (by ext; rfl) fun _ _ _ ↦ rfl

/-- The Leray–Hirsch map over the empty subset of `B` is bijective: its source and target vanish.
This is the base case of an induction over finite open covers of `B`. -/
lemma lerayHirschRestrict_empty_bijective (m : ℕ) :
    Function.Bijective (lerayHirschRestrict p e ∅ m) :=
  lerayHirsch_bijective_of_isEmpty _ m _

end Restrict


section Fiber

variable {X F : TopCat.{w}} {ι : ℕ → Type u} [∀ p, DecidableEq (ι p)]

/-- **The restriction of the Leray–Hirsch map to a fibre**: if `f : F ⟶ E` lands in the fibre of
`π : E ⟶ B` over `x`, restricting the image of `g` along `f` gives the combination of the
restricted classes `f^* e p i'` with coefficients the values at `x` of the base-degree-zero
components of `g`. -/
theorem singularCohomologyMap_lerayHirsch_of_comp_eq_const {E B : TopCat.{w}} (π : E ⟶ B)
    (f : F ⟶ E) (x : B) (hf : f ≫ π = TopCat.const (X := F) x) (p : ℕ)
    [Fintype (ι p)]
    (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)
    (g : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.val.1,
      B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2) :
    TopCat.singularCohomologyMap f p (lerayHirsch π p e g) =
      ∑ i', TauCeti.singularCohomologyZeroEval x (g ⟨⟨(p, 0), add_zero p⟩, i'⟩) •
        TopCat.singularCohomologyMap f p (e p i') := by
  -- In positive degrees the constant map induces zero.
  have hpos {q : ℕ} (hq : q ≠ 0) :
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := 𝟙_ (ModuleCat.{w} k)) (TopCat.const (X := F) x) q = 0 :=
    singularCohomologyMap_eq_zero_of_nullhomotopic (by
      rw [show (TopCat.const (X := F) x).hom = ContinuousMap.const F x from
        ContinuousMap.ext fun _ ↦ TopCat.const_apply _ _]
      exact ContinuousMap.nullhomotopic_of_constant x) hq
  have hlof (q' p' : ℕ) (h' : p' + q' = p) (i : ι p')
      (β : B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q') :
      TopCat.singularCohomologyMap f p (lerayHirsch π p e (DirectSum.of
          (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.val.1 ↦
            B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
          ⟨⟨(p', q'), h'⟩, i⟩ β)) =
        F.singularCup k (λ_ _).inv (λ_ _).hom q' p' p (by omega)
          (TopCat.singularCohomologyMap (TopCat.const (X := F) x) q' β)
          (TopCat.singularCohomologyMap f p' (e p' i)) := by
    rw [← DirectSum.lof_eq_of k, lerayHirsch_lof, ← singularCup_naturality,
      ← ConcreteCategory.comp_apply, ← singularCohomologyMap_comp, hf]
  induction g using DirectSum.induction_on with
  | zero => simp
  | add g g' hg hg' =>
    simp only [map_add, hg, hg', DirectSum.add_apply, add_smul, Finset.sum_add_distrib]
  | of j β =>
    obtain ⟨⟨⟨p', q'⟩, h'⟩, i⟩ := j
    rw [hlof]
    by_cases hq : q' = 0
    · subst hq
      obtain rfl : p' = p := by omega
      rw [TauCeti.singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul,
        LinearMap.map_smul₂,
        singularCup_singularCohomologyZeroOne_left, Finset.sum_eq_single i]
      · rw [DirectSum.of_eq_same]
      · intro l _ hl
        have : (DirectSum.of (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p'}, ι pq.val.1 ↦
            B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
            ⟨⟨(p', 0), h'⟩, i⟩ β) ⟨⟨(p', 0), add_zero p'⟩, l⟩ = 0 :=
          DirectSum.of_eq_of_ne _ _ _ fun he ↦ hl (eq_of_heq (Sigma.mk.inj_iff.1 he).2)
        rw [this, map_zero, zero_smul]
      · simp
    · simp only [hpos hq, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
      refine (Finset.sum_eq_zero fun l _ ↦ ?_).symm
      have : (DirectSum.of (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.val.1 ↦
          B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
          ⟨⟨(p', q'), h'⟩, i⟩ β) ⟨⟨(p, 0), add_zero p⟩, l⟩ = 0 :=
        DirectSum.of_eq_of_ne _ _ _ fun he ↦ hq (congrArg
          (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.val.1 ↦ j.1.val.2) he).symm
      rw [this, map_zero, zero_smul]

/-- **The restriction of the Leray–Hirsch map of the product to a fibre**: for the pullbacks
`pr₂^* b` of classes `b` on `F`, restricting the image of `g` to the fibre over `x` gives the
combination of the classes `b` with coefficients the values at `x` of the base-degree-zero
components of `g`. -/
theorem singularCohomologyMap_prodFiberInclusion_lerayHirsch (x : X) (p : ℕ) [Fintype (ι p)]
    (b : ∀ p, ι p → F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (g : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = p}, ι pq.val.1,
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2) :
    TopCat.singularCohomologyMap (prodFiberInclusion X F x) p
        (lerayHirsch (fst X F) p (fun p i ↦ TopCat.singularCohomologyMap (snd X F) p (b p i)) g) =
      ∑ i', TauCeti.singularCohomologyZeroEval x (g ⟨⟨(p, 0), add_zero p⟩, i'⟩) • b p i' := by
  rw [singularCohomologyMap_lerayHirsch_of_comp_eq_const _ _ x (prodFiberInclusion_fst X F x)]
  refine Finset.sum_congr rfl fun i' _ ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← singularCohomologyMap_comp, prodFiberInclusion_snd,
    singularCohomologyMap_id, ConcreteCategory.id_apply]

end Fiber

end TopCat
