/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.DivisorClass
public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Morphisms.OpenImmersion
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Restriction of Chow groups to an open subscheme, and the localization sequence

Let `k` be a field and `j : U ⟶ X` an open immersion of schemes locally of finite type over `k`.
Restriction of cycles `α ↦ α ∘ j` (`Chow.cyclesRestrict`) sends cycles rationally equivalent to
zero on `X` to cycles rationally equivalent to zero on `U`, and every cycle rationally equivalent
to zero on `U` arises in this way. Hence restriction descends to Chow groups, and with the
pushforward along the complementary closed immersion it gives the localization sequence
`CH_n(Z) → CH_n(X) → CH_n(U) → 0` (Fulton, *Intersection Theory*, Proposition 1.8;
[Stacks, Lemma 42.19.3](https://stacks.math.columbia.edu/tag/02RX)).

* `Chow.cyclesRestrict_mem_ratEquiv`: restriction preserves rational equivalence. A subscheme
  `W` of the family restricts to `W ∩ U`, the pullback of `W` along `j`, with the restricted
  rational function; orders of vanishing are local (`Scheme.ord_functionFieldMap`).
* `Chow.map_cyclesRestrict_ratEquiv`: the image of `RatEquiv X n` under restriction is all of
  `RatEquiv U n`. An integral closed subscheme `W` of `U` extends to its scheme-theoretic closure
  in `X`, which contains `W` as a dense open subscheme with the same function field, and a
  locally finite family of subschemes of `U` has locally finite closures in `X`, since `X` is
  covered by Noetherian opens (`LocallyFinite.closure_image_of_isOpenImmersion`). The extended
  family is a family of `n`-cycles by `Chow.RatEquivFamily.cycle_mem_cyclesOfDimension`.
* `Chow.ChowGroup.restrict k j`: the induced restriction `CH_n(X) →+ CH_n(U)`, functorial in `j`
  (`Chow.ChowGroup.restrict_id`, `Chow.ChowGroup.restrict_comp`) and surjective
  (`Chow.ChowGroup.restrict_surjective`).
* `Chow.ChowGroup.range_pushforward_eq_ker_restrict`: **the localization sequence**. If the image
  of a closed immersion `i : Z ⟶ X` is the complement of the image of `j`, then the classes on `X`
  restricting to zero on `U` are exactly those pushed forward from `Z`.
-/

public section

open AlgebraicGeometry Order CategoryTheory Limits Topology

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] {X U : Scheme.{u}}
  [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]

section Restriction

variable {k} [IsLocallyNoetherian X] [IsLocallyNoetherian U] (j : U ⟶ X) [IsOpenImmersion j]
  [j.IsOver (Spec (.of k))]

variable (k) in
include k in
omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] in
/-- Over a field, consider a commutative square `i ≫ j = f ≫ i'` with `j` the open immersion,
`i` and `i'` closed immersions of irreducible schemes and `f` dominant. Then the generic points of
the sources of `i` and `i'` have the same dimension. -/
private lemma genericPoint_mem_pointsOfDimension_iff {W W' : Scheme.{u}} [IrreducibleSpace W]
    [IrreducibleSpace W'] {i : W ⟶ U} {i' : W' ⟶ X} [IsClosedImmersion i] [IsClosedImmersion i']
    {f : W ⟶ W'} [IsDominant f] (h : i ≫ j = f ≫ i') {n : ℤ} :
    genericPoint W ∈ pointsOfDimension W n ↔ genericPoint W' ∈ pointsOfDimension W' n := by
  rw [mem_pointsOfDimension, mem_pointsOfDimension, ← i.height_apply_eq_height,
    ← height_apply_of_isOpenImmersion k j, ← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply,
    i'.height_apply_eq_height, f.genericPoint_eq_of_isDominant]

namespace RatEquivFamily

variable (k)

/-- The restriction of a family of integral closed subschemes with rational functions to an open
subscheme `j : U ⟶ X`: the members `W` meeting `U` are replaced by their pullbacks `W ×_X U`, with
the pulled-back rational functions. -/
private noncomputable def restrict {n : ℤ} (F : RatEquivFamily X n) : RatEquivFamily U n :=
  have hI (a : {a : F.ι // (Set.range (F.i a) ∩ Set.range j).Nonempty}) :=
    isIntegral_pullback_of_isOpenImmersion (F.i a.1) j a.2
  { ι := {a : F.ι // (Set.range (F.i a) ∩ Set.range j).Nonempty}
    W a := pullback (F.i a.1) j
    i a := pullback.snd (F.i a.1) j
    isIntegral := hI
    genericPoint_mem a :=
      have := hI a
      (genericPoint_mem_pointsOfDimension_iff k j pullback.condition.symm).mpr
        (F.genericPoint_mem a.1)
    r a :=
      have := hI a
      Units.map (pullback.fst (F.i a.1) j).functionFieldMap.hom.toMonoidHom (F.r a.1)
    locallyFinite := by
      refine ((F.locallyFinite.preimage_continuous j.continuous).comp_injective
        Subtype.val_injective).subset fun a ↦ ?_
      -- The `a`-th member is `pullback.snd`, whose range is the preimage of the range of `F.i a`.
      exact (Scheme.Pullback.range_snd (F.i a.1) j).subset }

variable {k}

private lemma component_restrict_apply {n : ℤ} (F : RatEquivFamily X n)
    (a : (F.restrict k j).ι) (u : U) :
    (F.restrict k j).component a u = F.component a.1 (j u) := by
  by_cases hu : u ∈ Set.range (pullback.snd (F.i a.1) j)
  · obtain ⟨p, rfl⟩ := hu
    have := isIntegral_pullback_of_isOpenImmersion (F.i a.1) j a.2
    have := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (F.i a.1) j)
    -- The `a`-th member of `F.restrict k j` is `W ×_X U ⟶ U` with the pulled-back function.
    refine ((F.restrict k j).component_apply a p).trans ?_
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, F.component_apply]
    exact Scheme.ord_functionFieldMap (pullback.fst (F.i a.1) j) _ p
  · rw [(F.restrict k j).component_apply_eq_zero_of_notMem_range a hu]
    rw [Scheme.Pullback.range_snd] at hu
    exact (F.component_apply_eq_zero_of_notMem_range a.1 hu).symm

/-- The cycle of the restriction of a family is the restriction of its cycle. -/
private lemma cycle_restrict_apply {n : ℤ} (F : RatEquivFamily X n) (u : U) :
    (F.restrict k j).cycle u = F.cycle (j u) := by
  rw [cycle_apply, cycle_apply]
  simp_rw [component_restrict_apply]
  -- The members of `F.restrict k j` are indexed by the members of `F` meeting `U`; the others
  -- contribute nothing at `j u`.
  refine (finsum_subtype_eq_finsum_cond (f := fun a ↦ F.component a (j u))
    fun a ↦ (Set.range (F.i a) ∩ Set.range j).Nonempty).trans (finsum_congr fun a ↦ ?_)
  classical
  rw [finsum_eq_if]
  split_ifs with ha
  · rfl
  · exact (F.component_apply_eq_zero_of_notMem_range a fun hx ↦ ha ⟨j u, hx, u, rfl⟩).symm

variable (k)

/-- The extension of a family of integral closed subschemes of an open subscheme `j : U ⟶ X` with
rational functions to `X`: each member `W` is replaced by its scheme-theoretic closure in
`X`, which contains `W` as a dense open subscheme, with the same rational function. -/
private noncomputable def extend {n : ℤ} (G : RatEquivFamily U n) : RatEquivFamily X n :=
  { ι := G.ι
    W a := (G.i a ≫ j).image
    i a := (G.i a ≫ j).imageι
    isIntegral _ := inferInstance
    genericPoint_mem a :=
      (genericPoint_mem_pointsOfDimension_iff k j (G.i a ≫ j).toImage_imageι.symm).mp
        (G.genericPoint_mem a)
    r a := Units.map (asIso (G.i a ≫ j).toImage.functionFieldMap).inv.hom.toMonoidHom (G.r a)
    locallyFinite := by
      refine (G.locallyFinite.closure_image_of_isOpenImmersion j).subset fun a ↦ ?_
      rw [Scheme.Hom.range_imageι]
      refine closure_mono ?_
      rintro _ ⟨w, rfl⟩
      exact ⟨G.i a w, ⟨w, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩ }

variable {k}

private lemma component_extend_apply {n : ℤ} (G : RatEquivFamily U n) (a : G.ι) (u : U) :
    (G.extend k j).component a (j u) = G.component a u := by
  by_cases hu : u ∈ Set.range (G.i a)
  · obtain ⟨w, rfl⟩ := hu
    have := LocallyOfFiniteType.isLocallyNoetherian (G.i a ≫ j).imageι
    have hw : (G.i a ≫ j).imageι ((G.i a ≫ j).toImage w) = j (G.i a w) := by
      rw [Scheme.Hom.imageι_toImage_apply, Scheme.Hom.comp_apply]
    -- The `a`-th member of `G.extend k j` is the closure of `W` with the transported function.
    rw [← hw, G.component_apply]
    refine ((G.extend k j).component_apply a _).trans
      ((Scheme.ord_functionFieldMap (G.i a ≫ j).toImage _ w).symm.trans ?_)
    congr 1
    exact CommRingCat.hom_inv_apply (asIso (G.i a ≫ j).toImage.functionFieldMap) _
  · rw [G.component_apply_eq_zero_of_notMem_range a hu]
    refine (G.extend k j).component_apply_eq_zero_of_notMem_range a fun hx ↦ hu ?_
    -- The closure of `j '' W` in `X` meets `U` in the closed subset `W`. The `change` unfolds the
    -- `a`-th member of `G.extend k j`, which is by definition the closure `(G.i a ≫ j).imageι`.
    change j u ∈ Set.range (G.i a ≫ j).imageι at hx
    rw [Scheme.Hom.range_imageι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at hx
    rw [← (G.i a).isClosedEmbedding.isClosed_range.closure_eq,
      j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
    exact hx

/-- The restriction of the cycle of the extension of a family is the cycle of the family. -/
private lemma cycle_extend_apply {n : ℤ} (G : RatEquivFamily U n) (u : U) :
    (G.extend k j).cycle (j u) = G.cycle u := by
  rw [cycle_apply, cycle_apply]
  exact finsum_congr fun a ↦ component_extend_apply j G a u

end RatEquivFamily

variable (k)

/-- Over a field, restriction to an open subscheme sends a cycle rationally equivalent to zero to a
cycle rationally equivalent to zero. -/
lemma cyclesRestrict_mem_ratEquiv {n : ℤ} {α : cyclesOfDimension X n}
    (hα : α ∈ RatEquiv X n) : cyclesRestrict k j α ∈ RatEquiv U n := by
  obtain ⟨F, hF⟩ := mem_ratEquiv_iff.mp hα
  refine mem_ratEquiv_iff.mpr ⟨F.restrict k j, Function.locallyFinsuppWithin.ext fun u ↦ ?_⟩
  rw [RatEquivFamily.cycle_restrict_apply, hF, cyclesRestrict_apply]

/-- Over a field, the cycles rationally equivalent to zero on an open subscheme `U` are exactly the
restrictions of cycles rationally equivalent to zero on `X`. -/
lemma map_cyclesRestrict_ratEquiv {n : ℤ} :
    (RatEquiv X n).map (cyclesRestrict k j) = RatEquiv U n := by
  refine le_antisymm (AddSubgroup.map_le_iff_le_comap.mpr fun α hα ↦
    cyclesRestrict_mem_ratEquiv k j hα) fun β hβ ↦ ?_
  obtain ⟨G, hG⟩ := mem_ratEquiv_iff.mp hβ
  refine ⟨⟨(G.extend k j).cycle, (G.extend k j).cycle_mem_cyclesOfDimension k⟩,
    mem_ratEquiv_iff.mpr ⟨G.extend k j, rfl⟩,
    Subtype.ext (Function.locallyFinsuppWithin.ext fun u ↦ ?_)⟩
  rw [cyclesRestrict_apply, RatEquivFamily.cycle_extend_apply, hG]

namespace ChowGroup

/-- The restriction `CH_n(X) →+ CH_n(U)` of Chow groups along an open immersion over a field,
induced by the restriction `α ↦ α ∘ j` of cycles. -/
noncomputable def restrict {n : ℤ} : ChowGroup X n →+ ChowGroup U n :=
  lift (cycleClass.comp (cyclesRestrict k j)) fun _ hα ↦
    cycleClass_eq_zero_iff.mpr (cyclesRestrict_mem_ratEquiv k j hα)

/-- The restriction of the class of a cycle is the class of its restriction. -/
@[simp]
lemma restrict_cycleClass {n : ℤ} (α : cyclesOfDimension X n) :
    restrict k j (cycleClass α) = cycleClass (cyclesRestrict k j α) :=
  lift_cycleClass _ _ α

variable (X) in
/-- Restriction along the identity is the identity. -/
@[simp]
lemma restrict_id {n : ℤ} : restrict k (𝟙 X) = AddMonoidHom.id (ChowGroup X n) := by
  ext α
  simp

/-- Restriction of Chow groups is functorial: `(j' ≫ j)^* = j'^* ∘ j^*`. -/
lemma restrict_comp {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [IsLocallyNoetherian V] (j' : V ⟶ U)
    [IsOpenImmersion j'] [j'.IsOver (Spec (.of k))] {n : ℤ} :
    restrict k (j' ≫ j) = (restrict k j').comp (restrict k j : _ →+ ChowGroup U n) := by
  ext α
  simp [cyclesRestrict_comp]

/-- Restriction of Chow groups to an open subscheme is surjective. -/
lemma restrict_surjective {n : ℤ} : Function.Surjective (restrict k j (n := n)) := by
  intro a
  obtain ⟨β, rfl⟩ := cycleClass_surjective a
  obtain ⟨α, rfl⟩ := cyclesRestrict_surjective k j β
  exact ⟨cycleClass α, restrict_cycleClass k j α⟩

/-- **The localization sequence for Chow groups.** If the image of a closed immersion `i : Z ⟶ X`
is the complement of the image of an open immersion `j : U ⟶ X` of schemes locally of finite type
over a field, then the sequence `CH_n(Z) → CH_n(X) → CH_n(U)` of pushforward and restriction is
exact; with `Chow.ChowGroup.restrict_surjective` it extends to the exact sequence
`CH_n(Z) → CH_n(X) → CH_n(U) → 0` (Fulton, *Intersection Theory*, Proposition 1.8; Stacks, Lemma
42.19.3 (02RX)). -/
@[stacks 02RX]
theorem range_pushforward_eq_ker_restrict {Z : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X)
    [IsClosedImmersion i] (hij : Set.range i = (Set.range j)ᶜ) {n : ℤ} :
    (pushforward i (k := n)).range = (restrict k j (n := n)).ker := by
  have hexact := range_cyclesPushforward_eq_ker_cyclesRestrict k i j hij (n := n)
  ext a
  obtain ⟨α, rfl⟩ := cycleClass_surjective a
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, restrict_cycleClass, cycleClass_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨β, rfl⟩ := cycleClass_surjective b
    rw [pushforward_cycleClass, cycleClass_eq_cycleClass_iff] at hb
    -- `α` differs from the pushforward of `β` by a rationally trivial cycle, and the pushforward
    -- of `β` restricts to zero.
    have hβ : cyclesRestrict k j (cyclesPushforward i β) = 0 :=
      AddMonoidHom.mem_ker.mp (hexact ▸ ⟨β, rfl⟩)
    simpa [hβ] using cyclesRestrict_mem_ratEquiv k j hb
  · intro hα
    -- A rational equivalence on `U` extends to `X`; the difference is supported on `Z`.
    rw [← map_cyclesRestrict_ratEquiv k j] at hα
    obtain ⟨γ, hγ, hγα⟩ := hα
    obtain ⟨β, hβ⟩ : α - γ ∈ (cyclesPushforward i).range := by
      rw [hexact, AddMonoidHom.mem_ker, map_sub, hγα, sub_self]
    refine ⟨cycleClass β, ?_⟩
    rw [pushforward_cycleClass, hβ, map_sub, cycleClass_eq_zero_iff.mpr hγ, sub_zero]

end ChowGroup

end Restriction

end TauCeti.AlgebraicGeometry.Chow
