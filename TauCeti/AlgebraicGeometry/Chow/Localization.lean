/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# The localization sequence for Chow groups

Let `k` be a field, `X` a scheme locally of finite type over `k`, `j : U ⟶ X` an open immersion
and `i : Z ⟶ X` a closed immersion whose image is the complement of the image of `j`. This file
proves that the sequence of Chow groups

`CH_n(Z) → CH_n(X) → CH_n(U) → 0`

of pushforward along `i` and restriction along `j` is exact (Fulton, *Intersection Theory*,
Proposition 1.8; [Stacks, Lemma 42.19.3](https://stacks.math.columbia.edu/tag/02RX)). The
cycle-level sequence is `Chow.range_cyclesPushforward_eq_ker_cyclesRestrict`; what is added here is
the behaviour of rational equivalence under restriction to `U` and under closure in `X`.

* `Chow.RatEquivFamily.cycle_mem_cyclesOfDimension`: over a field, the cycle
  `Σ_a (i_a)_* div(r_a)` of a family of integral closed subschemes of dimension `n + 1` with
  rational functions is an `n`-cycle, by the dimension formula on each member: a rational function
  only has zeros and poles at points of codimension one.
* `Chow.RatEquivFamily.restrict k j F`: the family `(W_a ∩ U, r_a|_{W_a ∩ U})` on `U` obtained by
  intersecting the members of a family on `X` with `U`, discarding those disjoint from `U`. Its
  cycle is the restriction of the cycle of `F` (`Chow.RatEquivFamily.cycle_restrict`), since
  orders of vanishing are local.
* `Chow.RatEquivFamily.closure k j G`: the family on `X` of the closures in `X` of the members of a
  family `G` on `U`, with the same rational functions. These are the scheme-theoretic images
  `Scheme.Hom.image` of the immersions `W_b ⟶ U ⟶ X`, which contain `W_b` as a dense open
  subscheme, and they form a locally finite family because `j` is quasi-compact. Its cycle
  restricts to the cycle of `G` (`Chow.RatEquivFamily.comap_cycle_closure`).
* `Chow.ChowGroup.restrict k j`: the restriction `CH_n(X) →+ CH_n(U)`, with
  `Chow.ChowGroup.restrict_cycleClass`, `Chow.ChowGroup.restrict_id`,
  `Chow.ChowGroup.restrict_comp` and `Chow.ChowGroup.restrict_surjective`.
* `Chow.ChowGroup.exact_pushforward_restrict`: the **localization sequence**: the sequence
  `CH_n(Z) → CH_n(X) → CH_n(U)` is exact; with `Chow.ChowGroup.restrict_surjective` this is the
  exactness of `CH_n(Z) → CH_n(X) → CH_n(U) → 0`.
-/

public section

open AlgebraicGeometry Order CategoryTheory CategoryTheory.Limits Topology

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] {X U V : Scheme.{u}}
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

include k in
/-- An open immersion into a scheme locally of finite type over a field preserves the dimension of
points; the source is given the structure over the field induced from the target. -/
private lemma height_apply_of_isOpenImmersion' (j : U ⟶ X) [IsOpenImmersion j] (u : U) :
    height (j u) = height u := by
  let : U.Over (Spec (.of k)) := ⟨j ≫ X ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ X ↘ Spec (.of k)))
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  exact height_apply_of_isOpenImmersion k j u

namespace RatEquivFamily

variable {n : ℤ}

include k in
/-- **Over a field, rational equivalences are `n`-cycles.** For a scheme locally of finite type over
a field, the cycle `Σ_a (i_a)_* div(r_a)` of a family of integral closed subschemes of dimension
`n + 1` with nonzero rational functions is an `n`-cycle: a rational function on `W_a` only has zeros
and poles at points of codimension one, which by the dimension formula have dimension `n`. -/
lemma cycle_mem_cyclesOfDimension [IsLocallyNoetherian X] (F : RatEquivFamily X n) :
    F.cycle ∈ cyclesOfDimension X n := by
  rw [mem_cyclesOfDimension_iff]
  intro x hx
  rw [Function.mem_support, cycle_apply] at hx
  obtain ⟨a, ha⟩ : ∃ a, F.component a x ≠ 0 := by
    by_contra! h
    exact hx (finsum_eq_zero_of_forall_eq_zero h)
  by_cases hxa : x ∈ Set.range (F.i a)
  swap
  · exact absurd (F.component_apply_eq_zero_of_notMem_range a hxa) ha
  obtain ⟨y, rfl⟩ := hxa
  rw [component_apply] at ha
  have hy : coheight y = 1 := by
    by_contra hy
    exact ha (Scheme.ord_eq_zero_of_coheight_neq_one hy _)
  -- the dimension formula on `W_a`, which is locally of finite type over `k` through `X`
  let : (F.W a).Over (Spec (.of k)) := ⟨F.i a ≫ X ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (F.W a ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (F.i a ≫ X ↘ Spec (.of k)))
  have hgen := coheight_add_height_eq_topologicalKrullDim k (genericPoint (F.W a))
  have hpt := coheight_add_height_eq_topologicalKrullDim k y
  rw [coheight_eq_zero.mpr (Scheme.isMax_iff_eq_genericPoint.mpr rfl)] at hgen
  obtain ⟨m, hm, hmn⟩ := mem_pointsOfDimension.mp (F.genericPoint_mem a)
  rw [hm, ← hpt, hy] at hgen
  have h1 : (1 : ℕ∞) + height y = m := by
    have h := hgen.symm
    norm_cast at h
    simpa using h
  obtain ⟨d, hd⟩ : ∃ d : ℕ, height y = d :=
    ⟨_, (ENat.natCast_toNat fun h ↦ by simp [h] at h1).symm⟩
  rw [hd] at h1
  have h2 : 1 + d = m := by exact_mod_cast h1
  refine mem_pointsOfDimension.mpr ⟨d, by rw [Scheme.Hom.height_apply_eq_height, hd], ?_⟩
  omega

section Restrict

variable (j : U ⟶ X) [IsOpenImmersion j] (F : RatEquivFamily X n)

/-- A member of a family meeting an open subscheme meets it in an integral scheme. -/
private lemma isIntegral_pullback (a : F.ι) [Nonempty ↥(pullback (F.i a) j)] :
    IsIntegral (pullback (F.i a) j) :=
  isIntegral_of_isOpenImmersion (pullback.fst (F.i a) j)

/-- The restriction of a family to an open subscheme `j : U ⟶ X`: the members `W_a` meeting `U`,
intersected with `U` (the pullbacks of `i_a` along `j`), with the restrictions of the rational
functions. -/
noncomputable def restrict : RatEquivFamily U n where
  ι := {a : F.ι // Nonempty ↥(pullback (F.i a) j)}
  W a := pullback (F.i a.1) j
  i a := pullback.snd (F.i a.1) j
  isIntegral a :=
    haveI : Nonempty ↥(pullback (F.i a.1) j) := a.2
    isIntegral_pullback j F a.1
  genericPoint_mem a := by
    have : Nonempty ↥(pullback (F.i a.1) j) := a.2
    have := isIntegral_pullback j F a.1
    rw [mem_pointsOfDimension, ← Scheme.Hom.height_apply_eq_height (pullback.snd (F.i a.1) j),
      ← height_apply_of_isOpenImmersion' k j, ← Scheme.Hom.comp_apply, ← pullback.condition,
      Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, Scheme.Hom.height_apply_eq_height]
    exact mem_pointsOfDimension.mp (F.genericPoint_mem a.1)
  r a :=
    haveI : Nonempty ↥(pullback (F.i a.1) j) := a.2
    haveI := isIntegral_pullback j F a.1
    haveI := Scheme.Hom.isDominant_of_isOpenImmersion (pullback.fst (F.i a.1) j)
    Units.map (pullback.fst (F.i a.1) j).functionFieldMap.hom (F.r a.1)
  locallyFinite := by
    refine ((F.locallyFinite.preimage_continuous j.continuous).comp_injective
      (Subtype.val_injective (p := fun a ↦ Nonempty ↥(pullback (F.i a) j)))).subset fun a ↦ ?_
    rintro _ ⟨p, rfl⟩
    exact ⟨pullback.fst (F.i a.1) j p, by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]⟩

variable {j F} in
/-- On `U`, the summands of the restricted family are the restrictions of the summands. -/
private lemma component_restrict_apply [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (a : {a : F.ι // Nonempty ↥(pullback (F.i a) j)}) (u : U) :
    (F.restrict k j).component a u = F.component a.1 (j u) := by
  by_cases hu : u ∈ Set.range (pullback.snd (F.i a.1) j)
  · obtain ⟨p, rfl⟩ := hu
    have : Nonempty ↥(pullback (F.i a.1) j) := a.2
    have := isIntegral_pullback j F a.1
    have := Scheme.Hom.isDominant_of_isOpenImmersion (pullback.fst (F.i a.1) j)
    have h : j (pullback.snd (F.i a.1) j p) = F.i a.1 (pullback.fst (F.i a.1) j p) := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    refine ((F.restrict k j).component_apply a p).trans ?_
    rw [h, component_apply]
    exact Scheme.ord_functionFieldMap (pullback.fst (F.i a.1) j) _ p
  · rw [(F.restrict k j).component_apply_eq_zero_of_notMem_range a hu, eq_comm]
    refine F.component_apply_eq_zero_of_notMem_range a.1 fun ⟨w, hw⟩ ↦ hu ?_
    obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback w u hw
    exact ⟨p, hp⟩

/-- **Restriction of a rational equivalence.** The cycle of the restriction of a family to an open
subscheme `j : U ⟶ X` is the restriction of its cycle: `(Σ_a (i_a)_* div r_a)|_U` is
`Σ_a (W_a ∩ U ⟶ U)_* div (r_a|_{W_a ∩ U})`. -/
lemma cycle_restrict [IsLocallyNoetherian X] [IsLocallyNoetherian U] :
    (F.restrict k j).cycle =
      Function.locallyFinsupp.comap j j.continuous j.isOpenEmbedding.injective F.cycle := by
  ext u
  rw [cycle_apply, Function.locallyFinsupp.comap_apply, cycle_apply]
  refine (finsum_congr fun a ↦ component_restrict_apply k a u).trans ?_
  classical
  refine (finsum_subtype_eq_finsum_cond (f := fun a ↦ F.component a (j u)) _).trans
    (finsum_congr fun a ↦ ?_)
  rw [finsum_eq_if]
  split_ifs with ha
  · rfl
  · refine (F.component_apply_eq_zero_of_notMem_range a fun ⟨w, hw⟩ ↦ ha ?_).symm
    obtain ⟨p, -⟩ := Scheme.Pullback.exists_preimage_pullback w u hw
    exact ⟨p⟩

end Restrict

section Closure

variable (j : U ⟶ X) [IsOpenImmersion j] [IsLocallyNoetherian X] (G : RatEquivFamily U n)

/-- The closure in `X` of a member `W_b` of a family on `U` is supported on the closure of `W_b`. -/
private lemma range_imageι_comp (b : G.ι) :
    Set.range (G.i b ≫ j).imageι = closure (j '' Set.range (G.i b)) := by
  rw [Scheme.Hom.range_imageι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

/-- The closure in `X` of a family on an open subscheme `j : U ⟶ X`: the scheme-theoretic images
`V_b` of the immersions `W_b ⟶ U ⟶ X`, which contain `W_b` as a dense open subscheme, with the
rational functions of the family, transported along the isomorphism `κ(V_b) ≅ κ(W_b)`. -/
noncomputable def closure : RatEquivFamily X n where
  ι := G.ι
  W b := (G.i b ≫ j).image
  i b := (G.i b ≫ j).imageι
  genericPoint_mem b := by
    rw [mem_pointsOfDimension, ← Scheme.Hom.height_apply_eq_height (G.i b ≫ j).imageι,
      ← genericPoint_eq_of_isOpenImmersion (G.i b ≫ j).toImage, ← Scheme.Hom.comp_apply,
      Scheme.Hom.toImage_imageι, Scheme.Hom.comp_apply, height_apply_of_isOpenImmersion' k j,
      Scheme.Hom.height_apply_eq_height]
    exact mem_pointsOfDimension.mp (G.genericPoint_mem b)
  r b := Units.map (inv (G.i b ≫ j).toImage.functionFieldMap).hom (G.r b)
  locallyFinite := by
    simp_rw [range_imageι_comp]
    refine LocallyFinite.closure fun x ↦ ?_
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    refine ⟨A, A.isOpen.mem_nhds hxA, ?_⟩
    refine (G.locallyFinite.finite_nonempty_inter_compact
      (j.isCompact_preimage hA.isCompact)).subset ?_
    rintro b ⟨_, ⟨y, hy, rfl⟩, hyA⟩
    exact ⟨y, hy, hyA⟩

variable {G} in
/-- On `U`, the summands of the closure of a family are the summands of the family. -/
private lemma component_closure_apply [IsLocallyNoetherian U] (b : G.ι) (u : U) :
    (G.closure k j).component b (j u) = G.component b u := by
  by_cases hu : u ∈ Set.range (G.i b)
  · obtain ⟨v, rfl⟩ := hu
    have := LocallyOfFiniteType.isLocallyNoetherian (G.i b ≫ j).imageι
    have hv : j (G.i b v) = (G.i b ≫ j).imageι ((G.i b ≫ j).toImage v) := by
      rw [← Scheme.Hom.comp_apply (G.i b ≫ j).toImage, Scheme.Hom.toImage_imageι,
        Scheme.Hom.comp_apply]
    rw [hv]
    refine ((G.closure k j).component_apply b _).trans ?_
    rw [component_apply]
    refine (Scheme.ord_functionFieldMap (G.i b ≫ j).toImage _ v).symm.trans ?_
    congr 1
    -- unfold the rational function of `G.closure k j` to the transported function `(f^*)⁻¹ r_b`
    change (G.i b ≫ j).toImage.functionFieldMap
      ((inv (G.i b ≫ j).toImage.functionFieldMap) (G.r b : (G.W b).functionField)) = _
    simp
  · rw [component_apply_eq_zero_of_notMem_range _ _ hu]
    refine (G.closure k j).component_apply_eq_zero_of_notMem_range b ?_
    -- the members of `G.closure k j` are indexed by `G.ι`, but `rw` does not see through the index
    -- type of the structure, so we restate the goal with the closed immersion it unfolds to
    change j u ∉ Set.range (G.i b ≫ j).imageι
    rw [range_imageι_comp, ← Set.mem_preimage,
      ← j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      (G.i b).isClosedEmbedding.isClosed_range.closure_eq]
    exact hu

/-- **Closure of a rational equivalence.** The cycle of the closure in `X` of a family on an open
subscheme `j : U ⟶ X` restricts on `U` to the cycle of the family. -/
lemma comap_cycle_closure [IsLocallyNoetherian U] :
    Function.locallyFinsupp.comap j j.continuous j.isOpenEmbedding.injective
      (G.closure k j).cycle = G.cycle := by
  ext u
  rw [Function.locallyFinsupp.comap_apply, cycle_apply, cycle_apply]
  exact finsum_congr fun b ↦ component_closure_apply k j b u

end Closure

end RatEquivFamily

section ChowGroup

variable [U.Over (Spec (.of k))] [V.Over (Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (V ↘ Spec (.of k))] (j : U ⟶ X) [IsOpenImmersion j]
  [j.IsOver (Spec (.of k))] [IsLocallyNoetherian X] [IsLocallyNoetherian U] {n : ℤ}

/-- Restriction of cycles to an open subscheme preserves rational equivalence: the restriction of
`Σ_a (i_a)_* div r_a` is the cycle of the restricted family. -/
lemma cyclesRestrict_mem_ratEquiv {α : cyclesOfDimension X n} (hα : α ∈ RatEquiv X n) :
    cyclesRestrict k j α ∈ RatEquiv U n := by
  obtain ⟨F, hF⟩ := mem_ratEquiv_iff.mp hα
  refine mem_ratEquiv_iff.mpr ⟨F.restrict k j, Function.locallyFinsuppWithin.ext fun u ↦ ?_⟩
  rw [F.cycle_restrict k j, Function.locallyFinsupp.comap_apply, cyclesRestrict_apply, hF]

namespace ChowGroup

/-- The restriction `CH_n(X) →+ CH_n(U)` of Chow groups along an open immersion over a field,
induced by the restriction of cycles `[V] ↦ [V ∩ U]`. -/
noncomputable def restrict : ChowGroup X n →+ ChowGroup U n :=
  lift (cycleClass.comp (cyclesRestrict k j)) fun _ hα ↦
    cycleClass_eq_zero_iff.mpr (cyclesRestrict_mem_ratEquiv k j hα)

/-- The restriction of the class of a cycle is the class of its restriction. -/
@[simp]
lemma restrict_cycleClass (α : cyclesOfDimension X n) :
    restrict k j (cycleClass α) = cycleClass (cyclesRestrict k j α) :=
  lift_cycleClass _ _ α

variable (X) in
/-- Restriction along the identity is the identity. -/
@[simp]
lemma restrict_id : restrict k (𝟙 X) = AddMonoidHom.id (ChowGroup X n) := by
  ext α
  simp [cyclesRestrict_id]

/-- Restriction of Chow groups is functorial: `(j' ≫ j)^* = j'^* ∘ j^*`. -/
lemma restrict_comp [IsLocallyNoetherian V] (j' : V ⟶ U) [IsOpenImmersion j']
    [j'.IsOver (Spec (.of k))] :
    restrict k (j' ≫ j) = (restrict k j').comp (restrict k j : ChowGroup X n →+ _) := by
  ext α
  simp [cyclesRestrict_comp]

/-- Restriction of Chow groups to an open subscheme is surjective. -/
lemma restrict_surjective : Function.Surjective (restrict k j : ChowGroup X n → ChowGroup U n) := by
  intro β
  obtain ⟨β, rfl⟩ := cycleClass_surjective β
  obtain ⟨α, rfl⟩ := cyclesRestrict_surjective k j β
  exact ⟨cycleClass α, restrict_cycleClass k j α⟩

/-- **The localization sequence for Chow groups.** If the image of a closed immersion `i : Z ⟶ X`
is the complement of the image of an open immersion `j : U ⟶ X`, of schemes locally of finite type
over a field, then the sequence `CH_n(Z) → CH_n(X) → CH_n(U)` of pushforward along `i` and
restriction along `j` is exact; restriction is moreover surjective
(`Chow.ChowGroup.restrict_surjective`). A cycle on `X` whose restriction to `U` is rationally
equivalent to zero differs from a cycle supported on `Z` by the closure in `X` of that rational
equivalence (Fulton, *Intersection Theory*, Proposition 1.8; Stacks, Lemma 42.19.3 (02RX)). -/
@[stacks 02RX]
theorem exact_pushforward_restrict {Z : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X)
    [IsClosedImmersion i] (hij : Set.range i = (Set.range j)ᶜ) :
    Function.Exact (pushforward i : ChowGroup Z n →+ ChowGroup X n) (restrict k j) := by
  have hexact := range_cyclesPushforward_eq_ker_cyclesRestrict k i j hij (n := n)
  intro y
  obtain ⟨α, rfl⟩ := cycleClass_surjective y
  rw [restrict_cycleClass, cycleClass_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨G, hG⟩ := mem_ratEquiv_iff.mp h
    -- the closure in `X` of the rational equivalence `G` on `U`
    let γ : cyclesOfDimension X n :=
      ⟨(G.closure k j).cycle, (G.closure k j).cycle_mem_cyclesOfDimension k⟩
    have hγ : γ ∈ RatEquiv X n := mem_ratEquiv_iff.mpr ⟨G.closure k j, rfl⟩
    have hres : α - γ ∈ (cyclesRestrict k j (n := n)).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun u ↦ ?_)
      rw [cyclesRestrict_apply, cyclesRestrict_apply]
      calc (α : AlgebraicCycle X ℤ) (j u) = G.cycle u := by rw [hG, cyclesRestrict_apply]
        _ = _ := by rw [← G.comap_cycle_closure k j, Function.locallyFinsupp.comap_apply]
    rw [← hexact] at hres
    obtain ⟨β, hβ⟩ := hres
    refine ⟨cycleClass β, ?_⟩
    rw [pushforward_cycleClass, hβ, map_sub, cycleClass_eq_zero_iff.mpr hγ, sub_zero]
  · rintro ⟨β, hβ⟩
    obtain ⟨β, rfl⟩ := cycleClass_surjective β
    rw [pushforward_cycleClass, cycleClass_eq_cycleClass_iff] at hβ
    have hzero : cyclesRestrict k j (cyclesPushforward i β) = 0 :=
      AddMonoidHom.mem_ker.mp (hexact ▸ ⟨β, rfl⟩)
    have := cyclesRestrict_mem_ratEquiv k j (neg_mem hβ)
    rwa [neg_sub, map_sub, hzero, sub_zero] at this

end ChowGroup

end ChowGroup

end TauCeti.AlgebraicGeometry.Chow

