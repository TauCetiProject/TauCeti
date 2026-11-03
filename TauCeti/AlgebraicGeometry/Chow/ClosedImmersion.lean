/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.Basic
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.Topology.LocallyFinite.Basic

/-!
# Pushforward of Chow groups along closed immersions

For a closed immersion `i : Z ⟶ X` of locally Noetherian schemes, Mathlib's pushforward of
algebraic cycles with height weights sends `k`-cycles on `Z` to `k`-cycles on `X` by transporting
coefficients, and sends cycles rationally equivalent to zero on `Z` to cycles rationally
equivalent to zero on `X`. It therefore induces a pushforward `i_* : CH_k(Z) → CH_k(X)`
([Stacks, Lemma 42.19.3](https://stacks.math.columbia.edu/tag/02RX); Fulton, *Intersection
Theory*, Proposition 1.8). This construction needs only local Noetherianity. For schemes locally
of finite type over a field, where restriction to the open complement `X \ Z` preserves the
dimension grading, it is the first map of the localization sequence
`CH_k(Z) → CH_k(X) → CH_k(X \ Z) → 0`; in general restriction to an open subscheme need not
preserve the grading by `Order.height`, and that sequence is not constructed here.

* `Chow.cyclesPushforward i`: the pushforward `Z_k(Z) →+ Z_k(X)` of `k`-cycles. It is injective
  (`Chow.cyclesPushforward_injective`), and its image consists of the `k`-cycles supported on
  the image of `i` (`Chow.mem_range_cyclesPushforward_iff`).
* `Chow.RatEquivFamily.pushforward i F`: a family of integral closed subschemes of `Z` with
  rational functions, viewed on `X`. It keeps the indices, subschemes and rational functions of
  `F` and composes the embeddings with `i` (`Chow.RatEquivFamily.pushforward_ι`,
  `Chow.RatEquivFamily.pushforward_W`, `Chow.RatEquivFamily.pushforward_i`,
  `Chow.RatEquivFamily.pushforward_r`). Its cycle is the pushforward of the cycle of `F`
  (`Chow.RatEquivFamily.cycle_pushforward`).
* `Chow.ChowGroup.pushforward i`: the induced map `CH_k(Z) →+ CH_k(X)`, functorial in `i`
  (`Chow.ChowGroup.pushforward_id`, `Chow.ChowGroup.pushforward_comp`).
* `Chow.ChowGroup.equivOfIso e`: an isomorphism of schemes `Z ≅ X` induces an isomorphism
  `CH_k(Z) ≃+ CH_k(X)`.
-/

public section

open AlgebraicGeometry Order CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

section Cycles

/-- The pushforward of `k`-cycles along a closed immersion: Mathlib's pushforward of cycles with
height weights, which transports coefficients. -/
noncomputable def cyclesPushforward {k : ℤ} : cyclesOfDimension Z k →+ cyclesOfDimension X k :=
  AddMonoidHom.mk' (fun α ↦ ⟨AlgebraicCycle.map i height height (α : AlgebraicCycle Z ℤ), by
      rw [mem_cyclesOfDimension_iff, AlgebraicCycle.support_map_height_of_isClosedImmersion]
      rintro _ ⟨y, hy, rfl⟩
      simpa only [mem_pointsOfDimension, Scheme.Hom.height_apply_eq_height] using
        mem_cyclesOfDimension_iff.mp α.2 hy⟩)
    fun α β ↦ Subtype.ext (AlgebraicCycle.map_height_add_of_isClosedImmersion i _ _)

variable {i}

/-- The underlying cycle of a pushforward is Mathlib's pushforward with height weights. -/
lemma coe_cyclesPushforward {k : ℤ} (α : cyclesOfDimension Z k) :
    (cyclesPushforward i α : AlgebraicCycle X ℤ) =
      AlgebraicCycle.map i height height (α : AlgebraicCycle Z ℤ) :=
  (rfl)

/-- The pushforward of a cycle along a closed immersion has, at the image of a point, the
coefficient of the cycle at that point. -/
@[simp]
lemma cyclesPushforward_apply {k : ℤ} (α : cyclesOfDimension Z k) (y : Z) :
    (cyclesPushforward i α : AlgebraicCycle X ℤ) (i y) = (α : AlgebraicCycle Z ℤ) y := by
  rw [coe_cyclesPushforward, AlgebraicCycle.map_height_apply_of_isClosedImmersion]

/-- The pushforward of a cycle along a closed immersion vanishes off the image. -/
lemma cyclesPushforward_apply_of_notMem_range {k : ℤ} (α : cyclesOfDimension Z k) {x : X}
    (hx : x ∉ Set.range i) : (cyclesPushforward i α : AlgebraicCycle X ℤ) x = 0 :=
  AlgebraicCycle.map_apply_eq_zero_of_notMem_range _ _ _ _ hx

/-- Pushforward of cycles along a closed immersion is injective. -/
lemma cyclesPushforward_injective {k : ℤ} :
    Function.Injective (cyclesPushforward i : cyclesOfDimension Z k → cyclesOfDimension X k) :=
  fun _ _ h ↦ Subtype.ext
    (AlgebraicCycle.map_height_injective_of_isClosedImmersion i congr($h.1))

/-- A `k`-cycle on `X` is a pushforward along the closed immersion `i` exactly when it is supported
on the image of `i`. -/
lemma mem_range_cyclesPushforward_iff {k : ℤ} {α : cyclesOfDimension X k} :
    α ∈ (cyclesPushforward i).range ↔ (α : AlgebraicCycle X ℤ).support ⊆ Set.range i := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨β, rfl⟩
    rw [coe_cyclesPushforward]
    exact AlgebraicCycle.support_map_subset_range _ _ _ _
  -- Pull `α` back along `i`: its support is the preimage of the support of `α`, which is
  -- locally finite because `i` is continuous.
  let β : AlgebraicCycle Z ℤ :=
    { toFun y := (α : AlgebraicCycle X ℤ) (i y)
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' y _ := by
        obtain ⟨U, hU, hfin⟩ := (α : AlgebraicCycle X ℤ).supportLocallyFiniteWithinDomain'
          (i y) (Set.mem_univ _)
        exact ⟨i ⁻¹' U, i.continuous.continuousAt.preimage_mem_nhds hU,
          (hfin.preimage i.isClosedEmbedding.injective.injOn).subset fun z hz ↦ hz⟩ }
  have hβ : β ∈ cyclesOfDimension Z k := mem_cyclesOfDimension_iff.mpr fun y hy ↦ by
    simpa only [mem_pointsOfDimension, Scheme.Hom.height_apply_eq_height] using
      mem_cyclesOfDimension_iff.mp α.2 hy
  refine ⟨⟨β, hβ⟩, Subtype.ext ?_⟩
  ext x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    exact cyclesPushforward_apply _ y
  · rw [cyclesPushforward_apply_of_notMem_range _ hx, eq_comm, ← Function.notMem_support]
    exact fun hx' ↦ hx (h hx')

end Cycles

section RatEquiv

namespace RatEquivFamily

variable {k : ℤ}

/-- A family of integral closed subschemes of `Z` with rational functions, viewed as a family on
`X` by composing with the closed immersion `i`. It is exposed because the data of the family
depends on its index type: the lemmas `pushforward_W`, `pushforward_i` and `pushforward_r` below
are stated over `F.ι`. -/
@[expose] noncomputable def pushforward (F : RatEquivFamily Z k) : RatEquivFamily X k where
  ι := F.ι
  W := F.W
  i j := F.i j ≫ i
  genericPoint_mem := F.genericPoint_mem
  r := F.r
  locallyFinite := by
    simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
      Set.range_comp] using F.locallyFinite.image_of_isClosedMap i.isClosedEmbedding.isClosedMap
        fun _ ↦ (Set.subsingleton_singleton.preimage i.isClosedEmbedding.injective).isCompact

/-- The pushforward of a family has the same index type. -/
lemma pushforward_ι (F : RatEquivFamily Z k) : (F.pushforward i).ι = F.ι :=
  rfl

/-- The pushforward of a family has the same integral closed subschemes. -/
@[simp]
lemma pushforward_W (F : RatEquivFamily Z k) (j : F.ι) : (F.pushforward i).W j = F.W j :=
  rfl

/-- The embeddings of the pushforward of a family are those of the family followed by `i`. -/
@[simp]
lemma pushforward_i (F : RatEquivFamily Z k) (j : F.ι) : (F.pushforward i).i j = F.i j ≫ i :=
  rfl

/-- The pushforward of a family has the same rational functions. -/
@[simp]
lemma pushforward_r (F : RatEquivFamily Z k) (j : F.ι) : (F.pushforward i).r j = F.r j :=
  rfl

variable [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (F : RatEquivFamily Z k)

-- The summands of `F.pushforward i` are indexed by `F.ι`, and the `j`-th one lives on the subscheme
-- `F.W j` embedded by `F.i j ≫ i`, by the definition of `pushforward`.
private lemma component_pushforward_apply (j : F.ι) (y : Z) :
    (F.pushforward i).component j (i y) = F.component j y := by
  by_cases hy : y ∈ Set.range (F.i j)
  · obtain ⟨w, rfl⟩ := hy
    exact ((F.pushforward i).component_apply j w).trans (F.component_apply j w).symm
  · rw [F.component_apply_eq_zero_of_notMem_range j hy]
    exact (F.pushforward i).component_apply_eq_zero_of_notMem_range j
      fun ⟨w, hw⟩ ↦ hy ⟨w, i.isClosedEmbedding.injective hw⟩

omit [IsLocallyNoetherian Z] in
private lemma component_pushforward_apply_of_notMem_range (j : F.ι) {x : X}
    (hx : x ∉ Set.range i) : (F.pushforward i).component j x = 0 :=
  (F.pushforward i).component_apply_eq_zero_of_notMem_range j fun ⟨w, hw⟩ ↦ hx ⟨F.i j w, hw⟩

/-- The cycle of a family pushed forward along a closed immersion is the pushforward of its
cycle. -/
lemma cycle_pushforward :
    (F.pushforward i).cycle = AlgebraicCycle.map i height height F.cycle := by
  ext x
  rw [cycle_apply]
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    rw [AlgebraicCycle.map_height_apply_of_isClosedImmersion, cycle_apply]
    exact finsum_congr fun j ↦ component_pushforward_apply i F j y
  · rw [AlgebraicCycle.map_apply_eq_zero_of_notMem_range _ _ _ _ hx]
    exact finsum_eq_zero_of_forall_eq_zero fun j ↦
      component_pushforward_apply_of_notMem_range i F j hx

end RatEquivFamily

variable [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- The pushforward along a closed immersion of a cycle rationally equivalent to zero is rationally
equivalent to zero. -/
lemma cyclesPushforward_mem_ratEquiv {k : ℤ} {α : cyclesOfDimension Z k}
    (hα : α ∈ RatEquiv Z k) : cyclesPushforward i α ∈ RatEquiv X k := by
  obtain ⟨F, hF⟩ := mem_ratEquiv_iff.mp hα
  exact mem_ratEquiv_iff.mpr
    ⟨F.pushforward i, by rw [RatEquivFamily.cycle_pushforward, hF, coe_cyclesPushforward]⟩

end RatEquiv

namespace ChowGroup

variable [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- The pushforward `i_* : CH_k(Z) →+ CH_k(X)` of Chow groups along a closed immersion. -/
noncomputable def pushforward {k : ℤ} : ChowGroup Z k →+ ChowGroup X k :=
  lift (cycleClass.comp (cyclesPushforward i)) fun _ hα ↦
    cycleClass_eq_zero_iff.mpr (cyclesPushforward_mem_ratEquiv i hα)

variable {i}

/-- The pushforward of the class of a cycle is the class of its pushforward. -/
@[simp]
lemma pushforward_cycleClass {k : ℤ} (α : cyclesOfDimension Z k) :
    pushforward i (cycleClass α) = cycleClass (cyclesPushforward i α) :=
  lift_cycleClass _ _ α

variable (X) in
/-- Pushforward along the identity is the identity. -/
@[simp]
lemma pushforward_id {k : ℤ} : pushforward (𝟙 X) = AddMonoidHom.id (ChowGroup X k) := by
  ext α
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, pushforward_cycleClass,
    AddMonoidHom.id_apply]
  congr 1
  exact Subtype.ext (AlgebraicCycle.map_id _ _)

/-- Pushforward of Chow groups along closed immersions is functorial. -/
lemma pushforward_comp {Y : Scheme.{u}} [IsLocallyNoetherian Y] (i' : Y ⟶ Z) [IsClosedImmersion i']
    {k : ℤ} :
    pushforward (i' ≫ i) = (pushforward i).comp (pushforward i' : _ →+ ChowGroup Z k) := by
  ext α
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, pushforward_cycleClass]
  congr 1
  exact Subtype.ext (AlgebraicCycle.map_height_comp_of_isClosedImmersion _ _ _)

/-- An isomorphism of locally Noetherian schemes induces an isomorphism of Chow groups. -/
noncomputable def equivOfIso (e : Z ≅ X) {k : ℤ} : ChowGroup Z k ≃+ ChowGroup X k :=
  AddMonoidHom.toAddEquiv (pushforward e.hom) (pushforward e.inv)
    (by simp only [← pushforward_comp, Iso.hom_inv_id, pushforward_id])
    (by simp only [← pushforward_comp, Iso.inv_hom_id, pushforward_id])

/-- The isomorphism of Chow groups induced by `e` is pushforward along `e.hom`. -/
@[simp]
lemma equivOfIso_apply (e : Z ≅ X) {k : ℤ} (a : ChowGroup Z k) :
    equivOfIso e a = pushforward e.hom a :=
  (rfl)

/-- The inverse of the isomorphism of Chow groups induced by `e` is pushforward along `e.inv`. -/
@[simp]
lemma equivOfIso_symm_apply (e : Z ≅ X) {k : ℤ} (a : ChowGroup X k) :
    (equivOfIso e).symm a = pushforward e.inv a :=
  (rfl)

end ChowGroup

end TauCeti.AlgebraicGeometry.Chow
