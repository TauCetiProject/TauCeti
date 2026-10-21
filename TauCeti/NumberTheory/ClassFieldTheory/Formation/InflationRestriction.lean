/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
import TauCeti.RepresentationTheory.Homological.GroupCohomology.InflationRestriction

/-!
# The inflation-restriction sequence of a refinement of layers

Let `T : LayerRefinement old new` enlarge the top field of a finite normal layer: in field
notation `old` is `K/F` and `new` is `L/F` for a tower `F ⊆ K ⊆ L` of fields Galois over `F`,
with Galois groups `U/V` and `U/V'`. The kernel `V/V'` of the quotient map
`T.galHom : U/V' → U/V` is a subgroup of the Galois group of `new`, and its layer
`new.subgroupLayer T.galHom.ker` is the layer `L/K`, a restriction of `new`.

This file proves that inflation from `K/F` and restriction to `L/K` form an exact sequence

`Hⁿ⁺¹(U/V, A^V) ⟶ Hⁿ⁺¹(U/V', A^{V'}) ⟶ Hⁿ⁺¹(V/V', A^{V'})`

as soon as `Hⁱ(V/V', A^{V'})` vanishes for `0 < i ≤ n`
(`LayerRefinement.range_cohomologyInfl_eq_ker_cohomologyRes`). For a class formation `H¹` of
every layer vanishes, so in degree two a class of `L/F` is inflated from `K/F` exactly when its
restriction to `L/K` vanishes. This is the finite-layer form of the statement that the classes of
`H²` split by `K` are those inflated from `K/F`.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRefinement.range_cohomologyInfl_eq_ker_cohomologyRes`: the
  inflation-restriction sequence of a refinement is exact.
* `TauCeti.ClassFieldTheory.LayerRefinement.cohomologyInfl_injective`: inflation is injective
  when the layer of the kernel has no cohomology in lower positive degrees.
* `TauCeti.ClassFieldTheory.LayerRefinement.exists_cohomologyInfl_eq_of_cohomologyRes_eq_zero`: in
  degree two, if `H¹(V/V', A^{V'})` vanishes, a class restricting to zero on `L/K` is inflated.
* `TauCeti.ClassFieldTheory.LayerRefinement.relativeDegree_subgroupRestriction_ker`: the
  restriction to `L/K` has relative degree `[K : F]`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, Proposition 1.34.
* J.-P. Serre, *Local Fields*, Chapter VII, §6, Proposition 5.
-/

public section

namespace TauCeti.ClassFieldTheory

namespace LayerRefinement

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {old new : NormalLayer G}

/-- The image of the inclusion `A^V ⊆ A^{V'}` of coefficient modules is the submodule of
`A^{V'}` fixed by the kernel `V/V'` of the quotient map of Galois groups. -/
private theorem range_repHom (T : LayerRefinement old new) (F : Formation G) :
    LinearMap.range (T.repHom F).hom.toLinearMap =
      Representation.invariants ((new.rep F).ρ.comp T.galHom.ker.subtype) := by
  ext x
  rw [Representation.mem_invariants]
  constructor
  · rintro ⟨y, rfl⟩ ⟨γ, hγ⟩
    induction γ using QuotientGroup.induction_on with
    | H u =>
      refine Subtype.ext ((new.rep_ρ_mk_apply_coe F u _).trans ?_)
      -- `repHom_hom_apply_coe` is stated for the morphism, not its underlying linear map.
      have hy : ((T.repHom F).hom.toLinearMap y : F.toRep.V) = y := T.repHom_hom_apply_coe F y
      rw [hy]
      exact (F.mem_level.1 y.2) _ ((T.galHom_mk_eq_one_iff u).1 hγ)
  · intro hx
    refine ⟨⟨x, F.mem_level.2 fun v hv => ?_⟩, Subtype.ext (T.repHom_hom_apply_coe F _)⟩
    have hvU : v ∈ new.ground := T.same_ground ▸ old.top_le_ground hv
    have hker : (QuotientGroup.mk ⟨v, hvU⟩ : new.Gal) ∈ T.galHom.ker :=
      (T.galHom_mk_eq_one_iff ⟨v, hvU⟩).2 hv
    exact congrArg Subtype.val (hx ⟨_, hker⟩)

/-- The inclusion `A^V ⊆ A^{V'}` of coefficient modules is injective. -/
private theorem injective_repHom (T : LayerRefinement old new) (F : Formation G) :
    Function.Injective (T.repHom F).hom := fun x y h =>
  Subtype.ext ((T.repHom_hom_apply_coe F x).symm.trans
    ((congrArg Subtype.val h).trans (T.repHom_hom_apply_coe F y)))

/-- **The inflation-restriction sequence of a refinement of layers.** For a refinement
`T : LayerRefinement old new`, the tower `F ⊆ K ⊆ L` with Galois groups `U/V` and `U/V'`, if
`Hⁱ(V/V', A^{V'})` vanishes for `0 < i ≤ n`, then a class of `Hⁿ⁺¹(U/V', A^{V'})` is inflated from
`Hⁿ⁺¹(U/V, A^V)` exactly when its restriction to the layer `L/K` of the kernel `V/V'` vanishes. -/
theorem range_cohomologyInfl_eq_ker_cohomologyRes (T : LayerRefinement old new)
    (F : Formation G) (n : ℕ)
    (hH : ∀ i < n, Subsingleton ((new.subgroupLayer T.galHom.ker).H F (i + 1))) :
    LinearMap.range (T.cohomologyInfl F (n + 1)).hom =
      LinearMap.ker ((new.subgroupRestriction T.galHom.ker).cohomologyRes F (n + 1)).hom := by
  rw [cohomologyInfl_def, LayerRestriction.cohomologyRes_def]
  exact groupCohomology.range_map_succ_eq_ker_map_succ T.galHom_surjective (injective_repHom T F)
    (range_repHom T F) (new.subgroupRestriction T.galHom.ker).galHom_injective
    (new.range_galHom_subgroupRestriction T.galHom.ker)
    (CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((new.subgroupRestriction T.galHom.ker).repIso F).inv) n
    fun i hi => have := hH i hi; ModuleCat.isZero_of_subsingleton _

/-- **Inflation along a refinement of layers is injective** when the layer of the kernel has no
cohomology below the degree. For a refinement `T : LayerRefinement old new`, the tower
`F ⊆ K ⊆ L` with Galois groups `U/V` and `U/V'`, if `Hⁱ(V/V', A^{V'})` vanishes for `0 < i ≤ n`,
then inflation `Hⁿ⁺¹(U/V, A^V) ⟶ Hⁿ⁺¹(U/V', A^{V'})` is injective. In degree two this needs only
the vanishing of `H¹` on the layer `L/K`. -/
theorem cohomologyInfl_injective (T : LayerRefinement old new) (F : Formation G) (n : ℕ)
    (hH : ∀ i < n, Subsingleton ((new.subgroupLayer T.galHom.ker).H F (i + 1))) :
    Function.Injective (T.cohomologyInfl F (n + 1)).hom := by
  rw [cohomologyInfl_def]
  exact groupCohomology.map_succ_injective_of_extension T.galHom_surjective
    (injective_repHom T F) (range_repHom T F)
    (new.subgroupRestriction T.galHom.ker).galHom_injective
    (new.range_galHom_subgroupRestriction T.galHom.ker)
    (CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((new.subgroupRestriction T.galHom.ker).repIso F).inv) n
    fun i hi => have := hH i hi; ModuleCat.isZero_of_subsingleton _

/-- **Degree-two inflation-restriction.** For a refinement `T : LayerRefinement old new`, the tower
`F ⊆ K ⊆ L`, if `H¹` of the layer `L/K` vanishes, then a class of `H²(L/F)` whose restriction to
`L/K` vanishes is inflated from `H²(K/F)`. -/
theorem exists_cohomologyInfl_eq_of_cohomologyRes_eq_zero (T : LayerRefinement old new)
    (F : Formation G) (hH : Subsingleton ((new.subgroupLayer T.galHom.ker).H F 1)) {y : new.H F 2}
    (hy : (new.subgroupRestriction T.galHom.ker).cohomologyRes F 2 y = 0) :
    ∃ x : old.H F 2, T.cohomologyInfl F 2 x = y :=
  LinearMap.mem_range.1 ((T.range_cohomologyInfl_eq_ker_cohomologyRes F 1 fun i hi => by
    obtain rfl : i = 0 := Nat.lt_one_iff.1 hi
    exact hH).ge hy)

/-- **The restriction to the layer `L/K` has relative degree `[K : F]`**: for a refinement
`T : LayerRefinement old new`, the index of the kernel `V/V'` of `T.galHom` in `U/V'` is the
degree of `old`. -/
theorem relativeDegree_subgroupRestriction_ker (T : LayerRefinement old new) :
    (new.subgroupRestriction T.galHom.ker).relativeDegree = old.degree := by
  rw [new.relativeDegree_subgroupRestriction, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 T.galHom_surjective, Subgroup.card_top,
    ← NormalLayer.degree_eq_natCard_gal]

end LayerRefinement

end TauCeti.ClassFieldTheory
