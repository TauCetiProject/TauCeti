/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
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

Restriction to an intermediate ground field commutes with inflation to a larger top field
(`LayerRestriction.cohomologyInfl_comp_cohomologyRes`), and every refinement of a layer restricts
to a refinement of each of its restrictions (`LayerRestriction.exists_refinement`).

## Main statements

* `TauCeti.ClassFieldTheory.LayerRefinement.range_cohomologyInfl_eq_ker_cohomologyRes`: the
  inflation-restriction sequence of a refinement is exact.
* `TauCeti.ClassFieldTheory.LayerRefinement.cohomologyInfl_injective`: inflation is injective
  when the layer of the kernel has no cohomology in lower positive degrees.
* `TauCeti.ClassFieldTheory.LayerRestriction.exists_refinement` and
  `TauCeti.ClassFieldTheory.LayerRestriction.cohomologyInfl_comp_cohomologyRes`: refinements
  restrict, and restriction commutes with inflation.

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

end LayerRefinement

/-! ### Restriction and inflation commute -/

open CategoryTheory

namespace LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big small' big' : NormalLayer G}

/-- **A refinement of a layer restricts to a refinement of its restriction.** In field notation,
for `F ⊆ E ⊆ K ⊆ L` with `K/F` and `L/F` Galois, the layer `L/E` refines `K/E` and is a
restriction of `L/F`. -/
theorem exists_refinement (R : LayerRestriction small big) (T : LayerRefinement big big') :
    ∃ small' : NormalLayer G, LayerRefinement small small' ∧ LayerRestriction small' big' := by
  refine ⟨{ ground := small.ground
            top := big'.top
            top_le_ground := T.top_le.trans (R.same_top ▸ small.top_le_ground)
            normal := ⟨fun v hv u ↦ Subgroup.mem_subgroupOf.2 ?_⟩ },
    ⟨rfl, T.top_le.trans R.same_top.ge⟩, ⟨rfl, R.ground_le.trans T.same_ground.le⟩⟩
  exact big'.conj_mem_top (T.same_ground ▸ R.ground_le u.2) (Subgroup.mem_subgroupOf.1 hv)

/-- **Restriction commutes with inflation.** For layers `K/F`, `K/E`, `L/F` and `L/E` related by
the restrictions `R`, `R'` and the refinements `T`, `T'`, inflating from `K/F` to `L/F` and then
restricting to `L/E` is restricting to `K/E` and then inflating to `L/E`. -/
@[reassoc, elementwise]
theorem cohomologyInfl_comp_cohomologyRes (R : LayerRestriction small big)
    (R' : LayerRestriction small' big') (T : LayerRefinement big big')
    (T' : LayerRefinement small small') (F : Formation G) (n : ℕ) :
    T.cohomologyInfl F n ≫ R'.cohomologyRes F n =
      R.cohomologyRes F n ≫ T'.cohomologyInfl F n := by
  rw [LayerRefinement.cohomologyInfl_def, LayerRefinement.cohomologyInfl_def, cohomologyRes_def,
    cohomologyRes_def]
  have h₁ := groupCohomology.map_comp T.galHom R'.galHom (T.repHom F) (R'.repIso F).inv n
  have h₂ := groupCohomology.map_comp R.galHom T'.galHom (R.repIso F).inv (T'.repHom F) n
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  refine groupCohomology.map_congr ?_ ?_ n
  · refine MonoidHom.ext fun γ ↦ ?_
    induction γ using QuotientGroup.induction_on with
    | H w =>
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, galHom_mk, LayerRefinement.galHom_mk,
        LayerRefinement.galHom_mk, galHom_mk]
      exact congrArg QuotientGroup.mk (Subtype.ext rfl)
  -- Both composites read an element of `A^V` in `A^{V'}`, moving no element of the ambient module.
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    Rep.resMap_hom_toLinearMap, LinearMap.coe_comp,
    Representation.IntertwiningMap.coe_toLinearMap, Function.comp_apply]
  exact ((R'.repIso_inv_apply_coe F _).trans (T.repHom_hom_apply_coe F x)).trans
    ((T'.repHom_hom_apply_coe F _).trans (R.repIso_inv_apply_coe F x)).symm

end LayerRestriction

end TauCeti.ClassFieldTheory
