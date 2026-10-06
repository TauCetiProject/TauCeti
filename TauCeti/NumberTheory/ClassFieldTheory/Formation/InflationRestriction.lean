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

## Main statements

* `TauCeti.ClassFieldTheory.LayerRefinement.range_cohomologyInfl_eq_ker_cohomologyRes`: the
  inflation-restriction sequence of a refinement is exact.

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

/-- **The inflation-restriction sequence of a refinement of layers.** For a refinement
`T : LayerRefinement old new`, the tower `F ⊆ K ⊆ L` with Galois groups `U/V` and `U/V'`, if
`Hⁱ(V/V', A^{V'})` vanishes for `0 < i ≤ n`, then a class of `Hⁿ⁺¹(U/V', A^{V'})` is inflated from
`Hⁿ⁺¹(U/V, A^V)` exactly when its restriction to the layer `L/K` of the kernel `V/V'` vanishes. -/
theorem range_cohomologyInfl_eq_ker_cohomologyRes (T : LayerRefinement old new)
    (F : Formation G) (n : ℕ)
    (hH : ∀ i < n, Subsingleton ((new.subgroupLayer T.galHom.ker).H F (i + 1))) :
    LinearMap.range (T.cohomologyInfl F (n + 1)).hom =
      LinearMap.ker ((new.subgroupRestriction T.galHom.ker).cohomologyRes F (n + 1)).hom := by
  set R := new.subgroupRestriction T.galHom.ker
  have hφ : Function.Injective (T.repHom F).hom := fun x y h =>
    Subtype.ext ((T.repHom_hom_apply_coe F x).symm.trans
      ((congrArg Subtype.val h).trans (T.repHom_hom_apply_coe F y)))
  have hψ : Function.Bijective (R.repIso F).inv.hom :=
    Function.bijective_iff_has_inverse.2 ⟨(R.repIso F).hom.hom,
      fun x => Subtype.ext ((R.repIso_hom_apply_coe F _).trans (R.repIso_inv_apply_coe F x)),
      fun x => Subtype.ext ((R.repIso_inv_apply_coe F _).trans (R.repIso_hom_apply_coe F x))⟩
  rw [cohomologyInfl_def, LayerRestriction.cohomologyRes_def]
  exact groupCohomology.range_map_succ_eq_ker_map_succ T.galHom_surjective hφ (range_repHom T F)
    R.galHom_injective (new.range_galHom_subgroupRestriction T.galHom.ker) hψ n
    fun i hi => have := hH i hi; ModuleCat.isZero_of_subsingleton _

end LayerRefinement

end TauCeti.ClassFieldTheory
