/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.GaloisMaps
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction

/-!
# Corestriction between finite normal layers

For a restriction of layers `K/E` inside `K/F`, corestriction carries
`Hⁿ(Gal(K/E), A^V)` to `Hⁿ(Gal(K/F), A^V)`. The smaller Galois group is identified with the
image of its inclusion into the larger one, and the coefficient identification `repIso`
then transports the generic group-cohomology corestriction to the layer cohomology groups.

The comparison with subgroup restriction is explicit. It gives the normalization
`cor ∘ res = [E : F]`, with precisely the relative degree of the restriction of layers.
This is the normalization used to compare invariants and fundamental classes under
corestriction.

Along a tower `F ⊆ E ⊆ E' ⊆ K`, corestricting from `K/E'` to `K/E` and then to `K/F` is
corestricting from `K/E'` to `K/F` (`cohomologyCor_trans`). This is the transitivity of
group-cohomology corestriction, `TauCeti.groupCohomology.corestriction_trans`, read through the
coefficient identifications `repIso`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§2–4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

/-- Cohomology of the smaller layer, identified with cohomology of the image of its Galois
group in the larger layer. The coefficient identification is `repIso`. -/
def cohomologyRangeIso (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    small.H F n ≅
      groupCohomology (Rep.res T.galHom.range.subtype (big.rep F)) n :=
  groupCohomology.mapIso (B := small.rep F)
    (A := Rep.res T.galHom.range.subtype (big.rep F))
    (MonoidHom.ofInjective T.galHom_injective)
    (Representation.equivOfIso (T.repIso F)).toLinearEquiv
    (fun g ↦ by
      apply LinearMap.ext
      intro x
      exact Rep.hom_comm_apply (T.repIso F).hom g x) n

/-- The range comparison is the canonical change-of-group isomorphism, with the
coefficient equivalence underlying `repIso`. -/
theorem cohomologyRangeIso_def (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.cohomologyRangeIso F n =
      groupCohomology.mapIso (B := small.rep F)
        (A := Rep.res T.galHom.range.subtype (big.rep F))
        (MonoidHom.ofInjective T.galHom_injective)
        (Representation.equivOfIso (T.repIso F)).toLinearEquiv
        (fun g ↦ by
          apply LinearMap.ext
          intro x
          exact Rep.hom_comm_apply (T.repIso F).hom g x) n := (rfl)

/-- Restriction to the image subgroup followed by the inverse coefficient and group
identification is the existing restriction between layer cohomology groups. -/
@[reassoc (attr := simp)]
theorem map_subtype_comp_cohomologyRangeIso_inv (T : LayerRestriction small big)
    (F : Formation G) (n : ℕ) :
    groupCohomology.map T.galHom.range.subtype
        (𝟙 (Rep.res T.galHom.range.subtype (big.rep F))) n ≫
      (T.cohomologyRangeIso F n).inv = T.cohomologyRes F n := by
  dsimp only [cohomologyRangeIso, groupCohomology.mapIso]
  rw [← groupCohomology.map_comp, cohomologyRes_def]
  apply groupCohomology.map_congr
  · ext g
    exact MonoidHom.ofInjective_apply T.galHom_injective
  · ext x
    rfl

/-- Corestriction between the cohomology groups of finite normal layers. This is subgroup
corestriction transported along the inclusion of Galois groups and `repIso`. -/
def cohomologyCor (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    small.H F n ⟶ big.H F n :=
  (T.cohomologyRangeIso F n).hom ≫
    TauCeti.groupCohomology.corestriction T.galHom.range (big.rep F) n

/-- Layer corestriction is the range comparison followed by subgroup corestriction. -/
theorem cohomologyCor_def (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.cohomologyCor F n = (T.cohomologyRangeIso F n).hom ≫
      TauCeti.groupCohomology.corestriction T.galHom.range (big.rep F) n := (rfl)

/-- Under the canonical identification with the image subgroup, layer corestriction is
generic group-cohomology corestriction. -/
@[reassoc (attr := simp)]
theorem cohomologyRangeIso_inv_comp_cohomologyCor (T : LayerRestriction small big)
    (F : Formation G) (n : ℕ) :
    (T.cohomologyRangeIso F n).inv ≫ T.cohomologyCor F n =
      TauCeti.groupCohomology.corestriction T.galHom.range (big.rep F) n := by
  simp [cohomologyCor]

/-- Corestriction after restriction multiplies every cohomology class by the relative
degree `[E : F]`. -/
@[reassoc, elementwise]
theorem cohomologyCor_cohomologyRes (T : LayerRestriction small big)
    (F : Formation G) (n : ℕ) :
    T.cohomologyRes F n ≫ T.cohomologyCor F n =
      T.relativeDegree • 𝟙 (big.H F n) := by
  rw [← T.map_subtype_comp_cohomologyRangeIso_inv F n, Category.assoc,
    cohomologyRangeIso_inv_comp_cohomologyCor,
    TauCeti.groupCohomology.map_subtype_id_comp_corestriction, T.index_range_galHom]

/-- Corestriction along the trivial restriction is the identity. -/
@[simp]
theorem cohomologyCor_self {L : NormalLayer G} (T : LayerRestriction L L)
    (F : Formation G) (n : ℕ) : T.cohomologyCor F n = 𝟙 (L.H F n) := by
  simpa [relativeDegree_def] using T.cohomologyCor_cohomologyRes F n

variable {a b c : NormalLayer G}

/-- **Corestriction of cohomology is functorial along a tower of restrictions.** Corestricting
from `K/E'` to `K/E` and then to `K/F` is corestricting from `K/E'` to `K/F`. -/
theorem cohomologyCor_trans (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (F : Formation G) (n : ℕ) :
    (T.trans T').cohomologyCor F n = T.cohomologyCor F n ≫ T'.cohomologyCor F n := by
  -- The two coefficient identifications, composed. Every coefficient map below moves no element
  -- of the ambient module, so the linear maps compared by `map_congr` agree.
  let δ : a.rep F ⟶ Rep.res T.galHom (Rep.res T'.galHom (c.rep F)) :=
    (T.repIso F).hom ≫ (Rep.resFunctor T.galHom).map (T'.repIso F).hom
  have hT' : (T'.cohomologyRangeIso F n).hom =
      groupCohomology.map (MonoidHom.id b.Gal) (T'.repIso F).hom n ≫
      (groupCohomology.mapIso (B := Rep.res T'.galHom (c.rep F))
        (A := Rep.res T'.galHom.range.subtype (c.rep F))
        (MonoidHom.ofInjective T'.galHom_injective) (LinearEquiv.refl ℤ (c.rep F))
        (fun _ => LinearMap.ext fun _ => rfl) n).hom := by
    rw [cohomologyRangeIso_def, groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
      ← groupCohomology.map_comp]
    exact groupCohomology.map_congr rfl (LinearMap.ext fun _ => rfl) n
  have hT : (T.cohomologyRangeIso F n).hom ≫
      groupCohomology.map (MonoidHom.id T.galHom.range)
        ((Rep.resFunctor T.galHom.range.subtype).map (T'.repIso F).hom) n =
      groupCohomology.map (MonoidHom.id a.Gal) δ n ≫
      (groupCohomology.mapIso (B := Rep.res T.galHom (Rep.res T'.galHom (c.rep F)))
        (A := Rep.res T.galHom.range.subtype (Rep.res T'.galHom (c.rep F)))
        (MonoidHom.ofInjective T.galHom_injective) (LinearEquiv.refl ℤ (c.rep F))
        (fun _ => LinearMap.ext fun _ => rfl) n).hom := by
    rw [cohomologyRangeIso_def, groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
      ← groupCohomology.map_comp, ← groupCohomology.map_comp]
    exact groupCohomology.map_congr rfl (LinearMap.ext fun _ => rfl) n
  have key := TauCeti.groupCohomology.corestriction_trans T.galHom_injective
    T'.galHom_injective (T.galHom_trans T').symm (c.rep F) n
  rw [cohomologyCor_def, cohomologyCor_def, cohomologyCor_def, hT']
  simp only [Category.assoc]
  rw [← TauCeti.groupCohomology.map_comp_corestriction_assoc, reassoc_of% hT, key,
    ← Category.assoc]
  congr 1
  rw [cohomologyRangeIso_def, groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp]
  refine groupCohomology.map_congr rfl (LinearMap.ext fun x => Subtype.ext ?_) n
  exact ((T.trans T').repIso_hom_apply_coe F x).trans
    ((T'.repIso_hom_apply_coe F _).trans (T.repIso_hom_apply_coe F x)).symm

end TauCeti.ClassFieldTheory.LayerRestriction
