/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Local
public import TauCeti.RingTheory.Henselization.Local

/-!
# From ordinary to strict henselization

For a local ring `R` with a local map to a henselian local ring `Ω`, there is a canonical
local map from the ordinary henselization of `R` to the colimit of its `Ω`-pointed étale
neighbourhoods. In particular, taking `Ω` to be a separable closure of the residue field gives
the comparison from ordinary to strict henselization. This comparison is needed to relate
their completions.

The construction does not require henselianity of the pointed colimit. The universal map
from the ordinary henselization to `Ω` points every ordinary étale neighbourhood. The maps
from these pointed neighbourhoods into the pointed colimit then induce the comparison.
It is the unique `R`-algebra map between these rings, and its composite with `toTarget` is
the universal map to `Ω`.

## References

* Stacks Project, Tag 04GP, property (1).
* `TauCeti.Henselization.lift` and `TauCeti.Henselization.descOfCompatible` supply the
  ordinary henselization's universal map and its colimit construction.
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [CommRing Ω]
  [HenselianLocalRing Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]

/-- The universal map to the pointing ring makes an ordinary neighbourhood into a pointed one. -/
private noncomputable abbrev pointedNeighbourhood
    (B : Henselization.Neighbourhood.{u, u} (maximalIdeal R)) : Neighbourhood R Ω :=
  let point : B.obj →ₐ[R] Ω :=
    (Henselization.lift (map_maximalIdeal_le (algebraMap R Ω))).comp
      (Henselization.stage (maximalIdeal R) B)
  ⟨Over.mk (CommAlgCat.ofHom (ULift.algEquiv.symm.toAlgHom.comp point)),
    (isPointedNeighbourhood_iff R Ω _).mpr
      ((Henselization.isNeighbourhood_iff _ _).mp B.property).1⟩

/-- Morphisms of ordinary neighbourhoods respect the points induced by the universal map. -/
private noncomputable def pointedNeighbourhoodHom
    {B C : Henselization.Neighbourhood.{u, u} (maximalIdeal R)} (f : B ⟶ C) :
    pointedNeighbourhood R Ω B ⟶ pointedNeighbourhood R Ω C :=
  ObjectProperty.homMk (Over.homMk f.hom (by
    apply CommAlgCat.hom_ext
    simp only [pointedNeighbourhood, Over.mk_left, Over.mk_hom, CommAlgCat.hom_comp,
      CommAlgCat.hom_ofHom, AlgHom.comp_assoc, Henselization.stage_naturality]))

/-- The maps from ordinary neighbourhoods into the pointed colimit form a compatible family. -/
private theorem pointedStage_comp
    {B C : Henselization.Neighbourhood.{u, u} (maximalIdeal R)} (f : B ⟶ C) :
    (stage R Ω (pointedNeighbourhood R Ω C)).comp f.hom.hom =
      stage R Ω (pointedNeighbourhood R Ω B) :=
  stage_naturality R Ω (pointedNeighbourhoodHom R Ω f)

/-- The canonical comparison from the ordinary henselization to the colimit of pointed étale
neighbourhoods. For `Ω` a separable closure of the residue field, this is the map from ordinary
to strict henselization. It is local and is the unique `R`-algebra map between these rings. -/
@[stacks 04GP "(1), comparison map"]
noncomputable def fromHenselization :
    Henselization.algebra (maximalIdeal R) →ₐ[R] algebra R Ω :=
  Henselization.descOfCompatible (maximalIdeal R)
    (fun B ↦ stage R Ω (pointedNeighbourhood R Ω B)) (pointedStage_comp R Ω)

/-- The comparison respects the universal map from ordinary henselization to the pointing ring. -/
@[simp]
theorem toTarget_comp_fromHenselization :
    (toTarget R Ω).comp (fromHenselization R Ω) =
      Henselization.lift (map_maximalIdeal_le (algebraMap R Ω)) :=
  Henselization.eq_lift _ _

/-- Elementwise form of `toTarget_comp_fromHenselization`. -/
@[simp]
theorem toTarget_fromHenselization (x : Henselization.algebra (maximalIdeal R)) :
    toTarget R Ω (fromHenselization R Ω x) =
      Henselization.lift (map_maximalIdeal_le (algebraMap R Ω)) x :=
  DFunLike.congr_fun (toTarget_comp_fromHenselization R Ω) x

/-- The map from ordinary to strict henselization is a local homomorphism. More generally,
this holds for any henselian local pointing ring receiving a local map from `R`. -/
@[stacks 04GP "(1), local map"]
instance isLocalHom_fromHenselization : IsLocalHom (fromHenselization R Ω) := by
  have : IsLocalHom (Henselization.lift (map_maximalIdeal_le (algebraMap R Ω))) :=
    Henselization.isLocalHom_lift _ _
  have : IsLocalHom ((toTarget R Ω).comp (fromHenselization R Ω)) :=
    toTarget_comp_fromHenselization R Ω ▸ this
  exact ⟨fun x hx ↦ this.map_nonunit x (hx.map (toTarget R Ω))⟩

/-- Every `R`-algebra map from the ordinary henselization to the pointed colimit agrees with
the canonical comparison, without any henselianity assumption on the colimit. -/
theorem eq_fromHenselization
    (f : Henselization.algebra (maximalIdeal R) →ₐ[R] algebra R Ω) :
    f = fromHenselization R Ω :=
  Henselization.algHom_ext_of_map_le_jacobson
    ((map_maximalIdeal_le (algebraMap R (algebra R Ω))).trans
      (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge)

end TauCeti.StrictHenselization
