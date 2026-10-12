/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Zeroth twisted homology and monodromy coinvariants

For a path-connected space, twisted zeroth homology is the coinvariants of the monodromy
representation on any chosen fibre. The comparison sends a coefficient at the basepoint to
its class modulo monodromy. In particular, it keeps the map from the fibre visible.

Paths used to construct the inverse disappear in the coinvariants, so the comparison is
characterized by the basepoint fibre map.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [CommRing R] {X : TopCat.{v}} [PathConnectedSpace X]
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (x : X)

private abbrev returnPath (y : FundamentalGroupoid X) : y ⟶ FundamentalGroupoid.mk x :=
  Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y.as x)

private def coinvariantsLeg (y : FundamentalGroupoid X) :
    L.obj y ⟶ ModuleCat.of R (monodromyRepresentation L x).Coinvariants :=
  L.map (returnPath x y) ≫ ModuleCat.ofHom (Representation.Coinvariants.mk _)

private lemma map_coinvariantsLeg {y z : FundamentalGroupoid X} (p : y ⟶ z) :
    L.map p ≫ coinvariantsLeg L x z = coinvariantsLeg L x y := by
  ext a
  let g : FundamentalGroup X x := inv (returnPath x y) ≫ p ≫ returnPath x z
  have hg : monodromyRepresentation L x g (L.map (returnPath x y) a) =
      L.map (returnPath x z) (L.map p a) := by
    simp only [monodromyRepresentation_apply, ← L.map_comp_apply, g]
    simp
  simp only [coinvariantsLeg, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [← hg]
  exact Representation.Coinvariants.mk_self_apply (monodromyRepresentation L x) g _

private def coinvariantsCocone : Cocone L where
  pt := ModuleCat.of R (monodromyRepresentation L x).Coinvariants
  ι :=
    { app := coinvariantsLeg L x
      naturality y z p := by
        rw [Functor.const_obj_map]
        exact (map_coinvariantsLeg L x p).trans (Category.comp_id _).symm }

-- The proof uses the groupoid-colimit description of twisted zeroth homology and Mathlib's
-- `Representation.Coinvariants.lift`.
private def isColimitCoinvariantsCocone : IsColimit (coinvariantsCocone L x) where
  desc s := ModuleCat.ofHom (Representation.Coinvariants.lift _
    (s.ι.app (FundamentalGroupoid.mk x)).hom (fun g ↦ by
      ext a
      exact s.w_apply g a))
  fac s y := by
    ext a
    simp only [coinvariantsCocone, coinvariantsLeg, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_ofHom, Representation.Coinvariants.lift_mk]
    exact s.w_apply (returnPath x y) a
  uniq s f hf := by
    dsimp only [coinvariantsCocone] at f hf
    apply ModuleCat.hom_ext
    apply Representation.Coinvariants.hom_ext
    ext a
    have h := congrArg (fun k ↦ k.hom a) (hf (FundamentalGroupoid.mk x))
    simp only [coinvariantsLeg, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_ofHom, Representation.Coinvariants.lift_mk] at h ⊢
    have hm : Representation.Coinvariants.mk (monodromyRepresentation L x)
        (L.map (returnPath x (FundamentalGroupoid.mk x)) a) =
        Representation.Coinvariants.mk (monodromyRepresentation L x) a :=
      Representation.Coinvariants.mk_self_apply (monodromyRepresentation L x)
        (returnPath x (FundamentalGroupoid.mk x)) a
    rw [hm] at h
    exact h

/-- **The degree-zero monodromy formula.** Twisted zeroth homology of a path-connected
space is the coinvariants of the monodromy representation on the fibre at `x`. -/
def twistedHomology₀IsoCoinvariants :
    twistedHomology L 0 ≅ ModuleCat.of R (monodromyRepresentation L x).Coinvariants :=
  (isColimitTwistedHomology₀Cocone L).coconePointUniqueUpToIso
    (isColimitCoinvariantsCocone L x)

/-- At the basepoint, the homology-to-coinvariants comparison is the monodromy quotient map. -/
@[reassoc (attr := simp)]
lemma ιTwistedHomology₀_isoCoinvariants_hom :
    ιTwistedHomology₀ L x ≫ (twistedHomology₀IsoCoinvariants L x).hom =
      ModuleCat.ofHom (Representation.Coinvariants.mk (monodromyRepresentation L x)) := by
  have h := (isColimitTwistedHomology₀Cocone L).comp_coconePointUniqueUpToIso_hom
    (isColimitCoinvariantsCocone L x) (FundamentalGroupoid.mk x)
  refine h.trans ?_
  ext a
  exact Representation.Coinvariants.mk_self_apply (monodromyRepresentation L x)
    (returnPath x (FundamentalGroupoid.mk x)) a

/-- At any point, transport to the basepoint followed by the monodromy quotient computes
the coinvariant class. Any path to the basepoint gives the same answer. -/
@[reassoc]
lemma ιTwistedHomology₀_isoCoinvariants_hom_of_path (y : X) (p : Path y x) :
    ιTwistedHomology₀ L y ≫ (twistedHomology₀IsoCoinvariants L x).hom =
      L.map (Path.Homotopic.Quotient.mk p) ≫
        ModuleCat.ofHom (Representation.Coinvariants.mk (monodromyRepresentation L x)) := by
  rw [← ιTwistedHomology₀_isoCoinvariants_hom L x, ← Category.assoc]
  erw [map_ιTwistedHomology₀ L (Path.Homotopic.Quotient.mk p)]

/-- The monodromy coinvariant formula is natural in the local coefficient system. -/
@[reassoc]
lemma twistedHomology₀IsoCoinvariants_hom_naturality
    {K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) :
    twistedHomologyCoefficientMap η 0 ≫ (twistedHomology₀IsoCoinvariants K x).hom =
      (twistedHomology₀IsoCoinvariants L x).hom ≫ ModuleCat.ofHom
        (Representation.Coinvariants.map _ _ (monodromyMap η x)) := by
  apply (cancel_epi (ιTwistedHomology₀ L x)).1
  rw [ιTwistedHomology₀_coefficientMap_assoc]
  erw [ιTwistedHomology₀_isoCoinvariants_hom K x,
    ιTwistedHomology₀_isoCoinvariants_hom_assoc L x]
  ext a
  simp

/-- The inverse comparison sends a coefficient modulo monodromy to its homology class. -/
@[reassoc (attr := simp)]
lemma coinvariants_mk_comp_twistedHomology₀IsoCoinvariants_inv :
    ModuleCat.ofHom (Representation.Coinvariants.mk (monodromyRepresentation L x)) ≫
        (twistedHomology₀IsoCoinvariants L x).inv = ιTwistedHomology₀ L x := by
  rw [← ιTwistedHomology₀_isoCoinvariants_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end TauCeti.LocalCoefficientSystem
