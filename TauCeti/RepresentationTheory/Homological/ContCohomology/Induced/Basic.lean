/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Functor
public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Induction as a smooth discrete representation

For an open subgroup of a compact group, Mathlib's algebraically induced representation
has a continuous action when equipped with the discrete topology. The finite-index
isomorphism `Rep.indCoindIso` transports continuity from `TauCeti.algebraicCoindAsSmooth`.
The resulting `TauCeti.algebraicIndAsSmooth` has the actual tensor-coinvariant carrier of
induction, and `TauCeti.algebraicIndIsoCoind` identifies it with algebraic coinduction as
smooth discrete representations. Composing with `TauCeti.topologicalCoindIsoAlgebraic`
gives the comparison with locally constant coinduction.

The algebraic comparison and its inverse are Mathlib's constructions, including their
normalization on tensor generators. No new algebraic induction model is introduced.

## References

* Mathlib's `Rep.indCoindIso`, by Amelia Livingston, supplies the algebraic comparison.
* L. Ribes, P. Zalesskii, *Profinite Groups*, second edition, §6.10.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (R : Type v) [CommRing R] [TopologicalSpace R]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : OpenSubgroup G) (A : SmoothDiscreteTopRep.{v, u, max u v w} R U.toSubgroup)

attribute [local instance] Classical.decRel

local instance : U.toSubgroup.FiniteIndex :=
  letI := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
  Subgroup.finiteIndex_of_finite_quotient

/-- Algebraic induction from an open subgroup, with discrete topology and continuous
scalar and group actions transported along Mathlib's finite-index comparison. -/
noncomputable abbrev algebraicIndDiscreteRep : DiscreteRep.{v, u, max u v w} R G := by
  let B := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  let C := algebraicCoindDiscreteRep R G U A
  letI : TopologicalSpace (Rep.coind U.toSubgroup.subtype B) := C.topologicalSpace
  letI : DiscreteTopology (Rep.coind U.toSubgroup.subtype B) := C.discreteTopology
  letI : DistribMulAction G (Rep.coind U.toSubgroup.subtype B) := C.distribMulAction
  letI : SMulCommClass G R (Rep.coind U.toSubgroup.subtype B) := C.smulCommClass
  letI : ContinuousSMul R (Rep.coind U.toSubgroup.subtype B) := C.continuousSMulRing
  letI : ContinuousSMul G (Rep.coind U.toSubgroup.subtype B) := C.continuousSMul
  let eRep := Representation.equivOfIso (Rep.indCoindIso.{max u w, v, u} B)
  let e := eRep.toLinearEquiv
  let V := Representation.IndV U.toSubgroup.subtype B.ρ
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  let ρ := Representation.ind U.toSubgroup.subtype B.ρ
  letI : DistribMulAction G V := DistribMulAction.compHom V ρ
  letI : SMulCommClass G R V := ⟨fun g r x ↦ (ρ g).map_smul r x⟩
  let h : V ≃ₜ C.V :=
    { toEquiv := e.toEquiv
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  letI : ContinuousSMul R V :=
    h.isInducing.continuousSMul continuous_id fun {r x} ↦ e.map_smul r x
  letI : ContinuousSMul G V :=
    h.isInducing.continuousSMul continuous_id fun {g x} ↦ by
      exact (eRep.toIntertwiningMap.isIntertwining _ _ g x).trans
          (LinearMap.congr_fun (DFunLike.congr_fun (algebraicCoindDiscreteRep_ρ R G U A) g)
            (e x)).symm
  exact { V := V }

/-- The smooth discrete induced representation carries Mathlib's algebraic induced action. -/
@[simp]
theorem algebraicIndDiscreteRep_ρ :
    (algebraicIndDiscreteRep R G U A).ρ =
      Representation.ind U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) := (rfl)

/-- Algebraic induction from an open subgroup, regarded as a smooth discrete topological
representation on its tensor-coinvariant carrier. -/
noncomputable abbrev algebraicIndAsSmooth : SmoothDiscreteTopRep.{v, u, max u v w} R G :=
  (toSmoothDiscrete R G).obj (algebraicIndDiscreteRep R G U A)

/-- Mathlib's finite-index comparison as an isomorphism of discrete representations. -/
private noncomputable def discreteIndIsoCoind :
    algebraicIndDiscreteRep R G U A ≅ algebraicCoindDiscreteRep R G U A := by
  let B := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  let e := Representation.equivOfIso (Rep.indCoindIso.{max u w, v, u} B)
  refine
    { hom := { toLinearMap := Rep.indToCoind B, isIntertwining' := ?_ }
      inv := { toLinearMap := Rep.coindToInd B, isIntertwining' := ?_ }
      hom_inv_id := Representation.IntertwiningMap.ext (Rep.indToCoind_coindToInd B)
      inv_hom_id := Representation.IntertwiningMap.ext (Rep.coindToInd_indToCoind B) }
  · intro g
    rw [algebraicIndDiscreteRep_ρ, algebraicCoindDiscreteRep_ρ]
    rw [← Rep.indCoindIso_hom_hom_toLinearMap.{max u w, v, u} B]
    exact e.toIntertwiningMap.isIntertwining' g
  · intro g
    rw [algebraicIndDiscreteRep_ρ, algebraicCoindDiscreteRep_ρ]
    exact e.symm.toIntertwiningMap.isIntertwining' g

/-- Induction and coinduction from an open subgroup are isomorphic as smooth discrete
representations. Its underlying map is Mathlib's `Rep.indToCoind`. -/
noncomputable def algebraicIndIsoCoind :
    algebraicIndAsSmooth R G U A ≅ algebraicCoindAsSmooth R G U A :=
  (toSmoothDiscrete R G).mapIso (discreteIndIsoCoind R G U A)

/-- The forward smooth comparison is the algebraic induction-to-coinduction map. -/
@[simp]
theorem algebraicIndIsoCoind_hom_toLinearMap :
    (algebraicIndIsoCoind R G U A).hom.hom.hom.toContinuousLinearMap.toLinearMap =
      Rep.indToCoind (Rep.of
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) := by
  apply LinearMap.ext
  intro x
  rw [algebraicIndIsoCoind, Functor.mapIso_hom]
  exact (toSmoothDiscrete_map_hom_apply R G (discreteIndIsoCoind R G U A).hom x).trans
    (by rfl)

/-- The inverse smooth comparison is the algebraic sum over right cosets. -/
@[simp]
theorem algebraicIndIsoCoind_inv_toLinearMap :
    (algebraicIndIsoCoind R G U A).inv.hom.hom.toContinuousLinearMap.toLinearMap =
      Rep.coindToInd (Rep.of
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) := by
  apply LinearMap.ext
  intro x
  rw [algebraicIndIsoCoind, Functor.mapIso_inv]
  exact (toSmoothDiscrete_map_hom_apply R G (discreteIndIsoCoind R G U A).inv x).trans
    (by rfl)

/-- On a tensor generator, the comparison is the equivariant function supported on its
right coset, with value `a` at `g`. -/
@[simp]
theorem algebraicIndIsoCoind_hom_mk_apply (g h : G) (a : A.obj.V) :
    (dsimp% only [Representation.IndV.mk, LinearMap.coe_comp,
      Function.comp_apply, TensorProduct.mk_apply] ((algebraicIndIsoCoind R G U A).hom.hom.hom
      (Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)).1 h) =
      Rep.indToCoindAux (Rep.of
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) g a h := by
  have he := LinearMap.congr_fun (algebraicIndIsoCoind_hom_toLinearMap R G U A)
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)
  let B := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  have hm : (Rep.indToCoind B (Representation.IndV.mk U.toSubgroup.subtype B.ρ g a)).1 h =
      Rep.indToCoindAux B g a h := by
    -- Freeze the representation before reducing the tensor lift: the dictionary equips the
    -- same carrier with additional structure, but does not change this algebraic computation.
    simp [Rep.indToCoind, Representation.IndV.mk]
    rfl
  exact (congrArg (fun f : Representation.coindV U.toSubgroup.subtype
    (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) ↦ f.1 h) he).trans hm

/-- Algebraic induction from an open subgroup is isomorphic to locally constant
coinduction, via the algebraic finite-index comparison. -/
noncomputable def topologicalIndIsoCoind :
    algebraicIndAsSmooth R G U A ≅ coindTopRep R G U.toSubgroup A :=
  algebraicIndIsoCoind R G U A ≪≫ (topologicalCoindIsoAlgebraic R G U A).symm

/-- The comparison with locally constant coinduction factors through algebraic coinduction. -/
theorem topologicalIndIsoCoind_def :
    topologicalIndIsoCoind R G U A =
      algebraicIndIsoCoind R G U A ≪≫ (topologicalCoindIsoAlgebraic R G U A).symm := (rfl)

/-- The locally constant comparison sends a tensor generator to the equivariant function
supported on its right coset. -/
-- Name the `DiscreteCoind` carrier before applying its function coercion: the smooth-discrete
-- dictionary presents the codomain as a bundled `TopRep`, as in the coinduction comparison API.
-- Keep this auxiliary-function formula out of `simp`: it introduces a chosen decidability
-- instance and shadows the direct normalization below.
theorem topologicalIndIsoCoind_hom_mk_apply (g h : G) (a : A.obj.V) :
    (show DiscreteCoind G U.toSubgroup A.obj.V from
      (topologicalIndIsoCoind R G U A).hom.hom.hom
      (Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)) h =
      Rep.indToCoindAux (Rep.of
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) g a h := by
  -- The composite comparison acts by function composition on the underlying carriers.
  -- Its second factor leaves all values unchanged, so use the two public computation lemmas.
  exact (topologicalCoindIsoAlgebraic_inv_hom_hom_apply_coe R G U A
    ((algebraicIndIsoCoind R G U A).hom.hom.hom
      (Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)) h).trans
          (algebraicIndIsoCoind_hom_mk_apply R G U A g h a)

/-- The tensor generator at `g` maps to a locally constant function taking value `a` at `g`.
This computation avoids exposing the decidability instance in Mathlib's auxiliary function. -/
@[simp]
theorem topologicalIndIsoCoind_hom_mk_self (g : G) (a : A.obj.V) :
    -- Normalize the generator and name the locally constant carrier, as above.
    (dsimp% only [Representation.IndV.mk, LinearMap.coe_comp,
      Function.comp_apply, TensorProduct.mk_apply] (show DiscreteCoind G U.toSubgroup A.obj.V from
      (topologicalIndIsoCoind R G U A).hom.hom.hom
        (Representation.IndV.mk U.toSubgroup.subtype
          (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)) g) = a := by
  exact (topologicalIndIsoCoind_hom_mk_apply R G U A g g a).trans
    (Rep.indToCoindAux_self (A := Rep.of
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) g a)

end TauCeti
