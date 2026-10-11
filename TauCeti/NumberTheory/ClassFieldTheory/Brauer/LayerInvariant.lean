/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.OpenSubgroup
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Conjugation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Layer.Inflation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
import TauCeti.NumberTheory.ClassFieldTheory.Formation.InflationRestriction
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# The local invariant of a finite normal layer of the units formation

Let `K` be a field with separable closure `Kˢ` and absolute Galois group `G_K`, and let
`V ◁ U` be a finite normal layer of open subgroups of `G_K` in the formation
`TauCeti.ClassFieldTheory.unitsFormation K` of `(Kˢ)ˣ`; in field notation it is the finite
Galois extension `E'/E` of the fixed fields of `U` and `V`. This file carries the second
cohomology `H²(U ⧸ V, ((Kˢ)ˣ)^V)` of the layer into the continuous cohomology
`H²(U, (Kˢ)ˣ)` of the ground subgroup by the inflation
`TauCeti.ClassFieldTheory.NormalLayer.explicitInfl2` of a layer, read on `(Kˢ)ˣ` through the
coefficient dictionary `unitsCoeffEquivUnitsFormation K`, and, for a nonarchimedean local field
`K`, composes with the local invariant `TauCeti.ClassFieldTheory.subgroupInvMap` of `U` to
obtain the **invariant of the layer**

`inv_{E'/E} : H²(U ⧸ V, ((Kˢ)ˣ)^V) → ℚ/ℤ`

(`layerInv`). This is the invariant map of a layer that the class-formation axioms for
`unitsFormation K` constrain, and this file proves the properties of it that come from Hilbert 90
and from the restriction and corestriction squares of the local invariant:

* it is injective (`layerInv_injective`), because inflation into `H²(U, (Kˢ)ˣ)` is injective by
  Hilbert 90 for `V` (`NormalLayer.explicitInfl2_injective_of_subsingleton`);
* its values have order dividing the degree `[U : V]` (`degree_nsmul_layerInv`), because
  restriction to `V` kills inflated classes (`NormalLayer.explicitMap2_explicitInfl2_eq_zero`)
  and multiplies
  the invariant by `[U : V]`;
* restriction to an intermediate ground field multiplies it by the relative degree
  (`layerInv_cohomologyRes`), and inflation to a larger top field does not change it
  (`layerInv_cohomologyInfl`), because inflation into the cohomology of the ground subgroup is
  compatible with both operations on layers (`NormalLayer.explicitInfl2_cohomologyRes`,
  `NormalLayer.explicitInfl2_cohomologyInfl`);
* its range is exactly the subgroup of `ℚ/ℤ` of order `[U : V]` (`range_layerInv`). Every class
  of `H²(U, (Kˢ)ˣ)` is inflated from a layer `V' ◁ U` with `V' ≤ V`
  (`NormalLayer.exists_explicitInfl2_eq`), and
  by the inflation-restriction sequence of the refinement `V' ◁ U` of `V ◁ U`
  (`LayerRefinement.range_cohomologyInfl_eq_ker_cohomologyRes`) together with Hilbert 90, a class
  of `V' ◁ U` whose restriction to `V' ◁ V` vanishes comes from `V ◁ U`;
* conjugation by `g : G_K` preserves it (`layerInv_conjugateCohomologyIso`), because inflation
  carries the conjugation of layers to the conjugation `H²(U, (Kˢ)ˣ) → H²(gUg⁻¹, (Kˢ)ˣ)`, which
  preserves the local invariant (`subgroupInvMap_explicitMap2_of_conj`).

## Main definitions

* `TauCeti.ClassFieldTheory.layerInv K L`: the invariant of a layer, for a nonarchimedean local
  field `K`.

## Main results

* `TauCeti.ClassFieldTheory.layerInv_injective`: the invariant of a layer is injective.
* `TauCeti.ClassFieldTheory.degree_nsmul_layerInv`: the invariant of a layer is killed by its
  degree.
* `TauCeti.ClassFieldTheory.layerInv_cohomologyRes`: restriction multiplies the invariant by the
  relative degree.
* `TauCeti.ClassFieldTheory.layerInv_cohomologyInfl`: inflation preserves the invariant.
* `TauCeti.ClassFieldTheory.range_layerInv`: the invariants of a layer form the subgroup of `ℚ/ℤ`
  of order its degree.
* `TauCeti.ClassFieldTheory.layerInv_conjugateCohomologyIso`: conjugation preserves the invariant.

## Implementation notes

The continuous cohomology of the ground subgroup is that of its underlying subgroup
`L.ground.toSubgroup` of `G_K`, as in `TauCeti.ClassFieldTheory.subgroupInvMap`, and the Galois
group of the layer is read as the quotient of that subgroup by
`L.top.toSubgroup.subgroupOf L.ground.toSubgroup`; this quotient is definitionally the Galois
group `L.Gal` of the layer. Inflation from a layer is the generic construction of
`TauCeti.NumberTheory.ClassFieldTheory.Formation.Layer.Inflation` at the coefficient dictionary
`unitsCoeffEquivUnitsFormation K`; only Hilbert 90 and the conjugation of layers are specific to
the formation of units here.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter XI, §1 and Chapter XIII, §3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.7), for
  the injectivity of inflation in degree two.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.groupCohomology ContCohomology

variable {K : Type} [Field K]

/-! ### Inflation from a layer of the formation of units -/

section Inflation

variable (L : NormalLayer (AbsoluteGaloisGroup K))

/-- Hilbert 90 for the top subgroup `V`, read as a subgroup of the ground subgroup `U`. -/
private theorem subsingleton_H1_top :
    Subsingleton (H1 (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) (UnitsCoeff K)) := by
  have := subsingleton_H1_unitsCoeff_of_isClosed K L.top.toSubgroup L.top.isClosed
  let φ : (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) ≃ₜ* L.top.toSubgroup :=
    { toMulEquiv := Subgroup.subgroupOfEquivOfLe (OpenSubgroup.toSubgroup_le.2 L.top_le_ground)
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact (explicitMap1Equiv _ _ _ _ φ (AddEquiv.refl (UnitsCoeff K)) continuous_id continuous_id
    fun _ _ => rfl).symm.injective.subsingleton

/-! ### Inflation and conjugation -/

section Conjugation

variable (g : AbsoluteGaloisGroup K)

/-- Inverse conjugation `v ↦ g⁻¹ v g`, from the ground subgroup `gUg⁻¹` of the conjugate layer to
the ground subgroup `U` of the layer. -/
private def conjugateGroundHom :
    (L.conjugate g).ground.toSubgroup →ₜ* L.ground.toSubgroup where
  toFun v := ⟨g⁻¹ * v * g, (L.mem_ground_conjugate g).1 v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' v w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  continuous_toFun := ((continuous_mul_const g).comp
    ((continuous_const_mul g⁻¹).comp continuous_subtype_val)).subtype_mk _

/-- Inverse conjugation on underlying elements of `G_K`. -/
private theorem conjugateGroundHom_apply_coe (v : (L.conjugate g).ground.toSubgroup) :
    (conjugateGroundHom L g v : AbsoluteGaloisGroup K) = g⁻¹ * v * g :=
  (rfl)

/-- The action of `g` on `(Kˢ)ˣ` and inverse conjugation form a compatible pair. -/
private theorem conjugateGroundHom_smul (v : (L.conjugate g).ground.toSubgroup)
    (m : UnitsCoeff K) :
    DistribSMul.toAddMonoidHom (UnitsCoeff K) g (conjugateGroundHom L g v • m) =
      v • DistribSMul.toAddMonoidHom (UnitsCoeff K) g m := by
  rw [DistribSMul.toAddMonoidHom_apply, DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def,
    Subgroup.smul_def, conjugateGroundHom_apply_coe, smul_smul, smul_smul]
  congr 1
  group

/-- The ground subgroup of the conjugate layer is the conjugate `gUg⁻¹`. -/
private theorem toSubgroup_ground_conjugate :
    (L.conjugate g).ground.toSubgroup = L.ground.toSubgroup.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, OpenSubgroup.mem_toSubgroup,
    OpenSubgroup.mem_toSubgroup]
  exact L.mem_ground_conjugate g

/-- The coefficient dictionary carries the action of `g` on the formation to its action on
`(Kˢ)ˣ`. -/
private theorem unitsCoeffEquivUnitsFormation_symm_ρ (y : (unitsFormation K).toRep.V) :
    (unitsCoeffEquivUnitsFormation K).symm ((unitsFormation K).toRep.ρ g y) =
      DistribSMul.toAddMonoidHom (UnitsCoeff K) g ((unitsCoeffEquivUnitsFormation K).symm y) := by
  rw [AddEquiv.symm_apply_eq, DistribSMul.toAddMonoidHom_apply, unitsCoeffEquivUnitsFormation_smul,
    AddEquiv.apply_symm_apply]

/-- The inflated cocycle of a layer cocycle pulled back along a pair `(f, φ)` that acts on Galois
groups by inverse conjugation and on coefficients by `g` is the inflated cocycle, pulled back along
inverse conjugation and pushed forward by `g`. -/
private theorem inflCocycle2_mapCocycles₂ (f : (L.conjugate g).Gal →* L.Gal)
    (φ : Rep.res f (L.rep (unitsFormation K)) ⟶ (L.conjugate g).rep (unitsFormation K))
    (hf : ∀ w : (L.conjugate g).ground.toSubgroup,
      f (w : (L.conjugate g).Gal) = (conjugateGroundHom L g w : L.Gal))
    (hφ : ∀ x : (L.rep (unitsFormation K)).V, (φ.hom x : (unitsFormation K).toRep.V) =
      (unitsFormation K).toRep.ρ g (x : (unitsFormation K).toRep.V))
    (c : cocycles₂ (L.rep (unitsFormation K))) (p : (L.conjugate g).ground.toSubgroup ×
      (L.conjugate g).ground.toSubgroup) :
    ((L.conjugate g).inflCocycle2 (unitsCoeffEquivUnitsFormation K)
        (unitsCoeffEquivUnitsFormation_smul K) (mapCocycles₂ f φ c) :
        (L.conjugate g).ground.toSubgroup × (L.conjugate g).ground.toSubgroup → UnitsCoeff K) p =
      DistribSMul.toAddMonoidHom (UnitsCoeff K) g
        ((L.inflCocycle2 (unitsCoeffEquivUnitsFormation K) (unitsCoeffEquivUnitsFormation_smul K)
          c : L.ground.toSubgroup × L.ground.toSubgroup → UnitsCoeff K)
          (conjugateGroundHom L g p.1, conjugateGroundHom L g p.2)) := by
  rw [NormalLayer.inflCocycle2_apply, NormalLayer.inflCocycle2_apply,
    TauCeti.groupCohomology.mapCocycles₂_apply, hφ,
    unitsCoeffEquivUnitsFormation_symm_ρ, hf, hf]

/-- **Inflation commutes with conjugation**: inflating the conjugate of a class to the ground
subgroup `gUg⁻¹` of the conjugate layer is conjugating the inflated class from `U` to `gUg⁻¹`. -/
private theorem explicitInfl2_conjugateCohomologyIso (x : L.H (unitsFormation K) 2) :
    (L.conjugate g).explicitInfl2 (unitsCoeffEquivUnitsFormation K)
        (unitsCoeffEquivUnitsFormation_smul K)
        ((L.conjugateCohomologyIso (unitsFormation K) g 2).hom x) =
      explicitMap2 L.ground.toSubgroup (UnitsCoeff K) (L.conjugate g).ground.toSubgroup
        (UnitsCoeff K) (conjugateGroundHom L g) (DistribSMul.toAddMonoidHom (UnitsCoeff K) g)
        continuous_of_discreteTopology (conjugateGroundHom_smul L g)
        (L.explicitInfl2 (unitsCoeffEquivUnitsFormation K) (unitsCoeffEquivUnitsFormation_smul K)
          x) := by
  refine L.explicitInfl2_eq_explicitMap2_explicitInfl2 _ _ _ _ _ _ _
    (fun y => (L.conjugateCohomologyIso (unitsFormation K) g 2).hom y) (fun c => ?_) x
  refine ⟨?_, ?hcls, ?hcocycle⟩
  case hcls =>
    rw [NormalLayer.conjugateCohomologyIso_def, groupCohomology.mapIso_hom]
    -- Rewriting with `H2π_comp_map_apply` times out here; the term is given explicitly.
    exact groupCohomology.H2π_comp_map_apply (L.conjugateGalEquiv g).symm.toMonoidHom _ c
  case hcocycle =>
    exact Subtype.ext (funext fun p => (inflCocycle2_mapCocycles₂ L g _ _
      (fun w => (L.conjugateGalEquiv_symm_mk g w).trans (congrArg QuotientGroup.mk
        (Subtype.ext (L.conjugateGroundEquiv_symm_apply_coe g w))))
      (fun x => L.conjugateCoefficientEquiv_apply_coe (unitsFormation K) g x) c p).trans
      (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ p.1 p.2).symm)

end Conjugation

end Inflation

/-! ### The invariant of a layer of the formation of units of a local field -/

section Invariant

variable (K) [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : NormalLayer (AbsoluteGaloisGroup K))

/-- **The invariant of a layer** `V ◁ U` of the formation of units of a nonarchimedean local
field `K`: inflation `NormalLayer.explicitInfl2` into `H²(U, (Kˢ)ˣ)` followed by the local invariant
`subgroupInvMap` of the open subgroup `U`. In field notation it is the invariant
`inv_{E'/E} : H²(Gal(E'/E), E'ˣ) → ℚ/ℤ` of the finite Galois extension `E'/E` that the layer cuts
out. It is injective (`layerInv_injective`) with values killed by the degree
(`degree_nsmul_layerInv`). -/
def layerInv : L.H (unitsFormation K) 2 →+ AddCircle (1 : ℚ) :=
  (subgroupInvMap K L.ground.toSubgroup L.ground.isOpen).toAddMonoidHom.comp
    (L.explicitInfl2 (unitsCoeffEquivUnitsFormation K) (unitsCoeffEquivUnitsFormation_smul K))

/-- The invariant of a layer is the local invariant of the ground subgroup on the inflated
class. -/
theorem layerInv_apply (x : L.H (unitsFormation K) 2) :
    layerInv K L x = subgroupInvMap K L.ground.toSubgroup L.ground.isOpen
      (L.explicitInfl2 (unitsCoeffEquivUnitsFormation K) (unitsCoeffEquivUnitsFormation_smul K)
        x) :=
  (rfl)

/-- **The invariant of a layer is injective.** -/
theorem layerInv_injective : Function.Injective (layerInv K L) :=
  have := subsingleton_H1_top L
  (subgroupInvMap K L.ground.toSubgroup L.ground.isOpen).injective.comp
    (L.explicitInfl2_injective_of_subsingleton _ _)

/-- **The invariant of a layer is killed by its degree**: `[U : V] • inv_{E'/E} x = 0`, so the
invariants of a layer lie in the subgroup of `ℚ/ℤ` of order `[U : V]`. -/
theorem degree_nsmul_layerInv (x : L.H (unitsFormation K) 2) :
    L.degree • layerInv K L x = 0 := by
  rw [layerInv_apply, L.degree_eq_relIndex, ← subgroupInvMap_explicitMap2_subgroupInclusion K
    L.ground.toSubgroup L.top.toSubgroup L.ground.isOpen L.top.isOpen
    (OpenSubgroup.toSubgroup_le.2 L.top_le_ground), NormalLayer.explicitMap2_explicitInfl2_eq_zero,
    map_zero]

/-- **Restriction multiplies the invariant by the relative degree**: for a restriction of a layer
to an intermediate ground field `E''`, `inv_{E'/E''} (res x) = [E'' : E] • inv_{E'/E} x`. -/
@[simp]
theorem layerInv_cohomologyRes {small big : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRestriction small big) (x : big.H (unitsFormation K) 2) :
    layerInv K small (T.cohomologyRes (unitsFormation K) 2 x) =
      T.relativeDegree • layerInv K big x := by
  rw [layerInv_apply, NormalLayer.explicitInfl2_cohomologyRes,
    subgroupInvMap_explicitMap2_subgroupInclusion,
    LayerRestriction.relativeDegree_def, layerInv_apply]

/-- **Inflation preserves the invariant**: for a refinement of a layer to a larger top field,
`inv (infl x) = inv x`. -/
@[simp]
theorem layerInv_cohomologyInfl {old new : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement old new) (x : old.H (unitsFormation K) 2) :
    layerInv K new (T.cohomologyInfl (unitsFormation K) 2 x) = layerInv K old x := by
  rw [layerInv_apply, NormalLayer.explicitInfl2_cohomologyInfl,
    subgroupInvMap_explicitMap2_subgroupInclusion,
    Subgroup.relIndex_eq_one.2 T.same_ground_toSubgroup.le, one_smul, layerInv_apply]

/-- **The invariants of a layer are the subgroup of `ℚ/ℤ` of order its degree**: the range of
`inv_{E'/E}` is the `[E' : E]`-torsion of `ℚ/ℤ`. Together with `layerInv_injective`, this makes
`H²(Gal(E'/E), E'ˣ)` cyclic of order `[E' : E]`. -/
@[simp]
theorem range_layerInv :
    Set.range (layerInv K L) =
      (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) L.degree : Set (AddCircle (1 : ℚ))) := by
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    exact AddSubgroup.torsionBy.nsmul_iff.2 (degree_nsmul_layerInv K L y)
  -- A rational `x` of order dividing `[U : V]` is the invariant of a class of `H²(U, (Kˢ)ˣ)`,
  -- which is inflated from a refinement `V' ◁ U` of the layer.
  obtain ⟨L', T, y, hy⟩ := L.exists_explicitInfl2_eq (unitsCoeffEquivUnitsFormation K)
    (unitsCoeffEquivUnitsFormation_smul K)
    ((subgroupInvMap K L.ground.toSubgroup L.ground.isOpen).symm x)
  have hinv : layerInv K L' y = x := by
    rw [layerInv_apply, hy, subgroupInvMap_explicitMap2_subgroupInclusion K _ _ L.ground.isOpen,
      Subgroup.relIndex_eq_one.2 T.same_ground_toSubgroup.le, one_smul, AddEquiv.apply_symm_apply]
  -- Restricted to the layer of the kernel `V/V'`, the class has invariant `[U : V] • x = 0`.
  have hres : (L'.subgroupRestriction T.galHom.ker).cohomologyRes (unitsFormation K) 2 y = 0 := by
    refine layerInv_injective K _ ?_
    rw [layerInv_cohomologyRes, map_zero, hinv, L'.relativeDegree_subgroupRestriction,
      Subgroup.index_ker, MonoidHom.range_eq_top.2 T.galHom_surjective, Subgroup.card_top,
      ← NormalLayer.degree_eq_natCard_gal]
    exact AddSubgroup.torsionBy.nsmul_iff.1 hx
  -- By the inflation-restriction sequence and Hilbert 90, the class is inflated from `V ◁ U`.
  obtain ⟨z, hz⟩ : y ∈ LinearMap.range (T.cohomologyInfl (unitsFormation K) 2).hom :=
    (T.range_cohomologyInfl_eq_ker_cohomologyRes (unitsFormation K) 1 fun i hi => by
      obtain rfl : i = 0 := Nat.lt_one_iff.1 hi
      exact subsingleton_h1_unitsFormation _).ge hres
  exact ⟨z, (layerInv_cohomologyInfl K T z).symm.trans (congrArg (layerInv K L') hz |>.trans hinv)⟩

/-- **Conjugation preserves the invariant**: for `g : G_K`, the conjugate class in the conjugate
layer `gV ◁ gU` has the same invariant, `inv_{gE'/gE} (g_* x) = inv_{E'/E} x`. -/
@[simp]
theorem layerInv_conjugateCohomologyIso (g : AbsoluteGaloisGroup K)
    (x : L.H (unitsFormation K) 2) :
    layerInv K (L.conjugate g) ((L.conjugateCohomologyIso (unitsFormation K) g 2).hom x) =
      layerInv K L x := by
  rw [layerInv_apply, explicitInfl2_conjugateCohomologyIso,
    subgroupInvMap_explicitMap2_of_conj K L.ground.toSubgroup (L.conjugate g).ground.toSubgroup
      L.ground.isOpen (L.conjugate g).ground.isOpen g _ (conjugateGroundHom_apply_coe L g)
      (DistribSMul.toAddMonoidHom (UnitsCoeff K) g) (DistribSMul.toAddMonoidHom_apply _ g)
      (toSubgroup_ground_conjugate L g),
    layerInv_apply]

end Invariant

end TauCeti.ClassFieldTheory
