/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.GaloisModule
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm
import TauCeti.NumberTheory.ClassFieldTheory.ClassField
import TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.HerbrandQuotient
import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer

/-!
# The first fundamental inequality

Let `L/K` be a cyclic extension of number fields. The **first fundamental inequality** says that
the idele-class norm group `N_{L/K}(C_L)` has index at least `[L : K]` in `C_K`
(`finrank_le_index_range_ideleClassNormMap`). In particular, if every idele class of `K` is a norm
from `L`, then `L = K` (`finrank_eq_one_of_surjective_ideleClassNormMap`). This is the form in
which the inequality is used to show that the Frobenius elements of an abelian extension generate
its Galois group, and that an `S`-unit which is a local `n`-th power at the right places is a
global `n`-th power, both steps of the proof of the second fundamental inequality.

The inequality holds on every cyclic layer `V ◁ U` of the idele-class formation
`globalFormation K`, whose ground subgroup `U` is any open subgroup of `G_K`: its norm quotient has
at least `[U : V]` elements (`degree_le_natCard_normQuotient_of_isCyclic`). Let `F` and `L` be the
fixed fields of `U` and `V`. Restriction to `L` identifies `U ⧸ V` with `Gal(L/F)`
(`NormalLayer.galEquivOfFixedField`), so `L/F` is a cyclic extension of number fields of degree
`[U : V]`, and the coefficient module of the layer is `C_L` as a `Gal(L/F)`-module
(`NormalLayer.herbrandQuotient_rep_globalFormation`). Its Herbrand quotient is therefore
`h(C_L) = [L : F] = [U : V]` (`herbrandQuotient_ideleClassRep_eq_finrank`,
`herbrandQuotient_rep_globalFormation_eq_degree`). For a cyclic layer, a Herbrand quotient equal to
the degree forces the norm quotient to have at least that many elements
(`NormalLayer.degree_le_natCard_normQuotient_of_herbrandQuotient_eq`): the norm quotient is the
zeroth Tate cohomology, whose order is `h` times the order of `H¹`. The ground subgroups of the
layers of prime degree inside a given layer are proper open subgroups of `G_K` in general, which is
why the inequality is stated for every layer rather than only for the layers `V ◁ G_K`. For the
layer of a cyclic extension `L/K` the norm quotient is `C_K / N_{L/K}(C_L)`
(`globalLayerNormQuotientEquiv`).

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_rep_globalFormation_eq_degree`: a cyclic layer of the
  idele-class formation has Herbrand quotient its degree.
* `TauCeti.ClassFieldTheory.degree_le_natCard_normQuotient_of_isCyclic`: the first inequality on a
  cyclic layer of the idele-class formation.
* `TauCeti.ClassFieldTheory.finrank_le_index_range_ideleClassNormMap`: for cyclic `L/K`,
  `[L : K] ≤ [C_K : N_{L/K}(C_L)]`.
* `TauCeti.ClassFieldTheory.finrank_eq_one_of_surjective_ideleClassNormMap`: a cyclic extension
  from which every idele class is a norm is trivial.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §4, Theorem 4.3 and Corollary 4.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §4.
-/

public section

noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- **A cyclic layer of the idele-class formation has Herbrand quotient its degree**: if the Galois
group `U ⧸ V` of a layer `V ◁ U` of `globalFormation K` is cyclic, then its coefficient module has
Herbrand quotient `[U : V]`. With `F` and `L` the fixed fields of `U` and `V`, that module is the
idele class group `C_L` as a `Gal(L/F)`-module, and `L/F` is a cyclic extension of number fields of
degree `[U : V]`. -/
theorem herbrandQuotient_rep_globalFormation_eq_degree (Lay : NormalLayer (AbsoluteGaloisGroup K))
    [IsCyclic Lay.Gal] :
    TateCohomology.herbrandQuotient (Lay.rep (globalFormation K)) = Lay.degree := by
  have hle : fixedField Lay.ground.toSubgroup ≤ fixedField Lay.top.toSubgroup :=
    fixedField_le (OpenSubgroup.toSubgroup_le.2 Lay.top_le_ground)
  have : NumberField (fixedField Lay.ground.toSubgroup) := .of_module_finite K _
  have : NumberField (fixedField Lay.top.toSubgroup) := .of_module_finite K _
  let := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower (fixedField Lay.ground.toSubgroup) (fixedField Lay.top.toSubgroup)
      (SeparableClosure K) := .of_algebraMap_eq fun _ ↦ rfl
  have := Lay.isGalois_of_fixedField rfl rfl
  let e := Lay.galEquivOfFixedField rfl rfl
  have : IsCyclic Gal(fixedField Lay.top.toSubgroup/fixedField Lay.ground.toSubgroup) :=
    e.isCyclic.1 ‹_›
  rw [Lay.herbrandQuotient_rep_globalFormation rfl (Lay.coe_galEquivOfFixedField_mk_apply rfl rfl),
    herbrandQuotient_ideleClassRep_eq_finrank, NormalLayer.degree_eq_natCard_gal,
    Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]

/-- **The first fundamental inequality on a layer of the idele-class formation**: if the Galois
group `U ⧸ V` of a layer `V ◁ U` of `globalFormation K` is cyclic, its norm quotient has at least
`[U : V]` elements. With `F` and `L` the fixed fields of `U` and `V`, the norm quotient is
`C_F / N_{L/F}(C_L)` (`NormalLayer.ideleClassNormQuotientEquiv`). -/
theorem degree_le_natCard_normQuotient_of_isCyclic (Lay : NormalLayer (AbsoluteGaloisGroup K))
    [IsCyclic Lay.Gal] :
    Lay.degree ≤ Nat.card (Lay.NormQuotient (globalFormation K)) :=
  Lay.degree_le_natCard_normQuotient_of_herbrandQuotient_eq _
    (herbrandQuotient_rep_globalFormation_eq_degree Lay)

variable (K) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsCyclic Gal(L/K)]

/-- **The first fundamental inequality**: for a cyclic extension `L/K` of number fields, the
idele-class norm group `N_{L/K}(C_L)` has index at least `[L : K]` in `C_K`. -/
theorem finrank_le_index_range_ideleClassNormMap :
    Module.finrank K L ≤ (GlobalNumberFields.ideleClassNormMap K L).range.index := by
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let e := layerGalEquiv ι
  have : IsCyclic (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal :=
    e.isCyclic.2 ‹_›
  calc Module.finrank K L
      = (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).degree := by
        rw [NormalLayer.degree_eq_natCard_gal, Nat.card_congr e.toEquiv,
          IsGalois.card_aut_eq_finrank]
    _ ≤ Nat.card ((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).NormQuotient
          (globalFormation K)) :=
        degree_le_natCard_normQuotient_of_isCyclic _
    -- The norm quotient of the layer of `L` is `C_K / N_{L/K}(C_L)`, written additively.
    _ = (GlobalNumberFields.ideleClassNormMap K L).range.index := by
        rw [Subgroup.index_eq_card]
        exact (Nat.card_congr (globalLayerNormQuotientEquiv K L).toEquiv).symm.trans
          (Nat.card_congr Additive.ofMul.symm)

/-- **A cyclic extension from which every idele class is a norm is trivial**: if the norm map
`N_{L/K} : C_L → C_K` of a cyclic extension of number fields is surjective, then `[L : K] = 1`. -/
theorem finrank_eq_one_of_surjective_ideleClassNormMap
    (h : Function.Surjective (GlobalNumberFields.ideleClassNormMap K L)) :
    Module.finrank K L = 1 := by
  have := finrank_le_index_range_ideleClassNormMap K L
  rw [MonoidHom.range_eq_top_of_surjective _ h, Subgroup.index_top] at this
  exact le_antisymm this Module.finrank_pos

end TauCeti.ClassFieldTheory
