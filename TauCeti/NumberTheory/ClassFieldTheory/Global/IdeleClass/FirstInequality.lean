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

The proof runs through the idele-class formation `globalFormation K`. For an open normal subgroup
`V` of `G_K` with class field `E`, the coefficient module of the layer `V ◁ G_K` is `C_E` as a
`Gal(E/K)`-module (`NormalLayer.herbrandQuotient_rep_globalFormation`), so its Herbrand quotient is
`h(C_E) = [E : K]` when `E/K` is cyclic (`herbrandQuotient_ideleClassRep_eq_finrank`). That is the
degree of the layer (`herbrandQuotient_rep_globalFormation_ofOpenNormal_eq_degree`). For a cyclic
layer, a Herbrand quotient equal to the degree forces the norm quotient to have at least that many
elements (`NormalLayer.degree_le_natCard_normQuotient_of_herbrandQuotient_eq`): the norm quotient
is `Ĥ⁰`, whose order is `h` times the order of `H¹`. This gives the inequality on the layer
(`degree_le_natCard_normQuotient_ofOpenNormal_of_isCyclic`), and the layer of `L/K` has norm
quotient `C_K / N_{L/K}(C_L)` (`globalLayerNormQuotientEquiv`).

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_rep_globalFormation_ofOpenNormal_eq_degree`: a cyclic
  layer `V ◁ G_K` of the idele-class formation has Herbrand quotient its degree.
* `TauCeti.ClassFieldTheory.degree_le_natCard_normQuotient_ofOpenNormal_of_isCyclic`: the first
  inequality on a cyclic layer `V ◁ G_K` of the idele-class formation.
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
group `G_K ⧸ V` of the layer `V ◁ G_K` is cyclic, then its coefficient module, the idele class group
of the class field of `V`, has Herbrand quotient `[G_K : V]`. -/
theorem herbrandQuotient_rep_globalFormation_ofOpenNormal_eq_degree
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    [IsCyclic (NormalLayer.ofOpenNormal V).Gal] :
    TateCohomology.herbrandQuotient ((NormalLayer.ofOpenNormal V).rep (globalFormation K)) =
      (NormalLayer.ofOpenNormal V).degree := by
  have hE : fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = classField K V := by
    rw [NormalLayer.top_ofOpenNormal, ← InfiniteGalois.fixedField_fixingSubgroup (classField K V),
      fixingSubgroup_classField]
  let e := (galClassFieldEquiv V).symm
  have he : ∀ (u : (NormalLayer.ofOpenNormal V).ground) (x : classField K V),
      ((e u x : classField K V) : SeparableClosure K) = (u : AbsoluteGaloisGroup K) x := by
    intro u x
    simp only [e, galClassFieldEquiv_symm_mk]
    exact AlgEquiv.restrictNormal_commutes _ _ x
  have : NumberField (classField K V) := .of_module_finite K _
  have : IsCyclic Gal(classField K V/K) := e.isCyclic.1 ‹_›
  rw [(NormalLayer.ofOpenNormal V).herbrandQuotient_rep_globalFormation hE he,
    herbrandQuotient_ideleClassRep_eq_finrank, NormalLayer.degree_eq_natCard_gal,
    Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]

/-- **The first fundamental inequality on a layer of the idele-class formation**: if the Galois
group `G_K ⧸ V` of the layer `V ◁ G_K` is cyclic, its norm quotient has at least `[G_K : V]`
elements. -/
theorem degree_le_natCard_normQuotient_ofOpenNormal_of_isCyclic
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    [IsCyclic (NormalLayer.ofOpenNormal V).Gal] :
    (NormalLayer.ofOpenNormal V).degree ≤
      Nat.card ((NormalLayer.ofOpenNormal V).NormQuotient (globalFormation K)) :=
  (NormalLayer.ofOpenNormal V).degree_le_natCard_normQuotient_of_herbrandQuotient_eq _
    (herbrandQuotient_rep_globalFormation_ofOpenNormal_eq_degree V)

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
        degree_le_natCard_normQuotient_ofOpenNormal_of_isCyclic _
    -- The norm quotient of the layer of `L` is `C_K / N_{L/K}(C_L)`, written additively.
    _ = (GlobalNumberFields.ideleClassNormMap K L).range.index :=
        ((Nat.card_congr (globalLayerNormQuotientEquiv K L).toEquiv).symm.trans
          (Nat.card_congr Additive.ofMul.symm))

/-- **A cyclic extension from which every idele class is a norm is trivial**: if the norm map
`N_{L/K} : C_L → C_K` of a cyclic extension of number fields is surjective, then `[L : K] = 1`. -/
theorem finrank_eq_one_of_surjective_ideleClassNormMap
    (h : Function.Surjective (GlobalNumberFields.ideleClassNormMap K L)) :
    Module.finrank K L = 1 := by
  have := finrank_le_index_range_ideleClassNormMap K L
  rw [MonoidHom.range_eq_top_of_surjective _ h, Subgroup.index_top] at this
  exact le_antisymm this Module.finrank_pos

end TauCeti.ClassFieldTheory
