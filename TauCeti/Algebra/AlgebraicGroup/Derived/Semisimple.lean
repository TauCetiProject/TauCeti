/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Reductive
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Derived.FreeBaseChange
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Central
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Reductive.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Normal
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Reductive
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed

/-!
# The derived subgroup of a reductive group is semisimple

Over any field and in every characteristic, the scheme-theoretic derived subgroup `[G, G]` of a
reductive affine group `G` is semisimple.

Over an algebraically closed field the argument is the classical one. The solvable radical
`R(G)` is a central torus, hence a central closed diagonalizable subgroup, so the determinant
argument of `BialgHom.moduleFinite_quotient_sup_derivedDefiningIdeal` shows that
`R(G) ∩ [G, G]` is finite. The solvable radical of the normal subgroup `[G, G]` lies in
`R(G) ∩ [G, G]`, and a finite connected smooth group is trivial. Over a general field,
formation of the derived subgroup commutes with extension to an algebraic closure, where the
geometric definition of semisimplicity is tested.

## Main declarations

* `TauCeti.reductiveCommHopfAlgProperty.moduleFinite_quotient_solvableRadical_sup_derived`:
  over an algebraically closed field, the solvable radical of a reductive group meets its derived
  subgroup in a finite subgroup scheme.
* `TauCeti.reductiveCommHopfAlgProperty.semisimple_derived`: the derived subgroup of a reductive
  group is semisimple.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §14.2.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 21.
-/

public section

open CategoryTheory

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

noncomputable section

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **The solvable radical of a reductive group meets the derived subgroup finitely.** Over an
algebraically closed field, in every characteristic, the coordinate algebra
`H ⧸ (R(H) ⊔ [H, H])` of the intersection of the solvable radical with the derived subgroup is
finite-dimensional. -/
theorem moduleFinite_quotient_solvableRadical_sup_derived [IsAlgClosed k]
    (hH : reductiveCommHopfAlgProperty k H) :
    Module.Finite k (H ⧸ (FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H ⊔
      CommHopfAlgCat.derivedDefiningIdeal H.obj).toIdeal) := by
  let I := FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H
  -- Over an algebraically closed field, the radical torus is a split torus `D(X)`.
  obtain ⟨n, ⟨e⟩⟩ := (splitTorusCommHopfAlgProperty_iff k _).mp
    (torusCommHopfAlgProperty.split k _ hH.torus_solvableRadical)
  let f : H.obj ⟶ (DiagonalizableGroup.coordinateRing k
      (SplitTorus.characterGroup (ULift.{u} (Fin n)))).obj :=
    CommHopfAlgCat.mkQuotient H.obj I ≫ e.inv.hom
  let π : H →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) := f.hom
  have hπ : Function.Surjective π :=
    (ConcreteCategory.bijective_of_isIso e.inv.hom).2.comp
      (CommHopfAlgCat.mkQuotient_surjective H.obj I)
  have hker : HopfIdeal.kerOfSurjective π hπ = I := by
    apply HopfIdeal.ext
    intro x
    rw [HopfIdeal.mem_kerOfSurjective, ← CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I x]
    simp only [π, f, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
      map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.inv.hom).1]
  have hfinite := BialgHom.moduleFinite_quotient_sup_derivedDefiningIdeal π hπ
    (hker ▸ hH.isCentral_solvableRadicalDefiningIdeal)
  rwa [hker] at hfinite

/-- **The derived subgroup of a reductive group is semisimple**, in every characteristic. The
ground field need not be algebraically closed, and the group need not split. -/
theorem semisimple_derived (hH : reductiveCommHopfAlgProperty k H) :
    semisimpleCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H (CommHopfAlgCat.derivedDefiningIdeal H.obj)) := by
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation]
  refine ⟨hH.derived.smooth, hH.derived.geometricallyConnected, ?_⟩
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let J := CommHopfAlgCat.baseChangeHopfIdeal (K := K) (CommHopfAlgCat.derivedDefiningIdeal H.obj)
  let e : FiniteTypeCommHopfAlgCat.baseChange (K := K)
      (FiniteTypeCommHopfAlgCat.quotient H (CommHopfAlgCat.derivedDefiningIdeal H.obj)) ≅
        FiniteTypeCommHopfAlgCat.quotient G J :=
    ObjectProperty.isoMk _ (CommHopfAlgCat.quotientBaseChangeIso (K := K)
      (CommHopfAlgCat.derivedDefiningIdeal H.obj)).symm
  have hG := hH.algebraicClosureBaseChange
  let _ : Algebra.Smooth K G := hG.smooth
  let _ : IsReduced G := isReduced_of_smooth K G
  -- The base-changed derived subgroup is the derived subgroup of the base change.
  have hJ : J = CommHopfAlgCat.derivedDefiningIdeal (R := K) G.obj :=
    CommHopfAlgCat.baseChangeHopfIdeal_derivedDefiningIdeal H.obj
  let _ : Module.Finite K
      (G ⧸ (FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal G ⊔ J).toIdeal) := by
    rw [hJ]
    exact hG.moduleFinite_quotient_solvableRadical_sup_derived
  have hN :=
    FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_quotient_eq_augmentation_of_moduleFinite
      G (CommHopfAlgCat.isNormal_baseChangeHopfIdeal
        (CommHopfAlgCat.isNormal_derivedDefiningIdeal H.obj))
  rw [← FiniteTypeCommHopfAlgCat.comapOfSurjective_solvableRadicalDefiningIdeal e, hN]
  exact HopfIdeal.comapOfSurjective_augmentation _ _

end

end TauCeti.reductiveCommHopfAlgProperty
