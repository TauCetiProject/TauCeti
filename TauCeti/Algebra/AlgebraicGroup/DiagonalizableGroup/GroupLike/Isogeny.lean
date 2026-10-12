/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Isogeny
import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.GroupLikeEvaluation

/-!
# Central isogenies between diagonalizable coordinate algebras

For diagonalizable coordinate Hopf algebras over a domain with torsion-free carriers, a morphism
is a central isogeny precisely when its map on group-like elements is injective with finite
cokernel.
The group-like elements give the intrinsic character groups; no presentation as a group
algebra needs to be chosen. This form applies to geometric fibres of groups of multiplicative
type, where the defining character group is available only after scalar extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9.
-/

public section

open CategoryTheory

namespace TauCeti.DiagonalizableGroup

universe u

variable {k : Type u} [CommRing k] [IsDomain k]
variable {H K : _root_.CommHopfAlgCat.{u} k}

variable [Module.IsTorsionFree k H] [Module.IsTorsionFree k K]

/-- A morphism between torsion-free diagonalizable coordinate algebras over a domain is a
central isogeny exactly when its intrinsic character map is injective with finite cokernel. -/
@[simp] theorem isCentralIsogeny_iff_groupLikeMap_injective_and_finite_quotient
    (hH : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤)
    (hK : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := K))) = ⊤)
    (f : H ⟶ K) :
    CommHopfAlgCat.IsCentralIsogeny f ↔
      Function.Injective (TauCeti.GroupLike.map f.hom) ∧
        Finite (_root_.GroupLike k K ⧸ (TauCeti.GroupLike.map f.hom).range) := by
  let eH := TauCeti.CommHopfAlgCat.evaluationIso hH
  let eK := TauCeti.CommHopfAlgCat.evaluationIso hK
  let p := TauCeti.GroupLike.map f.hom
  let g := _root_.CommHopfAlgCat.ofHom (_root_.MonoidAlgebra.mapDomainBialgHom k p)
  have hcomm : eH.hom ≫ f = g ≫ eK.hom :=
    TauCeti.CommHopfAlgCat.evaluationIso_naturality hH hK f
  have hiff : CommHopfAlgCat.IsCentralIsogeny f ↔ CommHopfAlgCat.IsCentralIsogeny g := by
    rw [CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map,
      CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map]
    let F := AlgebraicGeometry.hopfSpec (CommRingCat.of k)
    have hc : F.map f.op ≫ F.map eH.hom.op = F.map eK.hom.op ≫ F.map g.op := by
      simpa only [← F.map_comp, ← op_comp] using congrArg (fun q => F.map q.op) hcomm
    have h₁ := MorphismProperty.cancel_right_of_respectsIso
      (GroupScheme.centralIsogenies k) (F.map f.op) (F.map eH.hom.op)
    have h₂ := MorphismProperty.cancel_left_of_respectsIso
      (GroupScheme.centralIsogenies k) (F.map eK.hom.op) (F.map g.op)
    exact h₁.symm.trans (hc ▸ h₂)
  exact hiff.trans (isCentralIsogeny_mapDomainBialgHom_iff k p)

end TauCeti.DiagonalizableGroup
