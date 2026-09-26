/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Isogeny
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Isomorphism
import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import TauCeti.Algebra.Bialgebra.GroupLike.Map

/-!
# Central isogenies between diagonalizable coordinate algebras

For arbitrary diagonalizable coordinate Hopf algebras over a field, a morphism is a central
isogeny precisely when its map on group-like elements is injective with finite cokernel.
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

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{u} k}

private noncomputable def evaluationIso (H : _root_.CommHopfAlgCat.{u} k)
    (hH : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤) :
    _root_.CommHopfAlgCat.of k (_root_.MonoidAlgebra k (_root_.GroupLike k H)) ≅ H :=
  _root_.CommHopfAlgCat.isoMk
    (TauCeti.GroupLike.evaluationBialgEquiv k H hH)

private theorem evaluationIso_hom_single
    (hH : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤)
    (x : _root_.GroupLike k H) :
    (evaluationIso H hH).hom.hom (_root_.MonoidAlgebra.single x 1) = x.val := by
  simp [evaluationIso, TauCeti.GroupLike.evaluationBialgHom_single]

private theorem evaluationIso_naturality
    (hH : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤)
    (hK : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := K))) = ⊤)
    (f : H ⟶ K) :
    (evaluationIso H hH).hom ≫ f =
      _root_.CommHopfAlgCat.ofHom
        (_root_.MonoidAlgebra.mapDomainBialgHom k (TauCeti.GroupLike.map f.hom)) ≫
          (evaluationIso K hK).hom := by
  apply _root_.CommHopfAlgCat.hom_ext
  apply _root_.MonoidAlgebra.bialgHom_ext
  · intro x
    simp only [_root_.CommHopfAlgCat.hom_comp, _root_.BialgHom.comp_apply,
      _root_.CommHopfAlgCat.hom_ofHom, _root_.MonoidAlgebra.mapDomainBialgHom_single]
    rw [evaluationIso_hom_single (H := H) hH x,
      evaluationIso_hom_single (H := K) hK (TauCeti.GroupLike.map f.hom x)]
    exact (TauCeti.GroupLike.val_map f.hom x).symm
  · apply AlgHom.ext
    intro r
    simp [evaluationIso, MonoidAlgebra.singleOneAlgHom_apply]

/-- A morphism between diagonalizable coordinate algebras over a field is a central isogeny
exactly when its intrinsic character map is injective with finite cokernel. -/
@[simp] theorem isCentralIsogeny_iff_groupLikeMap_injective_finite_quotient
    (hH : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤)
    (hK : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := K))) = ⊤)
    (f : H ⟶ K) :
    CommHopfAlgCat.IsCentralIsogeny f ↔
      Function.Injective (TauCeti.GroupLike.map f.hom) ∧
        Finite (_root_.GroupLike k K ⧸ (TauCeti.GroupLike.map f.hom).range) := by
  let eH := evaluationIso H hH
  let eK := evaluationIso K hK
  let p := TauCeti.GroupLike.map f.hom
  let g := _root_.CommHopfAlgCat.ofHom (_root_.MonoidAlgebra.mapDomainBialgHom k p)
  have hcomm : eH.hom ≫ f = g ≫ eK.hom := evaluationIso_naturality hH hK f
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
