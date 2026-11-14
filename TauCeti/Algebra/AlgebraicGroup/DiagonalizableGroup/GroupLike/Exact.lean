/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Exact
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.GroupLikeEvaluation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Exact.Isomorphism

/-!
# Exactness in intrinsic character coordinates

A sequence of diagonalizable affine groups is short exact precisely when its intrinsic
character sequence is short exact in the opposite direction. The characters are the
group-like elements of the coordinate Hopf algebras. Evaluation identifies these algebras
with their group algebras, and its naturality transfers the explicit group-algebra theorem.

The statement requires no choice of presentations, finite generation, or smoothness.
In particular, it retains infinitesimal kernels such as `μ_p` in characteristic `p`.
It applies over a domain when the coordinate algebras are torsion-free; over a field the
torsion-free hypotheses hold automatically. This is the intrinsic calculation needed
on the geometric fibre of a sequence of groups of multiplicative type.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9.
-/

public section

open CategoryTheory

namespace TauCeti.DiagonalizableGroup

universe u

variable {k : Type u} [CommRing k] [IsDomain k]
variable {Q G N : _root_.CommHopfAlgCat.{u} k}
variable [Module.IsTorsionFree k Q] [Module.IsTorsionFree k G] [Module.IsTorsionFree k N]

/-- A sequence of diagonalizable affine groups is short exact exactly when the first
intrinsic character map is injective, the second is surjective, and image equals kernel. -/
@[simp]
theorem isShortExact_iff_groupLikeMap
    (hQ : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := Q))) = ⊤)
    (hG : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := G))) = ⊤)
    (hN : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := N))) = ⊤)
    (p : Q ⟶ G) (i : G ⟶ N) :
    CommHopfAlgCat.IsShortExact p i ↔
      Function.Injective (TauCeti.GroupLike.map p.hom) ∧
        Function.Surjective (TauCeti.GroupLike.map i.hom) ∧
          (TauCeti.GroupLike.map p.hom).range = (TauCeti.GroupLike.map i.hom).ker := by
  let eQ := CommHopfAlgCat.evaluationIso hQ
  let eG := CommHopfAlgCat.evaluationIso hG
  let eN := CommHopfAlgCat.evaluationIso hN
  have hp : eQ.hom ≫ p ≫ eG.inv =
      CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k
        (TauCeti.GroupLike.map p.hom)) := by
    simpa only [eQ, eG, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ eG.inv) (CommHopfAlgCat.evaluationIso_naturality hQ hG p)
  have hi : eG.hom ≫ i ≫ eN.inv =
      CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k
        (TauCeti.GroupLike.map i.hom)) := by
    simpa only [eG, eN, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ eN.inv) (CommHopfAlgCat.evaluationIso_naturality hG hN i)
  have hiff := CommHopfAlgCat.isShortExact_iso_iff (p := p) (i := i)
    eQ.symm eG.symm eN.symm
  simp only [Iso.symm_inv, Iso.symm_hom, hp, hi] at hiff
  exact hiff.symm.trans (isShortExact_mapDomainBialgHom_iff k _ _)

end TauCeti.DiagonalizableGroup
