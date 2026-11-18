/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Exact
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Bialgebra.GroupLike.Map
import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# Exactness in intrinsic character coordinates

A sequence of diagonalizable affine groups is short exact precisely when its intrinsic
character sequence is short exact in the opposite direction. The characters are the
group-like elements of the coordinate Hopf algebras. Evaluation identifies these algebras
with their group algebras, and its naturality transfers the explicit group-algebra theorem.

The statement requires no choice of presentations, finite generation, or smoothness.
In particular, it retains infinitesimal kernels such as `μ_p` in characteristic `p`.
The general form applies over any commutative ring when the group-like elements of each
coordinate algebra are linearly independent and span it. Over a domain linear independence
holds when the coordinate algebras are torsion-free, and over a field the torsion-free
hypotheses hold automatically. This is the intrinsic calculation needed on the geometric
fibre of a sequence of groups of multiplicative type.

## Main declarations

* `TauCeti.DiagonalizableGroup.isShortExact_iff_mapGroupLike_of_linearIndependent`: the
  criterion over a commutative ring, for linearly independent spanning group-like elements.
* `TauCeti.DiagonalizableGroup.isShortExact_iff_mapGroupLike`: the criterion over a domain,
  for torsion-free coordinate algebras spanned by their group-like elements.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9.
-/

public section

open CategoryTheory

namespace TauCeti.DiagonalizableGroup

universe u v

variable {R : Type u} [CommRing R] {Q G N : _root_.CommHopfAlgCat.{v} R}

/-- Over a commutative ring, let `p : Q ⟶ G` and `i : G ⟶ N` be morphisms of commutative Hopf
algebras whose group-like elements are linearly independent and span. They form a short exact
sequence of affine groups exactly when `p.hom.mapGroupLike` is injective,
`i.hom.mapGroupLike` is surjective, and the range of `p.hom.mapGroupLike` is the kernel of
`i.hom.mapGroupLike`. -/
theorem isShortExact_iff_mapGroupLike_of_linearIndependent
    (hQl : LinearIndependent R (_root_.GroupLike.val (R := R) (A := Q)))
    (hGl : LinearIndependent R (_root_.GroupLike.val (R := R) (A := G)))
    (hNl : LinearIndependent R (_root_.GroupLike.val (R := R) (A := N)))
    (hQ : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := Q))) = ⊤)
    (hG : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := G))) = ⊤)
    (hN : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := N))) = ⊤)
    (p : Q ⟶ G) (i : G ⟶ N) :
    CommHopfAlgCat.IsShortExact p i ↔
      Function.Injective p.hom.mapGroupLike ∧
        Function.Surjective i.hom.mapGroupLike ∧
          p.hom.mapGroupLike.range = i.hom.mapGroupLike.ker := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · -- Over the zero ring every coordinate algebra is zero, so both sides hold trivially.
    have (H : _root_.CommHopfAlgCat.{v} R) : Subsingleton H := Module.subsingleton R H
    have (H : _root_.CommHopfAlgCat.{v} R) : Subsingleton (_root_.GroupLike R H) :=
      _root_.GroupLike.val_injective.subsingleton
    exact iff_of_true
      ⟨.of_bijective ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩,
        Function.surjective_to_subsingleton _, Subsingleton.elim _ _⟩
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _,
        Subsingleton.elim _ _⟩
  · have hnat {H K : _root_.CommHopfAlgCat.{v} R} (f : H ⟶ K) :
        f.hom.comp (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)) =
          (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := K)).comp
            (MonoidAlgebra.mapDomainBialgHom R f.hom.mapGroupLike) := by
      refine MonoidAlgebra.bialgHom_ext (fun x ↦ ?_) (AlgHom.ext fun r ↦ ?_)
      · simp [BialgHom.val_mapGroupLike]
      · simp [MonoidAlgebra.singleOneAlgHom_apply]
    rw [← isShortExact_mapDomainBialgHom_iff R]
    refine (CommHopfAlgCat.isShortExact_iff_of_bialgEquiv
      (GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop R Q hQl hQ)
      (GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop R G hGl hG)
      (GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop R N hNl hN) ?_ ?_).symm
    · simpa only [GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop_toBialgHom,
        _root_.CommHopfAlgCat.hom_ofHom] using hnat p
    · simpa only [GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop_toBialgHom,
        _root_.CommHopfAlgCat.hom_ofHom] using hnat i

/-- Over a domain, let `p : Q ⟶ G` and `i : G ⟶ N` be morphisms of torsion-free commutative
Hopf algebras spanned by their group-like elements. They form a short exact sequence of
affine groups exactly when `p.hom.mapGroupLike` is injective, `i.hom.mapGroupLike` is
surjective, and the range of `p.hom.mapGroupLike` is the kernel of `i.hom.mapGroupLike`. -/
theorem isShortExact_iff_mapGroupLike [IsDomain R]
    [Module.IsTorsionFree R Q] [Module.IsTorsionFree R G] [Module.IsTorsionFree R N]
    (hQ : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := Q))) = ⊤)
    (hG : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := G))) = ⊤)
    (hN : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := N))) = ⊤)
    (p : Q ⟶ G) (i : G ⟶ N) :
    CommHopfAlgCat.IsShortExact p i ↔
      Function.Injective p.hom.mapGroupLike ∧
        Function.Surjective i.hom.mapGroupLike ∧
          p.hom.mapGroupLike.range = i.hom.mapGroupLike.ker :=
  isShortExact_iff_mapGroupLike_of_linearIndependent linearIndep_groupLikeVal
    linearIndep_groupLikeVal linearIndep_groupLikeVal hQ hG hN p i

end TauCeti.DiagonalizableGroup
