/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterKernel
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.RingTheory.TensorProduct.Reduced
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Commutative
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
import TauCeti.Algebra.AlgebraicGroup.Reductive.Solvable
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Character
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Solvable.FaithfullyFlat
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Character
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple

/-!
# The unipotent radical of a connected solvable group

Let `G` be a reduced connected affine group of finite type over an algebraically closed field
`k`, whose group of rational points is solvable. This file proves the structure theorem for the
unipotent part of `G`:

* the affine quotient `G ⧸ R_u(G)` of `G` by its unipotent radical is a torus;
* a rational point of `G` is unipotent exactly when it lies in `R_u(G)`, so the unipotent
  rational points of `G` form the rational points of a smooth connected normal closed subgroup;
* `R_u(G)` is the common kernel of the characters of `G`, scheme-theoretically.

The quotient `G ⧸ R_u(G)` is reductive
(`TauCeti.FiniteTypeCommHopfAlgCat.reductive_coinvariants_unipotentRadical`) and solvable, so it
is a torus by `TauCeti.reductiveCommHopfAlgProperty.torus_of_geometricallySolvable`. A unipotent
point of `G` maps to a unipotent point of this torus, which is also semisimple and hence trivial,
so it lies in the kernel `R_u(G)` of the quotient map. Conversely, points of the smooth unipotent
group `R_u(G)` are unipotent.

Over any field, the characters of `G` are trivial on `R_u(G)`
(`TauCeti.FiniteTypeCommHopfAlgCat.characterKernelIdeal_le_unipotentRadicalDefiningIdeal`). In
the other direction, the coordinate ring of the torus `G ⧸ R_u(G)` is spanned by its characters,
which are characters of `G`; hence every point on which all characters of `G` are trivial is
killed by the quotient map, over every commutative value algebra. This gives the equality of Hopf
ideals, without a reducedness assumption on the common kernel of characters.

For commutative `G` see
`TauCeti.HopfAlgebra.Point.mem_quotientPointsSubgroup_unipotentRadical_iff`. The weaker statement
that the common kernel of characters has only unipotent points is
`TauCeti.CommHopfAlgCat.geometricallyUnipotentPointsCommHopfAlgProperty_characterKernelIdeal`.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical`: `G ⧸ R_u(G)` is a
  torus.
* `TauCeti.FiniteTypeCommHopfAlgCat.groupLikeSpannedProperty_coinvariants_unipotentRadical`:
  `G ⧸ R_u(G)` is spanned by its characters.
* `TauCeti.FiniteTypeCommHopfAlgCat.mem_quotientPointsSubgroup_unipotentRadical_iff`: a rational
  point lies in `R_u(G)` exactly when it is unipotent.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_characterKernelIdeal`:
  `R_u(G)` is the common kernel of the characters of `G`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 10.6.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), Theorem 6.3.5.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Theorem 19.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k]
variable (G : FiniteTypeCommHopfAlgCat.{u, u} k)
variable [IsAlgClosed k]
variable [IsReduced G] [ConnectedSpace (PrimeSpectrum G)]
variable [Group.IsSolvable (WithConv (G →ₐ[k] k))]

/-- **The quotient of a connected solvable group by its unipotent radical is a torus**, over an
algebraically closed field and in every characteristic. -/
theorem torus_coinvariants_unipotentRadical :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    torusCommHopfAlgProperty k Q := by
  intro hR Q
  let _ : Algebra.Smooth k G := (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k G.obj)
  have hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k G.obj).mpr inferInstance
  -- Rational points and algebraic-closure points agree, since `k` is algebraically closed.
  let e : k ≃ₐ[k] AlgebraicClosure k :=
    AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff k G.obj).mpr
      (Group.isSolvable_of_isSolvable_injective
        (f := AlgHom.mapValue (H := G) (e.symm : AlgebraicClosure k →ₐ[k] k))
        (AlgHom.mapValue_injective e.symm.injective))
  have hQ : geometricallySolvablePointsCommHopfAlgProperty k Q.obj :=
    hsolv.of_faithfullyFlat (CommHopfAlgCat.coinvariantsι hR)
      (AlgHom.FiniteType.of_finitePresentation
        (CommHopfAlgCat.finitePresentation_coinvariantsι hR))
      (CommHopfAlgCat.faithfullyFlat_coinvariantsι hR)
  exact (reductive_coinvariants_unipotentRadical G hconnected).torus_of_geometricallySolvable hQ

/-- The torus `G ⧸ R_u(G)` of a connected solvable group is spanned by its characters, over an
algebraically closed field. -/
theorem groupLikeSpannedProperty_coinvariants_unipotentRadical :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    DiagonalizableGroup.groupLikeSpannedProperty k Q :=
  (torusCommHopfAlgProperty.split k _ (torus_coinvariants_unipotentRadical G)).groupLikeSpanned k _

/-- **The unipotent rational points of a connected solvable group are the rational points of its
unipotent radical**, over an algebraically closed field and in every characteristic. In
particular the unipotent rational points form a subgroup. -/
@[simp]
theorem mem_quotientPointsSubgroup_unipotentRadical_iff (g : WithConv (G →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup G.obj (unipotentRadicalDefiningIdeal G)
        (CommAlgCat.of k k) ↔ HopfAlgebra.IsUnipotentPoint g := by
  refine ⟨isUnipotentPoint_of_mem_quotientPointsSubgroup_unipotentRadical G, fun hg ↦ ?_⟩
  let hR := isNormal_unipotentRadicalDefiningIdeal G
  let _ := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨CommHopfAlgCat.coinvariants hR,
      (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
  let ι := CommHopfAlgCat.coinvariantsι hR
  let _ : IsReduced Q := isReduced_of_injective ι.hom.toAlgHom.toRingHom
    (CommHopfAlgCat.hopfSubalgebraι_injective hR.isHopfSubalgebra_coinvariants)
  -- Every rational point of the torus `G ⧸ R_u(G)` is semisimple.
  have hss :=
    ((DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint
      Q).mp (groupLikeSpannedProperty_coinvariants_unipotentRadical G)).2
  -- So the image of `g`, which is unipotent, is the identity.
  have h1 : BialgHom.mapDomain ι.hom g = 1 :=
    (hss _).eq_one_of_isUnipotent (hg.mapDomain ι.hom)
  rw [BialgHom.mapDomain_apply] at h1
  have hmem := (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff ι (CommAlgCat.of k k) g).mp h1
  rwa [CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hR] at hmem

/-- **The unipotent radical of a connected solvable group is the common kernel of its
characters**, scheme-theoretically, over an algebraically closed field and in every
characteristic. -/
theorem unipotentRadicalDefiningIdeal_eq_characterKernelIdeal :
    unipotentRadicalDefiningIdeal G = _root_.CommHopfAlgCat.characterKernelIdeal G.obj := by
  let C := _root_.CommHopfAlgCat.characterKernelIdeal G.obj
  apply le_antisymm
  · -- The torus `G ⧸ R_u(G)` is spanned by its characters, which are characters of `G`.
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    let _ := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    let ι := CommHopfAlgCat.coinvariantsι hR
    have hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := Q))) = ⊤ :=
      Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top.mp
        ((DiagonalizableGroup.groupLikeSpannedProperty_iff k Q).mp
          (groupLikeSpannedProperty_coinvariants_unipotentRadical G))
    let φ := (CommHopfAlgCat.mkQuotient G.obj C).hom.toAlgHom
    have hφ : ∀ x : GroupLike k G, φ x = 1 :=
      (_root_.CommHopfAlgCat.characterKernelIdeal_toIdeal_le_ker_iff G.obj φ).mp
        (CommHopfAlgCat.mkQuotient_ker G.obj C).ge
    have hadjoin : Algebra.adjoin k (Set.range (GroupLike.val (R := k) (A := Q))) = ⊤ :=
      eq_top_iff.mpr fun x _ ↦ Algebra.span_le_adjoin k _ (hspan ▸ Submodule.mem_top)
    -- Both maps send every character `y` of the torus to one: `ι y` is a character of `G`.
    have hcomp : φ.comp (ι.hom : Q →ₐ[k] G) =
        (Algebra.ofId k _).comp (Bialgebra.counitAlgHom k Q) := by
      refine AlgHom.ext_of_adjoin_eq_top hadjoin ?_
      rintro _ ⟨y, rfl⟩
      have hy := y.isGroupLikeElem_val
      simpa [hy.counit_eq_one] using hφ ⟨ι.hom y, hy.map ι.hom⟩
    rw [← CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hR, ← HopfIdeal.toIdeal_le_toIdeal,
      ← CommHopfAlgCat.mkQuotient_ker G.obj C]
    exact (CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff ι φ).mpr hcomp
  · exact characterKernelIdeal_le_unipotentRadicalDefiningIdeal G

end TauCeti.FiniteTypeCommHopfAlgCat
