/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterKernel
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent
public import TauCeti.RingTheory.TensorProduct.Reduced
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Commutative
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
import TauCeti.Algebra.AlgebraicGroup.Reductive.Solvable
import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Solvable.FaithfullyFlat
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Torus.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Torus.Reductive
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Character
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Quotient
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple

/-!
# The unipotent radical of a connected solvable group

Let `G` be a smooth geometrically connected affine group of finite type over a perfect field `k`,
with geometrically solvable points. This file proves the structure theorem for the unipotent part
of `G` (Milne, Theorem 16.33(a)–(c)):

* the normal affine quotient `G ⧸ R_u(G)` of `G` by its unipotent radical is a torus;
* formation of `R_u(G)` and `G ⧸ R_u(G)` commutes with **arbitrary** field extensions `K / k`
  (not merely separable or algebraic ones);
* for every field extension `K / k`, a `K`-point of `G` lies in `R_u(G)(K)` if and only if it is
  unipotent.

Over a perfect field `k`, the quotient `G ⧸ R_u(G)` is reductive
(`TauCeti.FiniteTypeCommHopfAlgCat.reductive_coinvariants_unipotentRadical`) and geometrically
solvable, hence a torus (`TauCeti.reductiveCommHopfAlgProperty.torus_of_geometricallySolvable`).
Because tori remain tori—and therefore reductive—after arbitrary scalar extension of the base
field, the base-changed radical candidate has reductive quotient over any extension `K / k`, forcing
it to agree with the native `K`-unipotent radical. Pushing any unipotent `K`-point of `G` to an
algebraic closure of `K` lands in a split torus, where every point is semisimple and hence trivial,
so the point lies in the kernel `R_u(G)` of the quotient map.

When `k` is algebraically closed, the torus `G ⧸ R_u(G)` splits over `k` and its coordinate ring is
spanned by `k`-rational characters; consequently `R_u(G)` is scheme-theoretically the common kernel
of the characters of `G`. (Over a non-algebraically closed perfect field `G ⧸ R_u(G)` may be an
anisotropic torus with no nontrivial `k`-rational characters.)

For commutative `G` see
`TauCeti.HopfAlgebra.Point.mem_quotientPointsSubgroup_unipotentRadical_iff`. The weaker statement
that the common kernel of characters has only unipotent points is
`TauCeti.CommHopfAlgCat.geometricallyUnipotentPointsCommHopfAlgProperty_characterKernelIdeal`.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical_of_geometricallySolvable`:
  over a perfect field, `G ⧸ R_u(G)` is a torus.
* `TauCeti.FiniteTypeCommHopfAlgCat.
  baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_geometricallySolvable`: over a perfect
  field, the defining Hopf ideal of `R_u(G)` commutes with arbitrary field extensions.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalBaseChangeIsoOfSolvable` and
  `TauCeti.FiniteTypeCommHopfAlgCat.coinvariantsUnipotentRadicalBaseChangeIsoOfSolvable`:
  the corresponding coordinate Hopf-algebra base-change isomorphisms for `R_u(G)` and `G ⧸ R_u(G)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.
  mem_quotientPointsSubgroup_unipotentRadical_iff_of_geometricallySolvable`: over a perfect field,
  a `K`-point lies in `R_u(G)(K)` if and only if it is unipotent.
* `TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical`,
  `TauCeti.FiniteTypeCommHopfAlgCat.groupLikeSpannedProperty_coinvariants_unipotentRadical`,
  `TauCeti.FiniteTypeCommHopfAlgCat.mem_quotientPointsSubgroup_unipotentRadical_iff`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_characterKernelIdeal`: the
  specializations and character-kernel identification over an algebraically closed field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33(a)–(c), pp. 335–336.
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

section PerfectField

variable [PerfectField k] [Algebra.Smooth k G]

/-- **The quotient of a smooth geometrically connected solvable group by its unipotent radical is
a torus**, over every perfect field (Milne, Theorem 16.33(a)). -/
theorem torus_coinvariants_unipotentRadical_of_geometricallySolvable
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj) :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    torusCommHopfAlgProperty k Q := by
  intro hR Q
  have hQ : geometricallySolvablePointsCommHopfAlgProperty k Q.obj :=
    hsolv.of_faithfullyFlat (CommHopfAlgCat.coinvariantsι hR)
      (AlgHom.FiniteType.of_finitePresentation
        (CommHopfAlgCat.finitePresentation_coinvariantsι hR))
      (CommHopfAlgCat.faithfullyFlat_coinvariantsι hR)
  exact (reductive_coinvariants_unipotentRadical G hconnected).torus_of_geometricallySolvable hQ

/-- **For a smooth geometrically connected solvable group over a perfect field, formation of the
unipotent radical commutes with arbitrary extension of the ground field**
(Milne, Theorem 16.33(b)). -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_geometricallySolvable
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    (K : Type u) [Field K] [Algebra k K] :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal G) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) G) := by
  let hR := isNormal_unipotentRadicalDefiningIdeal G
  let _ := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨CommHopfAlgCat.coinvariants hR,
      (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
  have hQ_torus : torusCommHopfAlgProperty k Q :=
    torus_coinvariants_unipotentRadical_of_geometricallySolvable G hconnected hsolv
  let hRK := CommHopfAlgCat.isNormal_baseChangeHopfIdeal (K := K) hR
  let _ := hRK.isHopfSubalgebra_coinvariants.hopfAlgebra
  let QK : FiniteTypeCommHopfAlgCat.{u, u} K :=
    ⟨CommHopfAlgCat.coinvariants hRK,
      (finiteTypeCommHopfAlgProperty_iff _).mpr hRK.finiteType_coinvariants⟩
  let eQ : baseChange (K := K) Q ≅ QK :=
    ObjectProperty.isoMk _ (CommHopfAlgCat.coinvariantsBaseChangeIso (K := K) hR)
  have hQK_red : reductiveCommHopfAlgProperty K QK :=
    (reductiveCommHopfAlgProperty K).prop_of_iso eQ (hQ_torus.baseChange (K := K)).reductive
  have hker := CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hRK
  have hcand : HopfIdeal.IsUnipotentRadicalCandidate (baseChange (K := K) G)
      (CommHopfAlgCat.kernelHopfIdeal (CommHopfAlgCat.coinvariantsι hRK)) := by
    rw [hker]
    exact (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal G).baseChange
  exact hker.symm.trans (unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_reductive
    (baseChange (K := K) G) QK hQK_red (CommHopfAlgCat.coinvariantsι hRK)
    (CommHopfAlgCat.hopfSubalgebraι_injective hRK.isHopfSubalgebra_coinvariants)
    hcand).symm

/-- For a smooth geometrically connected solvable group over a perfect field, the coordinate Hopf
algebra of the unipotent radical commutes canonically with arbitrary field extensions
(Milne, Theorem 16.33(b)). -/
noncomputable def unipotentRadicalBaseChangeIsoOfSolvable
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    (K : Type u) [Field K] [Algebra k K] :
    baseChange (K := K) (unipotentRadical G) ≅ unipotentRadical (baseChange (K := K) G) :=
  unipotentRadicalBaseChangeIsoOfEq G
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_geometricallySolvable
      G hconnected hsolv K)

/-- The forward base-change comparison on the unipotent radical of a connected solvable group
commutes with the coordinate quotient morphisms. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfSolvable_hom
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap (K := K) (unipotentRadicalCoordinateMap G) ≫
        (unipotentRadicalBaseChangeIsoOfSolvable G hconnected hsolv K).hom =
      unipotentRadicalCoordinateMap (baseChange (K := K) G) :=
  baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfEq_hom G _

/-- The inverse base-change comparison on the unipotent radical of a connected solvable group
commutes with the coordinate quotient morphisms. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfSolvable_inv
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    (K : Type u) [Field K] [Algebra k K] :
    unipotentRadicalCoordinateMap (baseChange (K := K) G) ≫
        (unipotentRadicalBaseChangeIsoOfSolvable G hconnected hsolv K).inv =
      baseChangeMap (K := K) (unipotentRadicalCoordinateMap G) :=
  unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfEq_inv G _

/-- For a smooth geometrically connected solvable group over a perfect field, the normal affine
quotient `G ⧸ R_u(G)` commutes canonically with arbitrary field extensions
(Milne, Theorem 16.33(b)). -/
noncomputable def coinvariantsUnipotentRadicalBaseChangeIsoOfSolvable
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    (K : Type u) [Field K] [Algebra k K] :
    CommHopfAlgCat.baseChange (K := K)
        (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G)) ≅
      CommHopfAlgCat.coinvariants
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) G)) :=
  coinvariantsUnipotentRadicalBaseChangeIsoOfEq G
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_geometricallySolvable
      G hconnected hsolv K)

/-- The forward base-change comparison on `G ⧸ R_u(G)` for a connected solvable group commutes with
the quotient coordinate inclusions. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIsoOfSolvable_hom_comp_coinvariantsι
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    (K : Type u) [Field K] [Algebra k K] :
    (coinvariantsUnipotentRadicalBaseChangeIsoOfSolvable G hconnected hsolv K).hom ≫
        CommHopfAlgCat.coinvariantsι
          (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) G)) =
      CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G)) :=
  coinvariantsUnipotentRadicalBaseChangeIsoOfEq_hom_comp_coinvariantsι G _

/-- The inverse base-change comparison on `G ⧸ R_u(G)` for a connected solvable group commutes with
the quotient coordinate inclusions. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIsoOfSolvable_inv_comp_baseChangeMap
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    (K : Type u) [Field K] [Algebra k K] :
    (coinvariantsUnipotentRadicalBaseChangeIsoOfSolvable G hconnected hsolv K).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G)) =
      CommHopfAlgCat.coinvariantsι
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) G)) :=
  coinvariantsUnipotentRadicalBaseChangeIsoOfEq_inv_comp_baseChangeMap G _

/-- **A field-valued point of a smooth geometrically connected solvable group over a perfect field
lies in the unipotent radical if and only if it is unipotent** (Milne, Theorem 16.33(c)). -/
@[simp]
theorem mem_quotientPointsSubgroup_unipotentRadical_iff_of_geometricallySolvable
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k G.obj)
    {K : Type u} [Field K] [Algebra k K] (g : WithConv (G →ₐ[k] K)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup G.obj (unipotentRadicalDefiningIdeal G)
        (CommAlgCat.of k K) ↔ HopfAlgebra.IsUnipotentPoint g := by
  refine ⟨fun ⟨q, hq⟩ ↦ hq ▸
    ((isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal G).smoothUnipotent.isUnipotentPoint
      q).mapDomain (CommHopfAlgCat.mkQuotient G.obj (unipotentRadicalDefiningIdeal G)).hom,
    fun hg ↦ ?_⟩
  let hR := isNormal_unipotentRadicalDefiningIdeal G
  let _ := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨CommHopfAlgCat.coinvariants hR,
      (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
  let ι := CommHopfAlgCat.coinvariantsι hR
  let L := AlgebraicClosure K
  let φ : K →ₐ[k] L := (Algebra.ofId K L).restrictScalars k
  let q : WithConv (Q →ₐ[k] K) := BialgHom.mapDomain ι.hom g
  let qL : WithConv (Q →ₐ[k] L) := AlgHom.mapValue (H := Q) φ q
  have hQ_torus : torusCommHopfAlgProperty k Q :=
    torus_coinvariants_unipotentRadical_of_geometricallySolvable G hconnected hsolv
  have hQL_span : DiagonalizableGroup.groupLikeSpannedProperty L (baseChange (K := L) Q) :=
    ((hQ_torus.baseChange (K := L)).split L _).groupLikeSpanned L _
  let _ : Algebra.Smooth k Q := (smoothCommHopfAlgProperty_iff Q.obj).mp (hQ_torus.smooth k Q)
  let _ : IsReduced (baseChange (K := L) Q) := isReduced_of_smooth L _
  have hss_all :=
    ((DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint
      (baseChange (K := L) Q)).mp hQL_span).2
  have hqL_ss : HopfAlgebra.IsSemisimplePoint qL :=
    (HopfAlgebra.isSemisimplePoint_baseChangePointsMulEquiv_iff qL).mp
      (hss_all (AlgHom.baseChangePointsMulEquiv (K := L) qL))
  have hqL_one : qL = 1 := hqL_ss.eq_one_of_isUnipotent ((hg.mapDomain ι.hom).mapValue φ)
  have hq_one : q = 1 := WithConv.ofConv_injective <| AlgHom.ext fun x ↦ φ.injective <| by
    simpa [qL, AlgHom.mapValue_apply, AlgHom.convOne_apply] using
      congrArg (fun p : WithConv (Q →ₐ[k] L) ↦ p.ofConv x) hqL_one
  simp only [q, BialgHom.mapDomain_apply] at hq_one
  have hmem := (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff ι (CommAlgCat.of k K) g).mp hq_one
  rwa [CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hR] at hmem

end PerfectField

section AlgebraicallyClosed

variable [IsAlgClosed k]
variable [IsReduced G] [ConnectedSpace (PrimeSpectrum G)]
variable [Group.IsSolvable (WithConv (G →ₐ[k] k))]

/-- **The quotient of a reduced connected solvable group by its unipotent radical is a torus**,
over an algebraically closed field and in every characteristic. -/
theorem torus_coinvariants_unipotentRadical :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    torusCommHopfAlgProperty k Q := by
  let _ : Algebra.Smooth k G := (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k G.obj)
  exact torus_coinvariants_unipotentRadical_of_geometricallySolvable G
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k G.obj).mpr inferInstance)
    (geometricallySolvablePointsCommHopfAlgProperty_of_isAlgClosed G.obj)

/-- The torus `G ⧸ R_u(G)` of a reduced connected solvable group is spanned by its characters,
over an algebraically closed field. -/
theorem groupLikeSpannedProperty_coinvariants_unipotentRadical :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    DiagonalizableGroup.groupLikeSpannedProperty k Q :=
  (torusCommHopfAlgProperty.split k _ (torus_coinvariants_unipotentRadical G)).groupLikeSpanned k _

/-- **The unipotent rational points of a reduced connected solvable group are the rational points
of its unipotent radical**, over an algebraically closed field and in every characteristic. In
particular the unipotent rational points form a subgroup. -/
@[simp]
theorem mem_quotientPointsSubgroup_unipotentRadical_iff (g : WithConv (G →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup G.obj (unipotentRadicalDefiningIdeal G)
        (CommAlgCat.of k k) ↔ HopfAlgebra.IsUnipotentPoint g := by
  let _ : Algebra.Smooth k G := (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k G.obj)
  exact mem_quotientPointsSubgroup_unipotentRadical_iff_of_geometricallySolvable G
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k G.obj).mpr inferInstance)
    (geometricallySolvablePointsCommHopfAlgProperty_of_isAlgClosed G.obj) g

/-- **The unipotent radical of a reduced connected solvable group is the common kernel of its
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

end AlgebraicallyClosed

end TauCeti.FiniteTypeCommHopfAlgCat
