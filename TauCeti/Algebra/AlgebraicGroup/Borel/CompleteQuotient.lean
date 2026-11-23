/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Flag
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
import TauCeti.Algebra.AlgebraicGroup.Borel.Dimension
import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Boundary
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Flag
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Solvability
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.StabilizerDimension
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.Coalgebra.Subcomodule.Finrank
import TauCeti.RingTheory.KrullDimension.FiniteType
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Completeness of Borel homogeneous quotients

Let `G` be a reduced affine group scheme of finite type over an algebraically closed field `k`,
and let `B` be a Borel subgroup of `G`. Combining Chevalley's theorem and the Lie--Kolchin theorem
produces a finite-dimensional `G`-comodule `M` and an upper-triangular basis `b` whose exterior
flag vector `w = exteriorFlagVector k d b` in `FlagSpace k M d` has line stabilizer `B`. Since
every point in the `G(k)`-stable flag locus has solvable stabilizer, `B` has minimal stabilizer
dimension in that locus, so the projective orbit of `[w]` is closed and represents `G / B`.

## Main results

* `TauCeti.HopfIdeal.IsBorelOverAlgClosed.isClosed_range_projectiveOrbitMap_exteriorFlagVector`:
  the projective orbit of `exteriorFlagVector k (1 + n) b` is closed.
* `TauCeti.HopfIdeal.IsBorelOverAlgClosed.exists_isClosed_projectiveOrbit_stabilizerHopfIdeal_eq`:
  every Borel subgroup `B` is the line stabilizer of a unimodular vector whose projective orbit
  has closed image, closed immersion into `ℙ`, proper morphism over `Spec k`, and represents
  `CommHopfAlgCat.fppfHomogeneousQuotient G.obj B`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.9(a), p. 354.
* J. E. Humphreys, *Linear Algebraic Groups*, §21.3.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.HopfIdeal

universe u

section BorelQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Chevalley's theorem and the Lie--Kolchin theorem produce a finite-dimensional `G`-comodule `M`
with a basis `b` whose first line has stabilizer `B` and whose corestriction to `G ⧸ B.toIdeal`
is upper triangular. -/
private theorem exists_basis_stabilizerHopfIdeal_eq_of_isBorelOverAlgClosed
    {B : HopfIdeal k G} (hB : IsBorelOverAlgClosed k G B) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k G M)
      (_ : Module.Finite k M) (n : ℕ) (b : Module.Basis (Fin (1 + n)) k M),
      (k ∙ b 0).stabilizerHopfIdeal G = B ∧
        (letI : Comodule k (G ⧸ B.toIdeal) M :=
          Comodule.Corestrict (CommHopfAlgCat.mkQuotient G.obj B).hom.toCoalgHom
         (Comodule.coefficientMatrix (C := G ⧸ B.toIdeal) b).IsUpperTriangular) := by
  have := Algebra.FiniteType.isNoetherianRing k G
  obtain ⟨M, instAddM, instModM, instComodM, instFinM, L, hL, hB_eq⟩ :=
    B.exists_line_stabilizerHopfIdeal_eq (IsNoetherian.noetherian B.toIdeal)
  let Q := FiniteTypeCommHopfAlgCat.quotient G B
  have hcand := ((isBorelOverAlgClosed_iff k G B).mp hB).2.prop
  let _ : Algebra.Smooth k Q := (smoothCommHopfAlgProperty_iff _).mp hcand.smooth
  let _ : _root_.IsReduced (G ⧸ B.toIdeal) := isReduced_of_smooth k Q
  let _ : ConnectedSpace (PrimeSpectrum (G ⧸ B.toIdeal)) :=
    hcand.geometricallyConnected.connectedSpace
  let _ : Group.IsSolvable (WithConv ((G ⧸ B.toIdeal) →ₐ[k] k)) :=
    isSolvable_points_of_geometricallySolvablePointsCommHopfAlgProperty Q.obj
      hcand.geometricallySolvable
  let _ : Comodule k (G ⧸ B.toIdeal) M :=
    Comodule.Corestrict (CommHopfAlgCat.mkQuotient G.obj B).hom.toCoalgHom
  obtain ⟨LQ, hLQ⟩ := (L.stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict B).mp hB_eq.le
  have hdimLQ : Module.finrank k LQ = 1 := by rwa [← Subcomodule.finrank_toSubmodule, hLQ]
  obtain ⟨n, b, htri, hb0⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_first_span_of_isSolvable
      (k := k) (H := G ⧸ B.toIdeal) (M := M) LQ hdimLQ
  exact ⟨M, instAddM, instModM, instComodM, instFinM, n, b, by rwa [hb0, hLQ], htri⟩

variable [_root_.IsReduced G]

/-- If `b : Module.Basis (Fin (1 + n)) k M` is upper triangular over `G ⧸ B.toIdeal` for a Borel
subgroup `B` of a reduced finite-type group `G` and `k ∙ b 0` has stabilizer `B`, then the
projective orbit of `exteriorFlagVector k (1 + n) b` is closed. -/
theorem IsBorelOverAlgClosed.isClosed_range_projectiveOrbitMap_exteriorFlagVector
    {B : HopfIdeal k G} (hB : IsBorelOverAlgClosed k G B)
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k G M] [Module.Finite k M] {n : ℕ}
    (b : Module.Basis (Fin (1 + n)) k M)
    (h0 : (k ∙ b 0).stabilizerHopfIdeal G = B)
    (htri : letI : Comodule k (G ⧸ B.toIdeal) M :=
        Comodule.Corestrict (CommHopfAlgCat.mkQuotient G.obj B).hom.toCoalgHom
      (Comodule.coefficientMatrix (C := G ⧸ B.toIdeal) b).IsUpperTriangular)
    (hw : Module.IsUnimodular k (exteriorPower.exteriorFlagVector k (1 + n) b)) :
    letI : AddCommGroup (exteriorPower.FlagSpace k M (1 + n)) :=
      Module.addCommMonoidToAddCommGroup k
    letI : Comodule k G (exteriorPower.FlagSpace k M (1 + n)) :=
      Comodule.exteriorFlag k G M (1 + n)
    IsClosed (Set.range (Comodule.projectiveOrbitMap (H := G)
      (exteriorPower.exteriorFlagVector k (1 + n) b) hw)) := by
  let _ : AddCommGroup (exteriorPower.FlagSpace k M (1 + n)) :=
    Module.addCommMonoidToAddCommGroup k
  let _ : Comodule k G (exteriorPower.FlagSpace k M (1 + n)) :=
    Comodule.exteriorFlag k G M (1 + n)
  let _ : Group.IsSolvable (WithConv ((G ⧸ B.toIdeal) →ₐ[k] k)) :=
    isSolvable_points_of_geometricallySolvablePointsCommHopfAlgProperty
      (FiniteTypeCommHopfAlgCat.quotient G B).obj
      ((isBorelOverAlgClosed_iff k G B).mp hB).2.prop.geometricallySolvable
  set w := exteriorPower.exteriorFlagVector k (1 + n) b
  have hstab_w : (k ∙ w).stabilizerHopfIdeal G = B :=
    Comodule.stabilizerHopfIdeal_span_exteriorFlagVector_eq b B h0 htri
  have hwZ : Set.range (Comodule.projectiveOrbitMap (H := G) w hw) ⊆
      ProjectiveSpectrum.zeroLocus _ (exteriorPower.exteriorFlagForms k M (1 + n)) := by
    rw [Comodule.range_projectiveOrbitMap_subset_iff_of_isClosed w hw
      (ProjectiveSpectrum.isClosed_zeroLocus _ _)
      (Comodule.mapsTo_projectivePointTranslation_exteriorFlagZeroLocus (1 + n))]
    exact (Comodule.projectiveOrbitMap_counit_mem_exteriorFlagZeroLocus_iff (1 + n) w hw).mpr
      (exteriorPower.exteriorFlagVector_mem_exteriorFlagCone b)
  refine Comodule.isClosed_range_projectiveOrbitMap_of_forall_mem w hw
    (ProjectiveSpectrum.isClosed_zeroLocus _ _) hwZ fun w' hw' hw'Z ↦ ?_
  have hw'_cone : w' ∈ exteriorPower.exteriorFlagCone k M (1 + n) :=
    (Comodule.projectiveOrbitMap_counit_mem_exteriorFlagZeroLocus_iff (1 + n) w' hw').mp hw'Z
  have hw'_ne : w' ≠ 0 := by
    obtain ⟨φ, hφ⟩ := Module.isUnimodular_iff.mp hw'
    exact fun h ↦ one_ne_zero (by rw [← hφ, h, map_zero])
  have hfin : Module.finrank k M = 1 + n :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin _)
  obtain ⟨c, b', rfl⟩ :=
    exteriorPower.exists_basis_of_mem_exteriorFlagCone_of_finrank_eq hfin hw'_cone hw'_ne
  set D := (k ∙ (c • exteriorPower.exteriorFlagVector k (1 + n) b')).stabilizerHopfIdeal G
  have hD_eq : D = (k ∙ exteriorPower.exteriorFlagVector k (1 + n) b').stabilizerHopfIdeal G :=
    congrArg (Submodule.stabilizerHopfIdeal G)
      (by rw [Units.smul_def, Submodule.span_singleton_smul_eq c.isUnit])
  have : Group.IsSolvable (WithConv ((G ⧸ D.toIdeal) →ₐ[k] k)) :=
    hD_eq ▸ Comodule.isSolvable_points_quotient_stabilizerHopfIdeal_exteriorFlagVector b' h0
  have ho_w := Comodule.topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_eq w hw B
    fun a ↦ hstab_w ▸ Comodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_span_iff w hw a
  have ho_w' := Comodule.topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_eq _ hw' D
    (Comodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_span_iff _ hw')
  have := Bialgebra.nontrivial (A := G ⧸ D.toIdeal) k
  exact TauCeti.le_of_add_ringKrullDim_quotient_eq_of_le k ho_w ho_w'
    (hB.ringKrullDim_quotient_le D)

/-- **Completeness of Borel homogeneous quotients.** Over an algebraically closed field `k`, every
Borel subgroup `B` of a reduced affine group `G` of finite type is the scheme-theoretic line
stabilizer of a unimodular vector `w` in a finite-dimensional `G`-comodule `W` whose projective
orbit has closed image, closed immersion into projective space, proper structural morphism over
`Spec k`, and represents the fppf homogeneous quotient `G / B`. Neither smoothness nor
connectedness of `G` is needed. -/
theorem IsBorelOverAlgClosed.exists_isClosed_projectiveOrbit_stabilizerHopfIdeal_eq
    {B : HopfIdeal k G} (hB : IsBorelOverAlgClosed k G B) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : Comodule k G W)
      (_ : Module.Finite k W) (w : W) (hw : Module.IsUnimodular k w),
      (k ∙ w).stabilizerHopfIdeal G = B ∧
        IsClosed (Set.range (Comodule.projectiveOrbitMap (H := G) w hw)) ∧
        IsClosedImmersion (Comodule.projectiveOrbitι (H := G) w hw) ∧
        IsProper (Comodule.projectiveOrbitToSpec (H := G) w hw) ∧
        Nonempty (CommHopfAlgCat.fppfHomogeneousQuotient G.obj B ≅
          Comodule.projectiveOrbitPointsSheaf (H := G.obj) w hw) := by
  obtain ⟨M, _, _, _, _, n, b, hb0_stab, htri⟩ :=
    exists_basis_stabilizerHopfIdeal_eq_of_isBorelOverAlgClosed hB
  let W := exteriorPower.FlagSpace k M (1 + n)
  let instAddW : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
  let instComodW : Comodule k G W := Comodule.exteriorFlag k G M (1 + n)
  let w : W := exteriorPower.exteriorFlagVector k (1 + n) b
  have hw : Module.IsUnimodular k w := Module.isUnimodular_iff.mpr
    (Module.Projective.exists_dual_eq_one k
      ((exteriorPower.exteriorFlagVector_ne_zero_iff (v := b)).mpr b.linearIndependent))
  have hstab_w : (k ∙ w).stabilizerHopfIdeal G = B :=
    Comodule.stabilizerHopfIdeal_span_exteriorFlagVector_eq b B hb0_stab htri
  have hclosed : IsClosed (Set.range (Comodule.projectiveOrbitMap (H := G) w hw)) :=
    hB.isClosed_range_projectiveOrbitMap_exteriorFlagVector b hb0_stab htri hw
  have hcoset (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := G.obj) A) :=
    B.coset_eq_iff_exists_units_matrixCoefficient w hw A (fun a ↦ by
      rw [← hstab_w, Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint]) g h
  exact ⟨W, instAddW, inferInstance, instComodW, inferInstance, w, hw, hstab_w, hclosed,
    (Comodule.isClosedImmersion_projectiveOrbitι_iff_isClosed w hw).2 hclosed,
    Comodule.isProper_projectiveOrbitToSpec_of_isClosed W w hw hclosed,
    ⟨Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints B w hw hcoset⟩⟩

end BorelQuotient

end TauCeti.HopfIdeal
