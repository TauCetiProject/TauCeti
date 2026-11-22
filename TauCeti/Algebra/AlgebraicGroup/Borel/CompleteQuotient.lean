/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.FlagStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
import TauCeti.Algebra.AlgebraicGroup.Borel.Dimension
import TauCeti.Algebra.AlgebraicGroup.Borel.ProjectiveOrbit
import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Character
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Boundary
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LineFibers
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Solvability
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.StabilizerDimension
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Translation
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.Coalgebra.Subcomodule.Finrank
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Completeness of Borel homogeneous quotients

Let `G` be a reduced affine group scheme of finite type over an algebraically closed field `k`
(including every smooth affine group scheme over `k`, without connectedness assumptions on `G`),
and let `B` be a Borel subgroup of `G`. By Chevalley's theorem (`B` is the line stabilizer of a
one-dimensional subspace `L` of an exterior-power comodule `M`) combined with the Lie--Kolchin
theorem for the connected smooth solvable group `B` (`L` extends to an upper-triangular basis `b`
of `M`), the exterior flag vector `w = exteriorFlagVector k d b` in `FlagSpace k M d` has
scheme-theoretic line stabilizer `B`.

Geometrically, the quadratic equations `exteriorFlagForms k M d` cut out a `G(k)`-stable closed
subvariety of `ℙ(FlagSpace k M d)` whose closed points correspond to complete flags in `M`. Every
such flag has stabilizer with solvable `k`-points
(`isSolvable_points_quotient_stabilizerHopfIdeal_exteriorFlagVector`), hence Krull dimension at
most `dim B` (`IsBorelOverAlgClosed.ringKrullDim_quotient_le`). By the orbit-stabilizer dimension
identity (`topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_eq`), the orbit of `[w]`
has minimal dimension among all orbits in the flag locus, so the relative closed-orbit lemma
(`isClosed_range_projectiveOrbitMap_of_forall_mem`) shows that the projective orbit of `[w]` is
closed in projective space, hence proper over `Spec k`, while representing the fppf homogeneous
quotient `G / B`.

## Main results

* `TauCeti.HopfIdeal.IsBorelOverAlgClosed.isClosed_range_projectiveOrbitMap_exteriorFlagVector`:
  for any basis `b` of `M` that is upper triangular over `B` with
  `(k ∙ b 0).stabilizerHopfIdeal G = B`, the projective orbit of `exteriorFlagVector k (1 + n) b`
  is closed.
* `TauCeti.HopfIdeal.IsBorelOverAlgClosed.exists_isClosed_projectiveOrbit_stabilizerHopfIdeal_eq`:
  every Borel subgroup `B` of a reduced finite-type affine group `G` over an algebraically closed
  field is the scheme-theoretic line stabilizer of a unimodular vector whose projective orbit has
  closed image, closed immersion into projective space, proper structural morphism over `Spec k`,
  and represents `CommHopfAlgCat.fppfHomogeneousQuotient G.obj B`.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Theorem 17.9(a), p. 354.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, Springer (1975), §21.3.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.HopfIdeal

universe u

section FlagZeroLocus

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M]

private theorem mapsTo_projectivePointTranslation_exteriorFlagZeroLocus (d : ℕ)
    (g : WithConv (H →ₐ[k] k)) :
    letI : Comodule k H (exteriorPower.FlagSpace k M d) := Comodule.exteriorFlag k H M d
    Set.MapsTo
      (Comodule.projectivePointTranslation (M := exteriorPower.FlagSpace k M d) g).hom
      (ProjectiveSpectrum.zeroLocus _ (exteriorPower.exteriorFlagForms k M d) :
        Set (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k
          (Module.Dual k (exteriorPower.FlagSpace k M d)))))
      (ProjectiveSpectrum.zeroLocus _ (exteriorPower.exteriorFlagForms k M d)) := by
  let _ : Comodule k H (exteriorPower.FlagSpace k M d) := Comodule.exteriorFlag k H M d
  intro x hx s hs
  by_contra hmem
  have hb : (Comodule.projectivePointTranslation (M := exteriorPower.FlagSpace k M d) g).hom x ∈
      Proj.basicOpen _ s := (Proj.mem_basicOpen _ s _).mpr hmem
  rw [← Scheme.Hom.mem_preimage, Comodule.projectivePointTranslation_hom,
    Proj.map_preimage_basicOpen, Proj.mem_basicOpen, SymmetricAlgebra.gradedMap_apply] at hb
  refine hb (hx ?_)
  rw [Comodule.basePointsRepresentation_exteriorFlag]
  exact exteriorPower.map_dualMap_mem_exteriorFlagForms
    (fun _ hw ↦ exteriorPower.exteriorFlagMap_mem_exteriorFlagCone _ hw) hs

private theorem projectiveOrbitMap_counit_mem_exteriorFlagZeroLocus_iff [Module.Finite k M]
    (d : ℕ) (w : exteriorPower.FlagSpace k M d) (hw : Module.IsUnimodular k w) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M d) := Comodule.exteriorFlag k H M d
     Comodule.projectiveOrbitMap (H := H) w hw
       (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
         ProjectiveSpectrum.zeroLocus _ (exteriorPower.exteriorFlagForms k M d)) ↔
      w ∈ exteriorPower.exteriorFlagCone k M d := by
  let _ : Comodule k H (exteriorPower.FlagSpace k M d) := Comodule.exteriorFlag k H M d
  have : FiniteDimensional k M := inferInstance
  refine (ProjectiveSpectrum.mem_zeroLocus _ _ _).trans ?_
  rw [exteriorPower.mem_exteriorFlagCone_iff]
  refine forall₂_congr fun s hs ↦ ?_
  have h := Comodule.mem_projectiveOrbitMap_kernelPoint_iff (H := H) w hw 1
    (exteriorPower.mem_homogeneousSubmodule_of_mem_exteriorFlagForms hs)
  simp only [map_one, one_apply_eq_self] at h
  simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp] at h
  exact h

end FlagZeroLocus

section BorelQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : FiniteTypeCommHopfAlgCat.{u, u} k}

omit [IsAlgClosed k] in
private theorem exists_line_stabilizerHopfIdeal_eq (B : HopfIdeal k G) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k G.obj M)
      (_ : Module.Finite k M) (L : Submodule k M),
      Module.finrank k L = 1 ∧ L.stabilizerHopfIdeal G.obj = B := by
  have := Algebra.FiniteType.isNoetherianRing k G
  obtain ⟨V, r, hV, L, hL, -, hstabL⟩ :=
    B.exists_finite_subcomodule_exteriorPower_line_stabilizer.{u, u, u}
      (IsNoetherian.noetherian B.toIdeal)
  let _ : Module.Finite k V := hV
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let instComodM : Comodule k G.obj (⋀[k]^r V) := Comodule.exteriorPower k G.obj V r
  exact ⟨⋀[k]^r V, inferInstance, inferInstance, instComodM, inferInstance, L, hL,
    L.stabilizerHopfIdeal_eq_of_forall_mem_quotientPointsSubgroup_iff B fun A _ _ g ↦
      hstabL (CommAlgCat.of k A) g⟩

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
  obtain ⟨M, instAddM, instModM, instComodM, instFinM, L, hL, hB_eq⟩ :=
    exists_line_stabilizerHopfIdeal_eq B
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
    letI : Comodule k G (exteriorPower.FlagSpace k M (1 + n)) :=
      Comodule.exteriorFlag k G M (1 + n)
    IsClosed (Set.range (Comodule.projectiveOrbitMap (H := G)
      (exteriorPower.exteriorFlagVector k (1 + n) b) hw)) := by
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
      (mapsTo_projectivePointTranslation_exteriorFlagZeroLocus (1 + n))]
    exact (projectiveOrbitMap_counit_mem_exteriorFlagZeroLocus_iff (1 + n) w hw).mpr
      (exteriorPower.exteriorFlagVector_mem_exteriorFlagCone b)
  refine Comodule.isClosed_range_projectiveOrbitMap_of_forall_mem w hw
    (ProjectiveSpectrum.isClosed_zeroLocus _ _) hwZ fun w' hw' hw'Z ↦ ?_
  have hw'_cone : w' ∈ exteriorPower.exteriorFlagCone k M (1 + n) :=
    (projectiveOrbitMap_counit_mem_exteriorFlagZeroLocus_iff (1 + n) w' hw').mp hw'Z
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
  exact Comodule.le_of_add_ringKrullDim_quotient_eq_of_le ho_w ho_w'
    (hB.ringKrullDim_quotient_le D)

private theorem exists_stabilizerHopfIdeal_eq_and_isClosed_range_projectiveOrbitMap
    {B : HopfIdeal k G} (hB : IsBorelOverAlgClosed k G B) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : Comodule k G W)
      (_ : Module.Finite k W) (w : W) (hw : Module.IsUnimodular k w),
      (k ∙ w).stabilizerHopfIdeal G = B ∧
        IsClosed (Set.range (Comodule.projectiveOrbitMap (H := G) w hw)) := by
  obtain ⟨M, _, _, _, _, n, b, hb0_stab, htri⟩ :=
    exists_basis_stabilizerHopfIdeal_eq_of_isBorelOverAlgClosed hB
  let W := exteriorPower.FlagSpace k M (1 + n)
  let instComodW : Comodule k G W := Comodule.exteriorFlag k G M (1 + n)
  let w : W := exteriorPower.exteriorFlagVector k (1 + n) b
  have hw : Module.IsUnimodular k w := Module.isUnimodular_iff.mpr
    (Module.Projective.exists_dual_eq_one k
      ((exteriorPower.exteriorFlagVector_ne_zero_iff (v := b)).mpr b.linearIndependent))
  exact ⟨W, inferInstance, inferInstance, instComodW, inferInstance, w, hw,
    Comodule.stabilizerHopfIdeal_span_exteriorFlagVector_eq b B hb0_stab htri,
    hB.isClosed_range_projectiveOrbitMap_exteriorFlagVector b hb0_stab htri hw⟩

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
  obtain ⟨W, instAddW, instModW, instComodW, instFinW, w, hw, hstab_w, hclosed⟩ :=
    exists_stabilizerHopfIdeal_eq_and_isClosed_range_projectiveOrbitMap hB
  have hcoset (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := G.obj) A) :=
    B.coset_eq_iff_exists_units_matrixCoefficient w hw A (fun a ↦ by
      have hker : (∀ x ∈ B, a.ofConv x = 0) ↔ B.toIdeal ≤ RingHom.ker a.ofConv :=
        ⟨fun ha _ hx ↦ ha _ hx, fun ha _ hx ↦ ha hx⟩
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, hker, ← hstab_w,
        Submodule.stabilizerHopfIdeal_le_ker_iff]) g h
  exact ⟨W, instAddW, instModW, instComodW, instFinW, w, hw, hstab_w, hclosed,
    (Comodule.isClosedImmersion_projectiveOrbitι_iff_isClosed w hw).2 hclosed,
    Comodule.isProper_projectiveOrbitToSpec_of_isClosed W w hw hclosed,
    ⟨Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints B w hw hcoset⟩⟩

end BorelQuotient

end TauCeti.HopfIdeal
