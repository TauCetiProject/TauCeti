/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.UnipotentMorphism
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Idempotent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Commutative
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.Coalgebra.Cocommutative

/-!
# Closed Jordan factors of commutative affine groups

For a reduced commutative affine group of finite type over an algebraically closed field,
the images of the regular Jordan projections are smooth closed subgroup schemes. Their
base-field points are exactly the semisimple and unipotent points, respectively.
The semisimple factor is diagonalizable, and is a torus when the ambient group is
connected; the unipotent factor is geometrically unipotent. This is the commutative
splitting used in the structure theory of solvable affine groups.

Over every commutative test algebra, the two closed factors are the fixed subgroups of
the projections, and multiplication gives a unique factorization into these subgroups.
The test-algebra universe is independent of the base-field and coordinate-algebra universe.
For nonreduced test algebras, these are scheme-theoretic Jordan factors; no assertion of
operator semisimplicity over such algebras is made.

The construction uses the regular projections `semisimplePartBialgHom` and
`unipotentPartBialgHom` and the coordinate image factorization `CommHopfAlgCat.image`.

## References

* A. Borel, *Linear Algebraic Groups*, §4.7.
* T. A. Springer, *Linear Algebraic Groups*, §§2.4 and 3.1.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.HopfAlgebra.Point

universe u v

variable (k H : Type u) [Field k] [IsAlgClosed k] [CommRing H]
  [_root_.HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
  [Coalgebra.IsCocomm k H]

/-- The coordinate Hopf algebra of the closed semisimple factor, the image of the regular
semisimple projection. -/
noncomputable abbrev semisimpleFactor : _root_.CommHopfAlgCat.{u} k :=
  CommHopfAlgCat.image (_root_.CommHopfAlgCat.ofHom (semisimplePartBialgHom k H))

/-- The coordinate Hopf algebra of the closed unipotent factor, the image of the regular
unipotent projection. -/
noncomputable abbrev unipotentFactor : _root_.CommHopfAlgCat.{u} k :=
  CommHopfAlgCat.image (_root_.CommHopfAlgCat.ofHom (unipotentPartBialgHom k H))

/-- The closed semisimple factor is commutative. -/
noncomputable instance instIsCocommSemisimpleFactor :
    Coalgebra.IsCocomm k (semisimpleFactor k H) :=
  (CommHopfAlgCat.mkImage (_root_.CommHopfAlgCat.ofHom
    (semisimplePartBialgHom k H))).hom.toCoalgHom.isCocomm_of_surjective
      (CommHopfAlgCat.mkImage_surjective _)

/-- The closed unipotent factor is commutative. -/
noncomputable instance instIsCocommUnipotentFactor :
    Coalgebra.IsCocomm k (unipotentFactor k H) :=
  (CommHopfAlgCat.mkImage (_root_.CommHopfAlgCat.ofHom
    (unipotentPartBialgHom k H))).hom.toCoalgHom.isCocomm_of_surjective
      (CommHopfAlgCat.mkImage_surjective _)

/-- The closed semisimple factor is smooth. -/
noncomputable instance instSmoothSemisimpleFactor : Algebra.Smooth k (semisimpleFactor k H) :=
  (smoothCommHopfAlgProperty_iff _).mp <|
    smoothCommHopfAlgProperty.image _
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _)

/-- The closed unipotent factor is smooth. -/
noncomputable instance instSmoothUnipotentFactor : Algebra.Smooth k (unipotentFactor k H) :=
  (smoothCommHopfAlgProperty_iff _).mp <|
    smoothCommHopfAlgProperty.image _
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _)

private theorem semisimplePart_idempotent :
    _root_.CommHopfAlgCat.ofHom (semisimplePartBialgHom k H) ≫
        _root_.CommHopfAlgCat.ofHom (semisimplePartBialgHom k H) =
      _root_.CommHopfAlgCat.ofHom (semisimplePartBialgHom k H) := by
  ext x
  exact DFunLike.congr_fun (semisimplePartBialgHom_comp_self (k := k) (H := H)) x

private theorem unipotentPart_idempotent :
    _root_.CommHopfAlgCat.ofHom (unipotentPartBialgHom k H) ≫
        _root_.CommHopfAlgCat.ofHom (unipotentPartBialgHom k H) =
      _root_.CommHopfAlgCat.ofHom (unipotentPartBialgHom k H) := by
  ext x
  exact DFunLike.congr_fun (unipotentPartBialgHom_comp_self k H) x

variable (A : CommAlgCat.{v} k)

/-- The closed semisimple factor represents fixed points of the regular semisimple
projection over every test algebra. -/
@[simp]
theorem mem_quotientPointsSubgroup_ker_semisimplePartBialgHom_iff
    (g : WithConv (H →ₐ[k] A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (HopfIdeal.ker (semisimplePartBialgHom k H)) A ↔
      BialgHom.mapDomain (semisimplePartBialgHom k H) g = g :=
  CommHopfAlgCat.mem_quotientPointsSubgroup_ker_iff_mapDomain_eq_self _
    (semisimplePart_idempotent k H) A g

/-- The closed unipotent factor represents fixed points of the regular unipotent
projection over every test algebra. -/
@[simp]
theorem mem_quotientPointsSubgroup_ker_unipotentPartBialgHom_iff
    (g : WithConv (H →ₐ[k] A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (HopfIdeal.ker (unipotentPartBialgHom k H)) A ↔
      BialgHom.mapDomain (unipotentPartBialgHom k H) g = g :=
  CommHopfAlgCat.mem_quotientPointsSubgroup_ker_iff_mapDomain_eq_self _
    (unipotentPart_idempotent k H) A g

/-- The base-field points of the closed semisimple factor are exactly the semisimple
points of the ambient group. -/
@[simp]
theorem mem_quotientPointsSubgroup_ker_semisimplePartBialgHom_base_iff
    (g : WithConv (H →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (HopfIdeal.ker (semisimplePartBialgHom k H)) (CommAlgCat.of k k) ↔
      IsSemisimplePoint g := by
  rw [mem_quotientPointsSubgroup_ker_semisimplePartBialgHom_iff,
    mapDomain_semisimplePartBialgHom_eq_self_iff]

/-- The base-field points of the closed unipotent factor are exactly the unipotent
points of the ambient group. -/
@[simp]
theorem mem_quotientPointsSubgroup_ker_unipotentPartBialgHom_base_iff
    (g : WithConv (H →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (HopfIdeal.ker (unipotentPartBialgHom k H)) (CommAlgCat.of k k) ↔
      IsUnipotentPoint g := by
  rw [mem_quotientPointsSubgroup_ker_unipotentPartBialgHom_iff,
    mapDomain_unipotentPartBialgHom_eq_self_iff]

/-- The closed semisimple factor is diagonalizable: its coordinate Hopf algebra is
spanned by its group-like elements. -/
theorem groupLikeSetSpan_semisimpleFactor_eq_top :
    Subcoalgebra.groupLikeSetSpan (R := k) (C := semisimpleFactor k H) Set.univ = ⊤ := by
  let _ : IsReduced (semisimpleFactor k H) := isReduced_of_smooth k _
  apply HopfAlgebra.groupLikeSetSpan_eq_top_of_isSemisimplePoint
  intro g
  let q := CommHopfAlgCat.mkImage (_root_.CommHopfAlgCat.ofHom (semisimplePartBialgHom k H))
  apply (HopfAlgebra.isSemisimplePoint_mapDomain_iff_of_surjective q.hom
    (CommHopfAlgCat.mkImage_surjective _) g).mp
  have h := (mem_quotientPointsSubgroup_ker_semisimplePartBialgHom_base_iff k H _).mp
    (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k H) _ (CommAlgCat.of k k) g)
  rwa [CommHopfAlgCat.quotientPointsHom_apply] at h

/-- The closed unipotent factor is a smooth unipotent affine group, with unipotence
understood geometrically through all finite-dimensional representations. -/
theorem smoothUnipotentCommHopfAlgProperty_unipotentFactor :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (unipotentFactor k H)) := by
  apply (smoothUnipotentCommHopfAlgProperty.iff_smooth_and_forall_isUnipotentPoint k).mpr
  refine ⟨inferInstance, fun g ↦ ?_⟩
  let q := CommHopfAlgCat.mkImage (_root_.CommHopfAlgCat.ofHom (unipotentPartBialgHom k H))
  apply (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective q.hom
    (CommHopfAlgCat.mkImage_surjective _) g).mp
  have h := (mem_quotientPointsSubgroup_ker_unipotentPartBialgHom_base_iff k H _).mp
    (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k H) _ (CommAlgCat.of k k) g)
  rwa [CommHopfAlgCat.quotientPointsHom_apply] at h

/-- For a connected commutative affine group, its closed semisimple factor is a torus. -/
theorem torusCommHopfAlgProperty_semisimpleFactor
    (hH : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H)) :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (semisimpleFactor k H)) := by
  let _ : IsReduced (semisimpleFactor k H) := isReduced_of_smooth k _
  let _ : ConnectedSpace (PrimeSpectrum (semisimpleFactor k H)) :=
    (hH.image (_root_.CommHopfAlgCat.ofHom (semisimplePartBialgHom k H))).connectedSpace k _
  exact torusCommHopfAlgProperty.of_groupLikeSetSpan_eq_top _
    (groupLikeSetSpan_semisimpleFactor_eq_top k H)

private theorem mapDomain_semisimplePart_mapDomain_unipotentPart
    (g : WithConv (H →ₐ[k] A)) :
    BialgHom.mapDomain (semisimplePartBialgHom k H)
        (BialgHom.mapDomain (unipotentPartBialgHom k H) g) = 1 := by
  rw [← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp,
    unipotentPartBialgHom_comp_semisimplePartBialgHom]
  apply ofConv_injective
  ext x
  simp [Bialgebra.unitBialgHom, AlgHom.convOne_apply]

private theorem mapDomain_unipotentPart_mapDomain_semisimplePart
    (g : WithConv (H →ₐ[k] A)) :
    BialgHom.mapDomain (unipotentPartBialgHom k H)
        (BialgHom.mapDomain (semisimplePartBialgHom k H) g) = 1 := by
  rw [← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp,
    semisimplePartBialgHom_comp_unipotentPartBialgHom]
  apply ofConv_injective
  ext x
  simp [Bialgebra.unitBialgHom, AlgHom.convOne_apply]

/-- Multiplication identifies ambient points with the product of the two closed Jordan
factor subgroups over every commutative test algebra. The forward map applies the two
regular Jordan projections; its inverse multiplies the included points. -/
noncomputable def jordanFactorsMulEquiv :
    WithConv (H →ₐ[k] A) ≃*
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
          (HopfIdeal.ker (semisimplePartBialgHom k H)) A ×
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
          (HopfIdeal.ker (unipotentPartBialgHom k H)) A where
  toFun g :=
    (⟨BialgHom.mapDomain (semisimplePartBialgHom k H) g, by
      rw [mem_quotientPointsSubgroup_ker_semisimplePartBialgHom_iff,
        ← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp,
        semisimplePartBialgHom_comp_self]⟩,
    ⟨BialgHom.mapDomain (unipotentPartBialgHom k H) g, by
      rw [mem_quotientPointsSubgroup_ker_unipotentPartBialgHom_iff,
        ← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp,
        unipotentPartBialgHom_comp_self]⟩)
  invFun p := p.1.val * p.2.val
  left_inv := mapDomain_semisimplePartBialgHom_mul_mapDomain_unipotentPartBialgHom k H
  right_inv p := by
    have hs := (mem_quotientPointsSubgroup_ker_semisimplePartBialgHom_iff k H A p.1.val).mp
      p.1.property
    have hu := (mem_quotientPointsSubgroup_ker_unipotentPartBialgHom_iff k H A p.2.val).mp
      p.2.property
    apply Prod.ext <;> apply Subtype.ext
    · simp only [map_mul, hs]
      rw [← hu, mapDomain_semisimplePart_mapDomain_unipotentPart, mul_one]
    · simp only [map_mul, hu]
      rw [← hs, mapDomain_unipotentPart_mapDomain_semisimplePart, one_mul]
  map_mul' g h := by
    apply Prod.ext <;> apply Subtype.ext <;> exact map_mul _ g h

/-- The first factor is the regular semisimple projection. -/
@[simp]
theorem jordanFactorsMulEquiv_fst_coe (g : WithConv (H →ₐ[k] A)) :
    ((jordanFactorsMulEquiv k H A g).1 : WithConv (H →ₐ[k] A)) =
      BialgHom.mapDomain (semisimplePartBialgHom k H) g :=
  (rfl)

/-- The second factor is the regular unipotent projection. -/
@[simp]
theorem jordanFactorsMulEquiv_snd_coe (g : WithConv (H →ₐ[k] A)) :
    ((jordanFactorsMulEquiv k H A g).2 : WithConv (H →ₐ[k] A)) =
      BialgHom.mapDomain (unipotentPartBialgHom k H) g :=
  (rfl)

/-- The inverse factorization map multiplies the two included points. -/
@[simp]
theorem jordanFactorsMulEquiv_symm_apply
    (s : CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.ker (semisimplePartBialgHom k H)) A)
    (u : CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.ker (unipotentPartBialgHom k H)) A) :
    (jordanFactorsMulEquiv k H A).symm (s, u) = s.val * u.val :=
  (rfl)

/-- The closed-factor decomposition is natural under a change of test algebra. -/
theorem jordanFactorsMulEquiv_mapValue {B : CommAlgCat.{v} k} (φ : A ⟶ B)
    (g : WithConv (H →ₐ[k] A)) :
    jordanFactorsMulEquiv k H B (AlgHom.mapValue φ.hom g) =
      (CommHopfAlgCat.mapQuotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (HopfIdeal.ker (semisimplePartBialgHom k H)) φ (jordanFactorsMulEquiv k H A g).1,
      CommHopfAlgCat.mapQuotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (HopfIdeal.ker (unipotentPartBialgHom k H)) φ (jordanFactorsMulEquiv k H A g).2) := by
  apply Prod.ext <;> apply Subtype.ext
  · rw [jordanFactorsMulEquiv_fst_coe, CommHopfAlgCat.coe_mapQuotientPointsSubgroup_apply,
      HopfAlgebra.mapPoints_apply, jordanFactorsMulEquiv_fst_coe]
    simpa only [MonoidHom.comp_apply, AlgHom.mapValue_apply] using DFunLike.congr_fun
      (BialgHom.mapValue_mapDomain (semisimplePartBialgHom k H) φ.hom) g
  · rw [jordanFactorsMulEquiv_snd_coe, CommHopfAlgCat.coe_mapQuotientPointsSubgroup_apply,
      HopfAlgebra.mapPoints_apply, jordanFactorsMulEquiv_snd_coe]
    simpa only [MonoidHom.comp_apply, AlgHom.mapValue_apply] using DFunLike.congr_fun
      (BialgHom.mapValue_mapDomain (unipotentPartBialgHom k H) φ.hom) g

end TauCeti.HopfAlgebra.Point
