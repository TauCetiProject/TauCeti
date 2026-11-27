/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.GroupTheory.GroupAction.Effective
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.Quotient
import TauCeti.Algebra.Lie.Quotient
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Quotients of Lie groups by closed normal subgroups

Let `N` be a closed normal subgroup of a finite-dimensional real Lie group `G` with boundaryless
model. The homogeneous space `G ⧸ N` is a smooth manifold for the charts
`Subgroup.quotientChartedSpaceOfIsClosed`, and the projection `π : G → G ⧸ N` is a surjective
smooth submersion (`Subgroup.isSubmersion_quotientMk`). This file shows that the group structure
of `G ⧸ N` is smooth, and describes its Lie algebra and its actions.

* **The quotient Lie group.** Multiplication and inversion of `G ⧸ N` are smooth
  (`Subgroup.lieGroup_quotientOfIsClosed`): composed with the submersions `π × π` and `π` they are
  `π` composed with the multiplication and the inversion of `G`, and smoothness descends along
  surjective submersions (`Manifold.IsSubmersion.lieGroup`). So `π` is a smooth homomorphism
  (`Subgroup.quotientMkSmoothHom`).
* **Descent of homomorphisms.** A smooth homomorphism `φ : G → G'` vanishing on `N` factors
  through a smooth homomorphism `G ⧸ N → G'` (`Subgroup.quotientLiftSmoothHom`), and uniquely so
  (`Subgroup.eq_quotientLiftSmoothHom`).
* **The Lie algebra.** The Lie map of `π`, its differential at the identity read on
  left-invariant derivations, is surjective
  (`Subgroup.surjective_lieMap_quotientMkSmoothHom`), and its kernel is the Lie algebra
  `𝔫 = TauCeti.Lie.lieSubalgebraOfSubgroup N` of `N`
  (`Subgroup.lieMap_quotientMkSmoothHom_eq_zero_iff`,
  `Subgroup.toLieSubalgebra_ker_lieMap_quotientMkSmoothHom`). Together these identify the Lie
  algebra of `G ⧸ N` with the quotient `𝔤 ⧸ 𝔫` through the Lie map of `π`
  (`Subgroup.quotientLieAlgebraEquiv`).
* **The tangent Lie algebras.** On the tangent spaces at the identity, the differentials
  `dι : Lie(N) → 𝔤` of the inclusion, for any embedded-Lie-subgroup structure on `N`, and
  `dπ : 𝔤 → Lie(G ⧸ N)` of the projection form a short exact sequence: `dι` is injective
  (`TauCeti.Lie.EmbeddedLieSubgroupData.injective_mfderiv_subtypeVal`), `ker dπ = range dι`
  (`Subgroup.ker_groupLieAlgebraMap_mk'`) and `dπ` is surjective
  (`Subgroup.surjective_groupLieAlgebraMap_mk'`). Consequently `N` acts trivially on `𝔤 ⧸ 𝔫`:
  `Ad_n ξ - ξ ∈ 𝔫` for `n ∈ N`
  (`Subgroup.adjointContinuousLinearMap_sub_self_mem_range_groupLieAlgebraMap_subtype`).
* **The residual action.** Let `G` act smoothly on a boundaryless manifold `M`, with `N` acting
  freely and properly. By the quotient manifold theorem the orbit space `M ⧸ N` is a smooth
  manifold (`Subgroup.orbitRelQuotientChartedSpaceOfIsClosed`,
  `Subgroup.isManifold_orbitRelQuotientOfIsClosed`) and the orbit projection is a submersion
  (`Subgroup.isSubmersion_orbitRelQuotientMkOfIsClosed`). As `N` is normal, `G ⧸ N` acts on
  `M ⧸ N` through representatives (`MulAction.orbitRel.Quotient.instMulActionQuotientGroup`), and
  this residual action is smooth (`Subgroup.contMDiffSMul_orbitRelQuotientOfIsClosed`).
* **The faithful quotient of an action.** If `G` acts smoothly on `M` and the kernel `K` of the
  action is closed, as it is when `M` is Hausdorff (`TauCeti.isClosed_ker_toPermHom`), the
  quotient Lie group `G ⧸ K` acts smoothly and faithfully on `M` by `[g] • x = g • x`
  (`TauCeti.contMDiffSMul_quotientKerToPermHom`).

These are the groups and actions of symplectic reduction in stages: for a Hamiltonian action of
`G` and a closed normal subgroup `N`, the residual group `G ⧸ N`, with Lie algebra `𝔤 ⧸ 𝔫`, acts on
the space reduced by `N`. Quotients of tori by closed subgroups, such as the residual torus of
Delzant's construction, are further examples.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 21 (the
  homogeneous space construction theorem, and quotients of Lie groups by closed normal subgroups).
* J. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007 (the residual action of `G ⧸ N` on the
  space reduced by a normal subgroup).
-/

public section

noncomputable section

open Function Manifold TauCeti
open scoped ContDiff Manifold

namespace Subgroup

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {N : Subgroup G}

/-! ### The quotient Lie group -/

/-- **The quotient of a Lie group by a closed normal subgroup is a Lie group**, for the charts
`Subgroup.quotientChartedSpaceOfIsClosed`, since the projection `G → G ⧸ N` is a surjective
submersion (`Manifold.IsSubmersion.lieGroup`). -/
theorem lieGroup_quotientOfIsClosed [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    LieGroup 𝓘(ℝ, QuotientModelSpace I N) ∞ (G ⧸ N) :=
  letI := quotientChartedSpaceOfIsClosed I hN
  haveI := isManifold_quotientOfIsClosed (I := I) hN
  (isSubmersion_quotientMk (I := I) hN).lieGroup (QuotientGroup.mk' N) QuotientGroup.mk_surjective

variable (I) in
/-- The projection `G → G ⧸ N` onto the quotient by a closed normal subgroup, as a smooth
homomorphism. -/
def quotientMkSmoothHom [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    ContMDiffMonoidMorphism I 𝓘(ℝ, QuotientModelSpace I N) ∞ G (G ⧸ N) :=
  letI := quotientChartedSpaceOfIsClosed I hN
  { QuotientGroup.mk' N with contMDiff_toFun := contMDiff_quotientMk hN }

/-- The smooth projection onto `G ⧸ N` is the quotient map. -/
@[simp]
theorem coe_quotientMkSmoothHom [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    ⇑(quotientMkSmoothHom I hN) = (QuotientGroup.mk : G → G ⧸ N) :=
  (rfl)

/-- The smooth projection onto `G ⧸ N` is the quotient homomorphism. -/
@[simp]
theorem toMonoidHom_quotientMkSmoothHom [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    (quotientMkSmoothHom I hN).toMonoidHom = QuotientGroup.mk' N :=
  (rfl)

section Lift

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']

/-- **Smooth homomorphisms descend to the quotient Lie group.** The smooth homomorphism
`G ⧸ N → G'` through which a smooth homomorphism `φ : G → G'` vanishing on the closed normal
subgroup `N` factors. -/
def quotientLiftSmoothHom [N.Normal] (hN : IsClosed (N : Set G))
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : N ≤ φ.toMonoidHom.ker) :
    letI := quotientChartedSpaceOfIsClosed I hN
    ContMDiffMonoidMorphism 𝓘(ℝ, QuotientModelSpace I N) I' ∞ (G ⧸ N) G' :=
  letI := quotientChartedSpaceOfIsClosed I hN
  { QuotientGroup.lift N φ.toMonoidHom hφ with
    contMDiff_toFun := ((isSubmersion_quotientMk (I := I) hN).contMDiff_comp_iff
      QuotientGroup.mk_surjective le_rfl).1 φ.contMDiff_toFun }

/-- The descended homomorphism sends the class of `g` to `φ g`. -/
@[simp]
theorem quotientLiftSmoothHom_mk [N.Normal] (hN : IsClosed (N : Set G))
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : N ≤ φ.toMonoidHom.ker) (g : G) :
    letI := quotientChartedSpaceOfIsClosed I hN
    quotientLiftSmoothHom hN φ hφ (g : G ⧸ N) = φ g :=
  (rfl)

/-- **Uniqueness of the descended homomorphism.** A smooth homomorphism `G ⧸ N → G'` that sends
the class of every `g` to `φ g` is `Subgroup.quotientLiftSmoothHom`. -/
theorem eq_quotientLiftSmoothHom [N.Normal] (hN : IsClosed (N : Set G))
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : N ≤ φ.toMonoidHom.ker) :
    letI := quotientChartedSpaceOfIsClosed I hN
    ∀ ψ : ContMDiffMonoidMorphism 𝓘(ℝ, QuotientModelSpace I N) I' ∞ (G ⧸ N) G',
      (∀ g : G, ψ g = φ g) → ψ = quotientLiftSmoothHom hN φ hφ := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  intro ψ hψ
  refine DFunLike.ext _ _ fun x ↦ ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact hψ g

end Lift

/-! ### The Lie algebra of the quotient -/

/-- **The kernel of the Lie map of the projection onto `G ⧸ N` is the Lie algebra of `N`**, the
Lie subalgebra `TauCeti.Lie.lieSubalgebraOfSubgroup N` of the Lie algebra of `G`. -/
theorem lieMap_quotientMkSmoothHom_eq_zero_iff [N.Normal] (hN : IsClosed (N : Set G))
    (D : LeftInvariantDerivation I G) :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    lieMap (quotientMkSmoothHom I hN) D = 0 ↔ D ∈ Lie.lieSubalgebraOfSubgroup (I := I) N := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  have := FiniteDimensional.completeSpace ℝ E
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, QuotientModelSpace I N)) (n := ∞) (by simp)
      (1 : G ⧸ N))
  let eN := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint
      (I := 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule)) (n := ∞) (by simp)
      (1 : N))
  -- Read at the identity, the Lie maps of `π` and of the inclusion `N → G` are differentials.
  have hπ : e' (lieMap (quotientMkSmoothHom I hN) D) =
      mfderiv I 𝓘(ℝ, QuotientModelSpace I N) (QuotientGroup.mk : G → G ⧸ N) 1 (e D) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap (quotientMkSmoothHom I hN) D
  have hι (Y : LeftInvariantDerivation
      𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule) N) :
      e (lieMap d.subtypeVal Y) =
        mfderiv 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule) I
          (fun k : N ↦ 1 * (k : G)) 1 (eN Y) := by
    -- At the identity, `k ↦ 1 * k` is the inclusion of `N`.
    rw [mfderiv_congr (funext fun k : N ↦ (one_mul (k : G)).trans (d.subtypeVal_apply k).symm)]
    exact leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap d.subtypeVal Y
  -- The kernel of the differential of `π` at the identity is the tangent space of `N`.
  have hker : mfderiv I 𝓘(ℝ, QuotientModelSpace I N) (QuotientGroup.mk : G → G ⧸ N) 1 (e D) = 0 ↔
      ∃ w, mfderiv 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule) I
        (fun k : N ↦ 1 * (k : G)) 1 w = e D :=
    SetLike.ext_iff.1 (ker_mfderiv_quotientMk (I := I) hN 1) (e D)
  calc lieMap (quotientMkSmoothHom I hN) D = 0
      ↔ e' (lieMap (quotientMkSmoothHom I hN) D) = 0 := (map_eq_zero_iff e' e'.injective).symm
    _ ↔ ∃ w, mfderiv 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule) I
          (fun k : N ↦ 1 * (k : G)) 1 w = e D := by rw [hπ]; exact hker
    _ ↔ ∃ Y, d.lieMapSubtypeVal Y = D := by
        constructor
        · rintro ⟨w, hw⟩
          have h := hι (eN.symm w)
          rw [LieEquiv.apply_symm_apply, hw] at h
          exact ⟨eN.symm w, e.injective ((congrArg e (d.lieMapSubtypeVal_apply _)).trans h)⟩
        · rintro ⟨Y, rfl⟩
          refine ⟨eN Y, ?_⟩
          rw [d.lieMapSubtypeVal_apply, hι]
    _ ↔ D ∈ Lie.lieSubalgebraOfSubgroup (I := I) N :=
        (LieHom.mem_range _ _).symm.trans (SetLike.ext_iff.1 d.range_lieMapSubtypeVal_eq D)

/-- **The kernel of the Lie map of the projection onto `G ⧸ N` is the Lie algebra of `N`**, as an
equality of Lie subalgebras of the Lie algebra of `G`. -/
theorem toLieSubalgebra_ker_lieMap_quotientMkSmoothHom [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    (lieMap (quotientMkSmoothHom I hN)).ker.toLieSubalgebra =
      Lie.lieSubalgebraOfSubgroup (I := I) N := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  ext D
  exact LieHom.mem_ker.trans (lieMap_quotientMkSmoothHom_eq_zero_iff hN D)

/-- **The Lie map of the projection onto `G ⧸ N` is surjective.** With
`Subgroup.lieMap_quotientMkSmoothHom_eq_zero_iff`, it identifies the Lie algebra of `G ⧸ N` with
the quotient of the Lie algebra of `G` by that of `N`. -/
theorem surjective_lieMap_quotientMkSmoothHom [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    Surjective (lieMap (quotientMkSmoothHom I hN)) := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : T2Space (G ⧸ N) := 𝓘(ℝ, QuotientModelSpace I N).t2Space_of_lieGroup ∞
  have := FiniteDimensional.completeSpace ℝ E
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, QuotientModelSpace I N)) (n := ∞) (by simp)
      (1 : G ⧸ N))
  intro D'
  obtain ⟨w, hw⟩ := (isSubmersion_quotientMk (I := I) hN).surjective_mfderiv (by simp) 1 (e' D')
  refine ⟨e.symm w, e'.injective ?_⟩
  -- Read at the identity, the Lie map of `π` is the differential of `π`.
  have hπ : e' (lieMap (quotientMkSmoothHom I hN) (e.symm w)) =
      mfderiv I 𝓘(ℝ, QuotientModelSpace I N) (QuotientGroup.mk : G → G ⧸ N) 1 (e (e.symm w)) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap (quotientMkSmoothHom I hN) (e.symm w)
  rw [LieEquiv.apply_symm_apply, hw] at hπ
  exact hπ

variable (I) in
/-- **The Lie algebra of `G ⧸ N` is the quotient `𝔤 ⧸ 𝔫`**: the Lie map of the projection onto
`G ⧸ N` induces an isomorphism from the quotient of the Lie algebra of `G` by its kernel, which is
the Lie algebra of `N` (`Subgroup.toLieSubalgebra_ker_lieMap_quotientMkSmoothHom`). -/
def quotientLieAlgebraEquiv [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    (LeftInvariantDerivation I G ⧸ (lieMap (quotientMkSmoothHom I hN)).ker) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, QuotientModelSpace I N) (G ⧸ N) :=
  letI := quotientChartedSpaceOfIsClosed I hN
  haveI := lieGroup_quotientOfIsClosed (I := I) hN
  (lieMap (quotientMkSmoothHom I hN)).quotKerEquivOfSurjective
    (surjective_lieMap_quotientMkSmoothHom hN)

/-- The identification of the Lie algebra of `G ⧸ N` with `𝔤 ⧸ 𝔫` sends the class of `D` to its
image under the Lie map of the projection. -/
@[simp]
theorem quotientLieAlgebraEquiv_apply_mk [N.Normal] (hN : IsClosed (N : Set G))
    (D : LeftInvariantDerivation I G) :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    quotientLieAlgebraEquiv I hN (LieSubmodule.Quotient.mk D) =
      lieMap (quotientMkSmoothHom I hN) D :=
  LieHom.quotKerEquivOfSurjective_apply_mk _ _ D

/-! ### The exact sequence of tangent Lie algebras -/

section TangentLieAlgebra

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **The differential at the identity of the projection onto `G ⧸ N` is surjective**, as a map
`dπ : 𝔤 → Lie(G ⧸ N)` of tangent Lie algebras. -/
theorem surjective_groupLieAlgebraMap_mk' [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    Surjective ((QuotientGroup.mk' N).groupLieAlgebraMap I 𝓘(ℝ, QuotientModelSpace I N)) := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  intro v
  obtain ⟨w, hw⟩ := (isSubmersion_quotientMk (I := I) hN).surjective_mfderiv (by simp) 1 v
  exact ⟨w, by rw [MonoidHom.groupLieAlgebraMap_apply, QuotientGroup.coe_mk', hw]⟩

/-- **The kernel of `dπ : 𝔤 → Lie(G ⧸ N)` is the image of `dι : Lie(N) → 𝔤`**, for the projection
`π` onto `G ⧸ N` and the inclusion `ι` of `N` with any embedded-Lie-subgroup structure `d`, such as
the closed-subgroup structure `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`. With the
injectivity of `dι` (`TauCeti.Lie.EmbeddedLieSubgroupData.injective_mfderiv_subtypeVal`) and the
surjectivity of `dπ` (`Subgroup.surjective_groupLieAlgebraMap_mk'`), this is the short exact
sequence `0 → 𝔫 → 𝔤 → Lie(G ⧸ N) → 0` of tangent Lie algebras. -/
theorem ker_groupLieAlgebraMap_mk' [N.Normal] (hN : IsClosed (N : Set G))
    (d : Lie.EmbeddedLieSubgroupData I N E') :
    letI := quotientChartedSpaceOfIsClosed I hN
    letI := d.chartedSpace
    LinearMap.ker ((QuotientGroup.mk' N).groupLieAlgebraMap I
        𝓘(ℝ, QuotientModelSpace I N)).toLinearMap =
      LinearMap.range (N.subtype.groupLieAlgebraMap 𝓘(ℝ, E') I).toLinearMap := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ := d.chartedSpace
  let _ := d.lieGroup
  have := d.finiteDimensional
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, QuotientModelSpace I N)) (n := ∞) (by simp)
      (1 : G ⧸ N))
  let eN := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E')) (n := ∞) (by simp) (1 : N))
  -- Read at the identity, the Lie maps of `π` and of `ι` are the differentials `dπ` and `dι`.
  have hπ (D : LeftInvariantDerivation I G) :
      e'.symm ((QuotientGroup.mk' N).groupLieAlgebraMap I 𝓘(ℝ, QuotientModelSpace I N) (e D)) =
        lieMap (quotientMkSmoothHom I hN) D := by
    rw [← toMonoidHom_quotientMkSmoothHom (I := I) hN]
    exact leftInvariantDerivationLieEquivGroupLieAlgebra_symm_groupLieAlgebraMap _ D
  have hι (Y : LeftInvariantDerivation 𝓘(ℝ, E') N) :
      e.symm (N.subtype.groupLieAlgebraMap 𝓘(ℝ, E') I (eN Y)) = d.lieMapSubtypeVal Y := by
    rw [← d.toMonoidHom_subtypeVal, d.lieMapSubtypeVal_apply]
    exact leftInvariantDerivationLieEquivGroupLieAlgebra_symm_groupLieAlgebraMap _ Y
  ext ξ
  obtain ⟨D, rfl⟩ : ∃ D, e D = ξ := e.surjective ξ
  -- Both sides say that `D` lies in the Lie algebra of `N`, the range of the Lie map of `ι`.
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ← map_eq_zero_iff e'.symm e'.symm.injective, hπ, lieMap_quotientMkSmoothHom_eq_zero_iff hN,
    ← d.range_lieMapSubtypeVal_eq, LieHom.mem_range, LinearMap.mem_range,
    ContinuousLinearMap.coe_coe]
  exact ⟨fun ⟨Y, hY⟩ ↦ ⟨eN Y, e.symm_apply_eq.1 ((hι Y).trans hY)⟩,
    fun ⟨w, hw⟩ ↦ ⟨eN.symm w, by rw [← hι, eN.apply_symm_apply]; exact e.symm_apply_eq.2 hw⟩⟩

/-- **A normal subgroup acts trivially on `𝔤 ⧸ 𝔫`.** For `n ∈ N` and `ξ ∈ 𝔤`, the difference
`Ad_n ξ - ξ` lies in the image `𝔫` of the differential `dι` of the inclusion of `N`, for any
embedded-Lie-subgroup structure on `N`. Indeed `dπ (Ad_n ξ) = Ad_{π n} (dπ ξ) = dπ ξ` for the
projection `π` onto `G ⧸ N`, as `π n = 1`, and the kernel of `dπ` is the image of `dι`
(`Subgroup.ker_groupLieAlgebraMap_mk'`). -/
theorem adjointContinuousLinearMap_sub_self_mem_range_groupLieAlgebraMap_subtype [N.Normal]
    (d : Lie.EmbeddedLieSubgroupData I N E') {n : G} (hn : n ∈ N) (ξ : GroupLieAlgebra I G) :
    letI := d.chartedSpace
    Lie.adjointContinuousLinearMap (I := I) n ξ - ξ ∈
      LinearMap.range (N.subtype.groupLieAlgebraMap 𝓘(ℝ, E') I).toLinearMap := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have hN := d.isClosed
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  rw [← ker_groupLieAlgebraMap_mk' hN d, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub,
    MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap]
  simp [(QuotientGroup.eq_one_iff n).2 hn]

end TangentLieAlgebra

/-! ### The residual action on an orbit space -/

section Action

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul N M] [IsCancelSMul N M]

/-- **The residual action is smooth.** If `G` acts smoothly on `M` and the closed normal subgroup
`N` acts freely and properly, then the quotient Lie group `G ⧸ N` acts smoothly on the orbit
manifold `M ⧸ N`, by `[g] • [x] = [g • x]`. -/
theorem contMDiffSMul_orbitRelQuotientOfIsClosed [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := orbitRelQuotientChartedSpaceOfIsClosed I I' M hN
    ContMDiffSMul 𝓘(ℝ, QuotientModelSpace I N)
      𝓘(ℝ, ProperSMul.QuotientModelSpace (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule E')
      ∞ (G ⧸ N) (MulAction.orbitRel.Quotient N M) := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ := orbitRelQuotientChartedSpaceOfIsClosed I I' M hN
  have := isManifold_quotientOfIsClosed (I := I) hN
  have := isManifold_orbitRelQuotientOfIsClosed (I := I) (I' := I') (M := M) hN
  have hπ := isSubmersion_quotientMk (I := I) hN
  have hπM := isSubmersion_orbitRelQuotientMkOfIsClosed (I := I) (I' := I') (M := M) hN
  refine ⟨((hπ.prodMap hπM).contMDiff_comp_iff
    (QuotientGroup.mk_surjective.prodMap Quotient.mk_surjective) le_rfl).1 ?_⟩
  -- On representatives the residual action is the action of `G` on `M`.
  have hcomp : (fun p : (G ⧸ N) × MulAction.orbitRel.Quotient N M ↦ p.1 • p.2) ∘
      Prod.map (QuotientGroup.mk : G → G ⧸ N) (Quotient.mk (MulAction.orbitRel N M)) =
        Quotient.mk (MulAction.orbitRel N M) ∘ fun p : G × M ↦ p.1 • p.2 :=
    funext fun p ↦ MulAction.orbitRel.Quotient.mk_smul_mk N p.1 p.2
  rw [hcomp]
  exact hπM.contMDiff.comp contMDiff_smul

end Action

end Subgroup

/-! ### The faithful quotient of an action -/

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]

/-- **The faithful quotient of a smooth action acts smoothly.** If the Lie group `G` acts smoothly
on `M` and the kernel `K` of the action is closed, the quotient Lie group `G ⧸ K` acts smoothly on
`M` by `[g] • x = g • x`, and faithfully (`TauCeti.instFaithfulSMulQuotientKerToPermHom`). The
kernel is closed as soon as `M` is Hausdorff (`TauCeti.isClosed_ker_toPermHom`). -/
theorem contMDiffSMul_quotientKerToPermHom
    (hK : IsClosed ((MulAction.toPermHom G M).ker : Set G)) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hK
    ContMDiffSMul 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.toPermHom G M).ker) I' ∞
      (G ⧸ (MulAction.toPermHom G M).ker) M := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hK
  refine ⟨fun p ↦ ?_⟩
  -- Near `p`, a smooth local section `s` of `G → G ⧸ K` writes the action as `(q, x) ↦ s q • x`.
  obtain ⟨U, hU, hpU, s, hs, hmks⟩ := (Subgroup.isSubmersion_quotientMk (I := I) hK)
    |>.exists_contMDiffOn_section_of_surjective QuotientGroup.mk_surjective p.1
  have hEq : (fun q : (G ⧸ (MulAction.toPermHom G M).ker) × M ↦ s q.1 • q.2) =ᶠ[nhds p]
      fun q ↦ q.1 • q.2 := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)] with q hq
    rw [← quotientKerToPermHom_mk_smul, hmks q.1 hq]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hEq.symm
  exact contMDiff_smul.contMDiffAt.comp p
    (((hs.contMDiffAt (hU.mem_nhds hpU)).comp p contMDiffAt_fst).prodMk contMDiffAt_snd)

end TauCeti
