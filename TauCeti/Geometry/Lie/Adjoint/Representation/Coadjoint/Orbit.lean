/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.Quotient

import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# The homogeneous coadjoint orbit `G ⧸ G_ν`

Let `G` be a real Lie group with finite-dimensional boundaryless model and Lie algebra
`𝔤 = GroupLieAlgebra I G`, and fix `ν ∈ 𝔤*`. Its coadjoint stabilizer
`G_ν = {g | Ad*_g ν = ν}` is a closed subgroup
(`TauCeti.Lie.isClosed_stabilizer_coadjointRepresentation`), so the coset space `G ⧸ G_ν` is a
smooth manifold, the homogeneous space of `Subgroup.quotientChartedSpaceOfIsClosed`, on which `G`
acts smoothly by left multiplication. This file installs that structure as instances: the coadjoint
orbit of `ν` with its intrinsic homogeneous smooth structure, whose points are cosets rather than
covectors.

The vertical directions of the projection `π : G → G ⧸ G_ν` at `g` are the left translate
`d(L_g)(𝔤_ν)` of the infinitesimal stabilizer `𝔤_ν = {ξ | ⁅ξ, ν⁆ = 0}`, the Lie algebra of `G_ν`.
The map `[g] ↦ Ad*_g ν` (`Module.Dual.coadjointOrbitMap`) is well defined on cosets of `G_ν`,
injective, `G`-equivariant for the coadjoint action, smooth in each component, and its image is the
orbit of `ν` in `𝔤*`.

The Kirillov–Kostant–Souriau form on `G ⧸ G_ν` and the moment-map property of the orbit map are in
`TauCeti.Geometry.Symplectic.Coadjoint.Orbit`.

## Main definitions

* `Module.Dual.coadjointOrbitMap ν`: the orbit map `[g] ↦ Ad*_g ν` into `𝔤*`.

## Main results

* `Module.Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation`: the projection
  `G → G ⧸ G_ν` is a smooth submersion.
* `Module.Dual.finrank_quotientModelSpace_add_finrank_lieAnnihilator`: the orbit has dimension
  `dim 𝔤 - dim 𝔤_ν`.
* `Module.Dual.finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator`: the orbit has the
  dimension of its algebraic tangent model `𝔤 ⧸ 𝔤_ν`.
* `Module.Dual.ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation`: the vertical
  directions of `G → G ⧸ G_ν` at `g` are `d(L_g)(𝔤_ν)`.
* `Module.Dual.injective_coadjointOrbitMap`, `Module.Dual.coadjointOrbitMap_smul`,
  `Module.Dual.range_coadjointOrbitMap`: the orbit map is an injective equivariant map onto the
  orbit of `ν`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.17 (the
  homogeneous space construction theorem).
-/

public section

noncomputable section

open Function Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace Module.Dual

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {ν : Module.Dual ℝ (GroupLieAlgebra I G)}

/-! ### The homogeneous orbit manifold -/

/-- **The charts of a coadjoint orbit.** The coadjoint stabilizer `G_ν` is closed, so `G ⧸ G_ν`
carries the charts of the homogeneous space of a closed subgroup, modelled on
`ℝ^(dim G - dim G_ν)`. -/
instance instChartedSpaceQuotientStabilizer :
    ChartedSpace (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  Subgroup.quotientChartedSpaceOfIsClosed I (isClosed_stabilizer_coadjointRepresentation I ν)

/-- A coadjoint orbit `G ⧸ G_ν` is a smooth manifold. -/
instance instIsManifoldQuotientStabilizer :
    IsManifold 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      ∞ (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  Subgroup.isManifold_quotientOfIsClosed (isClosed_stabilizer_coadjointRepresentation I ν)

/-- `G` acts smoothly on its coadjoint orbit `G ⧸ G_ν` by left multiplication. -/
instance instContMDiffSMulQuotientStabilizer :
    ContMDiffSMul I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞ G
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  Subgroup.contMDiffSMul_quotientOfIsClosed (isClosed_stabilizer_coadjointRepresentation I ν)

variable (ν)

/-- The projection `G → G ⧸ G_ν` onto a coadjoint orbit is a smooth submersion. -/
theorem isSubmersion_quotientMk_stabilizer_coadjointRepresentation :
    IsSubmersion I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  Subgroup.isSubmersion_quotientMk (isClosed_stabilizer_coadjointRepresentation I ν)

/-- **The dimension of a coadjoint orbit.** The model space of `G ⧸ G_ν` and the infinitesimal
stabilizer `𝔤_ν` have dimensions adding up to `dim 𝔤`. -/
theorem finrank_quotientModelSpace_add_finrank_lieAnnihilator :
    finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) +
      finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν) = finrank ℝ E := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have h := Subgroup.finrank_quotientModelSpace_add_finrank_lieSubalgebraOfSubgroup I _
    (isClosed_stabilizer_coadjointRepresentation I ν)
  -- A Lie subalgebra has the dimension of its underlying submodule.
  have hK : finrank ℝ (lieSubalgebraOfSubgroup (I := I)
      ((coadjointRepresentation ℝ I G).stabilizer ν)).toSubmodule =
        finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν) :=
    finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation
      BoundarylessManifold.isInteriorPoint
  omega

/-- **The tangent model of a coadjoint orbit.** The model space of `G ⧸ G_ν` has the dimension of
the algebraic tangent model `𝔤 ⧸ 𝔤_ν`. -/
theorem finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator :
    finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) =
      finrank ℝ (GroupLieAlgebra I G ⧸ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule) := by
  have h := ν.finrank_quotientModelSpace_add_finrank_lieAnnihilator
  have hq := Submodule.finrank_quotient_add_finrank
    (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule
  -- `𝔤 = GroupLieAlgebra I G` is the model space `E`, and a Lie subalgebra has the dimension of
  -- its underlying submodule.
  have hE : finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E := rfl
  have hS : finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule =
      finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν) := rfl
  omega

variable {ν}

/-- **The vertical directions of a coadjoint orbit.** The kernel of the differential at `g` of the
projection `G → G ⧸ G_ν` is the left translate `d(L_g)(𝔤_ν)` of the infinitesimal stabilizer
`𝔤_ν = {ξ | ⁅ξ, ν⁆ = 0}`. -/
theorem ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation (g : G) :
    (mfderiv I 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g).ker =
      mulInvariantDistribution (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule g :=
  have : T2Space G := I.t2Space_of_lieGroup ∞
  Subgroup.ker_mfderiv_quotientMk_eq_mulInvariantDistribution
    (isClosed_stabilizer_coadjointRepresentation I ν)
    (fun _ hξ ↦ mulInvariantExp_smul_mem_stabilizer_coadjointRepresentation_iff.2 hξ)
    (finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation
      BoundarylessManifold.isInteriorPoint).symm g

/-! ### The orbit map -/

variable (ν)

/-- **The orbit map** `[g] ↦ Ad*_g ν` from the coadjoint orbit `G ⧸ G_ν` to `𝔤*`. It is well
defined because `G_ν` fixes `ν`. -/
def coadjointOrbitMap :
    G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν → Module.Dual ℝ (GroupLieAlgebra I G) :=
  Quotient.lift (fun g : G ↦ coadjointRepresentation ℝ I G g ν) fun a b hab ↦ by
    rw [← mul_inv_cancel_left a b, map_mul, mul_apply_eq_comp,
      Representation.mem_stabilizer.1 (QuotientGroup.leftRel_apply.1 hab)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
@[simp]
theorem coadjointOrbitMap_mk (g : G) :
    ν.coadjointOrbitMap g = coadjointRepresentation ℝ I G g ν :=
  (rfl)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The orbit map is equivariant for the coadjoint action. -/
theorem coadjointOrbitMap_smul (g : G) (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    ν.coadjointOrbitMap (g • x) = coadjointRepresentation ℝ I G g (ν.coadjointOrbitMap x) := by
  induction x using QuotientGroup.induction_on with
  | H h => rw [MulAction.Quotient.smul_coe, coadjointOrbitMap_mk, coadjointOrbitMap_mk, smul_eq_mul,
      map_mul, mul_apply_eq_comp]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **The orbit map is injective**: `Ad*_a ν = Ad*_b ν` exactly when `a⁻¹ b` stabilizes `ν`. -/
theorem injective_coadjointOrbitMap : Function.Injective ν.coadjointOrbitMap := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  rw [coadjointOrbitMap_mk, coadjointOrbitMap_mk] at hxy
  refine QuotientGroup.eq.2 (Representation.mem_stabilizer.2 ?_)
  rw [map_mul, mul_apply_eq_comp, ← hxy, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The image of the orbit map is the coadjoint orbit `{Ad*_g ν | g ∈ G}` of `ν` in `𝔤*`. -/
theorem range_coadjointOrbitMap :
    Set.range ν.coadjointOrbitMap = Set.range fun g : G ↦ coadjointRepresentation ℝ I G g ν :=
  (QuotientGroup.mk_surjective.range_comp ν.coadjointOrbitMap).symm

/-- Each component `[g] ↦ (Ad*_g ν) ξ` of the orbit map is smooth. -/
theorem contMDiff_coadjointOrbitMap_apply (ξ : GroupLieAlgebra I G) :
    ContMDiff 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      𝓘(ℝ) ∞ fun x ↦ ν.coadjointOrbitMap x ξ :=
  (ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff_comp_iff
    QuotientGroup.mk_surjective le_rfl).1 (contMDiff_coadjointRepresentation_apply ν ξ)

end Module.Dual
