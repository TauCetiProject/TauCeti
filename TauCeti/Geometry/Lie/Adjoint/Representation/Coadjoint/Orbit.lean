/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.RepresentationTheory.Stabilizer

import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# The homogeneous coadjoint orbit `G ⧸ G_ν`

Let `G` be a real Lie group with finite-dimensional boundaryless model and Lie algebra
`𝔤 = GroupLieAlgebra I G`, and fix `ν ∈ 𝔤*`. Its coadjoint stabilizer
`G_ν = {g | Ad*_g ν = ν}` is a closed subgroup
(`TauCeti.Lie.isClosed_stabilizer_coadjointRepresentation`), so the coset space `G ⧸ G_ν` is a
Hausdorff smooth manifold, the homogeneous space of `Subgroup.quotientChartedSpaceOfIsClosed`, on
which `G` acts smoothly by left multiplication. This file installs that structure as instances:
the coadjoint orbit of `ν` with its intrinsic homogeneous smooth structure, whose points are cosets
rather than covectors.

The vertical directions of the projection `π : G → G ⧸ G_ν` at `g` are the left translate
`d(L_g)(𝔤_ν)` of the infinitesimal stabilizer `𝔤_ν = {ξ | ⁅ξ, ν⁆ = 0}`, the Lie algebra of `G_ν`.
The orbit map `[g] ↦ Ad*_g ν` of the coadjoint representation
(`Representation.orbitMap`, applied to `coadjointRepresentation ℝ I G` and `ν`) is well defined on
cosets of `G_ν`, injective, `G`-equivariant for the coadjoint action, and its image is the orbit of
`ν` in `𝔤*` (`TauCeti.RepresentationTheory.Stabilizer`); it is smooth in each component
(`Module.Dual.contMDiff_orbitMap_coadjointRepresentation_apply`).

The Kirillov–Kostant–Souriau form on `G ⧸ G_ν` and the moment-map property of the orbit map are in
`TauCeti.Geometry.Symplectic.Coadjoint.Orbit`.

## Main results

* `Module.Dual.isSubmersion_quotientMk_stabilizer_coadjointRepresentation`: the projection
  `G → G ⧸ G_ν` is a smooth submersion.
* `Module.Dual.finrank_quotientModelSpace_add_finrank_lieAnnihilator`: the orbit has dimension
  `dim 𝔤 - dim 𝔤_ν`.
* `Module.Dual.finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator`: the orbit has the
  dimension of its algebraic tangent model `𝔤 ⧸ 𝔤_ν`.
* `Module.Dual.ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation`: the vertical
  directions of `G → G ⧸ G_ν` at `g` are `d(L_g)(𝔤_ν)`.
* `Module.Dual.contMDiff_orbitMap_coadjointRepresentation_apply`: each component of the orbit map
  `[g] ↦ Ad*_g ν` is smooth.
* `Module.Dual.contMDiff_orbitMap_coadjointRepresentation_components`: the components of the
  orbit map in a basis of `𝔤` form a smooth map to `κ → ℝ`.

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

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- A coadjoint orbit `G ⧸ G_ν` is Hausdorff, as the quotient of a topological group by the closed
subgroup `G_ν`. -/
instance instT2SpaceQuotientStabilizer :
    T2Space (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := isClosed_stabilizer_coadjointRepresentation I ν
  QuotientGroup.instT2Space

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
  have hE : finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E := finrank_tangentSpace (1 : G)
  -- A Lie subalgebra has the dimension of its underlying submodule.
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

/-- Each component `[g] ↦ (Ad*_g ν) ξ` of the orbit map of the coadjoint representation is
smooth. -/
theorem contMDiff_orbitMap_coadjointRepresentation_apply (ξ : GroupLieAlgebra I G) :
    ContMDiff 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      𝓘(ℝ) ∞ fun x ↦ (coadjointRepresentation ℝ I G).orbitMap ν x ξ :=
  (ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff_comp_iff
    QuotientGroup.mk_surjective le_rfl).1 (by
      simpa only [comp_def, Representation.orbitMap_mk] using
        contMDiff_coadjointRepresentation_apply ν ξ)

/-- The components `[g] ↦ ((Ad*_g ν) (b i))ᵢ` of the orbit map of the coadjoint representation in a
basis `b` of `𝔤` form a smooth map to `κ → ℝ`. -/
theorem contMDiff_orbitMap_coadjointRepresentation_components {κ : Type*} [Fintype κ]
    (b : Basis κ ℝ (GroupLieAlgebra I G)) :
    ContMDiff 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      𝓘(ℝ, κ → ℝ) ∞ fun x i ↦ (coadjointRepresentation ℝ I G).orbitMap ν x (b i) :=
  contMDiff_pi_module_iff.2 fun i ↦ ν.contMDiff_orbitMap_coadjointRepresentation_apply (b i)

end Module.Dual
