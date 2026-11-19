/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.Geometry.Symplectic.Coadjoint.LieGroup
public import TauCeti.Geometry.Symplectic.Manifold.Descent

import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Symplectic.Coadjoint
import TauCeti.Geometry.Lie.FundamentalVectorField
import TauCeti.Geometry.Lie.RightInvariantVectorField

/-!
# The Kirillov–Kostant–Souriau form on a homogeneous coadjoint orbit

Let `G` be a real Lie group with finite-dimensional boundaryless model and Lie algebra
`𝔤 = GroupLieAlgebra I G`, and fix `ν ∈ 𝔤*`. Its coadjoint stabilizer
`G_ν = {g | Ad*_g ν = ν}` is a closed subgroup
(`TauCeti.Lie.isClosed_stabilizer_coadjointRepresentation`), so the coset space `G ⧸ G_ν` is a
smooth manifold, the homogeneous space of `Subgroup.quotientChartedSpaceOfIsClosed`, on which `G`
acts smoothly by left multiplication. This file installs that structure as instances and makes
`G ⧸ G_ν` a symplectic manifold: the coadjoint orbit of `ν` with its intrinsic homogeneous smooth
structure, whose points are cosets rather than covectors.

**The KKS form.** The left-invariant Kirillov form `σ_ν` on `G`
(`Module.Dual.leftInvariantKirillovForm`), with `σ_ν(ξ^L, η^L) = ν ⁅ξ, η⁆` for left-invariant
vector fields, is closed and invariant under right translation by `G_ν`, and its kernel at `g` is
the left translate `d(L_g)(𝔤_ν)` of the infinitesimal stabilizer `𝔤_ν = {ξ | ⁅ξ, ν⁆ = 0}`.
That translate is exactly the kernel of the differential of the projection `π : G → G ⧸ G_ν`
(`Module.Dual.ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation`): the curves
`t ↦ g exp (t ξ)` with `ξ ∈ 𝔤_ν` stay in the coset `g G_ν`, and both spaces have the dimension of
`𝔤_ν`, the Lie algebra of `G_ν`. Hence `σ_ν` is basic for `π` and descends to a unique two-form
`ω_ν` on `G ⧸ G_ν` with `π^* ω_ν = σ_ν` (`Module.Dual.coadjointOrbitForm`), which is symplectic
(`Module.Dual.isSymplectic_coadjointOrbitForm`) and invariant under the action of `G`.

**The orbit map.** The map `[g] ↦ Ad*_g ν` (`Module.Dual.coadjointOrbitMap`) is well defined on
cosets of `G_ν`, injective, `G`-equivariant for the coadjoint action, and its image is the orbit of
`ν` in `𝔤*`. It is a coadjoint-equivariant moment map of `ω_ν` for the action of `G`
(`Module.Dual.isEquivariantMomentMap_coadjointOrbitForm`), in the conventions
`d⟨μ, ξ⟩ = ι_(ξ_O) ω_ν` and `μ (g • x) = Ad*_g (μ x)`. Consequently `ω_ν` takes the defining
KKS values on generators,

`ω_ν(ξ_O, η_O) = μ ⁅ξ, η⁆` at the point `μ` of the orbit,

(`Module.Dual.eval₂_coadjointOrbitForm_fundamentalVectorField`), in particular `ν ⁅ξ, η⁆` at the
coset of the identity, and the differential of the orbit map in the direction `ξ_O` is the
infinitesimal coadjoint action. The differential of the orbit map is injective at every point
(`Module.Dual.injective_differential_coadjointOrbitMap`), so the orbit map is an injective
immersion into `𝔤*`. The orbit has dimension `dim 𝔤 - dim 𝔤_ν`, which is even.

## Main definitions

* `Module.Dual.coadjointOrbitForm ν`: the Kirillov–Kostant–Souriau form on `G ⧸ G_ν`.
* `Module.Dual.coadjointOrbitMap ν`: the orbit map `[g] ↦ Ad*_g ν` into `𝔤*`.

## Main results

* `Module.Dual.ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation`: the vertical
  directions of `G → G ⧸ G_ν` at `g` are `d(L_g)(𝔤_ν)`.
* `Module.Dual.mpullback_quotientMk_coadjointOrbitForm`, `Module.Dual.eq_coadjointOrbitForm_iff`:
  `ω_ν` is the unique two-form pulling back to `σ_ν`.
* `Module.Dual.isSymplectic_coadjointOrbitForm`: `ω_ν` is symplectic.
* `Module.Dual.mpullback_smul_coadjointOrbitForm`: `G` acts by symplectomorphisms.
* `Module.Dual.isEquivariantMomentMap_coadjointOrbitForm`: the orbit map is an equivariant moment
  map.
* `Module.Dual.eval₂_coadjointOrbitForm_fundamentalVectorField`: `ω_ν(ξ_O, η_O) = μ ⁅ξ, η⁆`.
* `Module.Dual.injective_differential_coadjointOrbitMap`: the orbit map is an immersion.
* `Module.Dual.finrank_quotientModelSpace_add_finrank_lieAnnihilator`,
  `Module.Dual.even_finrank_quotientModelSpace`: the dimension of the orbit.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22 (coadjoint orbits and their moment maps).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 14 (the KKS form and its pullback to the group).
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
private theorem isSubmersion_quotientMk :
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

/-- **A coadjoint orbit has even dimension.** Its dimension `dim 𝔤 - dim 𝔤_ν` is that of the
algebraic tangent model `𝔤 ⧸ 𝔤_ν`, which carries the nondegenerate alternating form
`[ξ], [η] ↦ ν ⁅ξ, η⁆`. -/
theorem even_finrank_quotientModelSpace :
    Even (finrank ℝ
      (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))) := by
  have h := ν.finrank_quotientModelSpace_add_finrank_lieAnnihilator
  have hq := Submodule.finrank_quotient_add_finrank
    (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule
  have he := even_finrank_quotient_lieAnnihilator ν
  -- `𝔤 = GroupLieAlgebra I G` is the model space `E`, and a Lie subalgebra has the dimension of
  -- its underlying submodule.
  have hE : finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E := rfl
  have hS : finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule =
      finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν) := rfl
  rwa [show finrank ℝ (GroupLieAlgebra I G ⧸ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule)
    = finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
    by omega] at he

variable {ν}

/-- The left-invariant directions of the infinitesimal stabilizer are vertical for the projection
onto the coadjoint orbit: for `ξ ∈ 𝔤_ν`, the curve `t ↦ g exp (t ξ)` has velocity `ξ^L(g)` and stays
in the coset `g G_ν`. -/
theorem mfderiv_quotientMk_mulInvariantVectorField {ξ : GroupLieAlgebra I G}
    (hξ : ξ ∈ lieAnnihilator ℝ (GroupLieAlgebra I G) ν) (g : G) :
    mfderiv I 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g
        (mulInvariantVectorField ξ g) = 0 := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have hL : HasMFDerivAt I I (g * ·) (mulInvariantExp (I := I) ((0 : ℝ) • ξ))
      (mfderiv I I (g * ·) 1) := by
    rw [zero_smul, mulInvariantExp_zero]
    exact ((contMDiff_mul_left (I := I) (n := ∞)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hc := hL.comp (0 : ℝ) (hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) ξ)
  have hconst : (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) ∘
      ((g * ·) ∘ fun t : ℝ ↦ mulInvariantExp (I := I) (t • ξ)) = fun _ ↦ (g : G ⧸ _) :=
    funext fun t ↦ QuotientGroup.mk_mul_of_mem g
      (mulInvariantExp_smul_mem_stabilizer_coadjointRepresentation_iff.2 hξ t)
  have hπ : MDifferentiableAt I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g :=
    ν.isSubmersion_quotientMk.contMDiff.mdifferentiableAt (by simp)
  have hy : ((g * ·) ∘ fun t : ℝ ↦ mulInvariantExp (I := I) (t • ξ)) 0 = g := by simp
  have h := mfderiv_comp_apply_of_eq (0 : ℝ) hπ hc.mdifferentiableAt hy (1 : ℝ)
  rw [hconst, mfderiv_const, hc.mfderiv] at h
  -- The composite applied to the unit tangent vector `1` of `ℝ` is `dπ_g (d(L_g)_1 (1 • ξ))`, and
  -- `d(L_g)_1 (1 • ξ)` is `(1 • ξ)^L(g)` by definition of the invariant vector field.
  have h' : mfderiv I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g
        (mulInvariantVectorField ((1 : ℝ) • ξ) g) = 0 :=
    h.symm
  rwa [one_smul] at h'

/-- **The vertical directions of a coadjoint orbit.** The kernel of the differential at `g` of the
projection `G → G ⧸ G_ν` is the left translate `d(L_g)(𝔤_ν)` of the infinitesimal stabilizer
`𝔤_ν = {ξ | ⁅ξ, ν⁆ = 0}`. -/
theorem ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation (g : G) :
    (mfderiv I 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g).ker =
      mulInvariantDistribution (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule g := by
  refine (Submodule.eq_of_le_of_finrank_eq (fun v hv ↦ ?_) ?_).symm
  · obtain ⟨ξ, hξ, rfl⟩ := mem_mulInvariantDistribution.1 hv
    exact mfderiv_quotientMk_mulInvariantVectorField hξ g
  -- Both spaces have the dimension of `𝔤_ν`: left translation is injective, and the projection is
  -- a submersion onto a manifold of dimension `dim 𝔤 - dim 𝔤_ν`.
  have hinj : Function.Injective
      (mfderiv I I (g * ·) 1 : GroupLieAlgebra I G →L[ℝ] TangentSpace I g) :=
    LeftInverse.injective fun w ↦ mfderiv_inv_mul_mulInvariantVectorField (I := I) w g
  have hmap : mulInvariantDistribution (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule g =
      (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule.map
        (mfderiv I I (g * ·) 1 : GroupLieAlgebra I G →L[ℝ] TangentSpace I g).toLinearMap := by
    ext v
    rw [mem_mulInvariantDistribution]
    exact Iff.rfl
  have hdist : finrank ℝ (mulInvariantDistribution
      (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule g) =
        finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν) := by
    rw [hmap]
    exact ((Submodule.equivMapOfInjective _ hinj _).finrank_eq).symm
  have hrange := LinearMap.finrank_range_add_finrank_ker
    (mfderiv I 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g).toLinearMap
  rw [LinearMap.range_eq_top.2 (ν.isSubmersion_quotientMk.surjective_mfderiv (by simp) g),
    finrank_top] at hrange
  have hdim := ν.finrank_quotientModelSpace_add_finrank_lieAnnihilator
  -- The tangent spaces are the model spaces.
  have hT : finrank ℝ (TangentSpace I g) = finrank ℝ E := rfl
  have hQ : finrank ℝ (TangentSpace
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (g : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)) =
        finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) :=
    rfl
  rw [hdist]
  omega

/-- The kernel of the left-invariant Kirillov form of `ν` at `g` is the kernel of the differential
of the projection onto the coadjoint orbit `G ⧸ G_ν`. -/
theorem ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv (g : G) :
    LinearMap.ker (ν.leftInvariantKirillovForm.bilinFormAt g) =
      (mfderiv I
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g).ker := by
  rw [ker_bilinFormAt_leftInvariantKirillovForm,
    ker_mfderiv_quotientMk_stabilizer_coadjointRepresentation]

variable (ν)

/-- **The left-invariant Kirillov form is basic** for the projection `G → G ⧸ G_ν`: it is invariant
under right translation by `G_ν`, which acts transitively on the fibres, and vertical vectors lie in
its kernel. -/
theorem isBasic_leftInvariantKirillovForm :
    RoughForm.IsBasic (V := ℝ)
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
      ν.leftInvariantKirillovForm.1 := by
  refine RoughForm.isBasic_of_mpullback_eq
    (σ := fun h : (coadjointRepresentation ℝ I G).stabilizer ν ↦ (· * (h : G)))
    (ν.isSubmersion_quotientMk.contMDiff.mdifferentiable (by simp))
    (fun h ↦ (contMDiff_mul_right (I := I) (n := ∞)).mdifferentiable (by simp))
    (fun h ↦ funext fun g ↦ QuotientGroup.mk_mul_of_mem g h.2)
    (fun x y hxy ↦ .inr ⟨⟨x⁻¹ * y, QuotientGroup.eq.1 hxy⟩, mul_inv_cancel_left x y⟩)
    (fun x v j hj ↦ ?_) fun h ↦ ?_
  · -- A vertical vector lies in the kernel of the form.
    have hnull (u w : TangentSpace I x) (hu : mfderiv I
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) x u = 0) :
        SmoothBundleForm.eval₂ ν.leftInvariantKirillovForm x u w = 0 := by
      have hu' : u ∈ LinearMap.ker (ν.leftInvariantKirillovForm.bilinFormAt x) := by
        rw [ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv]
        exact hu
      rw [← SmoothForm.bilinFormAt_apply, LinearMap.mem_ker.1 hu', LinearMap.zero_apply]
    have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
    rw [hv, ← SmoothBundleForm.eval₂_apply]
    obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · exact hnull _ _ hj
    · rw [SmoothBundleForm.eval₂_swap, hnull _ _ hj, neg_zero]
  · simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val
      (ν.mpullback_mul_right_leftInvariantKirillovForm_of_mem_stabilizer h.2)

/-! ### The Kirillov–Kostant–Souriau form -/

/-- **The Kirillov–Kostant–Souriau form** `ω_ν` on the coadjoint orbit `G ⧸ G_ν`: the descent of
the left-invariant Kirillov form `σ_ν` along the projection `G → G ⧸ G_ν`, the unique two-form with
`π^* ω_ν = σ_ν` (`Module.Dual.eq_coadjointOrbitForm_iff`). On generators it is
`ω_ν(ξ_O, η_O) = μ ⁅ξ, η⁆` at the point `μ` of the orbit
(`Module.Dual.eval₂_coadjointOrbitForm_fundamentalVectorField`). -/
def coadjointOrbitForm :
    SmoothTwoForm 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  SmoothForm.descendedForm ν.isSubmersion_quotientMk QuotientGroup.mk_surjective
    ν.leftInvariantKirillovForm ν.isBasic_leftInvariantKirillovForm

/-- The KKS form pulls back to the left-invariant Kirillov form along the projection
`G → G ⧸ G_ν`. -/
@[simp]
theorem mpullback_quotientMk_coadjointOrbitForm
    (hπ : ContMDiff I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)) :
    SmoothForm.mpullback QuotientGroup.mk hπ ν.coadjointOrbitForm = ν.leftInvariantKirillovForm :=
  SmoothForm.mpullback_descendedForm

/-- **Uniqueness of the KKS form**: it is the only two-form on `G ⧸ G_ν` pulling back to the
left-invariant Kirillov form along the projection. -/
theorem eq_coadjointOrbitForm_iff
    {η : SmoothTwoForm
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)}
    (hπ : ContMDiff I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)) :
    η = ν.coadjointOrbitForm ↔ SmoothForm.mpullback QuotientGroup.mk hπ η =
      ν.leftInvariantKirillovForm :=
  SmoothForm.eq_descendedForm_iff

/-- The KKS form evaluates on images under the differential of the projection `G → G ⧸ G_ν` as
the left-invariant Kirillov form: `ω_ν(dπ v, dπ w) = σ_ν(v, w)`. -/
theorem eval₂_coadjointOrbitForm_mfderiv (g : G) (v w : TangentSpace I g) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm
        (g : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (mfderiv I
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          QuotientGroup.mk g v)
        (mfderiv I
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
          QuotientGroup.mk g w) =
      SmoothBundleForm.eval₂ ν.leftInvariantKirillovForm g v w :=
  SmoothTwoForm.eval₂_descendedForm_mfderiv g v w

/-- **The KKS form is symplectic.** It is closed because `σ_ν` is exact, and nondegenerate because
the kernel of `σ_ν` is exactly the kernel of the differential of the projection. -/
theorem isSymplectic_coadjointOrbitForm : ν.coadjointOrbitForm.IsSymplectic :=
  SmoothTwoForm.isSymplectic_descendedForm_iff.2
    ⟨ν.isClosed_leftInvariantKirillovForm, ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv⟩

/-- **`G` acts on its coadjoint orbit by symplectomorphisms**: left translation by `g` preserves the
KKS form. -/
@[simp]
theorem mpullback_smul_coadjointOrbitForm (g : G)
    (hg : ContMDiff
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      fun x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν ↦ g • x) :
    SmoothForm.mpullback (g • ·) hg ν.coadjointOrbitForm = ν.coadjointOrbitForm := by
  have hπ := ν.isSubmersion_quotientMk.contMDiff
  rw [eq_coadjointOrbitForm_iff ν hπ, SmoothForm.mpullback_mpullback_of_comp_eq hπ hg
    contMDiff_mul_left hπ (funext fun h ↦ MulAction.Quotient.smul_coe _ g h),
    mpullback_quotientMk_coadjointOrbitForm, mpullback_mul_left_leftInvariantKirillovForm]

/-! ### The orbit map -/

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

/-- **The orbit map is a moment map.** For the action of `G` on its coadjoint orbit by left
multiplication, the orbit map `[g] ↦ Ad*_g ν` is a coadjoint-equivariant moment map of the KKS
form: `d⟨μ, ξ⟩ = ι_(ξ_O) ω_ν`. This is the moment map `g ↦ Ad*_g ν` of `σ_ν` on `G`
(`Module.Dual.isEquivariantMomentMap_leftInvariantKirillovForm`), descended along the projection. -/
theorem isEquivariantMomentMap_coadjointOrbitForm :
    ν.coadjointOrbitForm.IsEquivariantMomentMap ν.coadjointOrbitMap where
  contMDiff ξ := (ν.isSubmersion_quotientMk.contMDiff_comp_iff QuotientGroup.mk_surjective le_rfl).1
    (contMDiff_coadjointRepresentation_apply ν ξ)
  isHamiltonianVectorField ξ := SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
    have : T2Space G := I.t2Space_of_lieGroup ∞
    have hπ := ν.isSubmersion_quotientMk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u, rfl⟩ := hπ.surjective_mfderiv (by simp) g v
    have hcomp : (fun y ↦ ν.coadjointOrbitMap y ξ) ∘ QuotientGroup.mk =
        fun h : G ↦ coadjointRepresentation ℝ I G h ν ξ := rfl
    have hF : ContMDiff
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) 𝓘(ℝ) ∞
        fun y ↦ ν.coadjointOrbitMap y ξ :=
      (hπ.contMDiff_comp_iff QuotientGroup.mk_surjective le_rfl).1
        (contMDiff_coadjointRepresentation_apply ν ξ)
    -- The generator `ξ_O([g])` is the image of the generator `ξ_G(g)` of left multiplication.
    rw [InfinitesimalAction.fundamental_apply,
      ← mfderiv_fundamentalVectorField_of_map_smul (hπ.contMDiff.mdifferentiableAt (by simp))
        ((contMDiff_mul_right (I := I) (n := ∞)).mdifferentiableAt (by simp)) (fun _ ↦ rfl) ξ,
      eval₂_coadjointOrbitForm_mfderiv, ← mvfderiv_comp_apply g
        (hF.mdifferentiableAt (by simp)) (hπ.contMDiff.mdifferentiableAt (by simp)), hcomp,
      ← InfinitesimalAction.fundamental_apply]
    exact ν.isEquivariantMomentMap_leftInvariantKirillovForm.eval₂_apply ξ g u
  apply_smul := ν.coadjointOrbitMap_smul

/-- **The KKS form on generators.** At a point `x` of the coadjoint orbit with image
`μ = Ad*_g ν` in `𝔤*`, the KKS form pairs the generators of `ξ` and `η` to `μ ⁅ξ, η⁆`; at the coset
of the identity this is the Kirillov form `ν ⁅ξ, η⁆`. -/
theorem eval₂_coadjointOrbitForm_fundamentalVectorField
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) (ξ η : GroupLieAlgebra I G) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm x
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ξ x)
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) η x) =
      ν.coadjointOrbitMap x ⁅ξ, η⁆ := by
  simpa only [InfinitesimalAction.fundamental_apply] using SmoothTwoForm.momentCocycle_eq_zero_iff.1
    (ν.isEquivariantMomentMap_coadjointOrbitForm.momentCocycle_eq_zero x) ξ η

/-- **The derivative of the orbit map along generators**: in the direction `ξ_O`, the component
`⟨μ, η⟩` of the orbit map changes at the rate `μ ⁅η, ξ⁆`. -/
theorem mvfderiv_coadjointOrbitMap_apply_fundamentalVectorField
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) (ξ η : GroupLieAlgebra I G) :
    mvfderiv 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ ν.coadjointOrbitMap y η) x
        (fundamentalVectorField
          𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ξ x) =
      ν.coadjointOrbitMap x ⁅η, ξ⁆ := by
  rw [← ν.isEquivariantMomentMap_coadjointOrbitForm.eval₂_apply,
    InfinitesimalAction.fundamental_apply, eval₂_coadjointOrbitForm_fundamentalVectorField]

/-- **The orbit map is an immersion.** At every point of the coadjoint orbit, the differential
`v ↦ (ξ ↦ d⟨μ, ξ⟩(v))` of the orbit map is injective. Pulled back to `G`, a vector `u` with
`d⟨μ, ξ⟩(dπ u) = σ_ν(ξ_G, u) = 0` for every `ξ` lies in the kernel of `σ_ν`, since the generators
`ξ_G(g)` exhaust `T_g G`; that kernel is the kernel of `dπ`. -/
theorem injective_differential_coadjointOrbitMap
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    Function.Injective (ν.isEquivariantMomentMap_coadjointOrbitForm.differential x) := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have hπ := ν.isSubmersion_quotientMk
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  intro v hv
  obtain ⟨u, rfl⟩ := hπ.surjective_mfderiv (by simp) g v
  have hu : u ∈ LinearMap.ker (ν.leftInvariantKirillovForm.bilinFormAt g) := by
    refine LinearMap.mem_ker.2 (LinearMap.ext fun w ↦ ?_)
    -- Write `w` as the generator `ξ_G(g)`, the right-invariant field of `ξ`.
    obtain ⟨ξ, rfl⟩ := (bijective_mulRightInvariantVectorField (I := I) g).2 w
    have hξ := congr($hv ξ)
    rw [SmoothTwoForm.IsMomentMap.differential_apply_eq_eval₂,
      InfinitesimalAction.fundamental_apply,
      ← mfderiv_fundamentalVectorField_of_map_smul (hπ.contMDiff.mdifferentiableAt (by simp))
        ((contMDiff_mul_right (I := I) (n := ∞)).mdifferentiableAt (by simp)) (fun _ ↦ rfl) ξ,
      eval₂_coadjointOrbitForm_mfderiv, fundamentalVectorField_eq_mulRightInvariantVectorField,
      SmoothBundleForm.eval₂_swap, LinearMap.zero_apply, neg_eq_zero] at hξ
    rw [SmoothForm.bilinFormAt_apply, hξ, LinearMap.zero_apply]
  rw [ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv] at hu
  exact hu

end Module.Dual
