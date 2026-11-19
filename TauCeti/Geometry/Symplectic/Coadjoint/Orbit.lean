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

/-!
# The Kirillov–Kostant–Souriau form on a coadjoint orbit

Let `G` be a real Lie group with finite-dimensional boundaryless model and Lie algebra
`𝔤 = GroupLieAlgebra I G`, and fix `ν ∈ 𝔤*`. Its coadjoint stabilizer
`G_ν = {g | Ad*_g ν = ν}` is a closed subgroup
(`TauCeti.Lie.isClosed_stabilizer_coadjointRepresentation`), so the coset space `G ⧸ G_ν` is a
smooth manifold, the homogeneous space of `Subgroup.quotientChartedSpaceOfIsClosed`, on which `G`
acts smoothly by left multiplication. This file records these structures as instances and puts the
**Kirillov–Kostant–Souriau form** on `G ⧸ G_ν`.

On `G` itself the left-invariant Kirillov form `σ_ν = -dα_ν`
(`Module.Dual.leftInvariantKirillovForm`) satisfies `σ_ν(ξ^L, η^L) = ν ⁅ξ, η⁆` for left-invariant
vector fields. Its kernel at `g` is the left translate of `𝔤_ν = {ξ | ν ⁅ξ, ·⁆ = 0}`, which is
the tangent space of the coset `g G_ν`, that is, the kernel of the differential of the projection
`π : G → G ⧸ G_ν` (`Module.Dual.ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv`). The
form is invariant under right translation by `G_ν`, so it is basic for `π`, and since `σ_ν` is
closed it descends to a unique symplectic form on `G ⧸ G_ν`:

`ω_ν = Module.Dual.orbitKKSForm ν`, with `π^* ω_ν = σ_ν`.

In particular `ω_ν([g])(dπ ξ^L, dπ η^L) = ν ⁅ξ, η⁆` for all `g`
(`Module.Dual.eval₂_orbitKKSForm_mfderiv_mulInvariantVectorField`), and the form is `G`-invariant
(`Module.Dual.mpullback_smul_orbitKKSForm`). The dimensions of `G ⧸ G_ν` and `𝔤_ν` add up to that
of `G` (`Module.Dual.finrank_quotientModelSpace_stabilizer_add_finrank_lieAnnihilator`).

The **orbit map** `ι : G ⧸ G_ν → 𝔤*`, `[g] ↦ Ad*_g ν` (`Module.Dual.coadjointOrbitMap`), is
injective, has the coadjoint orbit of `ν` as its range, and is a coadjoint-equivariant moment map
for `ω_ν` (`Module.Dual.isEquivariantMomentMap_orbitKKSForm`): the inclusion of the coadjoint
orbit into `𝔤*` is a moment map for its KKS form. Consequently the KKS form takes its defining
values on the fundamental vector fields `ξ_O` of the action of `G` on `G ⧸ G_ν`: at every point
`x`, `ω_ν(ξ_O, η_O) = ι(x) ⁅ξ, η⁆`, which is `ν ⁅ξ, η⁆` at the base point `[1]`
(`Module.Dual.eval₂_orbitKKSForm_fundamentalVectorField`).

## Main definitions

* `Module.Dual.coadjointOrbitMap ν`: the orbit map `[g] ↦ Ad*_g ν`.
* `Module.Dual.orbitKKSForm ν`: the KKS symplectic form on `G ⧸ G_ν`.

## Main results

* `Module.Dual.injective_coadjointOrbitMap`, `Module.Dual.range_coadjointOrbitMap`: the orbit map
  is a bijection onto the coadjoint orbit.
* `Module.Dual.finrank_quotientModelSpace_stabilizer_add_finrank_lieAnnihilator`: the dimension of
  the orbit.
* `Module.Dual.ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv`: the kernel of `σ_ν` is
  the vertical space of `G → G ⧸ G_ν`.
* `Module.Dual.mpullback_quotientMk_orbitKKSForm`, `Module.Dual.eq_orbitKKSForm_iff`: `ω_ν` is the
  unique two-form on `G ⧸ G_ν` pulling back to `σ_ν`.
* `Module.Dual.isSymplectic_orbitKKSForm`: `ω_ν` is symplectic.
* `Module.Dual.mpullback_smul_orbitKKSForm`: `ω_ν` is invariant under `G`.
* `Module.Dual.isEquivariantMomentMap_orbitKKSForm`: the orbit map is an equivariant moment map.
* `Module.Dual.eval₂_orbitKKSForm_fundamentalVectorField`: `ω_ν(ξ_O, η_O) = ι(x) ⁅ξ, η⁆`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22.
-/

public section

open Function Manifold Module TauCeti TauCeti.Lie
open scoped Manifold ContDiff

noncomputable section

namespace Module.Dual

section OrbitMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I 1 G] (ν : Module.Dual ℝ (GroupLieAlgebra I G))

/-! ### The orbit map -/

/-- The **coadjoint orbit map** `[g] ↦ Ad*_g ν` from `G ⧸ G_ν` to `𝔤*`. It is a bijection onto the
coadjoint orbit of `ν` (`Module.Dual.injective_coadjointOrbitMap`,
`Module.Dual.range_coadjointOrbitMap`), and an equivariant moment map for the KKS form
(`Module.Dual.isEquivariantMomentMap_orbitKKSForm`). -/
def coadjointOrbitMap :
    G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν → Module.Dual ℝ (GroupLieAlgebra I G) :=
  Quotient.lift (s := QuotientGroup.leftRel _) (fun g : G ↦ coadjointRepresentation ℝ I G g ν)
    fun g h hgh ↦ by
    have hk : coadjointRepresentation ℝ I G (g⁻¹ * h) ν = ν :=
      Representation.mem_stabilizer.1 (QuotientGroup.leftRel_apply.1 hgh)
    rw [← mul_inv_cancel_left g h, map_mul, mul_apply_eq_comp, hk]

/-- The coadjoint orbit map sends the coset of `g` to `Ad*_g ν`. -/
@[simp]
theorem coadjointOrbitMap_mk (g : G) :
    ν.coadjointOrbitMap (g : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) =
      coadjointRepresentation ℝ I G g ν :=
  (rfl)

/-- The coadjoint orbit map is equivariant for the action of `G` on `G ⧸ G_ν` and the coadjoint
action on `𝔤*`. -/
theorem coadjointOrbitMap_smul (h : G) (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    ν.coadjointOrbitMap (h • x) = coadjointRepresentation ℝ I G h (ν.coadjointOrbitMap x) := by
  induction x using QuotientGroup.induction_on with
  | H g => rw [MulAction.Quotient.smul_coe, smul_eq_mul, coadjointOrbitMap_mk,
    coadjointOrbitMap_mk, map_mul, mul_apply_eq_comp]

/-- The coadjoint orbit map is injective: `Ad*_g ν = Ad*_h ν` exactly when `g⁻¹ h ∈ G_ν`. -/
theorem injective_coadjointOrbitMap : Function.Injective ν.coadjointOrbitMap := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H g =>
  induction y using QuotientGroup.induction_on with | H h =>
  refine QuotientGroup.eq.2 (Representation.mem_stabilizer.2 ?_)
  rw [coadjointOrbitMap_mk, coadjointOrbitMap_mk] at hxy
  rw [map_mul, mul_apply_eq_comp, ← hxy, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self]

/-- The range of the coadjoint orbit map is the coadjoint orbit `{Ad*_g ν | g ∈ G}` of `ν`. -/
theorem range_coadjointOrbitMap :
    Set.range ν.coadjointOrbitMap = Set.range fun g : G ↦ coadjointRepresentation ℝ I G g ν :=
  (QuotientGroup.mk_surjective.range_comp ν.coadjointOrbitMap).symm

end OrbitMap

section Smooth

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  (ν : Module.Dual ℝ (GroupLieAlgebra I G))

/-! ### The coadjoint orbit as a homogeneous space -/

/-- The coadjoint orbit `G ⧸ G_ν` carries the charts of the homogeneous space of the closed
subgroup `G_ν`. -/
instance instChartedSpaceQuotientStabilizer :
    ChartedSpace (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  Subgroup.quotientChartedSpaceOfIsClosed I (isClosed_stabilizer_coadjointRepresentation I ν)

/-- The coadjoint orbit `G ⧸ G_ν` is a smooth manifold. -/
instance instIsManifoldQuotientStabilizer :
    IsManifold 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      ∞ (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  Subgroup.isManifold_quotientOfIsClosed (isClosed_stabilizer_coadjointRepresentation I ν)

/-- `G` acts smoothly on the coadjoint orbit `G ⧸ G_ν` by left multiplication. -/
instance instContMDiffSMulQuotientStabilizer :
    ContMDiffSMul I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞ G
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  Subgroup.contMDiffSMul_quotientOfIsClosed (isClosed_stabilizer_coadjointRepresentation I ν)

/-- The projection `G → G ⧸ G_ν` is a smooth submersion. -/
theorem isSubmersion_quotientMk_stabilizer :
    IsSubmersion I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) ∞
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  Subgroup.isSubmersion_quotientMk (isClosed_stabilizer_coadjointRepresentation I ν)

/-- **The dimension of a coadjoint orbit.** The dimensions of `G ⧸ G_ν` and of the infinitesimal
stabilizer `𝔤_ν = {ξ | ν ⁅ξ, ·⁆ = 0}` add up to the dimension of `G`. -/
theorem finrank_quotientModelSpace_stabilizer_add_finrank_lieAnnihilator :
    finrank ℝ (Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) +
      finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) ν) = finrank ℝ E := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  rw [← finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation
    (BoundarylessManifold.isInteriorPoint (I := I) (x := (1 : G)))]
  exact Subgroup.finrank_quotientModelSpace_add_finrank_lieSubalgebraOfSubgroup I _
    (isClosed_stabilizer_coadjointRepresentation I ν)

/-! ### The kernel of the Kirillov form is vertical -/

/-- Left translates of the infinitesimal stabilizer `𝔤_ν` are vertical for `G → G ⧸ G_ν`: the curve
`t ↦ g exp (t ξ)` stays in the coset `g G_ν` when `ξ ∈ 𝔤_ν`. -/
private theorem mfderiv_quotientMk_mulInvariantVectorField [T2Space G] {ξ : GroupLieAlgebra I G}
    (hξ : ξ ∈ lieAnnihilator ℝ (GroupLieAlgebra I G) ν) (g : G) :
    mfderiv I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g
      (mulInvariantVectorField ξ g) = 0 := by
  set K := (coadjointRepresentation ℝ I G).stabilizer ν
  have hπ := isSubmersion_quotientMk_stabilizer ν
  -- The curve `c t = g exp (t ξ)` and its derivative at `0`.
  have hmul : HasMFDerivAt I I (g * ·) 1 (mfderiv I I (g * ·) 1) :=
    (contMDiffAt_mul_left (I := I) (n := ∞) (a := g) (b := (1 : G))).mdifferentiableAt
      (by simp) |>.hasMFDerivAt
  have hexp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ ↦ mulInvariantExp (I := I) (G := G) (t • ξ)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight ξ) := hasMFDerivAt_mulInvariantExp_smul_zero ξ
  have hexp1 : mulInvariantExp (I := I) (G := G) ((0 : ℝ) • ξ) = 1 := by
    rw [zero_smul, mulInvariantExp_zero]
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ ↦ g * mulInvariantExp (I := I) (G := G) (t • ξ)) 0
      ((mfderiv I I (g * ·) 1).comp ((1 : ℝ →L[ℝ] ℝ).smulRight ξ)) :=
    (show HasMFDerivAt I I (g * ·) (mulInvariantExp (I := I) (G := G) ((0 : ℝ) • ξ))
      (mfderiv I I (g * ·) 1) by rw [hexp1]; exact hmul).comp 0 hexp
  have hc0 : g * mulInvariantExp (I := I) (G := G) ((0 : ℝ) • ξ) = g := by rw [hexp1, mul_one]
  have hπg : HasMFDerivAt I
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ K) (g * mulInvariantExp (I := I) (G := G) ((0 : ℝ) • ξ))
      (mfderiv I
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (QuotientGroup.mk : G → G ⧸ K) g) := by
    rw [hc0]
    exact (hπ.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have hπc := hπg.comp 0 hc
  -- The composite with the projection is constant, so its derivative vanishes.
  have hconst : ((QuotientGroup.mk : G → G ⧸ K) ∘
      fun t : ℝ ↦ g * mulInvariantExp (I := I) (G := G) (t • ξ)) = fun _ ↦ (g : G ⧸ K) := by
    funext t
    refine QuotientGroup.eq.2 ?_
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact K.inv_mem (mulInvariantExp_smul_mem_stabilizer_coadjointRepresentation_iff.2 hξ t)
  rw [hconst] at hπc
  have h := hπc.mfderiv.symm.trans (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (g : G ⧸ K) (0 : ℝ)).mfderiv
  have h1 := DFunLike.congr_fun h (1 : ℝ)
  convert h1 using 1
  -- Unfold the composite derivative at `1`; the tangent spaces are all the model spaces.
  change _ = mfderiv I _ (QuotientGroup.mk : G → G ⧸ K) g
    (mfderiv I I (g * ·) 1 ((1 : ℝ →L[ℝ] ℝ).smulRight ξ (1 : ℝ)))
  rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  rfl

/-- **The kernel of the left-invariant Kirillov form is vertical.** At every `g`, the kernel of
`σ_ν` is the kernel of the differential of the projection `G → G ⧸ G_ν`, the tangent space of the
coset `g G_ν`. -/
theorem ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv (g : G) :
    LinearMap.ker (ν.leftInvariantKirillovForm.bilinFormAt g) =
      (mfderiv I
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) g).ker := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  set K := (coadjointRepresentation ℝ I G).stabilizer ν
  have hπ := isSubmersion_quotientMk_stabilizer ν
  rw [ker_bilinFormAt_leftInvariantKirillovForm]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_mulInvariantDistribution.mp hv
    exact mfderiv_quotientMk_mulInvariantVectorField ν hw g
  -- Both sides have the dimension of `𝔤_ν`: the kernel by rank-nullity for the surjective
  -- differential of the projection, the translate of `𝔤_ν` because left translation is injective.
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (mfderiv I 𝓘(ℝ, Subgroup.QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g).toLinearMap
  rw [LinearMap.range_eq_top.2 (hπ.surjective_mfderiv (by simp) g), finrank_top] at hrn
  have hdim := finrank_quotientModelSpace_stabilizer_add_finrank_lieAnnihilator ν
  rw [finrank_mulInvariantDistribution]
  -- The tangent spaces of `G` and of `G ⧸ G_ν` are their model spaces, so rank-nullity reads
  -- `dim (G ⧸ G_ν) + dim ker = dim G`.
  have hker : finrank ℝ (Subgroup.QuotientModelSpace I K) +
      finrank ℝ (LinearMap.ker (mfderiv I 𝓘(ℝ, Subgroup.QuotientModelSpace I K)
        (QuotientGroup.mk : G → G ⧸ K) g).toLinearMap) = finrank ℝ E := hrn
  exact Nat.add_left_cancel (hdim.trans hker.symm)

/-! ### The KKS form -/

/-- The left-invariant Kirillov form `σ_ν` is basic for the projection `G → G ⧸ G_ν`: its vertical
vectors are null directions, and right translations by `G_ν` preserve it. -/
theorem isBasic_leftInvariantKirillovForm :
    RoughForm.IsBasic (V := ℝ)
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
      ν.leftInvariantKirillovForm.1 := by
  set K := (coadjointRepresentation ℝ I G).stabilizer ν
  have hπ := isSubmersion_quotientMk_stabilizer ν
  refine RoughForm.isBasic_of_mpullback_eq (σ := fun (k : K) (g : G) ↦ g * k)
    (hπ.contMDiff.mdifferentiable (by simp))
    (fun k ↦ (contMDiff_mul_right (I := I) (n := ∞) (a := (k : G))).mdifferentiable (by simp))
    (fun k ↦ funext fun g ↦ QuotientGroup.mk_mul_of_mem g k.2)
    (fun g g' hgg' ↦ .inr ⟨⟨g⁻¹ * g', QuotientGroup.eq.1 hgg'⟩, mul_inv_cancel_left g g'⟩)
    (fun g v j hj ↦ ?_) fun k ↦ by
      simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val
        (ν.mpullback_mul_right_leftInvariantKirillovForm_of_mem_stabilizer k.2)
  -- A vertical vector lies in the kernel of `σ_ν`.
  have hnull (u w : TangentSpace I g)
      (hu : mfderiv I 𝓘(ℝ, Subgroup.QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g u =
        0) :
      SmoothBundleForm.eval₂ ν.leftInvariantKirillovForm g u w = 0 := by
    have hu' : u ∈ LinearMap.ker (ν.leftInvariantKirillovForm.bilinFormAt g) := by
      rw [ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv]
      exact hu
    rw [← SmoothForm.bilinFormAt_apply, LinearMap.mem_ker.1 hu', LinearMap.zero_apply]
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv, ← SmoothBundleForm.eval₂_apply]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · exact hnull _ _ hj
  · rw [SmoothBundleForm.eval₂_swap, hnull _ _ hj, neg_zero]

/-- **The Kirillov–Kostant–Souriau form** `ω_ν` on the coadjoint orbit `G ⧸ G_ν`: the descent of
the left-invariant Kirillov form `σ_ν` along the projection `G → G ⧸ G_ν`, so that
`π^* ω_ν = σ_ν` (`Module.Dual.mpullback_quotientMk_orbitKKSForm`). On fundamental vector fields at
the base point it is `ω_ν(ξ_O, η_O) = ν ⁅ξ, η⁆`. -/
def orbitKKSForm :
    SmoothTwoForm
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :=
  SmoothForm.descendedForm (isSubmersion_quotientMk_stabilizer ν) QuotientGroup.mk_surjective
    ν.leftInvariantKirillovForm (isBasic_leftInvariantKirillovForm ν)

/-- The KKS form pulls back to the left-invariant Kirillov form along `G → G ⧸ G_ν`. -/
@[simp]
theorem mpullback_quotientMk_orbitKKSForm :
    SmoothForm.mpullback (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
      (isSubmersion_quotientMk_stabilizer ν).contMDiff ν.orbitKKSForm =
      ν.leftInvariantKirillovForm :=
  SmoothForm.mpullback_descendedForm

/-- The KKS form is the unique two-form on `G ⧸ G_ν` pulling back to the left-invariant Kirillov
form. -/
theorem eq_orbitKKSForm_iff {β : SmoothTwoForm
      𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)} :
    β = ν.orbitKKSForm ↔
      SmoothForm.mpullback
        (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (isSubmersion_quotientMk_stabilizer ν).contMDiff β = ν.leftInvariantKirillovForm :=
  SmoothForm.eq_descendedForm_iff

/-- The KKS form evaluates on images of tangent vectors of `G` as the left-invariant Kirillov
form: `ω_ν([g])(dπ v, dπ w) = σ_ν(g)(v, w)`. -/
theorem eval₂_orbitKKSForm_mfderiv (g : G) (v w : TangentSpace I g) :
    SmoothBundleForm.eval₂ ν.orbitKKSForm (g : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (mfderiv I _ (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
          g v)
        (mfderiv I _ (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
          g w) =
      SmoothBundleForm.eval₂ ν.leftInvariantKirillovForm g v w :=
  SmoothTwoForm.eval₂_descendedForm_mfderiv g v w

/-- The KKS form pairs the images of the left-invariant vector fields of `ξ` and `η` at any point
to `ν ⁅ξ, η⁆`. -/
theorem eval₂_orbitKKSForm_mfderiv_mulInvariantVectorField (ξ η : GroupLieAlgebra I G) (g : G) :
    SmoothBundleForm.eval₂ ν.orbitKKSForm (g : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (mfderiv I _ (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
          g (mulInvariantVectorField ξ g))
        (mfderiv I _ (QuotientGroup.mk : G → G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
          g (mulInvariantVectorField η g)) =
      ν ⁅ξ, η⁆ := by
  rw [eval₂_orbitKKSForm_mfderiv, eval₂_leftInvariantKirillovForm_mulInvariantVectorField]

/-- **The KKS form is symplectic.** It is closed because its pullback `σ_ν = -dα_ν` is, and
nondegenerate because the kernel of `σ_ν` is exactly the vertical space of `G → G ⧸ G_ν`. -/
theorem isSymplectic_orbitKKSForm : ν.orbitKKSForm.IsSymplectic :=
  (SmoothTwoForm.isSymplectic_descendedForm_iff).2
    ⟨ν.isClosed_leftInvariantKirillovForm,
      ker_bilinFormAt_leftInvariantKirillovForm_eq_ker_mfderiv ν⟩

/-- **The KKS form is `G`-invariant**: every `h ∈ G` acting on `G ⧸ G_ν` preserves `ω_ν`. Under
the projection this is the invariance of `σ_ν` under left translations. -/
@[simp]
theorem mpullback_smul_orbitKKSForm (h : G) :
    SmoothForm.mpullback (fun x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν ↦ h • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) h) ν.orbitKKSForm = ν.orbitKKSForm := by
  rw [eq_orbitKKSForm_iff, SmoothForm.mpullback_mpullback_of_comp_eq
    (isSubmersion_quotientMk_stabilizer ν).contMDiff
    (ContMDiffSMul.contMDiff_const_smul (I := I) h) contMDiff_mul_left
    (isSubmersion_quotientMk_stabilizer ν).contMDiff
    (funext fun g ↦ (MulAction.Quotient.smul_coe _ h g).symm),
    mpullback_quotientMk_orbitKKSForm, mpullback_mul_left_leftInvariantKirillovForm]

/-- Each component `[g] ↦ (Ad*_g ν) ξ` of the coadjoint orbit map is smooth. -/
theorem contMDiff_coadjointOrbitMap_apply (ξ : GroupLieAlgebra I G) :
    ContMDiff 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      𝓘(ℝ) ∞ fun x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν ↦
      ν.coadjointOrbitMap x ξ :=
  ((isSubmersion_quotientMk_stabilizer ν).contMDiff_comp_iff QuotientGroup.mk_surjective
    le_rfl).1 (contMDiff_coadjointRepresentation_apply ν ξ)

/-- **The coadjoint orbit map is an equivariant moment map for the KKS form.** For the action of
`G` on `G ⧸ G_ν`, the orbit map `[g] ↦ Ad*_g ν` satisfies `d⟨ι, ξ⟩ = ι_(ξ_O) ω_ν` and
`ι (h • x) = Ad*_h (ι x)`. Pulled back to `G`, this is the moment map
`g ↦ Ad*_g ν` of the left-invariant Kirillov form
(`Module.Dual.isEquivariantMomentMap_leftInvariantKirillovForm`). -/
theorem isEquivariantMomentMap_orbitKKSForm :
    ν.orbitKKSForm.IsEquivariantMomentMap ν.coadjointOrbitMap := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  set K := (coadjointRepresentation ℝ I G).stabilizer ν
  have hπ := isSubmersion_quotientMk_stabilizer ν
  have hG := ν.isEquivariantMomentMap_leftInvariantKirillovForm
  refine ⟨⟨ν.contMDiff_coadjointOrbitMap_apply, fun ξ ↦
    SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ ?_⟩, ν.coadjointOrbitMap_smul⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨w, rfl⟩ := hπ.surjective_mfderiv (x := g) (by simp) v
  -- The projection carries the fundamental vector field of `ξ` on `G` to that on `G ⧸ G_ν`.
  have hfund : mfderiv I _ (QuotientGroup.mk : G → G ⧸ K) g (fundamentalVectorField I ξ g) =
      fundamentalVectorField _ ξ (g : G ⧸ K) :=
    mfderiv_fundamentalVectorField_of_map_smul (hπ.contMDiff.mdifferentiableAt (by simp))
      ((ContMDiffSMul.contMDiff_smul_const (n := ∞) g).mdifferentiableAt (by simp))
      (fun h ↦ (MulAction.Quotient.smul_coe K h g).symm) ξ
  -- The component of the orbit map pulls back to the component of `g ↦ Ad*_g ν`.
  have hcomp : (fun x : G ⧸ K ↦ ν.coadjointOrbitMap x ξ) ∘ (QuotientGroup.mk : G → G ⧸ K) =
      fun g ↦ coadjointRepresentation ℝ I G g ν ξ := rfl
  rw [InfinitesimalAction.fundamental_apply, ← hfund, eval₂_orbitKKSForm_mfderiv,
    ← mvfderiv_comp_apply g ((ν.contMDiff_coadjointOrbitMap_apply ξ).mdifferentiableAt (by simp))
      (hπ.contMDiff.mdifferentiableAt (by simp)), hcomp]
  have h := SmoothTwoForm.isHamiltonianVectorField_iff.1 (hG.isHamiltonianVectorField ξ) g w
  simpa only [InfinitesimalAction.fundamental_apply] using h

/-- **The KKS form on generators.** At every point `x` of `G ⧸ G_ν`, the KKS form pairs the
fundamental vector fields of `ξ` and `η` to `ι(x) ⁅ξ, η⁆`, where `ι(x) = Ad*_g ν` for `x = [g]`
is the point of the coadjoint orbit. -/
theorem eval₂_orbitKKSForm_fundamentalVectorField (ξ η : GroupLieAlgebra I G)
    (x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) :
    SmoothBundleForm.eval₂ ν.orbitKKSForm x (fundamentalVectorField _ ξ x)
        (fundamentalVectorField _ η x) =
      ν.coadjointOrbitMap x ⁅ξ, η⁆ := by
  have h := SmoothTwoForm.momentCocycle_eq_zero_iff.1
    ((isEquivariantMomentMap_orbitKKSForm ν).momentCocycle_eq_zero x) ξ η
  simpa only [InfinitesimalAction.fundamental_apply] using h

/-- At the base point `[1]` of `G ⧸ G_ν`, the KKS form pairs the fundamental vector fields of `ξ`
and `η` to `ν ⁅ξ, η⁆`. -/
theorem eval₂_orbitKKSForm_fundamentalVectorField_one (ξ η : GroupLieAlgebra I G) :
    SmoothBundleForm.eval₂ ν.orbitKKSForm
        ((1 : G) : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)
        (fundamentalVectorField _ ξ _) (fundamentalVectorField _ η _) =
      ν ⁅ξ, η⁆ := by
  rw [eval₂_orbitKKSForm_fundamentalVectorField, coadjointOrbitMap_mk, map_one,
    one_apply_eq_self]

end Smooth

end Module.Dual
