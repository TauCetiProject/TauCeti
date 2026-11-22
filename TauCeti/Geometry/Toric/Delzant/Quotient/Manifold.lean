/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Manifold.Algebra.Pi
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Smooth
public import TauCeti.Geometry.Toric.Delzant.Quotient.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Topology.Discrete

/-!
# The Delzant quotient is a smooth manifold

Let `i : N →+ V` be an integral lattice and `(u, c)` the facet presentation of a Delzant polytope
`Δ`. Delzant's construction realizes `Δ` as the moment polytope of the quotient
`M_Δ = Z / N_Δ` (`TauCeti.Toric.DelzantQuotient i u c`) of the zero level `Z ⊆ ℂ^ι` of the moment
map of the kernel torus `N_Δ ⊆ (ℝ / 2πℤ)^ι`. This file makes `M_Δ` a smooth manifold for which the
projection `Z → M_Δ` is a smooth submersion, by the quotient manifold theorem for free proper
actions of Lie groups.

* **The kernel torus is a Lie group.** The torus `(ℝ / 2πℤ)^ι` is a Lie group, a finite product
  of circles. For an integral lattice the kernel torus is a closed subgroup
  (`TauCeti.Toric.isClosed_kernelTorus`), so the closed-subgroup theorem makes it an embedded Lie
  subgroup (`TauCeti.Toric.kernelTorusData`), modelled on its Lie algebra. Lie groups are
  multiplicative in the quotient manifold theorem, so the kernel torus is taken in the
  multiplicative copy of `(ℝ / 2πℤ)^ι` (`TauCeti.Toric.kernelTorus`).
* **Its action on the level is smooth, free and proper.** The level `Z` is a smooth manifold by
  the implicit function theorem (`TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`). The rotation
  action of `(ℝ / 2πℤ)^ι` on `ℂ^ι` is smooth (`TauCeti.contMDiff_torusRotation`) and preserves
  `Z`, so the kernel torus acts smoothly on `Z`
  (`TauCeti.Toric.IsDelzant.contMDiffSMul_kernelTorus`). It acts freely because the normals at
  each vertex of `Δ` form a lattice basis (`TauCeti.Toric.IsDelzant.isCancelSMul_kernelTorus`),
  and properly because it is compact.
* **The quotient.** The orbit space of this action is the Delzant quotient, up to the
  homeomorphism `TauCeti.Toric.DelzantQuotient.homeomorphOrbitRelQuotient` comparing the orbit
  relations of the additive and the multiplicative actions. The slice charts of the quotient
  manifold theorem, pulled back along it, are the atlas
  `TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. For it, `M_Δ` is a smooth manifold
  (`TauCeti.Toric.IsDelzant.isManifold_delzantQuotient`) and the projection `Z → M_Δ` is a smooth
  submersion (`TauCeti.Toric.IsDelzant.isSubmersion_delzantQuotientMk`) whose vertical tangent
  vectors are exactly the directions of the orbits of the kernel torus
  (`TauCeti.Toric.IsDelzant.ker_mfderiv_delzantQuotientMk`). The reduced moment map
  `μ_Δ : M_Δ → V*` is smooth (`TauCeti.Toric.IsDelzant.contMDiff_reducedMomentMap`), because its
  composite with the projection is the smooth function `z ↦ μ(z) ∘ s` on the level, where `μ` is
  the moment map of the torus `(ℝ / 2πℤ)^ι` and `s` is a right inverse of `β_ℝ : ℝ^ι → V`.
* **The vertical tangent vectors in `ℂ^ι`.** Read in `ℂ^ι`, the orbit directions of the kernel
  torus at `x` are the generators `t_M(x)` of the rotations `z_j ↦ exp(-i s t_j) z_j` for `t` in
  `𝔫 = ker β_ℝ` (`TauCeti.Toric.kernelTorusOrbitTangent`). The projection is constant along the
  orbit curves `s ↦ exp(-i s t) x`, so these generators are images of vertical vectors
  (`TauCeti.Toric.IsDelzant.exists_mfderiv_delzantQuotientMk_eq_zero`). Conversely, the
  fundamental vector fields of the kernel torus are such generators
  (`TauCeti.Toric.IsDelzant.mfderiv_coe_fundamentalVectorField_mem`): a chart of the torus lifts
  the kernel torus near the identity to angles `t` with `β_ℝ t ∈ 2π i(N)`, and as this lattice is
  discrete, `β_ℝ t` is constant along the lift, so every tangent vector of the kernel torus at the
  identity lies in `𝔫` (`TauCeti.Toric.IsIntegralLattice.mfderiv_toAdd_coe_kernelTorus_mem`).
  Hence the vertical vectors are exactly those carried into `𝔫 · x`
  (`TauCeti.Toric.IsDelzant.ker_mfderiv_delzantQuotientMk_eq_comap`).

The atlas is modelled on `ℝ^(d + n - k)`, where `d` is the number of facets, `n = dim V` and `k`
is the dimension of the Lie algebra of the kernel torus. The inclusion carries the vertical tangent
space at `x` isomorphically onto `𝔫 · x`, of dimension `dim 𝔫 = d - n`
(`TauCeti.Toric.IsDelzant.finrank_kernelTorusOrbitTangent`), so `M_Δ` has dimension
`(d + n) - (d - n) = 2n` (`TauCeti.Toric.IsDelzant.finrank_delzantQuotientModelSpace`).

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 29.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.10 (the
  quotient manifold theorem).
-/

public section

noncomputable section

open Manifold Module Set Real TauCeti.Lie
open scoped Manifold ContDiff

namespace TauCeti.Toric

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### The kernel torus as a Lie group -/

variable (i u) in
/-- The kernel torus `N_Δ = ker (facetTorusHom i u (2π))`, as a subgroup of the multiplicative copy
of the torus `(ℝ / 2πℤ)^ι`, so that it can act as a Lie group. -/
abbrev kernelTorus : Subgroup (Multiplicative (ι → AddCircle (2 * π))) :=
  AddSubgroup.toSubgroup (facetTorusHom i u (2 * π)).ker

/-- An element of the multiplicative copy of `(ℝ / 2πℤ)^ι` lies in the kernel torus exactly when
its angles lie in the kernel of `facetTorusHom i u (2π)`. -/
theorem mem_kernelTorus {θ : Multiplicative (ι → AddCircle (2 * π))} :
    θ ∈ kernelTorus i u ↔ θ.toAdd ∈ (facetTorusHom i u (2 * π)).ker :=
  Multiplicative.mem_toSubgroup _ _

/-- For an integral lattice the kernel torus is a closed subgroup of `(ℝ / 2πℤ)^ι`. -/
theorem isClosed_kernelTorus (hi : IsIntegralLattice i) :
    IsClosed (kernelTorus i u : Set (Multiplicative (ι → AddCircle (2 * π)))) := by
  have h : (kernelTorus i u : Set (Multiplicative (ι → AddCircle (2 * π)))) =
      Multiplicative.toAdd ⁻¹'
        ((facetTorusHom i u (2 * π)).ker : Set (ι → AddCircle (2 * π))) := by
    ext θ
    exact mem_kernelTorus
  rw [h]
  exact (hi.isClosed_ker_facetTorusHom u (2 * π)).preimage continuous_toAdd

variable (i u) in
/-- The Lie algebra of the kernel torus, the model space of its Lie group structure
`TauCeti.Toric.kernelTorusData`. -/
abbrev kernelTorusLieAlgebra :
    Submodule ℝ (LeftInvariantDerivation (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (Multiplicative (ι → AddCircle (2 * π)))) :=
  (lieSubalgebraOfSubgroup (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (kernelTorus i u)).toSubmodule

variable (i u) in
/-- **The kernel torus is a Lie group.** For an integral lattice, the embedded Lie subgroup
structure of the closed subgroup `N_Δ` of `(ℝ / 2πℤ)^ι` given by the closed-subgroup theorem,
modelled on its Lie algebra. -/
def kernelTorusData (hi : IsIntegralLattice i) :
    EmbeddedLieSubgroupData (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (kernelTorus i u)
      (kernelTorusLieAlgebra i u) :=
  EmbeddedLieSubgroupData.ofIsClosed (isClosed_kernelTorus hi)

variable (u) in
/-- For an integral lattice, the inclusion of the kernel torus, with its Lie group structure
`TauCeti.Toric.kernelTorusData`, into the torus `(ℝ / 2πℤ)^ι` is smooth. -/
theorem contMDiff_toAdd_coe_kernelTorus (hi : IsIntegralLattice i) :
    letI := (kernelTorusData i u hi).chartedSpace
    ContMDiff 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞
      fun k : kernelTorus i u ↦ (k : Multiplicative (ι → AddCircle (2 * π))).toAdd :=
  letI := (kernelTorusData i u hi).chartedSpace
  Multiplicative.contMDiff_toAdd.comp (kernelTorusData i u hi).contMDiff_subtypeVal

/-- **The Lie algebra of the kernel torus lies in `𝔫`.** Read in the angle coordinates `ℝ^ι` of
the torus `(ℝ / 2πℤ)^ι`, every tangent vector at the identity of the kernel torus `N_Δ`, with its
Lie group structure as a closed subgroup, lies in `𝔫 = ker β_ℝ`. Near the identity, a chart of the
torus lifts `N_Δ` to angles `t` with `β_ℝ t ∈ 2π i(N)`, and since the lattice is discrete, `β_ℝ t`
is constant along this lift. -/
theorem IsIntegralLattice.mfderiv_toAdd_coe_kernelTorus_mem (hi : IsIntegralLattice i)
    (ξ : kernelTorusLieAlgebra i u) :
    letI := (kernelTorusData i u hi).chartedSpace
    mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (fun k : kernelTorus i u ↦ (k : Multiplicative (ι → AddCircle (2 * π))).toAdd) 1 ξ ∈
      LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)) := by
  let _ := (kernelTorusData i u hi).chartedSpace
  have := (kernelTorusData i u hi).lieGroup
  have hJ := contMDiff_toAdd_coe_kernelTorus u hi
  set J : kernelTorus i u → ι → AddCircle (2 * π) :=
    fun k ↦ (k : Multiplicative (ι → AddCircle (2 * π))).toAdd
  have hJ1 : J 1 = 0 := rfl
  set e := extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (0 : ι → AddCircle (2 * π))
  set β := Fintype.linearCombination ℝ fun j ↦ i (u j)
  have hsrc : ∀ᶠ k in nhds (1 : kernelTorus i u), J k ∈ e.source :=
    hJ.continuous.continuousAt.preimage_mem_nhds
      (hJ1 ▸ (isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source _))
  -- Along the lift `e ∘ J` of the kernel torus to angles, `β_ℝ` takes values in the discrete set
  -- `2π i(N)`, so it is constant near the identity.
  have hmem : ∀ᶠ k in nhds (1 : kernelTorus i u), β (e (J k)) ∈ ((2 * π) • i).range :=
    hsrc.mono fun k hk ↦ by
      have h0 : facetTorusHom i u (2 * π) (fun j ↦ (e (J k) j : AddCircle (2 * π))) = 0 := by
        rw [AddCircle.coe_extChartAt_pi_apply _ _ hk]
        exact mem_kernelTorus.1 k.property
      rw [facetTorusHom_coe] at h0
      exact (QuotientAddGroup.eq_zero_iff _).1 h0
  have hcont : ContinuousAt (fun k ↦ β (e (J k))) 1 :=
    (LinearMap.continuous_of_finiteDimensional β).continuousAt.comp
      (ContinuousAt.comp_of_eq (continuousAt_extChartAt (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (0 : ι → AddCircle (2 * π))) (hJ.continuous.continuousAt (x := 1)) hJ1)
  have hconst : ∀ᶠ k in nhds (1 : kernelTorus i u), β (e (J k)) = β (e (J 1)) :=
    (Filter.not_frequently.1 fun hne ↦ hcont.tendsto.not_isDiscrete hmem.self_of_nhds hmem hne
      (hi.isDiscrete_range_smul (2 * π))).mono fun _ ↦ not_not.1
  -- Differentiate: the lift has derivative `τ`, and `β_ℝ τ = 0`.
  have hs : MDifferentiableAt 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, ι → ℝ) (e ∘ J) 1 :=
    (mdifferentiableAt_extChartAt (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (hJ1 ▸ mem_chart_source _ _)).comp 1 (hJ.mdifferentiableAt (by simp))
  have hτ : mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) J 1 ξ =
      mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, ι → ℝ) (e ∘ J) 1 ξ := by
    have hJeq : J =ᶠ[nhds 1] (fun t : ι → ℝ ↦ fun j ↦ (t j : AddCircle (2 * π))) ∘ (e ∘ J) :=
      hsrc.mono fun k hk ↦ (AddCircle.coe_extChartAt_pi_apply _ _ hk).symm
    have h := ((AddCircle.hasMFDerivAt_coe_pi (2 * π) ((e ∘ J) 1)).comp 1
      hs.hasMFDerivAt).congr_of_eventuallyEq_abuse hJeq
    -- The derivative of the covering map is the identity of `ℝ^ι`.
    exact congrArg (fun L ↦ L ξ) (h.mfderiv.trans (ContinuousLinearMap.id_comp
      (mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, ι → ℝ) (e ∘ J) 1 :
        kernelTorusLieAlgebra i u →L[ℝ] ι → ℝ)))
  have hβ' : HasMFDerivAt 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, V) (fun k ↦ β (e (J k))) 1
      ((LinearMap.toContinuousLinearMap β).comp
        (mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, ι → ℝ) (e ∘ J) 1)) :=
    (LinearMap.toContinuousLinearMap β).hasMFDerivAt.comp 1 hs.hasMFDerivAt
  have h := DFunLike.congr_fun (hβ'.mfderiv.symm.trans
    ((hasMFDerivAt_const (β (e (J 1))) 1).congr_of_eventuallyEq_abuse hconst).mfderiv) ξ
  -- Membership in `ker β_ℝ`, for a tangent vector of the torus read in `ℝ^ι`.
  exact (LinearMap.mem_ker (f := β)).2 ((congrArg β hτ).trans (h.trans (zero_apply _)))

/-! ### The action of the kernel torus on the level -/

/-- An element of the kernel torus acts on the level through its angles. -/
@[simp]
theorem coe_kernelTorus_smul (θ : kernelTorus i u) (x : delzantLevel i u c) :
    ((θ • x : delzantLevel i u c) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =
      torusRotation (θ : Multiplicative (ι → AddCircle (2 * π))).toAdd x := by
  rw [Subgroup.smul_def, ← toAdd_vadd, coe_vadd_delzantLevel]

/-- The kernel torus acts continuously on the level. -/
instance : ContinuousSMul (kernelTorus i u) (delzantLevel i u c) :=
  ⟨continuous_induced_rng.2 (continuous_torusRotation.comp
    ((continuous_toAdd.comp (continuous_subtypeVal.comp continuous_fst)).prodMk
      (continuous_subtypeVal.comp continuous_snd)))⟩

/-- For an integral lattice the kernel torus is compact, so it acts properly on the level. -/
theorem properSMul_kernelTorus (hi : IsIntegralLattice i) :
    ProperSMul (kernelTorus i u) (delzantLevel i u c) :=
  have : CompactSpace (kernelTorus i u) :=
    isCompact_iff_compactSpace.1 (isClosed_kernelTorus hi).isCompact
  properSMul_of_compactSpace _ _

/-! ### The orbit directions of the kernel torus in `ℂ^ι` -/

variable (i u) in
/-- The tangent space at `x` of the orbit of the kernel torus `N_Δ` through `x` in `ℂ^ι`: the
generators `t_M(x)` of the elements `t` of its Lie algebra `𝔫 = ker β_ℝ`. -/
def kernelTorusOrbitTangent (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    Submodule ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).map
    (weightInfinitesimalAction (fun j ↦ -ContinuousLinearMap.proj j) x)

/-- A vector lies in the orbit directions `𝔫 · x` exactly when it is the generator `t_M(x)` of an
element `t` of `𝔫`. -/
@[simp]
theorem mem_kernelTorusOrbitTangent {x v : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} :
    v ∈ kernelTorusOrbitTangent i u x ↔
      ∃ t ∈ LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)),
        weightGenerator (-t) x = v := by
  simp only [kernelTorusOrbitTangent, Submodule.mem_map, weightInfinitesimalAction_apply]
  refine exists_congr fun t ↦ and_congr_right fun _ ↦ ?_
  rw [show (fun j ↦ (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j) t) = -t from
    funext fun j ↦ by simp]

/-! ### The Delzant quotient as an orbit space of a Lie group -/

namespace DelzantQuotient

/-- Two points of the level have the same class in the Delzant quotient exactly when an element
of the multiplicative copy of the kernel torus carries one to the other. -/
theorem mk_eq_mk_iff_exists_smul {x y : delzantLevel i u c} :
    mk x = mk y ↔ ∃ θ : kernelTorus i u, θ • y = x := by
  rw [mk_eq_mk_iff]
  refine ⟨fun ⟨θ, hθ, h⟩ ↦ ⟨⟨Multiplicative.ofAdd θ, mem_kernelTorus.2 hθ⟩, h⟩,
    fun ⟨θ, h⟩ ↦
      ⟨(θ : Multiplicative (ι → AddCircle (2 * π))).toAdd, mem_kernelTorus.1 θ.property, h⟩⟩

variable (i u c) in
/-- The Delzant quotient is homeomorphic to the orbit space of the multiplicative copy of the
kernel torus acting on the level: both are quotients of the level by the same orbit relation. -/
def homeomorphOrbitRelQuotient :
    DelzantQuotient i u c ≃ₜ
      MulAction.orbitRel.Quotient (kernelTorus i u) (delzantLevel i u c) where
  toFun := lift (Quotient.mk _) fun θ hθ x ↦ Quotient.sound (MulAction.orbitRel_apply.2
    (MulAction.mem_orbit_iff.2 ⟨⟨Multiplicative.ofAdd θ, mem_kernelTorus.2 hθ⟩, rfl⟩))
  invFun := Quotient.lift mk fun x y hxy ↦
    mk_eq_mk_iff_exists_smul.2 (MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxy))
  left_inv q := DelzantQuotient.inductionOn q fun x ↦ by rw [lift_mk, Quotient.lift_mk]
  right_inv q := Quotient.inductionOn q fun x ↦ by rw [Quotient.lift_mk, lift_mk]
  continuous_toFun := continuous_lift _ continuous_quot_mk
  continuous_invFun := continuous_quot_lift _ continuous_mk

@[simp]
theorem homeomorphOrbitRelQuotient_mk (x : delzantLevel i u c) :
    homeomorphOrbitRelQuotient i u c (mk x) = Quotient.mk _ x :=
  lift_mk _ _ x

@[simp]
theorem homeomorphOrbitRelQuotient_symm_mk (x : delzantLevel i u c) :
    (homeomorphOrbitRelQuotient i u c).symm (Quotient.mk _ x) = mk x :=
  (rfl)

end DelzantQuotient

variable [FiniteDimensional ℝ V]

namespace IsDelzant

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-- **The kernel torus acts freely on the level.** -/
theorem isCancelSMul_kernelTorus : IsCancelSMul (kernelTorus i u) (delzantLevel i u c) := by
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun θ x hθx ↦ Subtype.ext ?_
  obtain ⟨t, ht⟩ : ∃ t : ι → ℝ, (fun j ↦ (t j : AddCircle (2 * π))) =
      (θ : Multiplicative (ι → AddCircle (2 * π))).toAdd := by
    choose t ht using fun j ↦ QuotientAddGroup.mk_surjective
      ((θ : Multiplicative (ι → AddCircle (2 * π))).toAdd j)
    exact ⟨t, funext ht⟩
  have hker : (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker :=
    ht ▸ mem_kernelTorus.1 θ.property
  have hrot : weightRotation (-t) x = x := by
    rw [← torusRotation_coe, ht, ← coe_kernelTorus_smul, hθx]
  have h0 := (hΔ.weightRotation_neg_eq_self_iff hi x.property hker).1 hrot
  rwa [ht] at h0

/-- **The kernel torus acts smoothly on the level**, for the implicit-function atlas of the level
and the Lie group structure of the kernel torus. -/
theorem contMDiffSMul_kernelTorus :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := (kernelTorusData i u hi).chartedSpace
    ContMDiffSMul 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞
      (kernelTorus i u) (delzantLevel i u c) := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := (kernelTorusData i u hi).chartedSpace
  refine ⟨?_⟩
  -- The action is the restriction to the level of the smooth rotation action on `ℂ^ι`.
  have hg : ContMDiff (𝓘(ℝ, kernelTorusLieAlgebra i u).prod
      𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞
      fun p : kernelTorus i u × delzantLevel i u c ↦
        torusRotation (p.1 : Multiplicative (ι → AddCircle (2 * π))).toAdd p.2 :=
    contMDiff_torusRotation.comp
      (((contMDiff_toAdd_coe_kernelTorus u hi).comp contMDiff_fst).prodMk
        ((hΔ.contMDiff_coe_delzantLevel hi).comp contMDiff_snd))
  exact hΔ.contMDiff_codRestrict_delzantLevel hi hg fun p ↦ (p.1 • p.2).property

/-! ### The smooth structure of the Delzant quotient -/

-- Installs the hypotheses of the quotient manifold theorem for the kernel torus acting on the
-- level (the atlases of the level and of the kernel torus, its Lie group structure, and the
-- smooth, proper and free action) and the resulting slice atlas of the orbit space, which every
-- result below needs.
local macro "kernel_torus_quotient_instances" ι:ident V:ident i:ident u:ident c:ident hΔ:ident
    hi:ident : tactic => `(tactic| (
  let _ := ($hΔ).delzantLevelChartedSpace $hi
  let _ := (kernelTorusData $i $u $hi).chartedSpace
  have := (kernelTorusData $i $u $hi).lieGroup
  have := ($hΔ).isManifold_delzantLevel $hi ∞
  have := ($hΔ).contMDiffSMul_kernelTorus $hi
  have := properSMul_kernelTorus (u := $u) (c := $c) $hi
  have := ($hΔ).isCancelSMul_kernelTorus $hi
  let _ := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, kernelTorusLieAlgebra $i $u)
    (kernelTorus $i $u) 𝓘(ℝ, Fin (Fintype.card $ι + finrank ℝ $V) → ℝ)
    (delzantLevel $i $u $c)))

/-- **The atlas of the Delzant quotient.** The slice charts of the quotient manifold theorem for
the free proper smooth action of the kernel torus on the level, pulled back to the Delzant
quotient along `TauCeti.Toric.DelzantQuotient.homeomorphOrbitRelQuotient`. It is modelled on
`ℝ^(d + n - k)`, where `d` is the number of facets, `n = dim V` and `k` is the dimension of the
Lie algebra of the kernel torus. -/
@[instance_reducible]
def delzantQuotientChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace
      (kernelTorusLieAlgebra i u) (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      (DelzantQuotient i u c) := by
  kernel_torus_quotient_instances ι V i u c hΔ hi
  exact (DelzantQuotient.homeomorphOrbitRelQuotient i u c).pullbackChartedSpace

/-- **The Delzant quotient is a smooth manifold**, for the atlas
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. -/
theorem isManifold_delzantQuotient :
    letI := hΔ.delzantQuotientChartedSpace hi
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace
      (kernelTorusLieAlgebra i u) (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞
      (DelzantQuotient i u c) := by
  kernel_torus_quotient_instances ι V i u c hΔ hi
  exact (DelzantQuotient.homeomorphOrbitRelQuotient i u c).pullback_isManifold
    (I := 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ))) (n := ∞)

omit [FiniteDimensional ℝ V] hΔ hi in
/-- The projection onto the Delzant quotient is the orbit projection of the kernel torus acting on
the level, followed by the inverse of the diffeomorphism pulled back along
`TauCeti.Toric.DelzantQuotient.homeomorphOrbitRelQuotient`. -/
private theorem mk_eq_comp {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [ChartedSpace H (MulAction.orbitRel.Quotient (kernelTorus i u) (delzantLevel i u c))] :
    letI := (DelzantQuotient.homeomorphOrbitRelQuotient i u c).pullbackChartedSpace (H := H)
    (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) =
      ((DelzantQuotient.homeomorphOrbitRelQuotient i u c).pullbackDiffeomorph I ∞).symm ∘
        Quotient.mk (MulAction.orbitRel (kernelTorus i u) (delzantLevel i u c)) := by
  rw [Homeomorph.coe_pullbackDiffeomorph_symm]
  exact funext fun x ↦ (DelzantQuotient.homeomorphOrbitRelQuotient_symm_mk x).symm

/-- **The projection onto the Delzant quotient is a smooth submersion**, for the atlases
`TauCeti.Toric.IsDelzant.delzantLevelChartedSpace` and
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. In particular a map out of the Delzant
quotient is smooth exactly when its composite with the projection is
(`Manifold.IsSubmersion.contMDiff_comp_iff`). -/
theorem isSubmersion_delzantQuotientMk :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    IsSubmersion 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞
      (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) := by
  kernel_torus_quotient_instances ι V i u c hΔ hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  let e := (DelzantQuotient.homeomorphOrbitRelQuotient i u c).pullbackDiffeomorph
    𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞
  have hq := ProperSMul.isSubmersion_quotientMk (I := 𝓘(ℝ, kernelTorusLieAlgebra i u))
    (G := kernelTorus i u) (I' := 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ))
    (M := delzantLevel i u c)
  have h := hq.isSubmersionOfComplement_complement
  rw [mk_eq_comp 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
    (Fin (Fintype.card ι + finrank ℝ V) → ℝ))]
  exact IsSubmersionOfComplement.isSubmersion (F := hq.complement)
    (isSubmersionOfComplement_iff.2 fun x ↦
      (e.symm.isLocalDiffeomorph _).comp_isSubmersionAtOfComplement (h.isSubmersionAt x))

/-- **The vertical tangent vectors of the projection are the orbit directions.** The kernel of
the differential at `x` of the projection from the level onto the Delzant quotient is the
tangent space `𝔫 · x` of the orbit of the kernel torus through `x`. -/
theorem ker_mfderiv_delzantQuotientMk (x : delzantLevel i u c) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := (kernelTorusData i u hi).chartedSpace
    haveI := (kernelTorusData i u hi).lieGroup
    haveI := hΔ.isManifold_delzantLevel hi ∞
    haveI := hΔ.contMDiffSMul_kernelTorus hi
    letI := hΔ.delzantQuotientChartedSpace hi
    (mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) x).ker =
      (InfinitesimalAction.fundamental 𝓘(ℝ, kernelTorusLieAlgebra i u) (kernelTorus i u)
        𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) (delzantLevel i u c)).orbitTangent x := by
  kernel_torus_quotient_instances ι V i u c hΔ hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  let e : MulAction.orbitRel.Quotient (kernelTorus i u) (delzantLevel i u c) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))⟯ DelzantQuotient i u c :=
    ((DelzantQuotient.homeomorphOrbitRelQuotient i u c).pullbackDiffeomorph _ ∞).symm
  -- The projection is the orbit projection followed by the diffeomorphism `e`, whose
  -- differential is invertible.
  have hcomp := (e.isLocalDiffeomorph _).ker_mfderiv_comp (by simp)
    ((ProperSMul.contMDiff_quotientMk (I := 𝓘(ℝ, kernelTorusLieAlgebra i u))
      (G := kernelTorus i u) x).mdifferentiableAt (by simp))
  -- Rewriting `mk_eq_comp` inside the goal is slow, so it is transported by `congrArg` instead.
  have hmk := congrArg (fun f : delzantLevel i u c → DelzantQuotient i u c ↦
    (mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) f x).ker)
    (mk_eq_comp 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)))
  exact hmk.trans (hcomp.trans (ProperSMul.ker_mfderiv_quotientMk x))

/-- **The reduced moment map is smooth**, for the atlas
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. Its composite with the projection from the
level is `z ↦ μ(z) ∘ s` for a right inverse `s` of `β_ℝ : ℝ^ι → V`, since `μ(z) = β_ℝ^* μ_Δ [z]`
(`TauCeti.Toric.DelzantQuotient.delzantMomentMap_eq_comp_reducedMomentMap`). -/
theorem contMDiff_reducedMomentMap
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    letI := hΔ.delzantQuotientChartedSpace hi
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) 𝓘(ℝ, StrongDual ℝ V) ∞
      (DelzantQuotient.reducedMomentMap hβ (c := c)) := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  obtain ⟨s, hs⟩ := (Fintype.linearCombination ℝ fun j ↦ i (u j)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hβ)
  refine ((hΔ.isSubmersion_delzantQuotientMk hi).contMDiff_comp_iff
    DelzantQuotient.mk_surjective le_rfl).1 ?_
  have h : DelzantQuotient.reducedMomentMap hβ ∘ DelzantQuotient.mk = fun x : delzantLevel i u c ↦
      (delzantMomentMap c x).comp (LinearMap.toContinuousLinearMap s) := by
    funext x
    ext v
    simp [DelzantQuotient.delzantMomentMap_eq_comp_reducedMomentMap hβ x, ← LinearMap.comp_apply,
      hs]
  rw [h]
  exact ((contDiff_delzantMomentMap c).contMDiff.comp (hΔ.contMDiff_coe_delzantLevel hi)).clm_comp
    contMDiff_const

/-! ### The vertical tangent vectors and the dimension of the Delzant quotient -/

/-- **The orbits of the kernel torus in the level have dimension `dim 𝔫`.** At a point `x` of the
level the infinitesimal action of `𝔫` is injective, so the orbit directions `𝔫 · x` have the
dimension `d - n` of `𝔫`. -/
theorem finrank_kernelTorusOrbitTangent {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : x ∈ delzantLevel i u c) :
    finrank ℝ (kernelTorusOrbitTangent i u x) =
      finrank ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))) := by
  let g := (weightInfinitesimalAction (fun j ↦ -ContinuousLinearMap.proj j) x).comp
    (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtype
  have hgt (t : ι → ℝ) (ht) : g ⟨t, ht⟩ = weightGenerator (-t) x := by
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, weightInfinitesimalAction_apply]
    congr 1
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun ⟨t, ht⟩ h ↦ Subtype.ext ?_
    rw [hgt] at h
    exact (hΔ.weightGenerator_neg_eq_zero_iff hi hx ht).1 h
  have h := LinearMap.finrank_range_of_inj hg
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

/-- **The orbit directions are vertical.** For `t` in the Lie algebra `𝔫` of the kernel torus,
the generator `t_M(x)` is the image in `ℂ^ι` of a tangent vector of the level at `x` killed by the
differential of the projection onto the Delzant quotient: the velocity of the orbit curve
`s ↦ exp(-i s t) x`, along which the projection is constant. -/
theorem exists_mfderiv_delzantQuotientMk_eq_zero (x : delzantLevel i u c) {t : ι → ℝ}
    (ht : t ∈ LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    ∃ v : TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x,
      mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
            (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
          (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) x v = 0 ∧
        mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x v =
            weightGenerator (-t) x := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  -- The orbit curve `s ↦ exp(-i s t) x` in `ℂ^ι` is the rotation by the angles `[s t]`.
  set g : ℝ → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι := fun s ↦ weightRotation (s • -t) x
  have hg_eq : g = fun s ↦ torusRotation (fun j ↦ ((s • t) j : AddCircle (2 * π))) x := by
    funext s
    rw [torusRotation_coe, ← smul_neg]
  have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞ g := by
    rw [hg_eq]
    exact contMDiff_torusRotation.comp (((AddCircle.contMDiff_coe_pi (2 * π) ∞).comp
      (contMDiff_id.smul contMDiff_const)).prodMk contMDiff_const)
  have hgZ (s : ℝ) : g s ∈ delzantLevel i u c :=
    (weightRotation_mem_delzantLevel_iff _).2 x.property
  set γ : ℝ → delzantLevel i u c := fun s ↦ ⟨g s, hgZ s⟩
  have hγ : ContMDiff 𝓘(ℝ) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞ γ :=
    hΔ.contMDiff_codRestrict_delzantLevel hi hg hgZ
  have hγ0 : γ 0 = x := Subtype.ext (by simp [γ, g, weightRotation_zero])
  -- The projection is constant along the orbit curve.
  have hpγ : (DelzantQuotient.mk ∘ γ) = fun _ ↦ DelzantQuotient.mk x := by
    funext s
    refine DelzantQuotient.mk_eq_mk_iff.2 ⟨fun j ↦ ((s • t) j : AddCircle (2 * π)), ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, facetTorusHom_coe, map_smul, LinearMap.mem_ker.1 ht, smul_zero,
        QuotientAddGroup.mk_zero]
    · exact Subtype.ext ((coe_vadd_delzantLevel _ x).trans (congrFun hg_eq s).symm)
  have hp := (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff.mdifferentiable (by simp)
  have hi' := (hΔ.contMDiff_coe_delzantLevel hi (m := ∞)).mdifferentiable (by simp)
  have hγ' := hγ.mdifferentiable (by simp)
  refine ⟨mfderiv 𝓘(ℝ) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) γ 0 (1 : ℝ), ?_, ?_⟩
  · have h := (mfderiv_comp_apply_of_eq (0 : ℝ) (hp x) (hγ' 0) hγ0 (1 : ℝ)).symm
    rw [hpγ, mfderiv_const] at h
    exact h.trans (zero_apply _)
  · have h := (mfderiv_comp_apply_of_eq (0 : ℝ) (hi' x) (hγ' 0) hγ0 (1 : ℝ)).symm
    have hcomp : (Subtype.val ∘ γ) = g := rfl
    have h0 := (hasDerivAt_weightRotation_smul (-t) (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      0).hasFDerivAt
    rw [zero_smul, weightRotation_zero, ContinuousLinearMap.id_apply] at h0
    rw [hcomp, (hasMFDerivAt_iff_hasFDerivAt.2 h0).mfderiv] at h
    -- The derivative of a curve, as a linear map on `ℝ`, sends `1` to the velocity.
    exact h.trans (one_smul ℝ _)

/-- **The fundamental vector fields of the kernel torus are orbit directions.** The fundamental
vector field on the level `Z` of an element `ξ` of the Lie algebra of the kernel torus, embedded in
`ℂ^ι`, is the generator `t_M` of an element `t` of `𝔫`: the image of `ξ` in the angle coordinates
of the torus `(ℝ / 2πℤ)^ι`. -/
theorem mfderiv_coe_fundamentalVectorField_mem (x : delzantLevel i u c)
    (ξ : kernelTorusLieAlgebra i u) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := (kernelTorusData i u hi).chartedSpace
    mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x
        (fundamentalVectorField (I := 𝓘(ℝ, kernelTorusLieAlgebra i u)) (G := kernelTorus i u)
          𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ξ x) ∈
      kernelTorusOrbitTangent i u x := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := (kernelTorusData i u hi).chartedSpace
  have := (kernelTorusData i u hi).lieGroup
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.contMDiffSMul_kernelTorus hi
  have hJ := contMDiff_toAdd_coe_kernelTorus u hi
  set J : kernelTorus i u → ι → AddCircle (2 * π) :=
    fun k ↦ (k : Multiplicative (ι → AddCircle (2 * π))).toAdd
  set F := fun θ : ι → AddCircle (2 * π) ↦ torusRotation θ x
  have hF : ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞ F :=
    contMDiff_torusRotation.comp (contMDiff_id.prodMk contMDiff_const)
  -- In `ℂ^ι`, the orbit map of `x` is the orbit map of the rotation torus along `J`.
  have hval : (Subtype.val ∘ fun k : kernelTorus i u ↦ k • x) = F ∘ J :=
    funext fun k ↦ coe_kernelTorus_smul k x
  have ho := (ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℝ, kernelTorusLieAlgebra i u))
    (G := kernelTorus i u) (I' := 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (n := ∞)
      x).mdifferentiableAt
      (x := 1) (by simp)
  have hi' := (hΔ.contMDiff_coe_delzantLevel hi (m := ∞)).mdifferentiable (by simp) x
  have h1 := mfderiv_comp_apply_of_eq (1 : kernelTorus i u) hi' ho (one_smul (kernelTorus i u) x) ξ
  have h2 := mfderiv_comp_apply_of_eq (1 : kernelTorus i u)
    ((hF 0).mdifferentiableAt (by simp)) (hJ.mdifferentiableAt (by simp)) rfl ξ
  have h2' := h2.trans (mfderiv_torusRotation_zero (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) J 1 ξ))
  have h3 : mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      (Subtype.val ∘ fun k : kernelTorus i u ↦ k • x) 1 ξ =
      mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
        (F ∘ J) 1 ξ := by
    rw [hval]
  have h4 : mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) Subtype.val x
        (fundamentalVectorField (I := 𝓘(ℝ, kernelTorusLieAlgebra i u)) (G := kernelTorus i u)
          𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ξ x) =
      mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) Subtype.val x
        (mfderiv 𝓘(ℝ, kernelTorusLieAlgebra i u) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          (fun k : kernelTorus i u ↦ k • x) 1 ξ) :=
    congrArg _ (fundamentalVectorField_apply (I := 𝓘(ℝ, kernelTorusLieAlgebra i u))
      (G := kernelTorus i u) (I' := 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ξ x)
  exact mem_kernelTorusOrbitTangent.2
    ⟨_, hi.mfderiv_toAdd_coe_kernelTorus_mem ξ, h2'.symm.trans (h3.symm.trans (h1.trans h4.symm))⟩

/-- **The vertical tangent vectors of the Delzant quotient.** A tangent vector of the level `Z` at
`x` is killed by the differential of the projection onto the Delzant quotient exactly when its
image in `ℂ^ι` lies in the tangent space `𝔫 · x` of the orbit of the kernel torus. -/
theorem ker_mfderiv_delzantQuotientMk_eq_comap (x : delzantLevel i u c) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    (mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) x).ker =
      (kernelTorusOrbitTangent i u x).comap
        (mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
          ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x).toLinearMap := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  let _ := (kernelTorusData i u hi).chartedSpace
  have := (kernelTorusData i u hi).lieGroup
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.contMDiffSMul_kernelTorus hi
  ext v
  constructor
  · intro hv
    rw [hΔ.ker_mfderiv_delzantQuotientMk hi x] at hv
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hv
    refine Submodule.mem_comap.2 ?_
    rw [InfinitesimalAction.fundamental_apply]
    exact hΔ.mfderiv_coe_fundamentalVectorField_mem hi x ξ
  · intro hv
    obtain ⟨t, ht, hvt⟩ := mem_kernelTorusOrbitTangent.1 hv
    obtain ⟨w, hw0, hwi⟩ := hΔ.exists_mfderiv_delzantQuotientMk_eq_zero hi x ht
    obtain rfl : w = v := hΔ.injective_mfderiv_coe_delzantLevel hi x (hwi.trans hvt)
    exact hw0

/-- **The Delzant quotient has dimension `2 dim V`.** At each point `x` of the level, the projection
`Z → M_Δ` is a submersion whose vertical tangent vectors are carried by the inclusion
isomorphically onto the orbit directions `𝔫 · x`, of dimension `dim 𝔫 = d - n` since the
infinitesimal action of the kernel torus is free on the level. As `Z` has dimension `d + n`, the
model space of `M_Δ` has dimension `2n`, where `n = dim V`. -/
theorem finrank_delzantQuotientModelSpace :
    finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) = 2 * finrank ℝ V := by
  -- The level is nonempty, since its image under the moment map is the polytope `Δ`.
  obtain ⟨y, hy⟩ := hΔ.nonempty
  rw [← setOf_exists_mem_delzantLevel i u c] at hy
  obtain ⟨x, hx, -⟩ := hy
  lift x to delzantLevel i u c using hx
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  let D : TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x →L[ℝ]
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) x
  set P := mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
    𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
    (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) x
  -- Rank–nullity for the surjective differential of the projection.
  have hrn := LinearMap.finrank_range_add_finrank_ker P.toLinearMap
  rw [LinearMap.range_eq_top.2 ((hΔ.isSubmersion_delzantQuotientMk hi).surjective_mfderiv
    (x := x) (by simp)), finrank_top] at hrn
  -- The inclusion identifies the vertical tangent space with the orbit directions `𝔫 · x`.
  have hD : Function.Injective D := hΔ.injective_mfderiv_coe_delzantLevel hi x
  have hrange : LinearMap.range (D.toLinearMap.domRestrict (LinearMap.ker P.toLinearMap)) =
      kernelTorusOrbitTangent i u x := by
    refine le_antisymm ?_ fun y hy ↦ ?_
    · rintro _ ⟨⟨v, hv⟩, rfl⟩
      exact (SetLike.ext_iff.1 (hΔ.ker_mfderiv_delzantQuotientMk_eq_comap hi x) v).1 hv
    · obtain ⟨t, ht, rfl⟩ := mem_kernelTorusOrbitTangent.1 hy
      obtain ⟨w, hw0, hwi⟩ := hΔ.exists_mfderiv_delzantQuotientMk_eq_zero hi x ht
      exact ⟨⟨w, hw0⟩, hwi⟩
  have hker : finrank ℝ (LinearMap.ker P.toLinearMap) =
      finrank ℝ (kernelTorusOrbitTangent i u x) := by
    rw [← hrange, LinearMap.finrank_range_of_inj fun v w h ↦ Subtype.ext (hD h)]
  have hO := hΔ.finrank_kernelTorusOrbitTangent hi x.property
  have hdim := hΔ.finrank_ker_linearCombination_real_add_finrank hi
  rw [hker, hO] at hrn
  have h1 : finrank ℝ (TangentSpace 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) x) =
      Fintype.card ι + finrank ℝ V :=
    (finrank_tangentSpace x).trans (finrank_fin_fun ℝ)
  have h2 : finrank ℝ (TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (DelzantQuotient.mk x)) =
      finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) :=
    finrank_tangentSpace _
  omega

end IsDelzant

end TauCeti.Toric
