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
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

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
  (`TauCeti.Toric.IsDelzant.ker_mfderiv_delzantQuotientMk`).

The atlas is modelled on `ℝ^(d + n - k)`, where `d` is the number of facets, `n = dim V` and `k`
is the dimension of the Lie algebra of the kernel torus.

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
      ((Multiplicative.contMDiff_toAdd.comp
        ((kernelTorusData i u hi).contMDiff_subtypeVal.comp contMDiff_fst)).prodMk
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

end IsDelzant

end TauCeti.Toric
