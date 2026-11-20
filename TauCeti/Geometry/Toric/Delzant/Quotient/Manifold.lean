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
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Toric.Delzant.Quotient.Basic

import TauCeti.Geometry.Toric.Delzant.Free
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Smooth

/-!
# The Delzant quotient is a smooth manifold

Let `(u, c)` be a Delzant facet presentation of a polytope `Δ` for an integral lattice
`i : N →+ V`. Delzant's construction realizes `Δ` as the moment polytope of the quotient
`M_Δ = Z / N_Δ` (`TauCeti.Toric.DelzantQuotient`) of the zero level `Z ⊆ ℂ^ι` of the moment map of
the kernel torus `N_Δ ⊆ (ℝ / 2πℤ)^ι` by the action `z_j ↦ exp(-i θ_j) z_j`. The level is a
compact smooth manifold (`TauCeti.Toric.IsDelzant.isManifold_delzantLevel`) on which `N_Δ` acts
freely. This file applies the quotient manifold theorem
(`ProperSMul.instIsManifoldOrbitRelQuotient`) to make `M_Δ` a smooth manifold for which the
projection `Z → M_Δ` is a smooth submersion.

The quotient manifold theorem is stated for multiplicative Lie groups, so the kernel torus enters
as the subgroup `TauCeti.Toric.kernelTorus i u` of the torus `(ℝ / 2πℤ)^ι` written
multiplicatively. The torus `ι → AddCircle (2π)` is an additive Lie group for its product charts
(`Pi.lieAddGroup`), and the kernel torus is closed in it for an integral lattice
(`TauCeti.Toric.IsIntegralLattice.isClosed_kernelTorus`), so by the closed-subgroup theorem it is
an embedded Lie subgroup (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`). The statements below
are for any embedded Lie subgroup structure `d` on the kernel torus.

* **Smoothness.** The torus acts smoothly on `ℂ^ι` (`TauCeti.contMDiff_torusRotation_apply`) and
  the level is a regular level set, so the kernel torus acts smoothly on `Z`
  (`TauCeti.Toric.IsDelzant.contMDiffSMul_kernelTorus`).
* **Properness.** The kernel torus is compact, so its action is proper
  (`TauCeti.Toric.IsIntegralLattice.properSMul_kernelTorus`).
* **Freeness.** Every vertex of `Δ` is smooth, so the action is free
  (`TauCeti.Toric.IsDelzant.isCancelSMul_kernelTorus`).
* **The orbit spaces agree.** Two points of `Z` lie in one orbit of the multiplicative kernel torus
  exactly when they lie in one orbit of `N_Δ`, so `M_Δ` is homeomorphic to the orbit space of the
  quotient manifold theorem
  (`TauCeti.Toric.DelzantQuotient.orbitRelQuotientKernelTorusHomeomorph`), and the slice charts of
  that orbit space transport to `M_Δ`
  (`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`).

The model space is `ProperSMul.QuotientModelSpace F (Fin (d + n) → ℝ)`, the Euclidean space of
dimension `(d + n) - dim F`, where `d` is the number of facets, `d + n = dim Z` for `n = dim V`, and
`F` is the model space of the Lie group structure on the kernel torus; for the closed-subgroup
structure `F` is the Lie algebra of `N_Δ`.

## Main definitions

* `TauCeti.Toric.kernelTorus i u`: the kernel torus `N_Δ` as a subgroup of the multiplicative
  torus.
* `TauCeti.Toric.IsIntegralLattice.kernelTorusLieSubgroupData`: its closed-subgroup Lie group
  structure.
* `TauCeti.Toric.DelzantQuotient.orbitRelQuotientKernelTorusHomeomorph`: `M_Δ` as the orbit space
  of the multiplicative kernel torus.
* `TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`: the atlas of `M_Δ`.

## Main results

* `TauCeti.Toric.IsDelzant.isManifold_delzantQuotient`: **`M_Δ` is a smooth manifold.**
* `TauCeti.Toric.IsDelzant.isSubmersion_mk`: the projection `Z → M_Δ` is a smooth submersion.
* `TauCeti.Toric.IsDelzant.contMDiffSMul_kernelTorus`,
  `TauCeti.Toric.IsIntegralLattice.properSMul_kernelTorus`,
  `TauCeti.Toric.IsDelzant.isCancelSMul_kernelTorus`: the kernel torus acts smoothly, properly and
  freely on the level.
* `TauCeti.Toric.IsDelzant.contMDiff_comp_mk_iff`: a map out of `M_Δ` is smooth exactly when its
  composite with the projection is.

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

open Module Real
open scoped Manifold ContDiff

namespace TauCeti.Toric

/-- The circle `ℝ / 2πℤ` of angles has positive period, so it is a smooth manifold. -/
local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### The kernel torus as a multiplicative group -/

variable (i u) in
/-- The kernel torus `N_Δ = ker (facetTorusHom i u (2π))`, as a subgroup of the torus
`(ℝ / 2πℤ)^ι` written multiplicatively. The closed-subgroup theorem and the quotient manifold
theorem apply to it in this form. It acts on the Delzant level through
`z_j ↦ exp(-i θ_j) z_j` (`TauCeti.Toric.coe_smul_kernelTorus`). -/
def kernelTorus : Subgroup (Multiplicative (ι → AddCircle (2 * π))) :=
  (facetTorusHom i u (2 * π)).ker.toSubgroup

@[simp]
theorem mem_kernelTorus {θ : Multiplicative (ι → AddCircle (2 * π))} :
    θ ∈ kernelTorus i u ↔ θ.toAdd ∈ (facetTorusHom i u (2 * π)).ker :=
  Iff.rfl

/-- An element of the kernel torus acts on the level by the rotation by its angles. -/
@[simp]
theorem coe_smul_kernelTorus (θ : kernelTorus i u) (x : delzantLevel i u c) :
    ((θ • x : delzantLevel i u c) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =
      torusRotation (θ : Multiplicative (ι → AddCircle (2 * π))).toAdd x :=
  (rfl)

/-- **The kernel torus is closed** in the torus, for an integral lattice. -/
theorem IsIntegralLattice.isClosed_kernelTorus (hi : IsIntegralLattice i) :
    IsClosed (kernelTorus i u : Set (Multiplicative (ι → AddCircle (2 * π)))) :=
  hi.isClosed_ker_facetTorusHom u (2 * π)

/-- **The kernel torus is a Lie group.** For an integral lattice, the closed-subgroup theorem
makes the kernel torus an embedded Lie subgroup of the torus `(ℝ / 2πℤ)^ι`, modelled on its Lie
algebra. This is a choice of the structure `d` for which the Delzant quotient is a manifold
(`TauCeti.Toric.IsDelzant.isManifold_delzantQuotient`). -/
def IsIntegralLattice.kernelTorusLieSubgroupData (hi : IsIntegralLattice i) :
    Lie.EmbeddedLieSubgroupData (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (kernelTorus i u)
      (Lie.lieSubalgebraOfSubgroup (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (kernelTorus i u)).toSubmodule :=
  .ofIsClosed hi.isClosed_kernelTorus

/-- The kernel torus acts continuously on the level, by rotations. -/
instance : ContinuousSMul (kernelTorus i u) (delzantLevel i u c) where
  continuous_smul := continuous_induced_rng.2 <| continuous_torusRotation.comp
    ((continuous_toAdd.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- **The kernel torus acts properly on the level**, for an integral lattice: it is a closed
subgroup of the compact torus, hence compact. -/
theorem IsIntegralLattice.properSMul_kernelTorus (hi : IsIntegralLattice i) :
    ProperSMul (kernelTorus i u) (delzantLevel i u c) := by
  have : CompactSpace (kernelTorus i u) :=
    isCompact_iff_compactSpace.1 hi.isClosed_kernelTorus.isCompact
  exact properSMul_of_compactSpace _ _

/-- **The kernel torus acts freely on the level** of a Delzant polytope. -/
theorem IsDelzant.isCancelSMul_kernelTorus (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i) :
    IsCancelSMul (kernelTorus i u) (delzantLevel i u c) :=
  isCancelSMul_iff_eq_one_of_smul_eq.2 fun θ x hx ↦ Subtype.ext <|
    ((isDelzant_iff_forall_eq_zero_of_vadd_eq_self hi).1 hΔ).2.2 _ θ.2 x hx

namespace DelzantQuotient

variable (i u c) in
/-- The Delzant quotient `M_Δ` is homeomorphic to the orbit space of the multiplicative kernel
torus on the level, by the identity on orbits: two points of the level lie in one orbit of the
multiplicative kernel torus exactly when they lie in one orbit of `N_Δ`. -/
def orbitRelQuotientKernelTorusHomeomorph :
    DelzantQuotient i u c ≃ₜ
      MulAction.orbitRel.Quotient (kernelTorus i u) (delzantLevel i u c) where
  toFun := lift (Quotient.mk _) fun θ hθ x ↦
    Quotient.sound (MulAction.mem_orbit x (⟨Multiplicative.ofAdd θ, hθ⟩ : kernelTorus i u))
  invFun := Quotient.lift mk fun _ _ ⟨θ, h⟩ ↦ h ▸ mk_vadd_of_mem_ker θ.2 _
  left_inv q := DelzantQuotient.inductionOn q fun x ↦ by rw [lift_mk, Quotient.lift_mk]
  right_inv q := Quotient.inductionOn' q fun x ↦ by
    rw [Quotient.mk''_eq_mk, Quotient.lift_mk, lift_mk]
  continuous_toFun := continuous_lift _ continuous_quotient_mk'
  continuous_invFun := continuous_mk.quotient_lift _

@[simp]
theorem orbitRelQuotientKernelTorusHomeomorph_mk (x : delzantLevel i u c) :
    orbitRelQuotientKernelTorusHomeomorph i u c (mk x) = Quotient.mk _ x :=
  lift_mk _ _ x

@[simp]
theorem orbitRelQuotientKernelTorusHomeomorph_symm_mk (x : delzantLevel i u c) :
    (orbitRelQuotientKernelTorusHomeomorph i u c).symm (Quotient.mk _ x) = mk x :=
  (rfl)

end DelzantQuotient

/-! ### The smooth structure -/

namespace IsDelzant

variable [FiniteDimensional ℝ V] (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
include hΔ hi

/-- **The kernel torus acts smoothly on the level.** For a manifold structure on the kernel torus
whose inclusion into the torus is smooth, such as its closed-subgroup Lie group structure, the
action on the level `Z`, with the atlas `TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`, is
smooth. -/
theorem contMDiffSMul_kernelTorus [ChartedSpace F (kernelTorus i u)]
    (hK : ContMDiff 𝓘(ℝ, F) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞
      (Subtype.val : kernelTorus i u → Multiplicative (ι → AddCircle (2 * π)))) :
    letI := hΔ.delzantLevelChartedSpace hi
    ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞ (kernelTorus i u)
      (delzantLevel i u c) := by
  let _ := hΔ.delzantLevelChartedSpace hi
  refine ⟨(hΔ.contMDiff_delzantLevel_iff hi).2 ⟨continuous_smul, ?_⟩⟩
  -- On points of `ℂ^ι` the action is the rotation by the angles of the torus element.
  exact contMDiff_torusRotation_apply.comp
    (hK.prodMap (hΔ.contMDiff_coe_delzantLevel hi))

variable [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (kernelTorus i u) F)

omit [FiniteDimensional ℝ F] in
/-- The hypotheses of the quotient manifold theorem for the kernel torus acting on the level. -/
private theorem quotient_hypotheses :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := d.chartedSpace
    ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞ (kernelTorus i u)
        (delzantLevel i u c) ∧
      ProperSMul (kernelTorus i u) (delzantLevel i u c) ∧
      IsCancelSMul (kernelTorus i u) (delzantLevel i u c) ∧
      IsManifold 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞ (delzantLevel i u c) :=
  let _ := d.chartedSpace
  ⟨hΔ.contMDiffSMul_kernelTorus hi d.contMDiff_subtypeVal, hi.properSMul_kernelTorus,
    hΔ.isCancelSMul_kernelTorus hi, hΔ.isManifold_delzantLevel hi ∞⟩

/-- **The atlas of the Delzant quotient.** For a Lie group structure `d` on the kernel torus, such
as its closed-subgroup structure `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`, the slice charts
of the quotient manifold theorem (`ProperSMul.orbitRelQuotientChartedSpace`) on the orbit space of
the kernel torus acting on the level, carried to `M_Δ` along
`TauCeti.Toric.DelzantQuotient.orbitRelQuotientKernelTorusHomeomorph`. -/
@[instance_reducible]
def delzantQuotientChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace F (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      (DelzantQuotient i u c) :=
  letI := hΔ.delzantLevelChartedSpace hi
  letI := d.chartedSpace
  letI := d.lieGroup
  haveI := (hΔ.quotient_hypotheses hi d).1
  haveI := (hΔ.quotient_hypotheses hi d).2.1
  haveI := (hΔ.quotient_hypotheses hi d).2.2.1
  haveI := (hΔ.quotient_hypotheses hi d).2.2.2
  letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) (kernelTorus i u)
    𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) (delzantLevel i u c)
  (DelzantQuotient.orbitRelQuotientKernelTorusHomeomorph i u c).pullbackChartedSpace

/-- **The Delzant quotient is a smooth manifold** for the atlas
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. -/
theorem isManifold_delzantQuotient :
    letI := hΔ.delzantQuotientChartedSpace hi d
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞
      (DelzantQuotient i u c) := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := d.chartedSpace
  let _ := d.lieGroup
  obtain ⟨_, _, _, _⟩ := hΔ.quotient_hypotheses hi d
  let _ := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) (kernelTorus i u)
    𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) (delzantLevel i u c)
  exact (DelzantQuotient.orbitRelQuotientKernelTorusHomeomorph i u c).pullback_isManifold _ _

/-- **The projection onto the Delzant quotient is a smooth submersion**, for the atlases
`TauCeti.Toric.IsDelzant.delzantLevelChartedSpace` of the level and
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace` of the quotient. -/
theorem isSubmersion_mk :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi d
    Manifold.IsSubmersion 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞
      (DelzantQuotient.mk (i := i) (u := u) (c := c)) := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := d.chartedSpace
  let _ := d.lieGroup
  obtain ⟨_, _, _, _⟩ := hΔ.quotient_hypotheses hi d
  let _ := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) (kernelTorus i u)
    𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) (delzantLevel i u c)
  let _ := hΔ.delzantQuotientChartedSpace hi d
  have := hΔ.isManifold_delzantQuotient hi d
  set e := DelzantQuotient.orbitRelQuotientKernelTorusHomeomorph i u c
  -- The projection is the orbit projection of the quotient manifold theorem followed by the
  -- inverse of the diffeomorphism `e` of the transported atlas.
  have hmk : DelzantQuotient.mk (i := i) (u := u) (c := c) =
      (e.pullbackDiffeomorph 𝓘(ℝ, ProperSMul.QuotientModelSpace F
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞).symm ∘
        Quotient.mk (MulAction.orbitRel (kernelTorus i u) (delzantLevel i u c)) := by
    funext x
    rw [Function.comp_apply, Homeomorph.coe_pullbackDiffeomorph_symm,
      DelzantQuotient.orbitRelQuotientKernelTorusHomeomorph_symm_mk]
  rw [hmk]
  have h := ProperSMul.isSubmersion_quotientMk (I := 𝓘(ℝ, F)) (G := kernelTorus i u)
    (I' := 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (M := delzantLevel i u c)
  exact (Manifold.isSubmersionOfComplement_iff.2 fun x ↦
    ((e.pullbackDiffeomorph _ ∞).symm.isLocalDiffeomorph _).comp_isSubmersionAtOfComplement
      (h.isSubmersionOfComplement_complement.isSubmersionAt x)).isSubmersion

/-- **Smooth maps out of the Delzant quotient.** A map `g` out of `M_Δ` is `C^m`, for `m ≤ ∞`,
exactly when its composite with the projection from the level is `C^m`. -/
theorem contMDiff_comp_mk_iff {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    {g : DelzantQuotient i u c → P} {m : WithTop ℕ∞} (hm : m ≤ ∞) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi d
    ContMDiff 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) IP m (g ∘ DelzantQuotient.mk) ↔
      ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        IP m g :=
  letI := hΔ.delzantLevelChartedSpace hi
  letI := hΔ.delzantQuotientChartedSpace hi d
  (hΔ.isSubmersion_mk hi d).contMDiff_comp_iff DelzantQuotient.mk_surjective hm

end IsDelzant

end TauCeti.Toric
