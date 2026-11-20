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
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The Delzant quotient is a smooth manifold

Let `i : N →+ V` be an integral lattice and `(u, c)` a facet presentation of a Delzant polytope
`Δ`. Delzant's construction realizes `Δ` as the moment polytope of the reduced space

`M_Δ = Z / N_Δ` (`TauCeti.Toric.DelzantQuotient i u c`),

where the kernel torus `N_Δ = ker ((ℝ / 2πℤ)^ι → V / 2π i(N))` acts on the zero level `Z` of its
moment map through the rotations `z_j ↦ exp(-i θ_j) z_j` of `ℂ^ι`. The level is a compact
manifold of dimension `d + n`, where `d = #ι` and `n = dim V`
(`TauCeti.Toric.IsDelzant.isManifold_delzantLevel`). This file makes `M_Δ` a smooth manifold for
which the projection `Z → M_Δ` is a smooth submersion, by the quotient manifold theorem
(`ProperSMul.instIsManifoldOrbitRelQuotient`).

* **Smoothness of the rotations.** The rotation action `(θ, z) ↦ θ • z` of the torus
  `(ℝ / 2πℤ)^ι` on `ℂ^ι`, with the torus a manifold modelled on `ℝ^ι`, is smooth
  (`TauCeti.contMDiff_torusRotation`): its coefficients `cos θ_j` and `sin θ_j` are smooth on the
  circle (`Function.Periodic.contMDiff_lift`).
* **The kernel torus as a Lie group.** The torus is a Lie group (`TauCeti.instLieAddGroupPi`) and
  the kernel torus is a closed subgroup of it
  (`TauCeti.Toric.IsIntegralLattice.isClosed_ker_facetTorusHom`), so by the closed-subgroup
  theorem (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`) it is an embedded Lie subgroup,
  modelled on its Lie algebra. Since these theorems are stated for multiplicative groups, the
  kernel torus enters as the subgroup `TauCeti.Toric.kernelTorus i u` of `Multiplicative` of the
  torus.
* **The action on the level.** The kernel torus acts smoothly on `Z`: a smooth map with values
  in the regular level set `Z` is smooth into `Z` (`ContMDiff.codRestrict_levelSet`). It acts
  freely, because the vertices of `Δ` are smooth
  (`TauCeti.Toric.IsDelzant.weightRotation_neg_eq_self_iff`), and properly, because it is
  compact.
* **The quotient.** The orbit space of this action is the Delzant quotient up to the identity of
  points (`TauCeti.Toric.DelzantQuotient.kernelTorusQuotientHomeomorph`), along which the slice
  charts of the quotient manifold theorem are carried to `M_Δ`.

The model space is `ℝ^(d + n - k)`, where `k` is the dimension of the Lie algebra of the kernel
torus as a closed subgroup, so `M_Δ` has dimension `d + n - k`.

## Main definitions

* `TauCeti.Toric.kernelTorus i u`: the kernel torus `N_Δ`, as a subgroup of the multiplicative
  torus.
* `TauCeti.Toric.DelzantQuotient.kernelTorusQuotientHomeomorph`: the identification of `M_Δ` with
  the orbit space of `TauCeti.Toric.kernelTorus i u` acting on `Z`.
* `TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`: the slice charts of `M_Δ`.

## Main results

* `TauCeti.contMDiff_torusRotation`: the rotation action of `(ℝ / 2πℤ)^ι` on `ℂ^ι` is smooth.
* `TauCeti.Toric.IsDelzant.isManifold_delzantQuotient`: the Delzant quotient is a smooth
  manifold.
* `TauCeti.Toric.IsDelzant.isSubmersion_delzantQuotientMk`: the projection from the level onto
  the Delzant quotient is a smooth submersion.
* `TauCeti.Toric.IsDelzant.contMDiff_delzantQuotientMk`: this projection is smooth.
* `TauCeti.Toric.IsDelzant.contMDiff_reducedMomentMap`: the reduced moment map `μ_Δ` is smooth.
* `TauCeti.Toric.IsDelzant.contMDiffSMul_kernelTorus`,
  `TauCeti.Toric.IsDelzant.isCancelSMul_kernelTorus`,
  `TauCeti.Toric.IsIntegralLattice.properSMul_kernelTorus`: the kernel torus acts smoothly, freely
  and properly on the level.

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

open Set Real Manifold Module
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι]

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-! ### Smoothness of the rotation action -/

/-- The coefficients `cos θ_j` and `sin θ_j` of the rotation by `θ`, and the coordinates `z.1 j` and
`z.2 j` of the rotated point, are smooth functions of `(θ, z)`. -/
private theorem contMDiff_torusRotation_coefficients (j : ι) :
    let I := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    ContMDiff I 𝓘(ℝ) ∞
        (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
          cos_periodic.lift (p.1 j)) ∧
      ContMDiff I 𝓘(ℝ) ∞
        (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
          sin_periodic.lift (p.1 j)) ∧
      ContMDiff I 𝓘(ℝ) ∞
        (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
          p.2.1 j) ∧
      ContMDiff I 𝓘(ℝ) ∞
        (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
          p.2.2 j) := by
  have hfst : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) 𝓘(ℝ) ∞
      fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ x.1 j :=
    ((EuclideanSpace.proj j : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι))).contMDiff
  have hsnd : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) 𝓘(ℝ) ∞
      fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ x.2 j :=
    ((EuclideanSpace.proj j : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι))).contMDiff
  exact ⟨(cos_periodic.contMDiff_lift contDiff_cos).comp
      (contMDiff_apply.comp contMDiff_fst),
    (sin_periodic.contMDiff_lift contDiff_sin).comp (contMDiff_apply.comp contMDiff_fst),
    hfst.comp contMDiff_snd, hsnd.comp contMDiff_snd⟩

/-- **The rotation action of the torus `(ℝ / 2πℤ)^ι` on `ℂ^ι` is smooth**, for the torus
modelled on `ℝ^ι`: the map `(θ, z) ↦ (z_j ↦ exp(-i θ_j) z_j)` is smooth. -/
theorem contMDiff_torusRotation :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        torusRotation p.1 p.2 := by
  have hpair : (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
      torusRotation p.1 p.2) = fun p ↦ ((torusRotation p.1 p.2).1, (torusRotation p.1 p.2).2) :=
    (rfl)
  rw [hpair]
  -- Each coordinate of the rotated point is a polynomial in smooth functions.
  refine ContMDiff.prodMk_space ?_ ?_
  · have h : (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        (torusRotation p.1 p.2).1) = fun p ↦ (EuclideanSpace.equiv ι ℝ).symm
          fun j ↦ cos_periodic.lift (p.1 j) * p.2.1 j + sin_periodic.lift (p.1 j) * p.2.2 j := by
      funext p
      ext j
      exact torusRotation_apply_fst p.1 p.2 j
    rw [h]
    refine ((EuclideanSpace.equiv ι ℝ).symm : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι).contMDiff.comp
      (contMDiff_pi_module_iff.2 fun j ↦ ?_)
    obtain ⟨hcos, hsin, hfst, hsnd⟩ := contMDiff_torusRotation_coefficients (ι := ι) j
    exact (hcos.mul hfst).add (hsin.mul hsnd)
  · have h : (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        (torusRotation p.1 p.2).2) = fun p ↦ (EuclideanSpace.equiv ι ℝ).symm
          fun j ↦ -(sin_periodic.lift (p.1 j) * p.2.1 j) + cos_periodic.lift (p.1 j) * p.2.2 j := by
      funext p
      ext j
      exact torusRotation_apply_snd p.1 p.2 j
    rw [h]
    refine ((EuclideanSpace.equiv ι ℝ).symm : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι).contMDiff.comp
      (contMDiff_pi_module_iff.2 fun j ↦ ?_)
    obtain ⟨hcos, hsin, hfst, hsnd⟩ := contMDiff_torusRotation_coefficients (ι := ι) j
    exact (hsin.mul hfst).neg.add (hcos.mul hsnd)

namespace Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### The kernel torus as a Lie group -/

variable (i u) in
/-- The kernel torus `N_Δ = ker ((ℝ / 2πℤ)^ι → V / 2π i(N))` of `TauCeti.Toric.facetTorusHom`, as a
subgroup of `Multiplicative` of the torus `(ℝ / 2πℤ)^ι`. This is the form in which the
closed-subgroup theorem and the quotient manifold theorem apply to it. -/
abbrev kernelTorus : Subgroup (Multiplicative (ι → AddCircle (2 * π))) :=
  AddSubgroup.toSubgroup (facetTorusHom i u (2 * π)).ker

/-- For an integral lattice, the kernel torus is closed. -/
theorem IsIntegralLattice.isClosed_kernelTorus (hi : IsIntegralLattice i) :
    IsClosed (kernelTorus i u : Set (Multiplicative (ι → AddCircle (2 * π)))) :=
  hi.isClosed_ker_facetTorusHom u (2 * π)

/-- The kernel torus acts on the level through the rotations of `ℂ^ι`. -/
@[simp]
theorem coe_kernelTorus_smul (k : kernelTorus i u) (x : delzantLevel i u c) :
    ((k • x : delzantLevel i u c) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =
      torusRotation (Multiplicative.toAdd (k : Multiplicative (ι → AddCircle (2 * π)))) x :=
  (rfl)

/-- Two points of the level lie in one orbit of the kernel torus, acting as a subgroup of the
multiplicative torus, exactly when they have the same class in the Delzant quotient. -/
theorem DelzantQuotient.mk_eq_mk_iff_orbitRel {x y : delzantLevel i u c} :
    DelzantQuotient.mk x = DelzantQuotient.mk y ↔
      MulAction.orbitRel (kernelTorus i u) (delzantLevel i u c) x y := by
  rw [DelzantQuotient.mk_eq_mk_iff, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨fun ⟨θ, hθ, h⟩ ↦ ⟨⟨Multiplicative.ofAdd θ, hθ⟩, h⟩,
    fun ⟨k, hk⟩ ↦ ⟨Multiplicative.toAdd (k : Multiplicative (ι → AddCircle (2 * π))), k.2, hk⟩⟩

/-- The orbit space of the kernel torus, acting on the level as a subgroup of the multiplicative
torus, is the Delzant quotient: the two orbit relations agree
(`TauCeti.Toric.DelzantQuotient.mk_eq_mk_iff_orbitRel`), and the identity of points descends to a
homeomorphism. -/
def DelzantQuotient.kernelTorusQuotientHomeomorph :
    DelzantQuotient i u c ≃ₜ MulAction.orbitRel.Quotient (kernelTorus i u) (delzantLevel i u c) :=
  have hf (θ : ι → AddCircle (2 * π)) (hθ : θ ∈ (facetTorusHom i u (2 * π)).ker)
      (x : delzantLevel i u c) :
      Quotient.mk (MulAction.orbitRel (kernelTorus i u) (delzantLevel i u c)) (θ +ᵥ x) =
        Quotient.mk _ x :=
    Quotient.sound
      (DelzantQuotient.mk_eq_mk_iff_orbitRel.1 (DelzantQuotient.mk_vadd_of_mem_ker hθ x))
  { toFun := DelzantQuotient.lift (Quotient.mk _) hf
    invFun := Quotient.lift DelzantQuotient.mk fun _ _ h ↦
      DelzantQuotient.mk_eq_mk_iff_orbitRel.2 h
    left_inv q := DelzantQuotient.inductionOn q fun x ↦ by
      rw [DelzantQuotient.lift_mk, Quotient.lift_mk]
    right_inv q := Quotient.inductionOn q fun x ↦ by
      rw [Quotient.lift_mk, DelzantQuotient.lift_mk]
    continuous_toFun := DelzantQuotient.continuous_lift hf continuous_quotient_mk'
    continuous_invFun := continuous_quot_lift _ DelzantQuotient.continuous_mk }

@[simp]
theorem DelzantQuotient.kernelTorusQuotientHomeomorph_mk (x : delzantLevel i u c) :
    DelzantQuotient.kernelTorusQuotientHomeomorph (DelzantQuotient.mk x) =
      Quotient.mk (MulAction.orbitRel (kernelTorus i u) (delzantLevel i u c)) x :=
  DelzantQuotient.lift_mk _ _ x

@[simp]
theorem DelzantQuotient.kernelTorusQuotientHomeomorph_symm_mk (x : delzantLevel i u c) :
    DelzantQuotient.kernelTorusQuotientHomeomorph.symm
        (Quotient.mk (MulAction.orbitRel (kernelTorus i u) (delzantLevel i u c)) x) =
      DelzantQuotient.mk x :=
  (rfl)

/-! ### The Delzant quotient as a manifold -/

variable (i u) in
/-- The model space of the Delzant quotient, `ℝ^(d + n - k)`, where `d` is the number of facets,
`n = dim V` and `k` is the dimension of the Lie algebra of the kernel torus. -/
abbrev DelzantQuotientModel : Type :=
  ProperSMul.QuotientModelSpace
    (Lie.lieSubalgebraOfSubgroup (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (kernelTorus i u)).toSubmodule
    (Fin (Fintype.card ι + finrank ℝ V) → ℝ)

/-- **The kernel torus acts properly on the level**: it is a compact group acting continuously on
the Hausdorff space `Z`. -/
theorem IsIntegralLattice.properSMul_kernelTorus (hi : IsIntegralLattice i) :
    ProperSMul (kernelTorus i u) (delzantLevel i u c) :=
  have : CompactSpace (kernelTorus i u) :=
    isCompact_iff_compactSpace.1 hi.isClosed_kernelTorus.isCompact
  -- An element of the kernel torus acts through its underlying angles.
  have : ContinuousSMul (kernelTorus i u) (delzantLevel i u c) :=
    ⟨continuous_vadd.comp
      ((continuous_toAdd.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)⟩
  properSMul_of_compactSpace (kernelTorus i u) (delzantLevel i u c)

namespace IsDelzant

variable [FiniteDimensional ℝ V] (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)

include hΔ hi

/-- **The kernel torus acts smoothly on the level**, for the closed-subgroup structure of the
kernel torus and the regular-level atlas `TauCeti.Toric.IsDelzant.delzantLevelChartedSpace` of the
level. -/
theorem contMDiffSMul_kernelTorus :
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed
      (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (hi.isClosed_kernelTorus (u := u))).chartedSpace
    letI := hΔ.delzantLevelChartedSpace hi
    ContMDiffSMul 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
        (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (kernelTorus i u)).toSubmodule)
      𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞ (kernelTorus i u) (delzantLevel i u c) := by
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed
    (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (hi.isClosed_kernelTorus (u := u))
  let _ := d.chartedSpace
  let _ := hΔ.delzantLevelChartedSpace hi
  -- The action map, followed by the inclusion of the level, is the rotation of `ℂ^ι` by the
  -- underlying angles, which is smooth.
  have hg : ContMDiff (𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
        (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (kernelTorus i u)).toSubmodule).prod
      𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞
      fun p : kernelTorus i u × delzantLevel i u c ↦
        torusRotation (Multiplicative.toAdd (p.1 : Multiplicative (ι → AddCircle (2 * π))))
          (p.2 : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
    contMDiff_torusRotation.comp
      ((d.contMDiff_subtypeVal.comp contMDiff_fst).prodMk
        ((hΔ.contMDiff_coe_delzantLevel hi).comp contMDiff_snd))
  exact ⟨hΔ.contMDiff_codRestrict_delzantLevel hi hg
    fun p ↦ (torusRotation_mem_delzantLevel_iff _).2 p.2.2⟩

/-- **The kernel torus acts freely on the level**, because every vertex of the Delzant polytope is
smooth. -/
theorem isCancelSMul_kernelTorus : IsCancelSMul (kernelTorus i u) (delzantLevel i u c) := by
  refine isCancelSMul_iff_stabilizer_eq_bot.2 fun x ↦ (Subgroup.eq_bot_iff_forall _).2 fun k hk ↦ ?_
  set θ := Multiplicative.toAdd (k : Multiplicative (ι → AddCircle (2 * π)))
  choose t ht using fun j ↦ QuotientAddGroup.mk_surjective (θ j)
  have htθ : (fun j ↦ (t j : AddCircle (2 * π))) = θ := funext ht
  have hfix : weightRotation (-t) x = x := by
    rw [← torusRotation_coe, htθ]
    exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hk)
  have hθ : θ = 0 := by
    rw [← htθ]
    exact (hΔ.weightRotation_neg_eq_self_iff hi x.2 (htθ ▸ k.2)).1 hfix
  exact Subtype.ext (congrArg Multiplicative.ofAdd hθ)

/-- The hypotheses of the quotient manifold theorem for the action of the kernel torus on the
level, for the closed-subgroup structure of the kernel torus and the regular-level atlas of the
level. -/
private theorem quotient_hypotheses :
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed
      (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (hi.isClosed_kernelTorus (u := u))).chartedSpace
    letI := hΔ.delzantLevelChartedSpace hi
    LieGroup 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
        (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (kernelTorus i u)).toSubmodule) ∞
        (kernelTorus i u) ∧
      IsManifold 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞ (delzantLevel i u c) ∧
      ContMDiffSMul 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
          (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (kernelTorus i u)).toSubmodule)
        𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) ∞ (kernelTorus i u) (delzantLevel i u c) ∧
      ProperSMul (kernelTorus i u) (delzantLevel i u c) := by
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed
    (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (hi.isClosed_kernelTorus (u := u))
  let _ := d.chartedSpace
  let _ := hΔ.delzantLevelChartedSpace hi
  exact ⟨d.lieGroup, hΔ.isManifold_delzantLevel hi ∞, hΔ.contMDiffSMul_kernelTorus hi,
    hi.properSMul_kernelTorus⟩

/-- The slice charts of the quotient manifold theorem on the orbit space of the kernel torus. -/
@[instance_reducible]
private def orbitRelQuotientChartedSpace :
    ChartedSpace (DelzantQuotientModel i u)
      (MulAction.orbitRel.Quotient (kernelTorus i u) (delzantLevel i u c)) :=
  letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed
    (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (hi.isClosed_kernelTorus (u := u))).chartedSpace
  letI := hΔ.delzantLevelChartedSpace hi
  haveI := (hΔ.quotient_hypotheses hi).1
  haveI := (hΔ.quotient_hypotheses hi).2.1
  haveI := (hΔ.quotient_hypotheses hi).2.2.1
  haveI := (hΔ.quotient_hypotheses hi).2.2.2
  haveI := hΔ.isCancelSMul_kernelTorus hi
  ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
      (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (kernelTorus i u)).toSubmodule)
    (kernelTorus i u) 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) (delzantLevel i u c)

/-- By the quotient manifold theorem, the orbit space of the kernel torus is a smooth manifold and
the orbit projection is a smooth submersion. -/
private theorem isManifold_and_isSubmersion_orbitRelQuotient :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.orbitRelQuotientChartedSpace hi
    IsManifold 𝓘(ℝ, DelzantQuotientModel i u) ∞
        (MulAction.orbitRel.Quotient (kernelTorus i u) (delzantLevel i u c)) ∧
      IsSubmersion 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) 𝓘(ℝ, DelzantQuotientModel i u) ∞
        (Quotient.mk (MulAction.orbitRel (kernelTorus i u) (delzantLevel i u c))) := by
  let _ := (Lie.EmbeddedLieSubgroupData.ofIsClosed
    (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (hi.isClosed_kernelTorus (u := u))).chartedSpace
  let _ := hΔ.delzantLevelChartedSpace hi
  obtain ⟨_, _, _, _⟩ := hΔ.quotient_hypotheses hi
  have := hΔ.isCancelSMul_kernelTorus hi
  exact ⟨ProperSMul.instIsManifoldOrbitRelQuotient, ProperSMul.isSubmersion_quotientMk⟩

/-- **The atlas of the Delzant quotient** `M_Δ = Z / N_Δ`, modelled on `ℝ^(d + n - k)`: the slice
charts of the quotient manifold theorem for the free and proper action of the kernel torus `N_Δ`,
with its closed-subgroup structure, on the level `Z`, with its regular-level atlas
`TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`. -/
@[instance_reducible]
def delzantQuotientChartedSpace :
    ChartedSpace (DelzantQuotientModel i u) (DelzantQuotient i u c) :=
  letI := hΔ.orbitRelQuotientChartedSpace hi
  DelzantQuotient.kernelTorusQuotientHomeomorph.pullbackChartedSpace

/-- **The Delzant quotient is a smooth manifold**, for the atlas
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. -/
theorem isManifold_delzantQuotient :
    letI := hΔ.delzantQuotientChartedSpace hi
    IsManifold 𝓘(ℝ, DelzantQuotientModel i u) ∞ (DelzantQuotient i u c) :=
  letI := hΔ.orbitRelQuotientChartedSpace hi
  haveI := (hΔ.isManifold_and_isSubmersion_orbitRelQuotient hi).1
  DelzantQuotient.kernelTorusQuotientHomeomorph.pullback_isManifold _ _

/-- **The projection onto the Delzant quotient is a smooth submersion**, from the level `Z` with
its regular-level atlas to `M_Δ` with the atlas
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. In particular a map out of `M_Δ` is smooth
exactly when its composite with the projection is (`Manifold.IsSubmersion.contMDiff_comp_iff`). -/
theorem isSubmersion_delzantQuotientMk :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    IsSubmersion 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) 𝓘(ℝ, DelzantQuotientModel i u) ∞
      (DelzantQuotient.mk (i := i) (u := u) (c := c)) := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.orbitRelQuotientChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := (hΔ.isManifold_and_isSubmersion_orbitRelQuotient hi).1
  have := hΔ.isManifold_delzantQuotient hi
  -- The homeomorphism onto the orbit space is a diffeomorphism for the pulled-back charts.
  have he := ((DelzantQuotient.kernelTorusQuotientHomeomorph (i := i) (u := u)
    (c := c)).pullbackDiffeomorph 𝓘(ℝ, DelzantQuotientModel i u) ∞).symm.isLocalDiffeomorph
  rw [Homeomorph.coe_pullbackDiffeomorph_symm] at he
  have hF := (hΔ.isManifold_and_isSubmersion_orbitRelQuotient hi).2
  -- The projection is the orbit projection followed by the inverse homeomorphism.
  have hmk : (DelzantQuotient.mk : delzantLevel i u c → DelzantQuotient i u c) =
      DelzantQuotient.kernelTorusQuotientHomeomorph.symm ∘
        Quotient.mk (MulAction.orbitRel (kernelTorus i u) (delzantLevel i u c)) :=
    funext fun x ↦ (DelzantQuotient.kernelTorusQuotientHomeomorph_symm_mk x).symm
  refine (isSubmersionOfComplement_iff
    (F := hF.complement).2 fun x ↦ ?_).isSubmersion
  rw [hmk]
  exact (he _).comp_isSubmersionAtOfComplement
    (isSubmersionOfComplement_iff.1 hF.isSubmersionOfComplement_complement x)

/-- The projection from the level onto the Delzant quotient is smooth. -/
theorem contMDiff_delzantQuotientMk :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    ContMDiff 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) 𝓘(ℝ, DelzantQuotientModel i u) ∞
      (DelzantQuotient.mk (i := i) (u := u) (c := c)) := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  exact (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff

/-- **The reduced moment map is smooth** for the atlas
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace`. Its composite with the projection from the
level is `z ↦ μ(z) ∘ s` for a right inverse `s` of `β_ℝ : ℝ^ι → V`, by `μ(z) = β_ℝ^* μ_Δ [z]`. -/
theorem contMDiff_reducedMomentMap
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    letI := hΔ.delzantQuotientChartedSpace hi
    ContMDiff 𝓘(ℝ, DelzantQuotientModel i u) 𝓘(ℝ, StrongDual ℝ V) ∞
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
    rw [Function.comp_apply, DelzantQuotient.delzantMomentMap_eq_comp_reducedMomentMap hβ x]
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap']
    rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  rw [h]
  exact ((contDiff_delzantMomentMap c).contMDiff.comp (hΔ.contMDiff_coe_delzantLevel hi)).clm_comp
    contMDiff_const

end IsDelzant

end Toric

end TauCeti
