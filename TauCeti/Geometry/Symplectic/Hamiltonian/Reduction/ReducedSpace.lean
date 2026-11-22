/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.LevelAction
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Submanifold

import TauCeti.Geometry.Lie.Subgroup.Differential
import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# The Marsden–Weinstein–Meyer reduced space

Let a Lie group `G` act smoothly and properly by symplectomorphisms on a symplectic manifold
`(M, σ)`, with coadjoint-equivariant moment map `μ : M → 𝔤*`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`). Write `G_c` for the coadjoint stabilizer of
`c ∈ 𝔤*`, with Lie algebra `𝔤_c = {ξ | ⁅ξ, c⁆ = 0}`, and let `c` be a regular value of `μ` such
that `G_c` acts freely on the level `Z = μ⁻¹(c)`. The **Marsden–Weinstein–Meyer theorem** says
that the reduced space `Z / G_c` is a smooth manifold, of dimension `dim M - dim 𝔤 - dim 𝔤_c` when
`Z` is nonempty, carrying a unique symplectic form `ω_red` with

`π^* ω_red = i^* σ`,

for the orbit projection `π : Z → Z / G_c` and the inclusion `i : Z → M`. This file assembles it:

* If `G` acts freely at every point of `Z`, then `c` is a regular value
  (`forall_differential_surjective_of_stabilizer_eq_bot`) and `G_c` acts freely on `Z`
  (`isCancelSMul_levelSubMulAction`).
* As `c` is a regular value, `Z` is an embedded submanifold of `M` with tangent spaces `ker dμ`.
  Its regular-level atlas (`TauCeti.SmoothTwoForm.IsMomentMap.levelChartedSpace`) is carried to
  the `G_c`-space `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulAction`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`).
* Give `G_c` an embedded Lie subgroup structure `d`, for instance that of the closed-subgroup
  theorem (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` with
  `TauCeti.Lie.isClosed_stabilizer_coadjointRepresentation`). Then `G_c` acts smoothly, properly and
  freely on `Z`, and the quotient manifold theorem (`ProperSMul.instIsManifoldOrbitRelQuotient`)
  makes `Z / G_c` a smooth manifold
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isManifold_orbitRelQuotient`) for which `π` is a
  submersion
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isSubmersion_quotientMk_levelSubMulAction`).
* The kernel of `dπ_z` is the orbit tangent space of `G_c` at `z`. The inclusion carries it
  injectively into `𝔤 · z ∩ ker dμ_z = 𝔤_c · z`. It has the dimension of `𝔤_c`, since `G_c` acts
  freely and is a manifold of dimension `dim 𝔤_c`
  (`TauCeti.Lie.finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation`), while
  `𝔤_c · z` has dimension at most that. So **the
  vertical vectors of `π` are those that `di` sends into `𝔤_c · z`**
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.ker_mfderiv_quotientMk_levelSubMulAction`).

These are the level data of `existsUnique_isSymplectic_mpullback_eq_mpullback`
(`TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm`), which descends `i^* σ` to the
reduced symplectic form.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `levelSubMulActionChartedSpace`, `isManifold_levelSubMulAction`,
  `isSmoothEmbedding_coe_levelSubMulAction`, `range_mfderiv_coe_levelSubMulAction`: the regular
  level `μ⁻¹(c)`, as a `G_c`-space, is an embedded submanifold with tangent spaces `ker dμ`.
* `contMDiff_levelSubMulActionVal`: its `G_c`-equivariant inclusion into `M` is smooth.
* `orbitRelQuotientChartedSpace`, `isManifold_orbitRelQuotient`,
  `isSubmersion_quotientMk_levelSubMulAction`: the reduced space `μ⁻¹(c) / G_c` is a smooth
  manifold and the orbit projection is a submersion.
* `ker_mfderiv_quotientMk_levelSubMulAction`: the vertical directions of the orbit projection.
* `existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`: **the Marsden–Weinstein–Meyer
  theorem**, the unique reduced symplectic form.
* `finrank_quotientModelSpace_add_finrank_add_finrank_lieAnnihilator`: when the level is nonempty,
  the reduced space has dimension `dim M - dim 𝔤 - dim 𝔤_c`.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* K. Meyer, *Symmetries and integrals in mechanics*, in *Dynamical Systems* (M. Peixoto, ed.),
  Academic Press, 1973, 259–273.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the proof of the Marsden–Weinstein–Meyer theorem).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {n : ℕ}

/-! ### The level as a manifold -/

/-- The points of the `G_c`-space `μ⁻¹(c)` are those of the subtype `{x // μ x = c}`. -/
private def levelSubMulActionHomeomorph (h : σ.IsEquivariantMomentMap μ) :
    h.levelSubMulAction c ≃ₜ {x : M // μ x = c} :=
  (Homeomorph.refl M).subtype fun _ ↦ h.mem_levelSubMulAction

omit [I'.Boundaryless] in
private theorem coe_levelSubMulActionHomeomorph (h : σ.IsEquivariantMomentMap μ)
    (z : h.levelSubMulAction c) : (levelSubMulActionHomeomorph h z : M) = z :=
  (rfl)

variable (c) in
/-- **The atlas of the level `μ⁻¹(c)` as a `G_c`-space.** The regular-level atlas
`TauCeti.SmoothTwoForm.IsMomentMap.levelChartedSpace`, modelled on `Fin n → ℝ` for
`n = dim M - dim 𝔤`, carried to the `G_c`-space
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulAction` along the identity of points. -/
@[instance_reducible]
def levelSubMulActionChartedSpace (h : σ.IsEquivariantMomentMap μ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n) :
    ChartedSpace (Fin n → ℝ) (h.levelSubMulAction c) :=
  letI := h.toIsMomentMap.levelChartedSpace hreg hn
  (levelSubMulActionHomeomorph h).pullbackChartedSpace

variable (h : σ.IsEquivariantMomentMap μ)

section Level

variable (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)

/-- The two atlases of the level are identified by the identity of points. -/
private def levelSubMulActionDiffeomorph :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.toIsMomentMap.levelChartedSpace hreg hn
    h.levelSubMulAction c ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), 𝓘(ℝ, Fin n → ℝ)⟯ {x : M // μ x = c} :=
  letI := h.toIsMomentMap.levelChartedSpace hreg hn
  (levelSubMulActionHomeomorph h).pullbackDiffeomorph _ _

private theorem coe_comp_levelSubMulActionDiffeomorph :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.toIsMomentMap.levelChartedSpace hreg hn
    Subtype.val ∘ h.levelSubMulActionDiffeomorph hreg hn =
      (Subtype.val : h.levelSubMulAction c → M) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.toIsMomentMap.levelChartedSpace hreg hn
  funext z
  rw [Function.comp_apply, levelSubMulActionDiffeomorph, Homeomorph.coe_pullbackDiffeomorph,
    coe_levelSubMulActionHomeomorph]

/-- **A regular level is a smooth manifold**, as a `G_c`-space, for the atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`. -/
theorem isManifold_levelSubMulAction :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ (h.levelSubMulAction c) :=
  letI := h.toIsMomentMap.levelChartedSpace hreg hn
  letI := h.toIsMomentMap.isManifold_level hreg hn
  (levelSubMulActionHomeomorph h).pullback_isManifold _ _

/-- **A regular level is an embedded submanifold**, as a `G_c`-space: its inclusion into `M` is a
smooth embedding. -/
theorem isSmoothEmbedding_coe_levelSubMulAction :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) I' ∞
      (Subtype.val : h.levelSubMulAction c → M) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.toIsMomentMap.levelChartedSpace hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  rw [← h.coe_comp_levelSubMulActionDiffeomorph hreg hn]
  exact isSmoothEmbedding_comp_diffeomorph _
    (h.toIsMomentMap.isSmoothEmbedding_coe_level hreg hn)

/-- **The inclusion of a regular level is smooth**, as the `G_c`-equivariant map
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionVal`. -/
theorem contMDiff_levelSubMulActionVal :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    ContMDiff 𝓘(ℝ, Fin n → ℝ) I' ∞ (h.levelSubMulActionVal c) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  rw [coe_levelSubMulActionVal]
  exact (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff

/-- **The tangent space of a regular level is the kernel of `dμ`**, for the level as a
`G_c`-space: at `z`, the differential of the inclusion has range `ker dμ_z`. -/
theorem range_mfderiv_coe_levelSubMulAction (z : h.levelSubMulAction c) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    LinearMap.range
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.levelSubMulAction c → M) z).toLinearMap =
      LinearMap.ker (h.differential z) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.toIsMomentMap.levelChartedSpace hreg hn
  rw [← h.coe_comp_levelSubMulActionDiffeomorph hreg hn,
    Diffeomorph.range_mfderiv_comp_diffeomorph _ (by simp)]
  exact h.toIsMomentMap.range_mfderiv_coe_level hreg hn _

end Level

/-! ### The reduced space -/

section Quotient

variable [ProperSMul G M]
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)

omit [FiniteDimensional ℝ F]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The hypotheses of the quotient manifold theorem for the action of `G_c`, with the Lie group
structure `d`, on the regular level `μ⁻¹(c)`, other than freeness. -/
private theorem quotient_hypotheses :
    letI := d.chartedSpace
    letI := h.levelSubMulActionChartedSpace c hreg hn
    LieGroup 𝓘(ℝ, F) ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c) ∧
      IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ (h.levelSubMulAction c) ∧
      ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, Fin n → ℝ) ∞
        ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) ∧
      ProperSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) :=
  let := d.chartedSpace
  let := h.levelSubMulActionChartedSpace c hreg hn
  ⟨d.lieGroup, h.isManifold_levelSubMulAction hreg hn,
    h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn),
    h.properSMul_levelSubMulAction⟩

variable (c) in
/-- **The atlas of the reduced space** `μ⁻¹(c) / G_c`: the slice charts of the quotient manifold
theorem `ProperSMul.orbitRelQuotientChartedSpace`, for the free and proper action of the coadjoint
stabilizer `G_c`, with the Lie group structure `d`, on the regular level `μ⁻¹(c)`. If `G` acts
freely on the level, then `c` is a regular value
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.forall_differential_surjective_of_stabilizer_eq_bot`)
and `G_c` acts freely on the level
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCancelSMul_levelSubMulAction`). -/
@[instance_reducible]
def orbitRelQuotientChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace F (Fin n → ℝ))
      (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c)) :=
  letI := d.chartedSpace
  letI := h.levelSubMulActionChartedSpace c hreg hn
  haveI := (h.quotient_hypotheses hreg hn d).1
  haveI := (h.quotient_hypotheses hreg hn d).2.1
  haveI := (h.quotient_hypotheses hreg hn d).2.2.1
  haveI := (h.quotient_hypotheses hreg hn d).2.2.2
  ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F)
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) 𝓘(ℝ, Fin n → ℝ) (h.levelSubMulAction c)

/-- **The reduced space is a smooth manifold** `μ⁻¹(c) / G_c`, for the atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientChartedSpace`. -/
theorem isManifold_orbitRelQuotient :
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞
      (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c)) := by
  let := d.chartedSpace
  let := h.levelSubMulActionChartedSpace c hreg hn
  obtain ⟨_, _, _, _⟩ := h.quotient_hypotheses hreg hn d
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- **The orbit projection onto the reduced space is a smooth submersion.** -/
theorem isSubmersion_quotientMk_levelSubMulAction :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    Manifold.IsSubmersion 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞
      (Quotient.mk (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c))) := by
  let := d.chartedSpace
  let := h.levelSubMulActionChartedSpace c hreg hn
  obtain ⟨_, _, _, _⟩ := h.quotient_hypotheses hreg hn d
  exact ProperSMul.isSubmersion_quotientMk

omit [I'.Boundaryless] [ProperSMul G M] [FiniteDimensional ℝ F]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The orbit directions of `G_c` on the level are orbit directions of `G`: the inclusion of the
level is `G_c`-equivariant, and `G_c` acts on `M` through its inclusion into `G`, so the
differential of the inclusion carries the fundamental vector field of `ξ ∈ Lie(G_c)` to that of
its image in `𝔤`. -/
private theorem mfderiv_coe_fundamentalVectorField_mem_orbitTangent
    [ChartedSpace F ((Lie.coadjointRepresentation ℝ I G).stabilizer c)]
    [ChartedSpace (Fin n → ℝ) (h.levelSubMulAction c)]
    [ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, Fin n → ℝ) ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c)]
    (hGc : ContMDiff 𝓘(ℝ, F) I ∞
      (Subtype.val : (Lie.coadjointRepresentation ℝ I G).stabilizer c → G))
    (hi : ContMDiff 𝓘(ℝ, Fin n → ℝ) I' ∞ (Subtype.val : h.levelSubMulAction c → M))
    (z : h.levelSubMulAction c)
    (ξ : GroupLieAlgebra 𝓘(ℝ, F) ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.levelSubMulAction c → M) z
        (fundamentalVectorField 𝓘(ℝ, Fin n → ℝ) ξ z) ∈
      (InfinitesimalAction.fundamental I G I' M).orbitTangent z := by
  have h1 := mfderiv_fundamentalVectorField_of_map_smul (I := 𝓘(ℝ, F))
    (hi.mdifferentiableAt (by simp))
    ((ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, Fin n → ℝ)) (n := ∞)
      z).mdifferentiableAt (by simp)) (fun g ↦ SubMulAction.val_smul g z) ξ
  have h2 := MonoidHom.fundamentalVectorField_groupLieAlgebraMap (I := I) (I' := I') (M := M)
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c).subtype
    (hGc.mdifferentiableAt (by simp)) (fun k x ↦ Subgroup.smul_def k x) ξ
  refine (InfinitesimalAction.mem_orbitTangent_iff _ _).2
    ⟨((Lie.coadjointRepresentation ℝ I G).stabilizer c).subtype.groupLieAlgebraMap
      𝓘(ℝ, F) I ξ, ?_⟩
  rw [InfinitesimalAction.fundamental_apply, h2]
  exact h1.symm

/-- **The vertical directions of the reduced space are the stabilizer orbit directions.** At a
point `z` of the level, a tangent vector is in the kernel of the differential of the orbit
projection `μ⁻¹(c) → μ⁻¹(c) / G_c` exactly when the differential of the inclusion `i` sends it
into `𝔤_c · z`. -/
theorem ker_mfderiv_quotientMk_levelSubMulAction (z : h.levelSubMulAction c) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c))) z).ker =
      ((lieAnnihilator ℝ (GroupLieAlgebra I G) c).toSubmodule.map
        ((InfinitesimalAction.fundamental I G I' M).eval z)).comap
        (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.levelSubMulAction c → M) z).toLinearMap := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  let := d.chartedSpace
  let := h.levelSubMulActionChartedSpace c hreg hn
  obtain ⟨_, _, _, _⟩ := h.quotient_hypotheses hreg hn d
  have hemb := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  have : LieGroup 𝓘(ℝ, F) 3 ((Lie.coadjointRepresentation ℝ I G).stabilizer c) :=
    LieGroup.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  have hz : μ z = c := h.mem_levelSubMulAction.1 z.property
  set di := (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.levelSubMulAction c → M) z).toLinearMap
  set V := (InfinitesimalAction.fundamental 𝓘(ℝ, F)
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) 𝓘(ℝ, Fin n → ℝ)
    (h.levelSubMulAction c)).orbitTangent z
  set W := (lieAnnihilator ℝ (GroupLieAlgebra I G) c).toSubmodule.map
    ((InfinitesimalAction.fundamental I G I' M).eval z)
  rw [ProperSMul.ker_mfderiv_quotientMk]
  have hdi : Function.Injective di := hemb.isImmersion.mfderiv_injective (by simp) z
  -- `di` carries the orbit directions `V` of `G_c` on the level into `𝔤 · z ∩ ker dμ_z = W`.
  have hW : W = (InfinitesimalAction.fundamental I G I' M).orbitTangent z ⊓
      LinearMap.ker (h.differential z) := by
    rw [h.orbitTangent_inf_ker_differential (h.momentCocycle_eq_zero z), hz]
  have hle : V.map di ≤ W := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1 hv
    rw [hW]
    refine ⟨?_, ?_⟩
    · rw [InfinitesimalAction.fundamental_apply]
      exact h.mfderiv_coe_fundamentalVectorField_mem_orbitTangent d.contMDiff_subtypeVal
        hemb.contMDiff z ξ
    · rw [← h.range_mfderiv_coe_levelSubMulAction hreg hn]
      exact ⟨_, rfl⟩
  -- `G_c` acts freely, so `V` has the dimension of `𝔤_c`, which bounds that of `W`.
  have hdim : finrank ℝ W ≤ finrank ℝ (V.map di) := by
    have : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    have hV : V.map di ≃ₗ[ℝ] V := (Submodule.equivMapOfInjective di hdi V).symm
    have hiso := Lie.isotropy_eq_bot_of_stabilizer_eq_bot (I := 𝓘(ℝ, F))
      (I' := 𝓘(ℝ, Fin n → ℝ))
      (IsCancelSMul.stabilizer_eq_bot (G := (Lie.coadjointRepresentation ℝ I G).stabilizer c) z)
    rw [hV.finrank_eq, InfinitesimalAction.finrank_orbitTangent_of_isotropy_eq_bot _ _ hiso]
    exact (Submodule.finrank_map_le _ _).trans_eq
      (d.finrank_eq_finrank_lieSubalgebraOfSubgroup.trans
        (Lie.finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation
          BoundarylessManifold.isInteriorPoint)).symm
  rw [← Submodule.eq_of_le_of_finrank_le hle hdim, Submodule.comap_map_eq_of_injective hdi]

/-- **The Marsden–Weinstein–Meyer theorem.** Let a Lie group `G` act smoothly and properly by
symplectomorphisms on a symplectic manifold `(M, σ)`, with coadjoint-equivariant moment map `μ`,
let `c` be a regular value of `μ`, and let the coadjoint stabilizer `G_c` act freely on the level
`μ⁻¹(c)`. Then the reduced space `μ⁻¹(c) / G_c`, the orbit space of `G_c` acting on the level,
carries a unique symplectic form `ω_red` with `π^* ω_red = i^* σ`, for the orbit projection
`π : μ⁻¹(c) → μ⁻¹(c) / G_c` and the inclusion `i : μ⁻¹(c) → M`. -/
theorem existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      η.IsSymplectic ∧
        SmoothForm.mpullback _
            (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ := by
  let := d.chartedSpace
  have := d.lieGroup
  let := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have hemb := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal hemb
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  exact h.existsUnique_isSymplectic_mpullback_eq_mpullback hσ hG hemb.contMDiff
    (fun z ↦ h.mem_levelSubMulAction.1 z.property) (h.range_mfderiv_coe_levelSubMulAction hreg hn)
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d) Quotient.mk_surjective
    (h.ker_mfderiv_quotientMk_levelSubMulAction hreg hn d)
    (fun k ↦ ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k)
    (fun k z ↦ Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit z k)))
    (fun z z' hzz' ↦
      MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hzz'.symm)))
    Subtype.val fun k z ↦ SubMulAction.val_smul k z

include hreg hn d in
/-- **The dimension of the reduced space.** If the form is nondegenerate and the level `μ⁻¹(c)` is
nonempty, the reduced space `μ⁻¹(c) / G_c` has dimension `dim M - dim 𝔤 - dim 𝔤_c`: its model
space `ProperSMul.QuotientModelSpace F (Fin n → ℝ)` satisfies
`dim (μ⁻¹(c) / G_c) + dim 𝔤 + dim 𝔤_c = dim M`. -/
theorem finrank_quotientModelSpace_add_finrank_add_finrank_lieAnnihilator
    (hσ : σ.IsNondegenerate) (z : h.levelSubMulAction c) :
    finrank ℝ (ProperSMul.QuotientModelSpace F (Fin n → ℝ)) + finrank ℝ (GroupLieAlgebra I G) +
      finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) c) = finrank ℝ E' := by
  let := d.chartedSpace
  let := h.levelSubMulActionChartedSpace c hreg hn
  have hemb := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have hz : μ z = c := h.mem_levelSubMulAction.1 z.property
  exact h.toIsMomentMap.finrank_add_finrank_add_finrank_lieAnnihilator
    (hσ.nondegenerate_bilinFormAt z) hz (h.momentCocycle_eq_zero z)
    (h.range_mfderiv_coe_levelSubMulAction hreg hn z)
    (hemb.isImmersion.mfderiv_injective (by simp) z)
    ((h.toIsMomentMap.differential_surjective_iff (hσ.nondegenerate_bilinFormAt z)).1
      (hreg z hz))
    ((h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).surjective_mfderiv (by simp) z)
    (h.ker_mfderiv_quotientMk_levelSubMulAction hreg hn d z)

end Quotient

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
