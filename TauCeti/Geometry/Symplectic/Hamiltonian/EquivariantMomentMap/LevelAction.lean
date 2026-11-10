/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
public import TauCeti.Geometry.Manifold.GroupAction.Restrict
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The coadjoint stabilizer acting on a level of an equivariant moment map

Let a Lie group `G` act smoothly on a manifold `M` with a coadjoint-equivariant moment map
`μ : M → 𝔤*` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`), fix `c ∈ 𝔤*` and write
`G_c = {g | Ad*_g c = c}` for its coadjoint stabilizer
(`(TauCeti.Lie.coadjointRepresentation ℝ I G).stabilizer c`) and `Z = μ⁻¹(c)` for the level.
In Marsden–Weinstein–Meyer reduction the reduced space is the orbit space `Z / G_c`. This file
sets up the action of `G_c` on `Z` and proves the properties of it that the quotient construction
needs, all from the equivariance `μ (g • x) = Ad*_g (μ x)`.

* The stabilizer of a point lies in the coadjoint stabilizer of its value, `G_x ≤ G_{μ x}`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.stabilizer_le_stabilizer_coadjointRepresentation`).
* Conversely, an element of `G` carrying a point of `Z` into `Z` lies in `G_c`. Hence `Z` is
  invariant under exactly the elements of `G_c`, and is a `SubMulAction` of `G_c`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulAction`).
* Two points of `Z` lie in the same `G_c`-orbit exactly when they lie in the same `G`-orbit, so
  `Z / G_c → M / G` is injective, with image the orbits meeting `Z`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientMap_levelSubMulAction_injective`).
  Thus the reduced space at `c` is the space of `G`-orbits in `μ⁻¹(G · c)`.
* The stabilizer of a point of `Z` in `G_c` is its whole stabilizer in `G`. So `G_c` acts freely
  on `Z` exactly when `G` acts freely at every point of `Z`, and then **freeness implies
  regularity**: where the form is nondegenerate, `dμ_z` is surjective at every `z ∈ Z`
  (`IsEquivariantMomentMap.differential_surjective_of_stabilizer_levelSubMulAction_eq_bot`).
* If `G` acts properly on `M`, then `G_c` acts properly on `Z`, since `G_c` is a closed subgroup
  and `Z` is closed (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.properSMul_levelSubMulAction`).

* The action is smooth: for a manifold structure on `G_c` with smooth inclusion into `G`, such as
  its closed-subgroup Lie group structure, and a manifold structure on `Z` whose inclusion into
  `M` is a smooth embedding, such as that of a regular level, `G_c` acts smoothly on `Z`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.contMDiffSMul_levelSubMulAction`).

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130 (reduction at a value `c` by its coadjoint isotropy
  group `G_c`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the Marsden–Weinstein–Meyer theorem at a general value).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] lieGroupOne

/-! ### Stabilizers and the level -/

/-- **Stabilizers of points stabilize their values.** For an equivariant moment map, an element
fixing `x` fixes `μ x` under the coadjoint action: `G_x ≤ G_{μ x}`. -/
theorem stabilizer_le_stabilizer_coadjointRepresentation (h : σ.IsEquivariantMomentMap μ)
    (x : M) :
    MulAction.stabilizer G x ≤ (Lie.coadjointRepresentation ℝ I G).stabilizer (μ x) := by
  intro g hg
  rw [Representation.mem_stabilizer, ← h.apply_smul, MulAction.mem_stabilizer_iff.1 hg]

/-- **The coadjoint stabilizer preserves the level.** If `g` fixes `c` under the coadjoint action
and `μ x = c`, then `μ (g • x) = c`. -/
theorem apply_smul_eq_of_mem_stabilizer (h : σ.IsEquivariantMomentMap μ) {g : G}
    (hg : g ∈ (Lie.coadjointRepresentation ℝ I G).stabilizer c) {x : M} (hx : μ x = c) :
    μ (g • x) = c := by
  rw [h.apply_smul, hx]
  exact hg

/-- **Only the coadjoint stabilizer preserves the level.** If `g` carries a point of the level
`μ⁻¹(c)` into the same level, then `g` fixes `c` under the coadjoint action. -/
theorem mem_stabilizer_coadjointRepresentation_of_apply_eq (h : σ.IsEquivariantMomentMap μ)
    {g : G} {x : M} (hx : μ x = c) (hgx : μ (g • x) = c) :
    g ∈ (Lie.coadjointRepresentation ℝ I G).stabilizer c := by
  rw [Representation.mem_stabilizer, ← hx, ← h.apply_smul, hgx, hx]

variable (c) in
/-- **The level as a `G_c`-space.** The level `μ⁻¹(c)` of an equivariant moment map, as a
`SubMulAction` of the coadjoint stabilizer `G_c` of `c`. Its points form the subtype of `M` cut
out by `μ x = c` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mem_levelSubMulAction`), with the
subspace topology, and `G_c` acts on it by restricting the action on `M`. -/
def levelSubMulAction (h : σ.IsEquivariantMomentMap μ) :
    SubMulAction ((Lie.coadjointRepresentation ℝ I G).stabilizer c) M where
  carrier := μ ⁻¹' {c}
  smul_mem' g x hx := by
    rw [Set.mem_preimage, Set.mem_singleton_iff, Subgroup.smul_def]
    exact h.apply_smul_eq_of_mem_stabilizer g.2 hx

/-- A point lies in the level exactly when `μ` takes the value `c` there. -/
@[simp]
theorem mem_levelSubMulAction (h : σ.IsEquivariantMomentMap μ) {x : M} :
    x ∈ h.levelSubMulAction c ↔ μ x = c :=
  Iff.rfl

/-- The underlying set of the level is the preimage `μ⁻¹(c)`. -/
theorem coe_levelSubMulAction (h : σ.IsEquivariantMomentMap μ) :
    (h.levelSubMulAction c : Set M) = μ ⁻¹' {c} :=
  (rfl)

/-! ### Orbits -/

/-- **The `G_c`-orbits on the level are the `G`-orbits.** Two points of the level `μ⁻¹(c)` lie in
the same orbit of the coadjoint stabilizer `G_c` exactly when they lie in the same `G`-orbit. -/
theorem orbitRel_levelSubMulAction_iff (h : σ.IsEquivariantMomentMap μ)
    {z z' : h.levelSubMulAction c} :
    MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) z z' ↔
      MulAction.orbitRel G M z z' := by
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, SubMulAction.mem_orbit_subMul_iff,
    MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (Subgroup.smul_def g _).symm.trans hg⟩
  · rintro ⟨g, hg⟩
    have hgz : μ (g • (z' : M)) = c := by
      rw [hg]
      exact h.mem_levelSubMulAction.1 z.2
    refine ⟨⟨g, h.mem_stabilizer_coadjointRepresentation_of_apply_eq
      (h.mem_levelSubMulAction.1 z'.2) hgz⟩, ?_⟩
    rw [Subgroup.smul_def]
    exact hg

/-- **The reduced space is a space of `G`-orbits.** The map `μ⁻¹(c) / G_c → M / G` sending the
`G_c`-orbit of a point of the level to its `G`-orbit is injective. Its image consists of the
`G`-orbits meeting the level (`SubMulAction.range_orbitRelQuotientMap`). -/
theorem orbitRelQuotientMap_levelSubMulAction_injective (h : σ.IsEquivariantMomentMap μ) :
    Function.Injective (h.levelSubMulAction c).orbitRelQuotientMap :=
  SubMulAction.orbitRelQuotientMap_injective _ fun _ _ hy hgy ↦
    h.mem_stabilizer_coadjointRepresentation_of_apply_eq (h.mem_levelSubMulAction.1 hy)
      (h.mem_levelSubMulAction.1 hgy)

/-! ### Freeness -/

/-- **Stabilizers on the level.** The stabilizer in `G_c` of a point `z` of the level `μ⁻¹(c)` is
its stabilizer in `G`, viewed as a subgroup of `G_c`. -/
theorem stabilizer_levelSubMulAction (h : σ.IsEquivariantMomentMap μ)
    (z : h.levelSubMulAction c) :
    MulAction.stabilizer ((Lie.coadjointRepresentation ℝ I G).stabilizer c) z =
      (MulAction.stabilizer G (z : M)).subgroupOf
        ((Lie.coadjointRepresentation ℝ I G).stabilizer c) := by
  rw [SubMulAction.stabilizer_of_subMul, MulAction.stabilizer_subgroupOf]

/-- **Freeness on the level.** A point `z` of the level `μ⁻¹(c)` has trivial stabilizer in `G_c`
exactly when it has trivial stabilizer in `G`. So `G_c` acts freely on the level exactly when `G`
acts freely at each of its points. -/
theorem stabilizer_levelSubMulAction_eq_bot_iff (h : σ.IsEquivariantMomentMap μ)
    (z : h.levelSubMulAction c) :
    MulAction.stabilizer ((Lie.coadjointRepresentation ℝ I G).stabilizer c) z = ⊥ ↔
      MulAction.stabilizer G (z : M) = ⊥ := by
  have hle := h.stabilizer_le_stabilizer_coadjointRepresentation (z : M)
  rw [h.mem_levelSubMulAction.1 z.2] at hle
  rw [h.stabilizer_levelSubMulAction, Subgroup.subgroupOf_eq_bot, disjoint_iff,
    inf_eq_left.2 hle]

/-! ### Smoothness -/

/-- **The coadjoint stabilizer acts smoothly on the level.** Give `G_c` a manifold structure for
which its inclusion into `G` is smooth, such as its closed-subgroup Lie group structure, and give
the level `μ⁻¹(c)` a manifold structure for which its inclusion into `M` is a smooth embedding,
such as that of a regular level. Then the action of `G_c` on the level is smooth. -/
theorem contMDiffSMul_levelSubMulAction (h : σ.IsEquivariantMomentMap μ)
    {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HK]
    {J : ModelWithCorners ℝ F HK}
    [ChartedSpace HK ((Lie.coadjointRepresentation ℝ I G).stabilizer c)]
    (hGc : ContMDiff J I ∞ (Subtype.val : (Lie.coadjointRepresentation ℝ I G).stabilizer c → G))
    {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [ChartedSpace HZ (h.levelSubMulAction c)]
    (hZ : Manifold.IsSmoothEmbedding IZ I' ∞ (Subtype.val : h.levelSubMulAction c → M)) :
    ContMDiffSMul J IZ ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c) :=
  have := ContMDiffSMul.of_contMDiff_subtypeVal (I' := I') (M := M) hGc
  ContMDiffSMul.of_isSmoothEmbedding hZ fun g z ↦ SubMulAction.val_smul g z

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

/-! ### Properness -/

/-- **Properness on the level.** If `G` acts properly on `M`, then the coadjoint stabilizer `G_c`
acts properly on the level `μ⁻¹(c)`: it is a closed subgroup acting on a closed invariant
subset. -/
theorem properSMul_levelSubMulAction [ProperSMul G M] (h : σ.IsEquivariantMomentMap μ) :
    ProperSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) :=
  have : IsClosed ((Lie.coadjointRepresentation ℝ I G).stabilizer c : Set G) :=
    Lie.isClosed_stabilizer_coadjointRepresentation I c
  have hZ : IsClosed (h.levelSubMulAction c : Set M) := by
    rw [coe_levelSubMulAction]
    exact h.toIsMomentMap.isClosed_preimage_singleton c
  hZ.isClosedEmbedding_subtypeVal.properSMul (G := (Lie.coadjointRepresentation ℝ I G).stabilizer c)
    fun g z ↦ SubMulAction.val_smul g z

/-! ### Regularity -/

variable [T2Space M] [BoundarylessManifold I' M] [FiniteDimensional ℝ E']

/-- **Freeness implies regularity.** If the coadjoint stabilizer `G_c` acts freely at a point `z`
of the level `μ⁻¹(c)` and the form is nondegenerate at `z`, then the differential `dμ_z` is
surjective. So if `G_c` acts freely on the level of a symplectic form, then `c` is a regular value
of `μ`. -/
theorem differential_surjective_of_stabilizer_levelSubMulAction_eq_bot
    (h : σ.IsEquivariantMomentMap μ)
    {z : h.levelSubMulAction c} (hσ : (σ.bilinFormAt (z : M)).Nondegenerate)
    (hz : MulAction.stabilizer ((Lie.coadjointRepresentation ℝ I G).stabilizer c) z = ⊥) :
    Function.Surjective (h.differential (z : M)) :=
  h.toIsMomentMap.differential_surjective_of_stabilizer_eq_bot hσ
    ((h.stabilizer_levelSubMulAction_eq_bot_iff z).1 hz)

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
