/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Restrict
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Map
import TauCeti.Geometry.Lie.AutomaticSmoothness

/-!
# The residual moment map of reduction in stages

Let a Lie group `G` act on a symplectic manifold `(M, σ)` with a coadjoint-equivariant moment map
`μ : M → 𝔤*`. Reduction in stages by a normal subgroup `N ⊲ G` first reduces by `N`, at the level
`μ_N⁻¹(0)` of the restricted moment map `μ_N = μ|_𝔫`, and then by the residual group `G ⧸ N`
acting on the first-stage reduced space `μ_N⁻¹(0) / N`. This file constructs the moment map of
that residual action, which reduction in stages
(`IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq_of_ker_le_range`) takes as
data.

As there, the groups are a pair of homomorphisms of Lie groups

`K →ι G →p R`,

where `K` acts on `M` through `ι`, with restricted moment map `μ_K = μ ∘ dι`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_monoidHom`). The sequence is a complex,
`p ∘ ι = 1`, the homomorphism `p` and its differential `dp : 𝔤 → 𝔯` at the identity are
surjective, and `ker dp ≤ range dι`. For a closed normal subgroup `N`, take `K = N` with its
inclusion and `R = G ⧸ N` with the projection.

* **The first-stage level.** A point `x` lies in the level `Z₁ = μ_K⁻¹(0)` exactly when `μ x`
  factors through `dp`, that is, when `μ x = ν ∘ dp` for some `ν ∈ 𝔯*`
  (`IsEquivariantMomentMap.mem_levelSubMulAction_comp_monoidHom_iff`): this identifies the
  annihilator `𝔫⁰` of `𝔫 = ker dp` with `(𝔤 ⧸ 𝔫)* = 𝔯*`. Since
  `Ad*_g (ν ∘ dp) = (Ad*_{p g} ν) ∘ dp`, the level is invariant under all of `G`
  (`IsEquivariantMomentMap.compMonoidHomLevelMulAction`), which acts smoothly on it for the
  regular-level manifold structure
  (`IsEquivariantMomentMap.contMDiffSMul_compMonoidHomLevelMulAction`). On the level, `μ` is
  `K`-invariant, because `p (ι k) = 1` acts trivially on `𝔯*`
  (`IsEquivariantMomentMap.apply_smul_eq_of_mem_levelSubMulAction_comp_monoidHom`).
* **The residual moment map.** Let `π₁ : Z₁ → Q₁` be a surjective submersion whose fibres are
  the `K`-orbits, onto a manifold with an action of `R` for which `π₁ (g • z) = p g • π₁ z`, and
  let `η₁` be a two-form on `Q₁` with `π₁^* η₁ = i₁^* σ`, such as the first-stage reduced form.
  Then there is a unique map `μ₁ : Q₁ → 𝔯*` with `μ₁ (π₁ z) ∘ dp = μ z` for every `z ∈ Z₁`, and it
  is a coadjoint-equivariant moment map of the action of `R` on `(Q₁, η₁)`
  (`existsUnique_comp_groupLieAlgebraMap_eq_and_isEquivariantMomentMap`). These are the
  residual data from which the second stage reduces.

The moment map `μ₁` is obtained by descending `μ` along `π₁`, as a moment map of `G` acting on
`Q₁` through `p` (`IsEquivariantMomentMap.existsUnique_comp_eq_and_isEquivariantMomentMap`), and
then along `p`: a moment map of an action through a surjective homomorphism with surjective
differential which factors through `dp` is one of the target group
(`TauCeti.SmoothTwoForm.isEquivariantMomentMap_comp_monoidHom_iff`).

## References

* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 5 (the induced moment map
  of the residual group in reduction by a normal subgroup).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 24 (reduction in stages).
-/

public section

noncomputable section

open Module Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [FiniteDimensional ℝ EK]
  [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup IK ∞ K]
  {ER HR : Type*} [NormedAddCommGroup ER] [NormedSpace ℝ ER]
  [TopologicalSpace HR] {IR : ModelWithCorners ℝ ER HR}
  {R : Type*} [TopologicalSpace R] [ChartedSpace HR R] [Group R] [LieGroup IR ∞ R]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] [MulAction K M] [ContMDiffSMul IK I' ∞ K M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ι : K →* G} {p : G →* R}

variable (hμ : σ.IsEquivariantMomentMap μ) (hι : MDifferentiableAt IK I ι 1)
  (hsmul : ∀ (k : K) (x : M), k • x = ι k • x)

/-! ### The first-stage level -/

omit [LieGroup IR ∞ R] in
/-- **The first-stage level.** If `p ∘ ι = 1` and `ker dp ≤ range dι`, a point `x` lies in the
level `μ_K⁻¹(0)` of the restricted moment map `μ_K = μ ∘ dι` exactly when `μ x` factors through
`dp`, as `μ x = ν ∘ dp` for some `ν ∈ 𝔯*`. -/
theorem mem_levelSubMulAction_comp_monoidHom_iff (hpι : p.comp ι = 1)
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap) {x : M} :
    x ∈ (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0 ↔
      ∃ ν : Module.Dual ℝ (GroupLieAlgebra IR R),
        μ x = ν.comp (p.groupLieAlgebraMap I IR).toLinearMap := by
  rw [mem_levelSubMulAction]
  refine ⟨fun hx ↦ ?_, fun ⟨ν, hν⟩ ↦ ?_⟩
  · -- `μ x` vanishes on `range dι`, hence on `ker dp`, so it lies in the range of `dp^*`.
    have hann : μ x ∈ (LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap).dualAnnihilator :=
      (Submodule.mem_dualAnnihilator _).2 fun w hw ↦ by
        obtain ⟨v, rfl⟩ := hker hw
        exact LinearMap.congr_fun hx v
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
    obtain ⟨ν, hν⟩ := hann
    exact ⟨ν, hν.symm⟩
  · rw [hν, LinearMap.comp_assoc, ← ContinuousLinearMap.toLinearMap_comp,
      p.groupLieAlgebraMap_comp_groupLieAlgebraMap_eq_zero ι hpι]
    simp

/-- **The first-stage level is `G`-invariant.** If `p ∘ ι = 1` and `ker dp ≤ range dι`, every
element of `G` carries the level `μ_K⁻¹(0)` of the restricted moment map `μ_K = μ ∘ dι` into
itself. -/
theorem smul_mem_levelSubMulAction_comp_monoidHom (hpι : p.comp ι = 1)
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap) (g : G) {x : M}
    (hx : x ∈ (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0) :
    g • x ∈ (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0 := by
  obtain ⟨ν, hν⟩ := (hμ.mem_levelSubMulAction_comp_monoidHom_iff hι hsmul hpι hker).1 hx
  refine (hμ.mem_levelSubMulAction_comp_monoidHom_iff hι hsmul hpι hker).2
    ⟨Lie.coadjointRepresentation ℝ IR R (p g) ν, ?_⟩
  rw [hμ.apply_smul, hν, p.coadjointRepresentation_comp_groupLieAlgebraMap]

/-- **The moment map is `K`-invariant on the first-stage level.** If `p ∘ ι = 1` and
`ker dp ≤ range dι`, then `μ (k • x) = μ x` for every `k : K` and every point `x` of the level
`μ_K⁻¹(0)` of the restricted moment map `μ_K = μ ∘ dι`. -/
theorem apply_smul_eq_of_mem_levelSubMulAction_comp_monoidHom (hpι : p.comp ι = 1)
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap) (k : K) {x : M}
    (hx : x ∈ (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0) :
    μ (k • x) = μ x := by
  obtain ⟨ν, hν⟩ := (hμ.mem_levelSubMulAction_comp_monoidHom_iff hι hsmul hpι hker).1 hx
  have hk : p (ι k) = 1 := DFunLike.congr_fun hpι k
  rw [hsmul, hμ.apply_smul, hν, p.coadjointRepresentation_comp_groupLieAlgebraMap, hk, map_one,
    Module.End.one_eq_id, LinearMap.id_apply]

/-- **The action of `G` on the first-stage level.** If `p ∘ ι = 1` and `ker dp ≤ range dι`, the
level `μ_K⁻¹(0)` of the restricted moment map `μ_K = μ ∘ dι` is invariant under `G`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.smul_mem_levelSubMulAction_comp_monoidHom`), and `G`
acts on it by restricting its action on `M`. -/
@[instance_reducible]
def compMonoidHomLevelMulAction (hpι : p.comp ι = 1)
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap) :
    MulAction G ((hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0) where
  smul g z := ⟨g • (z : M),
    hμ.smul_mem_levelSubMulAction_comp_monoidHom hι hsmul hpι hker g z.property⟩
  one_smul z := Subtype.ext (one_smul G (z : M))
  mul_smul g g' z := Subtype.ext (mul_smul g g' (z : M))

/-- The action of `G` on the first-stage level is the restriction of its action on `M`. -/
@[simp]
theorem coe_smul_compMonoidHomLevelMulAction (hpι : p.comp ι = 1)
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap) (g : G)
    (z : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0) :
    letI := hμ.compMonoidHomLevelMulAction hι hsmul hpι hker
    ((g • z : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0) : M) = g • (z : M) :=
  (rfl)

variable {n₁ : ℕ} [I'.Boundaryless]

/-- **`G` acts smoothly on the first-stage level.** If `0` is a regular value of the restricted
moment map `μ_K = μ ∘ dι`, the action of `G` on the level `μ_K⁻¹(0)` is smooth for its
regular-level manifold structure. -/
theorem contMDiffSMul_compMonoidHomLevelMulAction (hpι : p.comp ι = 1)
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap)
    (hreg₁ : ∀ x, (μ x).comp (ι.groupLieAlgebraMap IK I).toLinearMap = 0 →
      Surjective ((hμ.comp_monoidHom ι hι hsmul).differential x))
    (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra IK K) = n₁) :
    letI := (hμ.comp_monoidHom ι hι hsmul).levelSubMulActionChartedSpace 0 hreg₁ hn₁
    letI := hμ.compMonoidHomLevelMulAction hι hsmul hpι hker
    ContMDiffSMul I 𝓘(ℝ, Fin n₁ → ℝ) ∞ G ((hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0) :=
  letI := (hμ.comp_monoidHom ι hι hsmul).levelSubMulActionChartedSpace 0 hreg₁ hn₁
  letI := hμ.compMonoidHomLevelMulAction hι hsmul hpι hker
  ((hμ.comp_monoidHom ι hι hsmul).isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiffSMul
    contMDiff_id (hμ.coe_smul_compMonoidHomLevelMulAction hι hsmul hpι hker)

/-! ### The residual moment map -/

variable [FiniteDimensional ℝ ER]
  {EQ₁ HQ₁ : Type*} [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [CompleteSpace EQ₁]
  [TopologicalSpace HQ₁] {IQ₁ : ModelWithCorners ℝ EQ₁ HQ₁}
  {Q₁ : Type*} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁] [IsManifold IQ₁ ∞ Q₁]
  [MulAction R Q₁] [ContMDiffSMul IR IQ₁ ∞ R Q₁]

/-- **The residual moment map of reduction in stages.** Let `K` act on `M` through `ι : K →* G`,
let `p : G →* R` be a surjective homomorphism with surjective differential `dp`, with
`p ∘ ι = 1` and `ker dp ≤ range dι`, and let `0` be a regular value of the restricted moment map
`μ_K = μ ∘ dι`, so that the level `Z₁ = μ_K⁻¹(0)` is a manifold. Let `π₁ : Z₁ → Q₁` be a surjective
submersion whose fibres are `K`-orbits, onto a manifold with a smooth action of `R` satisfying
`π₁ (g • z) = p g • π₁ z`, and let `η₁` be a two-form on `Q₁` with `π₁^* η₁ = i₁^* σ` for the
inclusion `i₁` of `Z₁`; for instance the first-stage reduced space `Z₁ / K`, with the residual
action of `R` and the reduced form. Then there is a unique map `μ₁ : Q₁ → 𝔯*` with
`μ₁ (π₁ z) ∘ dp = μ z` for every `z ∈ Z₁`, and it is a coadjoint-equivariant moment map of the
action of `R` on `(Q₁, η₁)`. -/
theorem existsUnique_comp_groupLieAlgebraMap_eq_and_isEquivariantMomentMap
    (hps : Surjective p) (hdp : Surjective (p.groupLieAlgebraMap I IR))
    (hpι : p.comp ι = 1)
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap)
    (hreg₁ : ∀ x, (μ x).comp (ι.groupLieAlgebraMap IK I).toLinearMap = 0 →
      Surjective ((hμ.comp_monoidHom ι hι hsmul).differential x))
    (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra IK K) = n₁)
    {η₁ : SmoothTwoForm IQ₁ Q₁} {π₁ : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0 → Q₁}
    (hπ₁surj : Surjective π₁) (hπ₁fib : ∀ z z', π₁ z = π₁ z' → ∃ k : K, k • (z' : M) = z)
    (hπ₁G : ∀ (g : G) (z z' : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0),
      (z' : M) = g • (z : M) → π₁ z' = p g • π₁ z) :
    letI := (hμ.comp_monoidHom ι hι hsmul).levelSubMulActionChartedSpace 0 hreg₁ hn₁
    haveI := (hμ.comp_monoidHom ι hι hsmul).isManifold_levelSubMulAction hreg₁ hn₁
    ∀ (hπ₁ : Manifold.IsSubmersion 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ ∞ π₁),
      SmoothForm.mpullback π₁ hπ₁.contMDiff η₁ = SmoothForm.mpullback Subtype.val
          ((hμ.comp_monoidHom ι hι hsmul).isSmoothEmbedding_coe_levelSubMulAction hreg₁
            hn₁).contMDiff σ →
        ∃! μ₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IR R),
          (∀ z, (μ₁ (π₁ z)).comp (p.groupLieAlgebraMap I IR).toLinearMap = μ z) ∧
            η₁.IsEquivariantMomentMap μ₁ := by
  have hK := hμ.comp_monoidHom ι hι hsmul
  let := hK.levelSubMulActionChartedSpace 0 hreg₁ hn₁
  have := hK.isManifold_levelSubMulAction hreg₁ hn₁
  rcases subsingleton_or_nontrivial ER with hER | hER
  · -- If `𝔯 = 0`, then `𝔯*` is a point, and `μ = 0` on the level since it factors through `dp`.
    intro _ _
    -- `GroupLieAlgebra IR R` is the tangent space at `1`, which unfolds to the model space `ER`.
    have : Subsingleton (GroupLieAlgebra IR R) := hER
    refine ⟨0, ⟨fun z ↦ ?_, ?_⟩, fun _ _ ↦ Subsingleton.elim _ _⟩
    · obtain ⟨ν, hν⟩ := (hμ.mem_levelSubMulAction_comp_monoidHom_iff hι hsmul hpι hker).1
        z.property
      rw [hν, Subsingleton.elim ν 0, Pi.zero_apply]
    · exact isEquivariantMomentMap_of_subsingleton 0
  -- Otherwise `p` is smooth, since its differential is surjective onto `𝔯 ≠ 0`.
  have hp := TauCeti.Lie.contMDiff_of_surjective_groupLieAlgebraMap hdp
  have hp1 : MDifferentiableAt I IR p 1 := hp.mdifferentiableAt (by simp)
  -- `G` acts on the first-stage level by restriction, and on `Q₁` through `p`.
  let := hμ.compMonoidHomLevelMulAction hι hsmul hpι hker
  have := hμ.contMDiffSMul_compMonoidHomLevelMulAction hι hsmul hpι hker hreg₁ hn₁
  let : MulAction G Q₁ := MulAction.compHom Q₁ p
  have : ContMDiffSMul I IQ₁ ∞ G Q₁ := MulAction.contMDiffSMul_compHom hp
  intro hπ₁ hη₁
  -- Descend `μ` along `π₁` to a moment map `ν` of `G` acting on `Q₁` through `p`.
  obtain ⟨ν, ⟨hνπ, hν⟩, -⟩ := hμ.existsUnique_comp_eq_and_isEquivariantMomentMap
    (hK.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff hπ₁ hη₁ hπ₁surj
    (hμ.coe_smul_compMonoidHomLevelMulAction hι hsmul hpι hker)
    (fun g z ↦ hπ₁G g z _ (hμ.coe_smul_compMonoidHomLevelMulAction hι hsmul hpι hker g z))
    (K := (Lie.coadjointRepresentation ℝ IK K).stabilizer 0)
    (fun z z' hzz' ↦ by
      obtain ⟨k, hk⟩ := hπ₁fib z' z hzz'.symm
      exact ⟨⟨k, by simp⟩, Subtype.ext hk⟩)
    (fun k z ↦ hμ.apply_smul_eq_of_mem_levelSubMulAction_comp_monoidHom hι hsmul hpι hker
      (k : K) z.property)
  -- Each value of `ν` factors through `dp`; this defines `μ₁`.
  have hfac (q : Q₁) : ∃ ν₁ : Module.Dual ℝ (GroupLieAlgebra IR R),
      ν q = ν₁.comp (p.groupLieAlgebraMap I IR).toLinearMap := by
    obtain ⟨z, rfl⟩ := hπ₁surj q
    rw [← comp_apply (f := ν), hνπ]
    exact (hμ.mem_levelSubMulAction_comp_monoidHom_iff hι hsmul hpι hker).1 z.property
  choose μ₁ hμ₁ using hfac
  have hμ₁fun : (fun q ↦ (μ₁ q).comp (p.groupLieAlgebraMap I IR).toLinearMap) = ν :=
    funext fun q ↦ (hμ₁ q).symm
  refine ⟨μ₁, ⟨fun z ↦ (hμ₁ (π₁ z)).symm.trans (congrFun hνπ z), ?_⟩,
    fun μ₁' ⟨hμ₁', _⟩ ↦ funext fun q ↦ ?_⟩
  · rw [← isEquivariantMomentMap_comp_monoidHom_iff p hp1 (MulAction.compHom_smul_def p) hps hdp,
      hμ₁fun]
    exact hν
  · -- Two such maps agree on the image of `π₁`, after composing with the surjection `dp`.
    obtain ⟨z, rfl⟩ := hπ₁surj q
    exact (LinearMap.cancel_right hdp).1 ((hμ₁' z).trans
      ((hμ₁ (π₁ z)).symm.trans (congrFun hνπ z)).symm)

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
