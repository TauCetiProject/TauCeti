/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Restrict
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Stages

/-!
# Reduction in stages at zero by a normal subgroup

Let a Lie group `G` act on a symplectic manifold `(M, σ)` with a coadjoint-equivariant moment map
`μ : M → 𝔤*`. Reduction in stages by a normal subgroup `N ⊲ G` first reduces by `N` and then by
the residual group `G ⧸ N`. This file proves it for a pair of homomorphisms of Lie groups

`K →ι G →p R`,

where `K` acts on `M` through `ι` and `R` is the residual group: `p` is surjective, its
differential `dp : 𝔤 → 𝔯` at the identity is surjective, and `ker dp ≤ range dι`. No exactness
of the groups themselves is needed. For a closed normal subgroup `N`, the intended instance is
`K = N` with its inclusion and `R = G ⧸ N` with the projection; the Lie-algebra conditions are
then the exactness of `𝔫 → 𝔤 → 𝔤 ⧸ 𝔫`, which
`Subgroup.toLieSubalgebra_ker_lieMap_quotientMkSmoothHom` and
`Subgroup.surjective_lieMap_quotientMkSmoothHom` state for the Lie maps on left-invariant
derivations. The two reductions at zero are:

* **directly**, by `G` acting on the level `Z = μ⁻¹(0)`, with orbit projection `π : Z → Q`;
* **in stages**, first by `K` acting on the level `Z₁ = μ_K⁻¹(0)` of the restricted moment map
  `μ_K = μ ∘ dι` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_monoidHom`), with projection
  `π₁ : Z₁ → Q₁` and reduced form `η₁`, on which `R` acts with a moment map `μ₁ : Q₁ → 𝔯*`
  satisfying `μ₁ (π₁ z) ∘ dp = μ z`; then by `R` acting on the level `Z₂ = μ₁⁻¹(0)` of `Q₁`, with
  projection `π₂ : Z₂ → Q₂` and reduced form `η₂`.

**Reduction in stages** says that the two results agree: there is a diffeomorphism `Φ : Q → Q₂`
with `Φ [z] = [[z]]` pulling `η₂` back to the direct reduced form `η`
(`IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq_of_ker_le_range`).

As in the reduction in stages for a product group
(`IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq_of_smul_eq_smul_smul`), the
theorem is stated for arbitrary presentations of the three reduced spaces: `π`, `π₁` and `π₂` are
surjective submersions out of the regular levels, with the submanifold structures of
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`, whose fibres are the
orbits of `G`, of `K` and of `R`, and the forms are related by `π^* η = i^* σ`, `π₁^* η₁ = i₁^* σ`
and `π₂^* η₂ = i₂^* η₁` for the inclusions `i`, `i₁`, `i₂` of the levels. The first-stage moment
map `μ₁` and the action of `R` on `Q₁` are data of the statement, required to be compatible with
`π₁`; this file does not construct them from the action of `G`. Regularity is assumed only at the
two stages: regularity of `0` for `μ` follows
(`IsEquivariantMomentMap.forall_differential_surjective_of_isSubmersion_of_ker_le_range`).

The proof compares the two presentations through the map `Z → Z₂`, `z ↦ π₁ z`. It is well
defined: `μ z = 0` gives `μ_K z = μ z ∘ dι = 0`, and `μ₁ (π₁ z) ∘ dp = μ z = 0` gives
`μ₁ (π₁ z) = 0` because `dp` is surjective. Its composite `Ψ : Z → Q₂` with `π₂` is surjective,
since `μ₁ (π₁ z) = 0` gives `μ z = 0`, and has the fibres of `π`: `[[z]] = [[z']]` exactly when
`p g • [z'] = [z]` for some `g : G`, as `p` is surjective, that is when `ι k • g • z' = z`. It
pulls `η₂` back to `i^* σ` and is a submersion: a tangent vector of `Z₂` lifts along `dπ₁` to a
tangent vector `v` of `Z₁` with `dμ v = dμ₁ (dπ₁ v) ∘ dp = 0`, so `v` is tangent to `Z`. The
diffeomorphism and the comparison of the forms then follow as for a product group
(`TauCeti.SmoothForm.exists_diffeomorph_comp_eq_and_mpullback_eq_of_comp_eq`).

Regularity of `0` for `μ` is where `ker dp ≤ range dι` enters. Given `λ ∈ 𝔤*`, pick `w` with
`dμ_K w = λ ∘ dι`. Then `λ - dμ w` vanishes on `range dι`, hence on `ker dp`, so it is `λ' ∘ dp`
for some `λ' ∈ 𝔯*` (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`), and a tangent vector `v`
of `Z₁` with `dμ₁ (dπ₁ v) = λ'` gives `dμ (w + v) = λ`.

## Main results

* `IsEquivariantMomentMap.forall_differential_surjective_of_isSubmersion_of_ker_le_range`:
  regularity at both stages gives regularity of `0` for `μ`.
* `IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq_of_ker_le_range`:
  **reduction in stages** by a normal subgroup.

## References

* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 5 (reduction by stages for a
  normal subgroup, and the induced moment map `μ₁` of the residual group).
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
  {ER HR : Type*} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
  [TopologicalSpace HR] {IR : ModelWithCorners ℝ ER HR}
  {R : Type*} [TopologicalSpace R] [ChartedSpace HR R] [Group R] [LieGroup IR ∞ R]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] [MulAction K M] [ContMDiffSMul IK I' ∞ K M]
  {EQ₁ HQ₁ : Type*} [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [FiniteDimensional ℝ EQ₁]
  [TopologicalSpace HQ₁] {IQ₁ : ModelWithCorners ℝ EQ₁ HQ₁} [IQ₁.Boundaryless]
  {Q₁ : Type*} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁] [IsManifold IQ₁ ∞ Q₁]
  [MulAction R Q₁] [ContMDiffSMul IR IQ₁ ∞ R Q₁]
  {EQ₂ HQ₂ : Type*} [NormedAddCommGroup EQ₂] [NormedSpace ℝ EQ₂] [FiniteDimensional ℝ EQ₂]
  [TopologicalSpace HQ₂] {IQ₂ : ModelWithCorners ℝ EQ₂ HQ₂}
  {Q₂ : Type*} [TopologicalSpace Q₂] [ChartedSpace HQ₂ Q₂] [IsManifold IQ₂ ∞ Q₂]
  {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ι : K →* G} {p : G →* R} {n₁ n₂ n : ℕ}

section Level

variable (hμ : σ.IsEquivariantMomentMap μ) (hι : MDifferentiableAt IK I ι 1)
  (hsmul : ∀ (k : K) (x : M), k • x = ι k • x)

omit [I'.Boundaryless] in
/-- The level `μ⁻¹(0)` lies in the level `μ_K⁻¹(0)` of the restricted moment map `μ_K = μ ∘ dι`. -/
private theorem mem_levelSubMulAction_comp_monoidHom {x : M}
    (hx : x ∈ hμ.levelSubMulAction 0) :
    x ∈ (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0 := by
  rw [mem_levelSubMulAction] at hx ⊢
  rw [hx, LinearMap.zero_comp]

/-- The inclusion of the level `μ⁻¹(0)` into the level `μ_K⁻¹(0)`. -/
private abbrev levelToLevelComp (z : hμ.levelSubMulAction 0) :
    (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0 :=
  ⟨z, mem_levelSubMulAction_comp_monoidHom hμ hι hsmul z.property⟩

variable {η₁ : SmoothTwoForm IQ₁ Q₁} {μ₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IR R)}
  (h₁ : η₁.IsEquivariantMomentMap μ₁)
  {π₁ : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0 → Q₁}

omit [FiniteDimensional ℝ ER] [LieGroup IR ∞ R] [I'.Boundaryless] [TopologicalSpace Q₁]
  [MulAction R Q₁] in
/-- On the first-stage level, `μ₁ (π₁ z) = 0` exactly when `μ z = 0`, since
`μ₁ (π₁ z) ∘ dp = μ z` and `dp` is surjective. -/
private theorem apply_eq_zero_iff (hdp : Surjective (p.groupLieAlgebraMap I IR))
    (hμ₁ : ∀ z, (μ₁ (π₁ z)).comp (p.groupLieAlgebraMap I IR).toLinearMap = μ z) (z) :
    μ₁ (π₁ z) = 0 ↔ μ z = 0 := by
  rw [← hμ₁ z, ← LinearMap.zero_comp (p.groupLieAlgebraMap I IR).toLinearMap]
  exact (LinearMap.cancel_right hdp).symm

/-- The map from the level `μ⁻¹(0)` to the level of `μ₁` at `0` in the first-stage reduced space,
`z ↦ π₁ z`. -/
private abbrev levelToLevelSnd (hdp : Surjective (p.groupLieAlgebraMap I IR))
    (hμ₁ : ∀ z, (μ₁ (π₁ z)).comp (p.groupLieAlgebraMap I IR).toLinearMap = μ z)
    (z : hμ.levelSubMulAction 0) : h₁.levelSubMulAction 0 :=
  ⟨π₁ (levelToLevelComp hμ hι hsmul z), h₁.mem_levelSubMulAction.2
    ((apply_eq_zero_iff hμ hι hsmul hdp hμ₁ _).2 (hμ.mem_levelSubMulAction.1 z.property))⟩

omit [I'.Boundaryless] [IQ₁.Boundaryless] [TopologicalSpace Q₂] in
/-- Every point of the second-stage reduced space is the image of a point of the level `μ⁻¹(0)`. -/
private theorem surjective_comp_levelToLevelSnd {π₂ : h₁.levelSubMulAction 0 → Q₂}
    (hdp : Surjective (p.groupLieAlgebraMap I IR))
    (hμ₁ : ∀ z, (μ₁ (π₁ z)).comp (p.groupLieAlgebraMap I IR).toLinearMap = μ z)
    (hπ₁surj : Surjective π₁) (hπ₂surj : Surjective π₂) :
    Surjective (π₂ ∘ levelToLevelSnd hμ hι hsmul h₁ hdp hμ₁) := by
  intro q
  obtain ⟨y, rfl⟩ := hπ₂surj q
  obtain ⟨z₁, hz₁⟩ := hπ₁surj y
  have h0 : μ z₁ = 0 := (apply_eq_zero_iff hμ hι hsmul hdp hμ₁ z₁).1
    (hz₁ ▸ h₁.mem_levelSubMulAction.1 y.property)
  exact ⟨⟨z₁, hμ.mem_levelSubMulAction.2 h0⟩, congrArg π₂ (Subtype.ext hz₁)⟩

omit [I'.Boundaryless] [IQ₁.Boundaryless] [TopologicalSpace Q₂] in
/-- Two points of the level `μ⁻¹(0)` have the same image in the second-stage reduced space exactly
when they lie in the same orbit of `G`: `[[z]] = [[z']]` exactly when `p g • [z'] = [z]` for some
`g : G`, that is when `ι k • g • z' = z` for some `k : K`. -/
private theorem comp_levelToLevelSnd_eq_iff {π₂ : h₁.levelSubMulAction 0 → Q₂}
    (hp : Surjective p) (hdp : Surjective (p.groupLieAlgebraMap I IR))
    (hμ₁ : ∀ z, (μ₁ (π₁ z)).comp (p.groupLieAlgebraMap I IR).toLinearMap = μ z)
    (hπ₁fib : ∀ z z', π₁ z = π₁ z' ↔ ∃ k : K, k • (z' : M) = z)
    (hπ₁G : ∀ (g : G) (z z' : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0),
      (z' : M) = g • (z : M) → π₁ z' = p g • π₁ z)
    (hπ₂fib : ∀ y y', π₂ y = π₂ y' ↔ ∃ r : R, r • (y' : Q₁) = y) (z z') :
    (π₂ ∘ levelToLevelSnd hμ hι hsmul h₁ hdp hμ₁) z =
        (π₂ ∘ levelToLevelSnd hμ hι hsmul h₁ hdp hμ₁) z' ↔
      ∃ g : G, g • (z' : M) = z := by
  -- The level `μ⁻¹(0)` is `G`-invariant, by equivariance of `μ`.
  have hw (g : G) : g • (z' : M) ∈ hμ.levelSubMulAction 0 := hμ.mem_levelSubMulAction.2 <| by
    rw [hμ.apply_smul, hμ.mem_levelSubMulAction.1 z'.property, map_zero]
  rw [comp_apply, comp_apply, hπ₂fib]
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ⟨p g, ?_⟩⟩
  · obtain ⟨g, rfl⟩ := hp r
    obtain ⟨k, hk⟩ := (hπ₁fib (levelToLevelComp hμ hι hsmul z)
      (levelToLevelComp hμ hι hsmul ⟨_, hw g⟩)).1 <| by
        rw [hπ₁G g (levelToLevelComp hμ hι hsmul z') (levelToLevelComp hμ hι hsmul ⟨_, hw g⟩) rfl]
        exact hr.symm
    exact ⟨ι k * g, by rw [mul_smul, ← hsmul]; exact hk⟩
  · rw [← hπ₁G g (levelToLevelComp hμ hι hsmul z') (levelToLevelComp hμ hι hsmul z) hg.symm]

end Level

omit [I'.Boundaryless] [IQ₁.Boundaryless] in
/-- Differentiating `μ₁ (π₁ z) ∘ dp = μ z` along the first-stage level: for a tangent vector `v`
of the level, `dμ₁ (dπ₁ v) (dp ξ) = dμ (di₁ v) ξ`, where `i₁` is the inclusion of the level. -/
private theorem differential_mfderiv_apply_eq {N : Type*} [TopologicalSpace N]
    [ChartedSpace (Fin n₁ → ℝ) N] {i₁ : N → M} {η₁ : SmoothTwoForm IQ₁ Q₁}
    {μ₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IR R)} (hμ : σ.IsEquivariantMomentMap μ)
    (h₁ : η₁.IsEquivariantMomentMap μ₁) {π₁ : N → Q₁}
    (hμ₁ : ∀ z, (μ₁ (π₁ z)).comp (p.groupLieAlgebraMap I IR).toLinearMap = μ (i₁ z)) (z : N)
    (hi : MDifferentiableAt 𝓘(ℝ, Fin n₁ → ℝ) I' i₁ z)
    (hπ : MDifferentiableAt 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ π₁ z)
    (v : TangentSpace 𝓘(ℝ, Fin n₁ → ℝ) z) (ξ : GroupLieAlgebra I G) :
    h₁.differential (π₁ z) (mfderiv 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ π₁ z v)
        (p.groupLieAlgebraMap I IR ξ) =
      hμ.differential (i₁ z) (mfderiv 𝓘(ℝ, Fin n₁ → ℝ) I' i₁ z v) ξ := by
  have hcomp : (fun q ↦ μ₁ q (p.groupLieAlgebraMap I IR ξ)) ∘ π₁ = (fun x ↦ μ x ξ) ∘ i₁ :=
    funext fun y ↦ LinearMap.congr_fun (hμ₁ y) ξ
  rw [IsMomentMap.differential_apply, IsMomentMap.differential_apply,
    ← mvfderiv_comp_apply z (h₁.mdifferentiableAt _ (π₁ z)) hπ, hcomp,
    mvfderiv_comp_apply z (hμ.mdifferentiableAt ξ (i₁ z)) hi]

omit [IQ₁.Boundaryless] in
/-- **Regularity in stages gives regularity at zero.** Let `K` act on `M` through `ι : K →* G`,
let `0` be a regular value of the restricted moment map `μ_K = μ ∘ dι`, let `π₁ : μ_K⁻¹(0) → Q₁`
be a submersion out of the level with its submanifold structure, and let `μ₁` be a moment map of
an action of `R` on `Q₁` with `μ₁ (π₁ z) ∘ dp = μ z` having `0` as a regular value. If
`ker dp ≤ range dι`, then `0` is a regular value of `μ`. -/
theorem forall_differential_surjective_of_isSubmersion_of_ker_le_range
    (hμ : σ.IsEquivariantMomentMap μ) (hι : MDifferentiableAt IK I ι 1)
    (hsmul : ∀ (k : K) (x : M), k • x = ι k • x) (hdp : Surjective (p.groupLieAlgebraMap I IR))
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap)
    (hreg₁ : ∀ x, (μ x).comp (ι.groupLieAlgebraMap IK I).toLinearMap = 0 →
      Surjective ((hμ.comp_monoidHom ι hι hsmul).differential x))
    (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra IK K) = n₁)
    {η₁ : SmoothTwoForm IQ₁ Q₁} {μ₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IR R)}
    (h₁ : η₁.IsEquivariantMomentMap μ₁) (hreg₂ : ∀ y, μ₁ y = 0 → Surjective (h₁.differential y))
    {π₁ : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0 → Q₁}
    (hμ₁ : ∀ z, (μ₁ (π₁ z)).comp (p.groupLieAlgebraMap I IR).toLinearMap = μ z) :
    letI := (hμ.comp_monoidHom ι hι hsmul).levelSubMulActionChartedSpace 0 hreg₁ hn₁
    Manifold.IsSubmersion 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ ∞ π₁ →
      ∀ x, μ x = 0 → Surjective (hμ.differential x) := by
  have hK := hμ.comp_monoidHom ι hι hsmul
  let := hK.levelSubMulActionChartedSpace 0 hreg₁ hn₁
  intro hπ₁ x hx φ
  have hemb₁ := hK.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁
  let x₁ : hK.levelSubMulAction 0 :=
    ⟨x, hK.mem_levelSubMulAction.2 (by rw [hx, LinearMap.zero_comp])⟩
  -- Pick `w` with `dμ_K w = φ ∘ dι`; then `φ - dμ w` vanishes on `range dι ≥ ker dp`.
  obtain ⟨w, hw⟩ := hreg₁ x (by rw [hx, LinearMap.zero_comp])
    (φ.comp (ι.groupLieAlgebraMap IK I).toLinearMap)
  have hψ : φ - hμ.differential x w ∈
      (LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro ξ hξ
    obtain ⟨κ, rfl⟩ := hker hξ
    have hwκ := LinearMap.congr_fun hw κ
    rw [IsMomentMap.differential_apply] at hwκ
    rw [LinearMap.sub_apply, IsMomentMap.differential_apply, sub_eq_zero]
    exact hwκ.symm
  -- So `φ - dμ w = φ' ∘ dp`, and `φ'` is `dμ₁ (dπ₁ u)` for a tangent vector `u` of the level.
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hψ
  obtain ⟨φ', hφ'⟩ := hψ
  obtain ⟨w', hw'⟩ := hreg₂ (π₁ x₁) ((apply_eq_zero_iff hμ hι hsmul hdp hμ₁ x₁).2 hx) φ'
  obtain ⟨u, rfl⟩ := hπ₁.surjective_mfderiv (by simp) x₁ w'
  refine ⟨w + mfderiv _ I' Subtype.val x₁ u, LinearMap.ext fun ξ ↦ ?_⟩
  have hu := differential_mfderiv_apply_eq hμ h₁ hμ₁ x₁
    (hemb₁.contMDiff.mdifferentiableAt (by simp))
    ((hπ₁.contMDiff x₁).mdifferentiableAt (by simp)) u ξ
  rw [hw'] at hu
  have hφξ := LinearMap.congr_fun hφ' ξ
  rw [LinearMap.dualMap_apply, LinearMap.sub_apply] at hφξ
  rw [map_add, LinearMap.add_apply, ← hu]
  simp only [ContinuousLinearMap.coe_coe] at hφξ
  rw [hφξ, add_sub_cancel]

/-- **Reduction in stages by a normal subgroup.** Let `G` act on `(M, σ)` with a
coadjoint-equivariant moment map `μ`, let `K` act on `M` through a homomorphism `ι : K →* G`,
`k • x = ι k • x`, with the restricted moment map `μ_K = μ ∘ dι`, and let `p : G →* R` be a
surjective homomorphism whose differential `dp` at the identity is surjective with
`ker dp ≤ range dι`; for a closed normal subgroup `N ⊲ G`, these are `K = N` and `R = G ⧸ N`.

* Let `0` be a regular value of `μ_K`, with the level `Z₁ = μ_K⁻¹(0)` carrying its submanifold
  structure, and let `π₁ : Z₁ → Q₁` be a surjective submersion onto a manifold with an action of
  `R`, whose fibres are the `K`-orbits, with `π₁ (g • z) = p g • π₁ z`, carrying a form `η₁` with
  `π₁^* η₁ = i₁^* σ` and a coadjoint-equivariant moment map `μ₁` of `R` with
  `μ₁ (π₁ z) ∘ dp = μ z`. This is the first stage of the reduction, by `K` at `0`.
* Let `0` be a regular value of `μ₁`, and `π₂ : Z₂ → Q₂` a surjective submersion out of the level
  `Z₂ = μ₁⁻¹(0)` whose fibres are the `R`-orbits, carrying a form `η₂` with `π₂^* η₂ = i₂^* η₁`.
  This is the second stage, by `R` at `0`.
* Then `0` is a regular value of `μ`
  (`IsEquivariantMomentMap.forall_differential_surjective_of_isSubmersion_of_ker_le_range`),
  so the level `Z = μ⁻¹(0)` carries its submanifold structure. Let `π : Z → Q` be a surjective
  submersion whose fibres are the `G`-orbits, carrying a form `η` with `π^* η = i^* σ`. This is the
  direct reduction by `G` at `0`.

Then there is a diffeomorphism `Φ : Q → Q₂` with `Φ [z] = [[z]]` and `Φ^* η₂ = η`. -/
theorem exists_diffeomorph_apply_eq_and_mpullback_eq_of_ker_le_range
    (hμ : σ.IsEquivariantMomentMap μ) (hι : MDifferentiableAt IK I ι 1)
    (hsmul : ∀ (k : K) (x : M), k • x = ι k • x) (hp : Surjective p)
    (hdp : Surjective (p.groupLieAlgebraMap I IR))
    (hker : LinearMap.ker (p.groupLieAlgebraMap I IR).toLinearMap ≤
      LinearMap.range (ι.groupLieAlgebraMap IK I).toLinearMap)
    (hreg₁ : ∀ x, (μ x).comp (ι.groupLieAlgebraMap IK I).toLinearMap = 0 →
      Surjective ((hμ.comp_monoidHom ι hι hsmul).differential x))
    (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra IK K) = n₁)
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
    {η₁ : SmoothTwoForm IQ₁ Q₁} {μ₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IR R)}
    (h₁ : η₁.IsEquivariantMomentMap μ₁) (hreg₂ : ∀ y, μ₁ y = 0 → Surjective (h₁.differential y))
    (hn₂ : finrank ℝ EQ₁ - finrank ℝ (GroupLieAlgebra IR R) = n₂)
    {π₁ : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0 → Q₁}
    {π₂ : h₁.levelSubMulAction 0 → Q₂} {π : hμ.levelSubMulAction 0 → Q}
    {η₂ : SmoothTwoForm IQ₂ Q₂} {η : SmoothTwoForm IQ Q}
    (hπ₁surj : Surjective π₁) (hπ₁fib : ∀ z z', π₁ z = π₁ z' ↔ ∃ k : K, k • (z' : M) = z)
    (hπ₁G : ∀ (g : G) (z z' : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0),
      (z' : M) = g • (z : M) → π₁ z' = p g • π₁ z)
    (hμ₁ : ∀ z, (μ₁ (π₁ z)).comp (p.groupLieAlgebraMap I IR).toLinearMap = μ z)
    (hπ₂surj : Surjective π₂) (hπ₂fib : ∀ y y', π₂ y = π₂ y' ↔ ∃ r : R, r • (y' : Q₁) = y)
    (hπsurj : Surjective π) (hπfib : ∀ z z', π z = π z' ↔ ∃ g : G, g • (z' : M) = z) :
    letI := (hμ.comp_monoidHom ι hι hsmul).levelSubMulActionChartedSpace 0 hreg₁ hn₁
    letI := h₁.levelSubMulActionChartedSpace 0 hreg₂ hn₂
    haveI := (hμ.comp_monoidHom ι hι hsmul).isManifold_levelSubMulAction hreg₁ hn₁
    haveI := h₁.isManifold_levelSubMulAction hreg₂ hn₂
    ∀ (hπ₁ : Manifold.IsSubmersion 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ ∞ π₁),
      letI := hμ.levelSubMulActionChartedSpace 0
        (hμ.forall_differential_surjective_of_isSubmersion_of_ker_le_range hι hsmul hdp hker
          hreg₁ hn₁ h₁ hreg₂ hμ₁ hπ₁) hn
      haveI := hμ.isManifold_levelSubMulAction
        (hμ.forall_differential_surjective_of_isSubmersion_of_ker_le_range hι hsmul hdp hker
          hreg₁ hn₁ h₁ hreg₂ hμ₁ hπ₁) hn
      ∀ (hπ₂ : Manifold.IsSubmersion 𝓘(ℝ, Fin n₂ → ℝ) IQ₂ ∞ π₂)
        (hπ : Manifold.IsSubmersion 𝓘(ℝ, Fin n → ℝ) IQ ∞ π),
        SmoothForm.mpullback π₁ hπ₁.contMDiff η₁ = SmoothForm.mpullback Subtype.val
          ((hμ.comp_monoidHom ι hι hsmul).isSmoothEmbedding_coe_levelSubMulAction hreg₁
            hn₁).contMDiff σ →
        SmoothForm.mpullback π₂ hπ₂.contMDiff η₂ = SmoothForm.mpullback Subtype.val
          (h₁.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff η₁ →
        SmoothForm.mpullback π hπ.contMDiff η = SmoothForm.mpullback Subtype.val
          (hμ.isSmoothEmbedding_coe_levelSubMulAction
            (hμ.forall_differential_surjective_of_isSubmersion_of_ker_le_range hι hsmul hdp hker
              hreg₁ hn₁ h₁ hreg₂ hμ₁ hπ₁) hn).contMDiff σ →
        ∃ Φ : Q ≃ₘ⟮IQ, IQ₂⟯ Q₂,
          (∀ (z : hμ.levelSubMulAction 0)
            (z₁ : (hμ.comp_monoidHom ι hι hsmul).levelSubMulAction 0)
            (y : h₁.levelSubMulAction 0),
            (z₁ : M) = z → (y : Q₁) = π₁ z₁ → Φ (π z) = π₂ y) ∧
          SmoothForm.mpullback Φ Φ.contMDiff η₂ = η := by
  have hK := hμ.comp_monoidHom ι hι hsmul
  let := hK.levelSubMulActionChartedSpace 0 hreg₁ hn₁
  let := h₁.levelSubMulActionChartedSpace 0 hreg₂ hn₂
  have := hK.isManifold_levelSubMulAction hreg₁ hn₁
  have := h₁.isManifold_levelSubMulAction hreg₂ hn₂
  intro hπ₁
  have hreg := hμ.forall_differential_surjective_of_isSubmersion_of_ker_le_range hι hsmul hdp hker
    hreg₁ hn₁ h₁ hreg₂ hμ₁ hπ₁
  let := hμ.levelSubMulActionChartedSpace 0 hreg hn
  have := hμ.isManifold_levelSubMulAction hreg hn
  intro hπ₂ hπ hη₁ hη₂ hη
  refine (SmoothForm.exists_diffeomorph_comp_eq_and_mpullback_eq_of_comp_eq
    (j := levelToLevelComp hμ hι hsmul) (k := levelToLevelSnd hμ hι hsmul h₁ hdp hμ₁)
    hπ hπsurj hπ₁ hπ₂ (hμ.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    (hK.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁)
    (h₁.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂) rfl rfl
    (surjective_comp_levelToLevelSnd hμ hι hsmul h₁ hdp hμ₁ hπ₁surj hπ₂surj)
    (fun z z' ↦ (comp_levelToLevelSnd_eq_iff hμ hι hsmul h₁ hp hdp hμ₁ hπ₁fib hπ₁G hπ₂fib z
      z').trans (hπfib z z').symm) hη₁ hη₂ hη fun z v w hvw ↦ ?_).imp
    fun Φ hΦ ↦ ⟨fun z z₁ y hz₁ hy ↦ ?_, hΦ.2⟩
  · -- A tangent vector `w` of the level of `μ₁` lifts along `dπ₁` to a tangent vector `v` of
    -- `μ_K⁻¹(0)`; then `dμ v = dμ₁ (dπ₁ v) ∘ dp = dμ₁ w ∘ dp = 0`, so `v` is tangent to `μ⁻¹(0)`.
    let j₁ := levelToLevelComp hμ hι hsmul z
    have hv := differential_mfderiv_apply_eq hμ h₁ hμ₁ j₁
      ((hK.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff.mdifferentiableAt (by simp))
      ((hπ₁.contMDiff j₁).mdifferentiableAt (by simp)) v
    refine LinearMap.mem_range.1 ((hμ.range_mfderiv_coe_levelSubMulAction hreg hn z).ge
      (LinearMap.mem_ker.2 (LinearMap.ext fun ξ ↦ (hv ξ).symm.trans ?_)))
    rw [← hvw]
    exact LinearMap.congr_fun (h₁.differential_mfderiv_eq_zero
      (fun y ↦ h₁.mem_levelSubMulAction.1 y.property) _ w) _
  rw [← comp_apply (f := Φ), hΦ.1, comp_apply]
  exact congrArg π₂ (Subtype.ext (hy.trans (congrArg π₁ (Subtype.ext hz₁))).symm)

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
