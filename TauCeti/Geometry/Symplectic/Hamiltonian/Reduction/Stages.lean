/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.MomentMap

/-!
# Reduction in stages for a product group

Let Lie groups `G` and `L` act on a symplectic manifold `(M, σ)` with coadjoint-equivariant moment
maps `μ : M → 𝔤*` and `ν : M → 𝔩*`, where `μ` is invariant under `L` and `ν` under `G`, and let
`G × L` act by `(g, l) • x = g • l • x`. Then `x ↦ (μ x, ν x)` is a coadjoint-equivariant moment
map of `G × L` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_of_smul_eq_smul_smul`), and the
symplectic manifold can be reduced in two ways at a pair of values `(c, b)`:

* **directly**, by the coadjoint stabilizer `G_c × L_b` of `(c, b)` acting on the level
  `Z = μ⁻¹(c) ∩ ν⁻¹(b)`, with orbit projection `π : Z → Q`;
* **in stages**, first by `G_c` acting on `Z₁ = μ⁻¹(c)`, with projection `π₁ : Z₁ → Q₁` and reduced
  form `η₁`, on which `L` still acts, with the moment map `ν₁` induced by `ν`; then by `L_b` acting
  on the level `Z₂ = ν₁⁻¹(b)` of `Q₁`, with projection `π₂ : Z₂ → Q₂` and reduced form `η₂`.

**Reduction in stages** says that the two results agree: there is a diffeomorphism `Φ : Q → Q₂`
with `Φ [z] = [[z]]` pulling `η₂` back to the direct reduced form `η`
(`IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq_of_smul_eq_smul_smul`).

The theorem is stated for arbitrary presentations of the three reduced spaces: `π`, `π₁` and `π₂`
are surjective submersions out of the regular levels, with the submanifold structures of
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`, whose fibres are the
orbits of `G × L`, of `G` and of `L`, and the forms are related by `π^* η = i^* σ`,
`π₁^* η₁ = i₁^* σ` and `π₂^* η₂ = i₂^* η₁` for the inclusions `i`, `i₁`, `i₂` of the levels. The
theorem assumes regularity only at the two stages: regularity of `(c, b)` for `(μ, ν)` follows
(`SmoothTwoForm.IsEquivariantMomentMap.forall_differential_surjective_prod_of_isSubmersion`).
No freeness, properness or nondegeneracy is assumed beyond what these presentations provide. The
Marsden–Weinstein–Meyer reduced spaces of
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace` are candidate presentations,
under their own hypotheses: freeness of the stabilizers and properness of the actions at each
stage, and for the first stage the action of `L` of
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Symmetry`. This file does not check them
against the hypotheses of the theorem, and does not construct the second-stage reduced space.

The proof compares the two presentations of `Q` and `Q₂` through the map
`Z → Z₂`, `z ↦ π₁ z`, which is well defined because a point of `Z` lies in `Z₁` and its image
in `Q₁` lies in `ν₁⁻¹(b)`. Its composite `Ψ : Z → Q₂` with `π₂` is surjective, has the fibres of
`π`, and pulls `η₂` back to `i^* σ`. It is a submersion: a tangent vector of `Z₂` lifts along
`dπ₁` to a tangent vector `v` of `Z₁`, with `dμ v = 0`, and with `dν v = dν₁ (dπ₁ v) = 0`
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_mfderiv_eq_of_comp_eq`), so `v` is tangent to
`Z`, the level of `(μ, ν)`
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_prod_of_smul_eq_smul_smul`). Two surjective
submersions with the same fibres induce a diffeomorphism (`Equiv.diffeomorphOfSubmersions`).
This comparison uses only the maps of levels and the pullback equations, not the groups, and is
stated for any such data
(`TauCeti.SmoothForm.exists_diffeomorph_comp_eq_and_mpullback_eq_of_comp_eq`), so that other
reductions in stages, such as the one by a normal subgroup, share it.

## Main results

* `SmoothForm.exists_diffeomorph_comp_eq_and_mpullback_eq_of_comp_eq`: reduction in stages for
  reduction data, given maps of the levels compatible with the projections and the inclusions.
* `SmoothTwoForm.IsEquivariantMomentMap.mem_levelSubMulAction_prod_of_smul_eq_smul_smul_iff`: the
  level of `(μ, ν)` at `(c, b)` is `μ⁻¹(c) ∩ ν⁻¹(b)`.
* `SmoothTwoForm.IsEquivariantMomentMap.forall_differential_surjective_prod_of_isSubmersion`:
  regularity at both stages gives regularity of `(c, b)` for `(μ, ν)`.
* `IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq_of_smul_eq_smul_smul`:
  **reduction in stages**.

## References

* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 5 (reduction by stages for a
  normal subgroup, here the factor `G` of `G × L`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 24 (reduction for product groups).
-/

public section

noncomputable section

open Module Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

section Stages

variable {E H M EZ HZ Z EQ HQ Q EZ₁ HZ₁ Z₁ EQ₁ HQ₁ Q₁ EZ₂ HZ₂ Z₂ EQ₂ HQ₂ Q₂ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] [TopologicalSpace Z] [ChartedSpace HZ Z]
  [IsManifold IZ ∞ Z]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q]
  [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
  {IZ₁ : ModelWithCorners ℝ EZ₁ HZ₁} [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁]
  [IsManifold IZ₁ ∞ Z₁]
  [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [TopologicalSpace HQ₁]
  {IQ₁ : ModelWithCorners ℝ EQ₁ HQ₁} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁]
  [IsManifold IQ₁ ∞ Q₁]
  [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
  {IZ₂ : ModelWithCorners ℝ EZ₂ HZ₂} [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂]
  [IsManifold IZ₂ ∞ Z₂]
  [NormedAddCommGroup EQ₂] [NormedSpace ℝ EQ₂] [FiniteDimensional ℝ EQ₂] [TopologicalSpace HQ₂]
  {IQ₂ : ModelWithCorners ℝ EQ₂ HQ₂} [TopologicalSpace Q₂] [ChartedSpace HQ₂ Q₂]
  [IsManifold IQ₂ ∞ Q₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
  {σ : SmoothForm I M F m} {η₁ : SmoothForm IQ₁ Q₁ F m} {η₂ : SmoothForm IQ₂ Q₂ F m}
  {η : SmoothForm IQ Q F m} {i : Z → M} {i₁ : Z₁ → M} {i₂ : Z₂ → Q₁} {π : Z → Q} {π₁ : Z₁ → Q₁}
  {π₂ : Z₂ → Q₂} {j : Z → Z₁} {k : Z → Z₂}

/-- **Reduction in stages for reduction data.** Let `π₁^* η₁ = i₁^* σ` for a submersion
`π₁ : Z₁ → Q₁` and an embedding `i₁ : Z₁ → M`, let `π₂^* η₂ = i₂^* η₁` for a submersion
`π₂ : Z₂ → Q₂` and an embedding `i₂ : Z₂ → Q₁`, and let `π^* η = i^* σ` for a surjective
submersion `π : Z → Q` out of a boundaryless manifold. Let `j : Z → Z₁` and `k : Z → Z₂` satisfy
`i₁ ∘ j = i` and `i₂ ∘ k = π₁ ∘ j`, such that `π₂ ∘ k` is surjective with the fibres of `π`, and
such that every tangent vector `v` of `Z₁` with `dπ₁ v` tangent to `Z₂` has `di₁ v` tangent to `Z`.
Then there is a diffeomorphism `Φ : Q → Q₂` with `Φ ∘ π = π₂ ∘ k` and `Φ^* η₂ = η`. -/
theorem exists_diffeomorph_comp_eq_and_mpullback_eq_of_comp_eq
    (hπ : Manifold.IsSubmersion IZ IQ ∞ π) (hπsurj : Surjective π)
    (hπ₁ : Manifold.IsSubmersion IZ₁ IQ₁ ∞ π₁) (hπ₂ : Manifold.IsSubmersion IZ₂ IQ₂ ∞ π₂)
    (hi : ContMDiff IZ I ∞ i) (hi₁ : Manifold.IsSmoothEmbedding IZ₁ I ∞ i₁)
    (hi₂ : Manifold.IsSmoothEmbedding IZ₂ IQ₁ ∞ i₂) (hij : i₁ ∘ j = i) (hik : i₂ ∘ k = π₁ ∘ j)
    (hsurj : Surjective (π₂ ∘ k)) (hfib : ∀ z z', (π₂ ∘ k) z = (π₂ ∘ k) z' ↔ π z = π z')
    (hη₁ : mpullback π₁ hπ₁.contMDiff η₁ = mpullback i₁ hi₁.contMDiff σ)
    (hη₂ : mpullback π₂ hπ₂.contMDiff η₂ = mpullback i₂ hi₂.contMDiff η₁)
    (hη : mpullback π hπ.contMDiff η = mpullback i hi σ)
    (hkey : ∀ z v w, mfderiv IZ₂ IQ₁ i₂ (k z) w = mfderiv IZ₁ IQ₁ π₁ (j z) v →
      ∃ u, mfderiv IZ I i z u = mfderiv IZ₁ I i₁ (j z) v) :
    ∃ Φ : Q ≃ₘ⟮IQ, IQ₂⟯ Q₂, ⇑Φ ∘ π = π₂ ∘ k ∧ mpullback Φ Φ.contMDiff η₂ = η := by
  subst hij
  have hj : ContMDiff IZ IZ₁ ∞ j := hi₁.contMDiff_iff_comp.2 hi
  have hk : ContMDiff IZ IZ₂ ∞ k := hi₂.contMDiff_iff_comp.2 (hik ▸ hπ₁.contMDiff.comp hj)
  -- `dk` is onto by a diagram chase, so `π₂ ∘ k` is a surjective submersion with the fibres of `π`
  -- and induces a diffeomorphism `Φ : Q → Q₂`.
  have hΨ : Manifold.IsSubmersion IZ IQ₂ ∞ (π₂ ∘ k) := by
    refine ((hπ₂.contMDiff.comp hk).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      fun z ↦ ?_).isSubmersion
    rw [mfderiv_comp z ((hπ₂.contMDiff (k z)).mdifferentiableAt (by simp))
      ((hk z).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
    exact (hπ₂.surjective_mfderiv (by simp) (k z)).comp <| surjective_mfderiv_of_comp_eq
      ((hj z).mdifferentiableAt (by simp)) ((hk z).mdifferentiableAt (by simp))
      (hi₁.contMDiff.mdifferentiableAt (by simp)) (hi₂.contMDiff.mdifferentiableAt (by simp))
      ((hπ₁.contMDiff (j z)).mdifferentiableAt (by simp)) hik
      (hi₁.isImmersion.mfderiv_injective (by simp) (j z))
      (hi₂.isImmersion.mfderiv_injective (by simp) (k z))
      (hπ₁.surjective_mfderiv (by simp) (j z)) (hkey z)
  obtain ⟨Φ, hΦ⟩ := hπ.exists_diffeomorph_comp_eq hπsurj hΨ hsurj hfib
  refine ⟨Φ, hΦ, mpullback_injective_of_surjective hπ.contMDiff hπsurj
    (hπ.surjective_mfderiv (by simp)) ?_⟩
  -- `π^* Φ^* η₂ = (π₂ ∘ k)^* η₂ = k^* i₂^* η₁ = j^* π₁^* η₁ = j^* i₁^* σ = π^* η`.
  rw [mpullback_mpullback, hη]
  simp only [hΦ]
  rw [← mpullback_mpullback _ _ hk hπ₂.contMDiff, hη₂,
    mpullback_mpullback_of_comp_eq hk hi₂.contMDiff hj hπ₁.contMDiff hik, hη₁,
    mpullback_mpullback]

end Stages

end TauCeti.SmoothForm

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EL HL : Type*} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
  [TopologicalSpace HL] {IL : ModelWithCorners ℝ EL HL}
  {L : Type*} [TopologicalSpace L] [ChartedSpace HL L] [Group L] [LieGroup IL ∞ L]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] [MulAction L M] [ContMDiffSMul IL I' ∞ L M]
  [MulAction (G × L) M] [ContMDiffSMul (I.prod IL) I' ∞ (G × L) M]
  {EQ₁ HQ₁ : Type*} [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [FiniteDimensional ℝ EQ₁]
  [TopologicalSpace HQ₁] {IQ₁ : ModelWithCorners ℝ EQ₁ HQ₁} [IQ₁.Boundaryless]
  {Q₁ : Type*} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁] [IsManifold IQ₁ ∞ Q₁]
  [MulAction L Q₁] [ContMDiffSMul IL IQ₁ ∞ L Q₁]
  {EQ₂ HQ₂ : Type*} [NormedAddCommGroup EQ₂] [NormedSpace ℝ EQ₂] [FiniteDimensional ℝ EQ₂]
  [TopologicalSpace HQ₂] {IQ₂ : ModelWithCorners ℝ EQ₂ HQ₂}
  {Q₂ : Type*} [TopologicalSpace Q₂] [ChartedSpace HQ₂ Q₂] [IsManifold IQ₂ ∞ Q₂]
  {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ν : M → Module.Dual ℝ (GroupLieAlgebra IL L)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {b : Module.Dual ℝ (GroupLieAlgebra IL L)}
  {n₁ n₂ n : ℕ}

section Level

variable (hμ : σ.IsEquivariantMomentMap μ) (hν : σ.IsEquivariantMomentMap ν)
  (hsmul : ∀ (g : G × L) (x : M), g • x = g.1 • g.2 • x)
  (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x) (hνG : ∀ (g : G) (x : M), ν (g • x) = ν x)

omit [I'.Boundaryless] in
/-- **The level of a pair of moment maps.** For commuting Hamiltonian actions of `G` and `L`, a
point lies in the level of the moment map `x ↦ (μ x, ν x)` of `G × L` at `(c, b)` exactly when it
lies in both levels `μ⁻¹(c)` and `ν⁻¹(b)`. -/
theorem mem_levelSubMulAction_prod_of_smul_eq_smul_smul_iff {x : M} :
    x ∈ (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulAction
        (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b)) ↔ μ x = c ∧ ν x = b := by
  rw [(hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).mem_levelSubMulAction,
    (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L).injective.eq_iff, Prod.mk.injEq]

/-- The inclusion of the level of `(μ, ν)` at `(c, b)` into the level of `μ` at `c`. -/
private abbrev levelProdToLevel
    (z : (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulAction
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b))) :
    hμ.levelSubMulAction c :=
  ⟨z, hμ.mem_levelSubMulAction.2
    ((mem_levelSubMulAction_prod_of_smul_eq_smul_smul_iff hμ hν hsmul hμL hνG).1 z.property).1⟩

variable {η₁ : SmoothTwoForm IQ₁ Q₁} {ν₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IL L)}
  (h₁ : η₁.IsEquivariantMomentMap ν₁) {π₁ : hμ.levelSubMulAction c → Q₁}
  (hν₁ : ν₁ ∘ π₁ = ν ∘ Subtype.val)

/-- The map from the level of `(μ, ν)` at `(c, b)` to the level of the induced moment map `ν₁` at
`b` in the first-stage reduced space, `z ↦ π₁ z`. -/
private abbrev levelProdToLevelSnd
    (z : (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulAction
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b))) :
    h₁.levelSubMulAction b :=
  ⟨π₁ (levelProdToLevel hμ hν hsmul hμL hνG z), h₁.mem_levelSubMulAction.2
    ((congrFun hν₁ _).trans
      ((mem_levelSubMulAction_prod_of_smul_eq_smul_smul_iff hμ hν hsmul hμL hνG).1 z.property).2)⟩

omit [I'.Boundaryless] [IQ₁.Boundaryless] [TopologicalSpace Q₂] in
/-- Every point of the second-stage reduced space is the image of a point of the level of
`(μ, ν)`. -/
private theorem surjective_comp_levelProdToLevelSnd {π₂ : h₁.levelSubMulAction b → Q₂}
    (hπ₁surj : Surjective π₁) (hπ₂surj : Surjective π₂) :
    Surjective (π₂ ∘ levelProdToLevelSnd hμ hν hsmul hμL hνG h₁ hν₁) := by
  intro q
  obtain ⟨y, rfl⟩ := hπ₂surj q
  obtain ⟨z₁, hz₁⟩ := hπ₁surj y
  have hb : ν z₁ = b := by
    rw [← comp_apply (f := ν), ← congrFun hν₁ z₁, comp_apply, hz₁]
    exact h₁.mem_levelSubMulAction.1 y.property
  exact ⟨⟨z₁, (mem_levelSubMulAction_prod_of_smul_eq_smul_smul_iff hμ hν hsmul hμL hνG).2
    ⟨hμ.mem_levelSubMulAction.1 z₁.property, hb⟩⟩, congrArg π₂ (Subtype.ext hz₁)⟩

omit [I'.Boundaryless] [IQ₁.Boundaryless] [TopologicalSpace Q₂] in
/-- Two points of the level of `(μ, ν)` have the same image in the second-stage reduced space
exactly when they lie in the same orbit of `G × L`: `[[z]] = [[z']]` exactly when `l • [z'] = [z]`
for some `l : L`, that is when `g • l • z' = z` for some `g : G`. -/
private theorem comp_levelProdToLevelSnd_eq_iff {π₂ : h₁.levelSubMulAction b → Q₂}
    (hπ₁fib : ∀ z z', π₁ z = π₁ z' ↔ ∃ g : G, g • (z' : M) = z)
    (hπ₁L : ∀ (l : L) (z z' : hμ.levelSubMulAction c), (z' : M) = l • (z : M) →
      π₁ z' = l • π₁ z)
    (hπ₂fib : ∀ y y', π₂ y = π₂ y' ↔ ∃ l : L, l • (y' : Q₁) = y) (z z') :
    (π₂ ∘ levelProdToLevelSnd hμ hν hsmul hμL hνG h₁ hν₁) z =
        (π₂ ∘ levelProdToLevelSnd hμ hν hsmul hμL hνG h₁ hν₁) z' ↔
      ∃ g : G × L, g • (z' : M) = z := by
  have hw (l : L) : l • (z' : M) ∈ hμ.levelSubMulAction c := hμ.mem_levelSubMulAction.2
    ((hμL l z').trans
      ((mem_levelSubMulAction_prod_of_smul_eq_smul_smul_iff hμ hν hsmul hμL hνG).1 z'.property).1)
  rw [comp_apply, comp_apply, hπ₂fib]
  refine ⟨fun ⟨l, hl⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ⟨g.2, ?_⟩⟩
  · obtain ⟨g, hg⟩ := (hπ₁fib (levelProdToLevel hμ hν hsmul hμL hνG z) ⟨_, hw l⟩).1 <| by
      rw [hπ₁L l (levelProdToLevel hμ hν hsmul hμL hνG z') ⟨_, hw l⟩ rfl]
      exact hl.symm
    exact ⟨(g, l), (hsmul _ _).trans hg⟩
  · rw [← hπ₁L g.2 (levelProdToLevel hμ hν hsmul hμL hνG z') ⟨_, hw g.2⟩ rfl]
    exact ((hπ₁fib (levelProdToLevel hμ hν hsmul hμL hνG z) ⟨_, hw g.2⟩).2
      ⟨g.1, (hsmul _ _).symm.trans hg⟩).symm

end Level

omit [IQ₁.Boundaryless] in
/-- **Regularity in stages gives regularity of the pair.** Let `c` be a regular value of `μ`, let
`π₁ : μ⁻¹(c) → Q₁` be a submersion out of the level with its submanifold structure, and let `ν₁` be
a moment map on `Q₁` with `ν₁ ∘ π₁ = ν ∘ i₁` having `b` as a regular value. Then `(c, b)` is a
regular value of the moment map `x ↦ (μ x, ν x)` of `G × L`. -/
theorem forall_differential_surjective_prod_of_isSubmersion (hμ : σ.IsEquivariantMomentMap μ)
    (hν : σ.IsEquivariantMomentMap ν) (hsmul : ∀ (g : G × L) (x : M), g • x = g.1 • g.2 • x)
    (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x) (hνG : ∀ (g : G) (x : M), ν (g • x) = ν x)
    (hreg₁ : ∀ x, μ x = c → Surjective (hμ.differential x))
    (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n₁)
    {η₁ : SmoothTwoForm IQ₁ Q₁} {ν₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IL L)}
    (h₁ : η₁.IsEquivariantMomentMap ν₁) (hreg₂ : ∀ y, ν₁ y = b → Surjective (h₁.differential y))
    {π₁ : hμ.levelSubMulAction c → Q₁} (hν₁ : ν₁ ∘ π₁ = ν ∘ Subtype.val) :
    letI := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
    Manifold.IsSubmersion 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ ∞ π₁ →
      ∀ x, Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (μ x, ν x) =
          Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b) →
        Surjective ((hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).differential x) := by
  let := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
  -- Given `(α, β)`, pick `v₀` with `dμ v₀ = α`, then a tangent vector `u` of `μ⁻¹(c)` with
  -- `dν₁ (dπ₁ u) = β - dν v₀`; on it `dμ` vanishes and `dν = dν₁ ∘ dπ₁`, so `v₀ + u` maps to
  -- `(α, β)`.
  intro hπ₁ x hx φ
  rw [(Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L).injective.eq_iff, Prod.mk.injEq] at hx
  have hemb₁ := hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁
  let x₁ : hμ.levelSubMulAction c := ⟨x, hμ.mem_levelSubMulAction.2 hx.1⟩
  set p := (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L).symm φ
  obtain ⟨v₀, hv₀⟩ := hreg₁ x hx.1 p.1
  obtain ⟨w, hw⟩ := hreg₂ (π₁ x₁) ((congrFun hν₁ x₁).trans hx.2) (p.2 - hν.differential x v₀)
  obtain ⟨u, rfl⟩ := hπ₁.surjective_mfderiv (by simp) x₁ w
  have hμu : hμ.differential x (mfderiv _ I' Subtype.val x₁ u) = 0 :=
    hμ.toIsMomentMap.differential_mfderiv_eq_zero
      (fun y ↦ hμ.mem_levelSubMulAction.1 y.property) x₁ u
  have hνu : hν.differential x (mfderiv _ I' Subtype.val x₁ u) = p.2 - hν.differential x v₀ := by
    rw [← hw]
    exact (hν.toIsMomentMap.differential_mfderiv_eq_of_comp_eq h₁.toIsMomentMap hν₁ x₁
      (hemb₁.contMDiff.mdifferentiableAt (by simp)) ((hπ₁.contMDiff x₁).mdifferentiableAt (by simp))
      u).symm
  refine ⟨v₀ + mfderiv _ I' Subtype.val x₁ u, ?_⟩
  rw [IsMomentMap.differential_prod_of_smul_eq_smul_smul hμ.toIsMomentMap hν.toIsMomentMap hsmul,
    map_add, map_add, hv₀, hμu, hνu, add_zero, add_sub_cancel, Prod.mk.eta,
    LinearEquiv.apply_symm_apply]

/-- **Reduction in stages for a product group.** Let `G` and `L` act on `(M, σ)` with
coadjoint-equivariant moment maps `μ` and `ν`, where `μ` is invariant under `L` and `ν` under `G`,
and let `G × L` act by `(g, l) • x = g • l • x`, with the moment map `x ↦ (μ x, ν x)`. Let `c` be a
regular value of `μ`, with the level `Z₁ = μ⁻¹(c)` carrying its submanifold structure.

* Let `π₁ : Z₁ → Q₁` be a surjective submersion onto a manifold with an action of `L`, whose fibres
  are the `G`-orbits, with `π₁ (l • z) = l • π₁ z`, carrying a form `η₁` with `π₁^* η₁ = i₁^* σ` and
  a coadjoint-equivariant moment map `ν₁` of `L` with `ν₁ ∘ π₁ = ν ∘ i₁`. These are the first stage
  of the reduction, by `G` at `c`.
* Let `b` be a regular value of `ν₁`, and `π₂ : Z₂ → Q₂` a surjective submersion out of the level
  `Z₂ = ν₁⁻¹(b)` whose fibres are the `L`-orbits, carrying a form `η₂` with `π₂^* η₂ = i₂^* η₁`.
  This is the second stage, by `L` at `b`.
* Then `(c, b)` is a regular value of `(μ, ν)`
  (`SmoothTwoForm.IsEquivariantMomentMap.forall_differential_surjective_prod_of_isSubmersion`),
  so the level `Z = μ⁻¹(c) ∩ ν⁻¹(b)` carries its submanifold structure. Let `π : Z → Q` be a
  surjective submersion whose fibres are the `G × L`-orbits, carrying a form `η` with
  `π^* η = i^* σ`. This is the direct reduction by `G × L` at `(c, b)`.

Then there is a diffeomorphism `Φ : Q → Q₂` with `Φ [z] = [[z]]` and `Φ^* η₂ = η`. -/
theorem exists_diffeomorph_apply_eq_and_mpullback_eq_of_smul_eq_smul_smul
    (hμ : σ.IsEquivariantMomentMap μ) (hν : σ.IsEquivariantMomentMap ν)
    (hsmul : ∀ (g : G × L) (x : M), g • x = g.1 • g.2 • x)
    (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x) (hνG : ∀ (g : G) (x : M), ν (g • x) = ν x)
    (hreg₁ : ∀ x, μ x = c → Surjective (hμ.differential x))
    (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n₁)
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra (I.prod IL) (G × L)) = n)
    {η₁ : SmoothTwoForm IQ₁ Q₁} {ν₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IL L)}
    (h₁ : η₁.IsEquivariantMomentMap ν₁) (hreg₂ : ∀ y, ν₁ y = b → Surjective (h₁.differential y))
    (hn₂ : finrank ℝ EQ₁ - finrank ℝ (GroupLieAlgebra IL L) = n₂)
    {π₁ : hμ.levelSubMulAction c → Q₁} {π₂ : h₁.levelSubMulAction b → Q₂}
    {π : (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulAction
      (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b)) → Q}
    {η₂ : SmoothTwoForm IQ₂ Q₂} {η : SmoothTwoForm IQ Q}
    (hπ₁surj : Surjective π₁) (hπ₁fib : ∀ z z', π₁ z = π₁ z' ↔ ∃ g : G, g • (z' : M) = z)
    (hπ₁L : ∀ (l : L) (z z' : hμ.levelSubMulAction c), (z' : M) = l • (z : M) →
      π₁ z' = l • π₁ z)
    (hν₁ : ν₁ ∘ π₁ = ν ∘ Subtype.val)
    (hπ₂surj : Surjective π₂) (hπ₂fib : ∀ y y', π₂ y = π₂ y' ↔ ∃ l : L, l • (y' : Q₁) = y)
    (hπsurj : Surjective π) (hπfib : ∀ z z', π z = π z' ↔ ∃ g : G × L, g • (z' : M) = z) :
    letI := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
    letI := h₁.levelSubMulActionChartedSpace b hreg₂ hn₂
    haveI := hμ.isManifold_levelSubMulAction hreg₁ hn₁
    haveI := h₁.isManifold_levelSubMulAction hreg₂ hn₂
    ∀ (hπ₁ : Manifold.IsSubmersion 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ ∞ π₁),
      letI := (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulActionChartedSpace _
        (hμ.forall_differential_surjective_prod_of_isSubmersion hν hsmul hμL hνG hreg₁ hn₁ h₁
          hreg₂ hν₁ hπ₁) hn
      haveI := (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).isManifold_levelSubMulAction
        (hμ.forall_differential_surjective_prod_of_isSubmersion hν hsmul hμL hνG hreg₁ hn₁ h₁
          hreg₂ hν₁ hπ₁) hn
      ∀ (hπ₂ : Manifold.IsSubmersion 𝓘(ℝ, Fin n₂ → ℝ) IQ₂ ∞ π₂)
        (hπ : Manifold.IsSubmersion 𝓘(ℝ, Fin n → ℝ) IQ ∞ π),
        SmoothForm.mpullback π₁ hπ₁.contMDiff η₁ = SmoothForm.mpullback Subtype.val
          (hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff σ →
        SmoothForm.mpullback π₂ hπ₂.contMDiff η₂ = SmoothForm.mpullback Subtype.val
          (h₁.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff η₁ →
        SmoothForm.mpullback π hπ.contMDiff η = SmoothForm.mpullback Subtype.val
          ((hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).isSmoothEmbedding_coe_levelSubMulAction
            (hμ.forall_differential_surjective_prod_of_isSubmersion hν hsmul hμL hνG hreg₁ hn₁
              h₁ hreg₂ hν₁ hπ₁) hn).contMDiff σ →
        ∃ Φ : Q ≃ₘ⟮IQ, IQ₂⟯ Q₂,
          (∀ (z : (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulAction
              (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b)))
            (z₁ : hμ.levelSubMulAction c) (y : h₁.levelSubMulAction b),
            (z₁ : M) = z → (y : Q₁) = π₁ z₁ → Φ (π z) = π₂ y) ∧
          SmoothForm.mpullback Φ Φ.contMDiff η₂ = η := by
  have H := hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG
  let := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
  let := h₁.levelSubMulActionChartedSpace b hreg₂ hn₂
  have := hμ.isManifold_levelSubMulAction hreg₁ hn₁
  have := h₁.isManifold_levelSubMulAction hreg₂ hn₂
  intro hπ₁
  have hreg := hμ.forall_differential_surjective_prod_of_isSubmersion hν hsmul hμL hνG hreg₁ hn₁ h₁
    hreg₂ hν₁ hπ₁
  let := H.levelSubMulActionChartedSpace _ hreg hn
  have := H.isManifold_levelSubMulAction hreg hn
  intro hπ₂ hπ hη₁ hη₂ hη
  refine (SmoothForm.exists_diffeomorph_comp_eq_and_mpullback_eq_of_comp_eq
    (j := levelProdToLevel hμ hν hsmul hμL hνG)
    (k := levelProdToLevelSnd hμ hν hsmul hμL hνG h₁ hν₁)
    hπ hπsurj hπ₁ hπ₂ (H.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    (hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁)
    (h₁.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂) rfl rfl
    (surjective_comp_levelProdToLevelSnd hμ hν hsmul hμL hνG h₁ hν₁ hπ₁surj hπ₂surj)
    (fun z z' ↦ (comp_levelProdToLevelSnd_eq_iff hμ hν hsmul hμL hνG h₁ hν₁ hπ₁fib hπ₁L hπ₂fib z
      z').trans (hπfib z z').symm) hη₁ hη₂ hη fun z v w hvw ↦ ?_).imp
    fun Φ hΦ ↦ ⟨fun z z₁ y hz₁ hy ↦ ?_, hΦ.2⟩
  · -- A tangent vector `w` of the level of `ν₁` lifts along `dπ₁` to a tangent vector `v` of
    -- `μ⁻¹(c)`; then `dμ v = 0` and `dν v = dν₁ (dπ₁ v) = dν₁ w = 0`, so `v` is tangent to the
    -- level of `(μ, ν)`.
    have hemb₁ := hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁
    let j₁ : hμ.levelSubMulAction c := levelProdToLevel hμ hν hsmul hμL hνG z
    have hμv : hμ.differential j₁ (mfderiv _ I' Subtype.val j₁ v) = 0 :=
      hμ.toIsMomentMap.differential_mfderiv_eq_zero
        (fun y ↦ hμ.mem_levelSubMulAction.1 y.property) j₁ v
    have hνv : hν.differential j₁ (mfderiv _ I' Subtype.val j₁ v) = 0 := by
      rw [← hν.toIsMomentMap.differential_mfderiv_eq_of_comp_eq h₁.toIsMomentMap hν₁ j₁
        (hemb₁.contMDiff.mdifferentiableAt (by simp)) ((hπ₁.contMDiff j₁).mdifferentiableAt
        (by simp)) v, ← hvw]
      exact h₁.toIsMomentMap.differential_mfderiv_eq_zero
        (fun y ↦ h₁.mem_levelSubMulAction.1 y.property) _ w
    refine LinearMap.mem_range.1 ((H.range_mfderiv_coe_levelSubMulAction hreg hn z).ge
      (LinearMap.mem_ker.2 ?_))
    rw [IsMomentMap.differential_prod_of_smul_eq_smul_smul hμ.toIsMomentMap hν.toIsMomentMap
      hsmul, hμv, hνv, Prod.mk_zero_zero, map_zero]
  rw [← comp_apply (f := Φ), hΦ.1, comp_apply]
  exact congrArg π₂ (Subtype.ext (hy.trans (congrArg π₁ (Subtype.ext hz₁))).symm)

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
