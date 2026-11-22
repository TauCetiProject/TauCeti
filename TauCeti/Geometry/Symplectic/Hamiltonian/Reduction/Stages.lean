/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

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
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq`).

The theorem is stated for arbitrary presentations of the three reduced spaces: `π`, `π₁` and `π₂`
are surjective submersions out of the regular levels, with the submanifold structures of
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`, whose fibres are the
orbits of `G × L`, of `G` and of `L`, and the forms are related by `π^* η = i^* σ`,
`π₁^* η₁ = i₁^* σ` and `π₂^* η₂ = i₂^* η₁` for the inclusions `i`, `i₁`, `i₂` of the levels. The
Marsden–Weinstein–Meyer reduced spaces of
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace`, with the action of `L` on the
first stage of `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Symmetry`, are such
presentations. No freeness, properness or nondegeneracy enters beyond what these presentations
provide.

The proof compares the two presentations of `Q` and `Q₂` through the map
`Z → Z₂`, `z ↦ π₁ z`, which is well defined because a point of `Z` lies in `Z₁` and its image
in `Q₁` lies in `ν₁⁻¹(b)`. Its composite `Ψ : Z → Q₂` with `π₂` is surjective, has the fibres of
`π`, and pulls `η₂` back to `i^* σ`. It is a submersion: a tangent vector of `Z₂` lifts along
`dπ₁` to a tangent vector `v` of `Z₁`, with `dμ v = 0`, and with `dν v = dν₁ (dπ₁ v) = 0`
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_mfderiv_eq_of_comp_eq`), so `v` is tangent to
`Z`, the level of `(μ, ν)`
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_prod_of_smul_eq_smul_smul`). Two surjective
submersions with the same fibres induce a diffeomorphism (`Equiv.diffeomorphOfSubmersions`).

## Main results

* `SmoothTwoForm.IsEquivariantMomentMap.mem_levelSubMulAction_prod_of_smul_eq_smul_smul_iff`: the
  level of `(μ, ν)` at `(c, b)` is `μ⁻¹(c) ∩ ν⁻¹(b)`.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq`:
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

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- A map `k : Z → Z₂` covering `π₁ ∘ j` along immersions `i₁ : Z₁ → M` and `i₂ : Z₂ → Q₁` has
surjective differential at `z` when every tangent vector of `Z₁` at `j z` whose image under
`dπ₁` is tangent to `Z₂` is carried by `di₁` into the tangent image of `i₁ ∘ j`. -/
private theorem surjective_mfderiv_of_comp_eq
    {EZ HZ Z EZ₁ HZ₁ Z₁ EZ₂ HZ₂ Z₂ EM HM M EQ₁ HQ₁ Q₁ : Type*}
    [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
    {IZ₁ : ModelWithCorners ℝ EZ₁ HZ₁} [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁]
    [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
    {IZ₂ : ModelWithCorners ℝ EZ₂ HZ₂} [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
    [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [TopologicalSpace HQ₁]
    {IQ₁ : ModelWithCorners ℝ EQ₁ HQ₁} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁]
    {i₁ : Z₁ → M} {i₂ : Z₂ → Q₁} {π₁ : Z₁ → Q₁} {j : Z → Z₁} {k : Z → Z₂} {z : Z}
    (hj : MDifferentiableAt IZ IZ₁ j z) (hk : MDifferentiableAt IZ IZ₂ k z)
    (hi₁ : MDifferentiableAt IZ₁ IM i₁ (j z)) (hi₂ : MDifferentiableAt IZ₂ IQ₁ i₂ (k z))
    (hπ₁ : MDifferentiableAt IZ₁ IQ₁ π₁ (j z)) (hik : i₂ ∘ k = π₁ ∘ j)
    (hi₁inj : Injective (mfderiv IZ₁ IM i₁ (j z)))
    (hi₂inj : Injective (mfderiv IZ₂ IQ₁ i₂ (k z)))
    (hπ₁surj : Surjective (mfderiv IZ₁ IQ₁ π₁ (j z)))
    (hkey : ∀ v w, mfderiv IZ₂ IQ₁ i₂ (k z) w = mfderiv IZ₁ IQ₁ π₁ (j z) v →
      ∃ u, mfderiv IZ IM (i₁ ∘ j) z u = mfderiv IZ₁ IM i₁ (j z) v) :
    Surjective (mfderiv IZ IZ₂ k z) := by
  intro w
  obtain ⟨v, hv⟩ := hπ₁surj (mfderiv IZ₂ IQ₁ i₂ (k z) w)
  obtain ⟨u, hu⟩ := hkey v w hv.symm
  -- `di₁ (dj u) = d(i₁ ∘ j) u = di₁ v`, so `dj u = v`, and then
  -- `di₂ (dk u) = dπ₁ (dj u) = dπ₁ v = di₂ w`.
  have hju : mfderiv IZ IZ₁ j z u = v := hi₁inj <| by
    rw [← mfderiv_comp_apply z hi₁ hj]
    exact hu
  refine ⟨u, hi₂inj ?_⟩
  rw [← mfderiv_comp_apply z hi₂ hk, hik, mfderiv_comp_apply z hπ₁ hj, hju, hv]

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

/-- The map `z ↦ π₁ z` from the level of `(μ, ν)` at `(c, b)` to the level of `ν₁` at `b` is smooth
with surjective differentials. A tangent vector `w` of the level of `ν₁` lifts along `dπ₁` to a
tangent vector `v` of `μ⁻¹(c)`; then `dμ v = 0` and `dν v = dν₁ (dπ₁ v) = dν₁ w = 0`, so `v` is
tangent to the level of `(μ, ν)`. -/
private theorem contMDiff_levelProdToLevelSnd (hμ : σ.IsEquivariantMomentMap μ)
    (hν : σ.IsEquivariantMomentMap ν) (hsmul : ∀ (g : G × L) (x : M), g • x = g.1 • g.2 • x)
    (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x) (hνG : ∀ (g : G) (x : M), ν (g • x) = ν x)
    (hreg₁ : ∀ x, μ x = c → Surjective (hμ.differential x))
    (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n₁)
    (hreg : ∀ x, Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (μ x, ν x) =
        Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b) →
      Surjective ((hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).differential x))
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra (I.prod IL) (G × L)) = n)
    {η₁ : SmoothTwoForm IQ₁ Q₁} {ν₁ : Q₁ → Module.Dual ℝ (GroupLieAlgebra IL L)}
    (h₁ : η₁.IsEquivariantMomentMap ν₁) (hreg₂ : ∀ y, ν₁ y = b → Surjective (h₁.differential y))
    (hn₂ : finrank ℝ EQ₁ - finrank ℝ (GroupLieAlgebra IL L) = n₂)
    {π₁ : hμ.levelSubMulAction c → Q₁} (hν₁ : ν₁ ∘ π₁ = ν ∘ Subtype.val) :
    letI := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
    letI := h₁.levelSubMulActionChartedSpace b hreg₂ hn₂
    letI := (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulActionChartedSpace _ hreg hn
    haveI := hμ.isManifold_levelSubMulAction hreg₁ hn₁
    haveI := h₁.isManifold_levelSubMulAction hreg₂ hn₂
    haveI := (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).isManifold_levelSubMulAction hreg hn
    Manifold.IsSubmersion 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ ∞ π₁ →
      ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n₂ → ℝ) ∞
          (levelProdToLevelSnd hμ hν hsmul hμL hνG (c := c) (b := b) h₁ hν₁) ∧
        ∀ z, Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n₂ → ℝ)
          (levelProdToLevelSnd hμ hν hsmul hμL hνG (c := c) (b := b) h₁ hν₁) z) := by
  have H := hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG
  let := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
  let := h₁.levelSubMulActionChartedSpace b hreg₂ hn₂
  let := H.levelSubMulActionChartedSpace _ hreg hn
  have := hμ.isManifold_levelSubMulAction hreg₁ hn₁
  have := h₁.isManifold_levelSubMulAction hreg₂ hn₂
  have := H.isManifold_levelSubMulAction hreg hn
  intro hπ₁
  let j := levelProdToLevel hμ hν hsmul hμL hνG (c := c) (b := b)
  let k := levelProdToLevelSnd hμ hν hsmul hμL hνG (c := c) (b := b) h₁ hν₁
  have hemb₁ := hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁
  have hemb₂ := h₁.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂
  have hj : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n₁ → ℝ) ∞ j :=
    hemb₁.contMDiff_iff_comp.2 (H.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
  have hk : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n₂ → ℝ) ∞ k :=
    hemb₂.contMDiff_iff_comp.2 (hπ₁.contMDiff.comp hj)
  refine ⟨hk, fun z ↦ surjective_mfderiv_of_comp_eq ((hj z).mdifferentiableAt (by simp))
    ((hk z).mdifferentiableAt (by simp)) (hemb₁.contMDiff.mdifferentiableAt (by simp))
    (hemb₂.contMDiff.mdifferentiableAt (by simp))
    ((hπ₁.contMDiff (j z)).mdifferentiableAt (by simp)) rfl
    (hemb₁.isImmersion.mfderiv_injective (by simp) (j z))
    (hemb₂.isImmersion.mfderiv_injective (by simp) (k z)) (hπ₁.surjective_mfderiv (by simp) (j z))
    fun v w hvw ↦ ?_⟩
  have hμv : hμ.differential (j z) (mfderiv _ I' Subtype.val (j z) v) = 0 := by
    rw [← LinearMap.mem_ker, ← hμ.range_mfderiv_coe_levelSubMulAction hreg₁ hn₁ (j z)]
    exact ⟨v, rfl⟩
  have hνv : hν.differential (j z) (mfderiv _ I' Subtype.val (j z) v) = 0 := by
    rw [← hν.toIsMomentMap.differential_mfderiv_eq_of_comp_eq h₁.toIsMomentMap
      (hemb₁.contMDiff.mdifferentiable (by simp)) (hπ₁.contMDiff.mdifferentiable (by simp)) hν₁
      (j z) v, ← hvw, ← LinearMap.mem_ker,
      ← h₁.range_mfderiv_coe_levelSubMulAction hreg₂ hn₂ (k z)]
    exact ⟨w, rfl⟩
  have hker : H.differential z (mfderiv _ I' Subtype.val (j z) v) = 0 := by
    rw [IsMomentMap.differential_prod_of_smul_eq_smul_smul hμ.toIsMomentMap hν.toIsMomentMap
      hsmul, hμv, hνv, Prod.mk_zero_zero, map_zero]
  rw [← LinearMap.mem_ker, ← H.range_mfderiv_coe_levelSubMulAction hreg hn z] at hker
  exact hker

/-- **Reduction in stages for a product group.** Let `G` and `L` act on `(M, σ)` with
coadjoint-equivariant moment maps `μ` and `ν`, where `μ` is invariant under `L` and `ν` under `G`,
and let `G × L` act by `(g, l) • x = g • l • x`, with the moment map `x ↦ (μ x, ν x)`. Let `c` be a
regular value of `μ`, `(c, b)` one of `(μ, ν)`, with the levels `Z₁ = μ⁻¹(c)` and
`Z = μ⁻¹(c) ∩ ν⁻¹(b)` carrying their submanifold structures.

* Let `π₁ : Z₁ → Q₁` be a surjective submersion onto a manifold with an action of `L`, whose fibres
  are the `G`-orbits, with `π₁ (l • z) = l • π₁ z`, carrying a form `η₁` with `π₁^* η₁ = i₁^* σ` and
  a coadjoint-equivariant moment map `ν₁` of `L` with `ν₁ ∘ π₁ = ν ∘ i₁`. These are the first stage
  of the reduction, by `G` at `c`.
* Let `b` be a regular value of `ν₁`, and `π₂ : Z₂ → Q₂` a surjective submersion out of the level
  `Z₂ = ν₁⁻¹(b)` whose fibres are the `L`-orbits, carrying a form `η₂` with `π₂^* η₂ = i₂^* η₁`.
  This is the second stage, by `L` at `b`.
* Let `π : Z → Q` be a surjective submersion whose fibres are the `G × L`-orbits, carrying a form
  `η` with `π^* η = i^* σ`. This is the direct reduction by `G × L` at `(c, b)`.

Then there is a diffeomorphism `Φ : Q → Q₂` with `Φ [z] = [[z]]` and `Φ^* η₂ = η`. -/
theorem exists_diffeomorph_apply_eq_and_mpullback_eq (hμ : σ.IsEquivariantMomentMap μ)
    (hν : σ.IsEquivariantMomentMap ν) (hsmul : ∀ (g : G × L) (x : M), g • x = g.1 • g.2 • x)
    (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x) (hνG : ∀ (g : G) (x : M), ν (g • x) = ν x)
    (hreg₁ : ∀ x, μ x = c → Surjective (hμ.differential x))
    (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n₁)
    (hreg : ∀ x, Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (μ x, ν x) =
        Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b) →
      Surjective ((hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).differential x))
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
    letI := (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulActionChartedSpace _ hreg hn
    haveI := hμ.isManifold_levelSubMulAction hreg₁ hn₁
    haveI := h₁.isManifold_levelSubMulAction hreg₂ hn₂
    haveI := (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).isManifold_levelSubMulAction hreg hn
    ∀ (hπ₁ : Manifold.IsSubmersion 𝓘(ℝ, Fin n₁ → ℝ) IQ₁ ∞ π₁)
      (hπ₂ : Manifold.IsSubmersion 𝓘(ℝ, Fin n₂ → ℝ) IQ₂ ∞ π₂)
      (hπ : Manifold.IsSubmersion 𝓘(ℝ, Fin n → ℝ) IQ ∞ π),
      SmoothForm.mpullback π₁ hπ₁.contMDiff η₁ = SmoothForm.mpullback Subtype.val
        (hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff σ →
      SmoothForm.mpullback π₂ hπ₂.contMDiff η₂ = SmoothForm.mpullback Subtype.val
        (h₁.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff η₁ →
      SmoothForm.mpullback π hπ.contMDiff η = SmoothForm.mpullback Subtype.val
        ((hμ.prod_of_smul_eq_smul_smul hν hsmul hμL
          hνG).isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
      ∃ Φ : Q ≃ₘ⟮IQ, IQ₂⟯ Q₂,
        (∀ (z : (hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG).levelSubMulAction
            (Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G IL L (c, b)))
          (z₁ : hμ.levelSubMulAction c) (y : h₁.levelSubMulAction b),
          (z₁ : M) = z → (y : Q₁) = π₁ z₁ → Φ (π z) = π₂ y) ∧
        SmoothForm.mpullback Φ Φ.contMDiff η₂ = η := by
  have H := hμ.prod_of_smul_eq_smul_smul hν hsmul hμL hνG
  let := hμ.levelSubMulActionChartedSpace c hreg₁ hn₁
  let := h₁.levelSubMulActionChartedSpace b hreg₂ hn₂
  let := H.levelSubMulActionChartedSpace _ hreg hn
  have := hμ.isManifold_levelSubMulAction hreg₁ hn₁
  have := h₁.isManifold_levelSubMulAction hreg₂ hn₂
  have := H.isManifold_levelSubMulAction hreg hn
  intro hπ₁ hπ₂ hπ hη₁ hη₂ hη
  let k := levelProdToLevelSnd hμ hν hsmul hμL hνG (c := c) (b := b) h₁ hν₁
  obtain ⟨hk, hkd⟩ := contMDiff_levelProdToLevelSnd hμ hν hsmul hμL hνG hreg₁ hn₁ hreg hn h₁ hreg₂
    hn₂ hν₁ hπ₁
  have hj : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n₁ → ℝ) ∞
      (levelProdToLevel hμ hν hsmul hμL hνG (c := c) (b := b)) :=
    (hμ.isSmoothEmbedding_coe_levelSubMulAction hreg₁ hn₁).contMDiff_iff_comp.2
      (H.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
  have hΨ : ContMDiff 𝓘(ℝ, Fin n → ℝ) IQ₂ ∞ (π₂ ∘ k) := hπ₂.contMDiff.comp hk
  -- `π₂ ∘ k` is a surjective submersion with the fibres of `π`, so it induces a diffeomorphism
  -- `Φ : Q → Q₂`, which pulls `η₂` back to `η` since `π^* Φ^* η₂ = (π₂ ∘ k)^* η₂ = π^* η`.
  have hΨsub : Manifold.IsSubmersion 𝓘(ℝ, Fin n → ℝ) IQ₂ ∞ (π₂ ∘ k) := by
    refine (hΨ.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun z ↦ ?_).isSubmersion
    rw [mfderiv_comp z ((hπ₂.contMDiff (k z)).mdifferentiableAt (by simp))
      ((hk z).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
    exact (hπ₂.surjective_mfderiv (by simp) (k z)).comp (hkd z)
  obtain ⟨Φ, hΦ⟩ := hπ.exists_diffeomorph_comp_eq hπsurj hΨsub
    (surjective_comp_levelProdToLevelSnd hμ hν hsmul hμL hνG h₁ hν₁ hπ₁surj hπ₂surj) fun z z' ↦
      (comp_levelProdToLevelSnd_eq_iff hμ hν hsmul hμL hνG h₁ hν₁ hπ₁fib hπ₁L hπ₂fib z z').trans
        (hπfib z z').symm
  refine ⟨Φ, fun z z₁ y hz₁ hy ↦ ?_, SmoothForm.mpullback_injective_of_surjective hπ.contMDiff
    hπsurj (hπ.surjective_mfderiv (by simp)) ?_⟩
  · rw [← comp_apply (f := Φ), hΦ, comp_apply]
    exact congrArg π₂ (Subtype.ext (hy.trans (congrArg π₁ (Subtype.ext hz₁))).symm)
  -- `π^* Φ^* η₂ = (π₂ ∘ k)^* η₂ = k^* i₂^* η₁ = j^* π₁^* η₁ = j^* i₁^* σ = i^* σ = π^* η`.
  rw [SmoothForm.mpullback_mpullback, hη]
  simp only [hΦ]
  rw [← SmoothForm.mpullback_mpullback _ _ hk hπ₂.contMDiff, hη₂,
    SmoothForm.mpullback_mpullback_of_comp_eq hk
      (h₁.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff hj hπ₁.contMDiff rfl, hη₁,
    SmoothForm.mpullback_mpullback]
  rfl

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
