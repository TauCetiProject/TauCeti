/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice

/-!
# The action map of a balanced product is a local diffeomorphism

Let a finite-dimensional real Lie group `G` act smoothly on a manifold `M`, let `K` be a closed
subgroup of `G` acting smoothly on a manifold `Z`, and let `ι : Z → M` be a smooth `K`-equivariant
map. The action map `[g, z] ↦ g • ι z` descends from `G × Z` to the balanced product `G ×_K Z`
(`TauCeti.BalancedProduct.liftRightTranslation`). This file proves that the descended map is a
local diffeomorphism at `[g, z]` when the differential of `(g, z) ↦ g • ι z` is onto there and the
dimensions match, and in particular at the identity coset `[1, z₀]` when `ι` is a transverse slice
at `z₀`: its differential at `z₀` is injective with range a complement of the orbit tangent space
`𝔤 · ι z₀`, and `dim K = dim 𝔤_{ι z₀}`. This is the local half of the slice theorem
`G ×_K S ≅ G • S` for proper actions (Meinrenken, Theorem 1.25), with `K` the stabilizer of `ι z₀`,
whose Lie algebra is the isotropy algebra `𝔤_{ι z₀}`
(`TauCeti.Lie.finrank_lieSubalgebraOfSubgroup_stabilizer`). The linear slice data at a point of a
proper action are `ProperSMul.exists_equivariant_slice`.

The differential of `(g, z) ↦ g • ι z` at `(1, z₀)` is `(ξ, v) ↦ ξ_M(ι z₀) + dι v`, which is onto
`T_{ι z₀} M` because the orbit tangent space and the range of `dι` together span it. The
projection `G × Z → G ×_K Z` is a submersion, so the differential of the descended map at
`[1, z₀]` is onto too. Since `dim G + dim Z - dim K = dim (𝔤 · ι z₀) + dim Z = dim M`, it is
bijective, and the inverse function theorem applies.

The descended map is `G`-equivariant: left translation by `g` on the `G` factor intertwines
`(h, z) ↦ h • ι z` with the diffeomorphism `g • ·` of `M`. So surjectivity of the differential at
`(1, z)` propagates to `(g, z)` for every `g`
(`TauCeti.surjective_mfderiv_smul_slice_of_surjective_one`), and the descended map is a local
diffeomorphism along the whole orbit `G ×_K {z}`; if this holds for every `z ∈ Z`, it is a local
diffeomorphism on all of `G ×_K Z`.

## Main results

* `TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation`: the descended action map
  is a local diffeomorphism at `[g, z]` when the differential of `(g, z) ↦ g • ι z` is onto there
  and `dim G + dim Z = dim M + dim K`.
* `TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_one`: the slice theorem at
  the identity coset, for a transverse slice `ι`.
* `TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_of_surjective_one` and
  `TauCeti.BalancedProduct.isLocalDiffeomorph_liftRightTranslation`: the descended action map is a
  local diffeomorphism along the orbit of `[1, z]`, and everywhere when this holds for every `z`.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.25 and its proof.
-/

public section

noncomputable section

open Function Set Manifold MulAction Module
open scoped ContDiff Manifold

namespace TauCeti.BalancedProduct

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {G : Type*} [Group G] {K : Subgroup G} {Z : Type*} [MulAction K Z]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace G]
  [ChartedSpace H G] [LieGroup I ∞ G] [IsClosed (K : Set G)]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] [TopologicalSpace Z]
  [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ K Z]
  {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M] [MulAction G M] [ContMDiffSMul I IM ∞ G M]
  {ι : Z →ₑ[((↑) : K → G)] M}

/-- **The action map of a balanced product is a local diffeomorphism where the action map of the
product is onto.** Let `ι : Z → M` be a smooth `K`-equivariant map, and let the dimensions satisfy
`dim G + dim Z = dim M + dim K`, so that `G ×_K Z` and `M` have the same dimension. If the
differential of `(g, z) ↦ g • ι z` at `(g, z)` is onto, then `[g, z] ↦ g • ι z` is a local
diffeomorphism at `[g, z]`. -/
theorem isLocalDiffeomorphAt_liftRightTranslation (hι : ContMDiff IZ IM ∞ ι) {g : G} {z : Z}
    (hsurj : Surjective (mfderiv (I.prod IZ) IM (fun p : G × Z ↦ p.1 • ι p.2) (g, z)))
    (hdim : finrank ℝ E + finrank ℝ EZ = finrank ℝ EM + finrank ℝ F) :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
      (liftRightTranslation ι) (mk K (K.toRightTranslation g) z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  -- `M` is finite-dimensional, as the onto image of the tangent space `E × EZ` of `G × Z`.
  have : FiniteDimensional ℝ (TangentSpace (I.prod IZ) (g, z)) :=
    inferInstanceAs (FiniteDimensional ℝ (E × EZ))
  have : FiniteDimensional ℝ EM := Module.Finite.of_surjective _ hsurj
  have := isManifold_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)
  have hπ := isSubmersion_quotientMk_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ)
    (F := F)
  have hΦ := contMDiff_liftRightTranslation (I := I) (F := F) hι
  set π := Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))
  set p₀ : K.RightTranslation × Z := (K.toRightTranslation g, z)
  have hd := mfderiv_comp p₀ (hΦ.mdifferentiableAt (by simp))
    (hπ.contMDiff.mdifferentiableAt (by simp) : MDifferentiableAt _ _ π p₀)
  rw [liftRightTranslation_comp_quotientMk] at hd
  -- The differential of `[g, z] ↦ g • ι z` is onto, as its composite with that of the
  -- projection is.
  have hs : Surjective (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM
      (liftRightTranslation ι) (π p₀)) := by
    -- `K.RightTranslation` is a type synonym of `G` with the same charts, and
    -- `K.toRightTranslation` is `Equiv.refl G`, so this is `hsurj` up to definitional unfolding.
    have hs' : Surjective (mfderiv (I.prod IZ) IM
        (fun p : K.RightTranslation × Z ↦ K.toRightTranslation.symm p.1 • ι p.2) p₀) := hsurj
    rw [hd] at hs'
    exact Surjective.of_comp (g := mfderiv (I.prod IZ)
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) π p₀) hs'
  have hdim' : finrank ℝ (ProperSMul.QuotientModelSpace F (E × EZ)) = finrank ℝ EM := by
    rw [ProperSMul.finrank_quotientModelSpace, finrank_prod]
    omega
  -- Between spaces of the same finite dimension, it is also injective.
  have hinj : Injective (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM
      (liftRightTranslation ι) (π p₀)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').2 hs
  exact isLocalDiffeomorphAt_of_injective_mfderiv hΦ.contMDiffOn isOpen_univ (mem_univ _)
    BoundarylessManifold.isInteriorPoint (by simp) hinj hdim'

/-- **The slice theorem at the identity coset.** Let `ι : Z → M` be a smooth `K`-equivariant map
whose differential at `z₀` is injective with range a complement of the orbit tangent space
`𝔤 · ι z₀`, and let `dim K = dim 𝔤_{ι z₀}`, as for the stabilizer `K = G_{ι z₀}` with its
closed-subgroup structure. Then `[g, z] ↦ g • ι z` is a local diffeomorphism from `G ×_K Z` at
`[1, z₀]`. -/
theorem isLocalDiffeomorphAt_liftRightTranslation_one [CompleteSpace EM] (hι : ContMDiff IZ IM ∞ ι)
    {z₀ : Z} (hinj : Injective (mfderiv IZ IM ι z₀))
    (hcompl : IsCompl ((InfinitesimalAction.fundamental I G IM M).orbitTangent (ι z₀))
      (LinearMap.range (mfderiv IZ IM ι z₀).toLinearMap))
    (hF : finrank ℝ F = finrank ℝ ((InfinitesimalAction.fundamental I G IM M).isotropy (ι z₀))) :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
      (liftRightTranslation ι) (mk K (K.toRightTranslation 1) z₀) := by
  -- Every tangent vector at `ι z₀` is `ξ_M(ι z₀) + dι v`, the differential at `(1, z₀)`.
  have hsurj : Surjective (mfderiv (I.prod IZ) IM (fun p : G × Z ↦ p.1 • ι p.2) (1, z₀)) := by
    intro (w : TangentSpace IM (ι z₀))
    have hw : w ∈ (InfinitesimalAction.fundamental I G IM M).orbitTangent (ι z₀) ⊔
        LinearMap.range (mfderiv IZ IM ι z₀).toLinearMap := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨a, ha, b, ⟨v, rfl⟩, hab⟩ := Submodule.mem_sup.1 hw
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1 ha
    refine ⟨(ξ, v), ?_⟩
    rw [mfderiv_smul_slice_apply (hι.mdifferentiableAt (by simp)), ← hab,
      InfinitesimalAction.fundamental_apply, ContinuousLinearMap.coe_coe]
  -- `M` is finite-dimensional, as the onto image of the tangent space `E × EZ` of `G × Z`.
  have : FiniteDimensional ℝ (TangentSpace (I.prod IZ) ((1 : G), z₀)) :=
    inferInstanceAs (FiniteDimensional ℝ (E × EZ))
  have : FiniteDimensional ℝ (TangentSpace IM (ι z₀)) := Module.Finite.of_surjective _ hsurj
  refine isLocalDiffeomorphAt_liftRightTranslation hι hsurj ?_
  have h₁ := Submodule.finrank_add_eq_of_isCompl hcompl
  have h₂ := (InfinitesimalAction.fundamental I G IM M).finrank_orbitTangent_add_finrank_isotropy
    (ι z₀)
  have h₃ := LinearMap.finrank_range_of_inj hinj
  have h₄ : finrank ℝ (TangentSpace IM (ι z₀)) = finrank ℝ EM := rfl
  have h₅ : finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E := rfl
  have h₆ : finrank ℝ (TangentSpace IZ z₀) = finrank ℝ EZ := rfl
  omega

/-- **The descended action map is a local diffeomorphism along the orbit of `[1, z]`.** If the
differential of `(h, z) ↦ h • ι z` at `(1, z)` is onto and `dim G + dim Z = dim M + dim K`, then
`[g, z] ↦ g • ι z` is a local diffeomorphism at `[g, z]` for every `g ∈ G`. -/
theorem isLocalDiffeomorphAt_liftRightTranslation_of_surjective_one (hι : ContMDiff IZ IM ∞ ι)
    {z : Z} (hsurj : Surjective (mfderiv (I.prod IZ) IM (fun p : G × Z ↦ p.1 • ι p.2) (1, z)))
    (hdim : finrank ℝ E + finrank ℝ EZ = finrank ℝ EM + finrank ℝ F) (g : G) :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
      (liftRightTranslation ι) (mk K (K.toRightTranslation g) z) :=
  isLocalDiffeomorphAt_liftRightTranslation hι
    (surjective_mfderiv_smul_slice_of_surjective_one (hι.mdifferentiableAt (by simp)) hsurj g)
    hdim

/-- **The action map of a balanced product is a local diffeomorphism everywhere** when the
differential of `(h, z) ↦ h • ι z` is onto at `(1, z)` for every `z ∈ Z` and
`dim G + dim Z = dim M + dim K`: every point of `G ×_K Z` is a class `[g, z]`. -/
theorem isLocalDiffeomorph_liftRightTranslation (hι : ContMDiff IZ IM ∞ ι)
    (hsurj : ∀ z : Z,
      Surjective (mfderiv (I.prod IZ) IM (fun p : G × Z ↦ p.1 • ι p.2) (1, z)))
    (hdim : finrank ℝ E + finrank ℝ EZ = finrank ℝ EM + finrank ℝ F) :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsLocalDiffeomorph 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
      (liftRightTranslation ι) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  intro q
  induction q using induction_on_toRightTranslation with
  | h g z => exact isLocalDiffeomorphAt_liftRightTranslation_of_surjective_one hι (hsurj z) hdim g

end TauCeti.BalancedProduct
