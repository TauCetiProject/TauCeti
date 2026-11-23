/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

/-!
# Transport of Marsden–Weinstein–Meyer reduced spaces

Let a Lie group `G` act smoothly and properly by symplectomorphisms on `(M, σ)` with
coadjoint-equivariant moment map `μ`, and let `G₂` act likewise on `(M₂, σ₂)` with moment map
`μ₂`. For regular values `c` and `c₂` whose coadjoint stabilizers act freely on the levels, the
reduced spaces `μ⁻¹(c) / G_c` and `μ₂⁻¹(c₂) / G₂_{c₂}` are smooth manifolds carrying unique
reduced symplectic forms
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isManifold_orbitRelQuotient`, and
`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback` in the same namespace).
This file shows that they are symplectomorphic as soon as the data match.

Let `φ : M ≃ M₂` be a diffeomorphism carrying the level `μ⁻¹(c)` onto `μ₂⁻¹(c₂)`, and let
`ψ : G_c ≃* G₂_{c₂}` be a group isomorphism with `φ (k • x) = ψ k • φ x`. Then `φ` restricts to a
diffeomorphism of the levels
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelDiffeomorph`), since both are embedded
submanifolds, and this restriction descends to a diffeomorphism of the reduced spaces,
`[z] ↦ [φ z]` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientDiffeomorph`). If
moreover `φ^* σ₂ = σ`, it pulls the reduced form of `M₂` back to the reduced form of `M`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_orbitRelQuotientDiffeomorph`). Neither `ψ`
nor `φ` needs to be compatible with the Lie group structures chosen on the stabilizers.

Three instances of this are classical.

* **Equivariant symplectomorphisms.** A `G`-equivariant symplectomorphism `φ : M ≃ M₂` with
  `μ₂ ∘ φ = μ` induces a symplectomorphism of the reduced spaces at every regular value `c`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.exists_diffeomorph_mpullback_eq_of_map_smul`),
  with `ψ` the identity of `G_c`.
* **Points of one coadjoint orbit.** For `g ∈ G`, the action `x ↦ g • x` carries `μ⁻¹(c)` onto
  `μ⁻¹(Ad*_g c)`, and conjugation by `g` carries `G_c` onto `G_{Ad*_g c} = g G_c g⁻¹`. So the
  reduced spaces at `c` and at `Ad*_g c` are symplectomorphic
  (`IsEquivariantMomentMap.exists_diffeomorph_mpullback_eq_coadjointRepresentation`): the reduced
  space depends only on the coadjoint orbit of `c`.
* **Shifts by a coadjoint-fixed value.** If `ν ∈ 𝔤*` is fixed by the coadjoint action, then
  `μ + ν` is again an equivariant moment map, with the same levels shifted by `ν` and the same
  stabilizers, and the identity of `M` induces a symplectomorphism between the reduced space of `μ`
  at `c` and that of `μ + ν` at `c + ν`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.exists_diffeomorph_mpullback_eq_add_const`). For
  a coadjoint-fixed `c` and `ν = -c`, this compares reduction of `μ` at `c` with reduction of
  `μ - c` at zero.

## Main definitions

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelDiffeomorph`: the restriction of `φ` to the
  regular levels.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientDiffeomorph`: the induced
  diffeomorphism of reduced spaces.

## Main results

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_orbitRelQuotientDiffeomorph`: it pulls
  the reduced form back to the reduced form.
* `IsEquivariantMomentMap.exists_diffeomorph_mpullback_eq_of_map_smul`,
  `IsEquivariantMomentMap.exists_diffeomorph_mpullback_eq_coadjointRepresentation`,
  `IsEquivariantMomentMap.exists_diffeomorph_mpullback_eq_add_const`: the three instances above, in
  the namespace `TauCeti.SmoothTwoForm`.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* J.-P. Ortega, T. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics 222,
  Birkhäuser, 2004.
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
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

section General

variable {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {G₂ : Type*} [TopologicalSpace G₂] [ChartedSpace H₂ G₂] [Group G₂] [LieGroup I₂ ∞ G₂]
  {E₂' H₂' : Type*} [NormedAddCommGroup E₂'] [NormedSpace ℝ E₂'] [FiniteDimensional ℝ E₂']
  [TopologicalSpace H₂'] {I₂' : ModelWithCorners ℝ E₂' H₂'} [I₂'.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂' M₂] [IsManifold I₂' ∞ M₂]
  [MulAction G₂ M₂] [ContMDiffSMul I₂ I₂' ∞ G₂ M₂]
  {σ₂ : SmoothTwoForm I₂' M₂} {μ₂ : M₂ → Module.Dual ℝ (GroupLieAlgebra I₂ G₂)}
  {c₂ : Module.Dual ℝ (GroupLieAlgebra I₂ G₂)} {n₂ : ℕ}
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  (h : σ.IsEquivariantMomentMap μ) (h₂ : σ₂.IsEquivariantMomentMap μ₂)
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  (hreg₂ : ∀ x, μ₂ x = c₂ → Function.Surjective (h₂.differential x))
  (hn₂ : finrank ℝ E₂' - finrank ℝ (GroupLieAlgebra I₂ G₂) = n₂)
  (φ : M ≃ₘ⟮I', I₂'⟯ M₂) (hφ : ∀ x, μ₂ (φ x) = c₂ ↔ μ x = c)

/-! ### The levels -/

include φ hφ in
/-- **A diffeomorphism matching two regular levels restricts to a diffeomorphism of the levels.**
If `φ : M ≃ M₂` carries the level `μ⁻¹(c)` onto the level `μ₂⁻¹(c₂)`, then `z ↦ φ z` is a
diffeomorphism between them, for their regular-level atlases
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`). -/
def levelDiffeomorph :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    h.levelSubMulAction c ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), 𝓘(ℝ, Fin n₂ → ℝ)⟯ h₂.levelSubMulAction c₂ :=
  letI := h.levelSubMulActionChartedSpace c hreg hn
  letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
  { toEquiv := φ.toEquiv.subtypeEquiv fun x ↦
      h.mem_levelSubMulAction.trans ((hφ x).symm.trans h₂.mem_levelSubMulAction.symm)
    contMDiff_toFun :=
      (h₂.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff_iff_comp.2
        (φ.contMDiff.comp (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff)
    contMDiff_invFun :=
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff_iff_comp.2
        (φ.symm.contMDiff.comp (h₂.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff) }

/-- The restriction of `φ` to the levels is `φ`. -/
@[simp]
theorem coe_levelDiffeomorph_apply (z : h.levelSubMulAction c) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    (h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ z : M₂) = φ z :=
  (rfl)

/-- The inverse of the restriction of `φ` to the levels is the restriction of `φ⁻¹`. -/
@[simp]
theorem coe_levelDiffeomorph_symm_apply (z : h₂.levelSubMulAction c₂) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    ((h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ).symm z : M) = φ.symm z :=
  (rfl)

/-- The restriction of `φ` to the levels intertwines the two inclusions:
`i₂ ∘ φ_Z = φ ∘ i`. -/
theorem coe_comp_levelDiffeomorph :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    Subtype.val ∘ h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ =
      φ ∘ (Subtype.val : h.levelSubMulAction c → M) :=
  (rfl)

/-- If `φ (k • x) = ψ k • φ x` for a homomorphism `ψ : G_c →* G₂_{c₂}`, then the restriction of
`φ` to the levels is `ψ`-equivariant. -/
theorem levelDiffeomorph_smul
    (ψ : (Lie.coadjointRepresentation ℝ I G).stabilizer c →*
      (Lie.coadjointRepresentation ℝ I₂ G₂).stabilizer c₂)
    (hψ : ∀ (k : (Lie.coadjointRepresentation ℝ I G).stabilizer c) (x : M),
      φ (k • x) = ψ k • φ x)
    (k : (Lie.coadjointRepresentation ℝ I G).stabilizer c) (z : h.levelSubMulAction c) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ (k • z) =
      ψ k • h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ z :=
  Subtype.ext <| by
    simp only [coe_levelDiffeomorph_apply, SubMulAction.val_smul, hψ]

/-! ### The reduced spaces -/

section Quotient

variable [ProperSMul G M] [ProperSMul G₂ M₂]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I₂ G₂).stabilizer c₂) (h₂.levelSubMulAction c₂)]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  (d₂ : Lie.EmbeddedLieSubgroupData I₂ ((Lie.coadjointRepresentation ℝ I₂ G₂).stabilizer c₂) F₂)
  (ψ : (Lie.coadjointRepresentation ℝ I G).stabilizer c ≃*
    (Lie.coadjointRepresentation ℝ I₂ G₂).stabilizer c₂)
  (hψ : ∀ (k : (Lie.coadjointRepresentation ℝ I G).stabilizer c) (x : M), φ (k • x) = ψ k • φ x)

include φ hφ ψ hψ in
/-- **Matching data induce a diffeomorphism of reduced spaces.** If `φ : M ≃ M₂` carries the
level `μ⁻¹(c)` onto `μ₂⁻¹(c₂)` and intertwines the stabilizers along a group isomorphism
`ψ : G_c ≃* G₂_{c₂}`, then `[z] ↦ [φ z]` is a diffeomorphism from the reduced space
`μ⁻¹(c) / G_c` onto `μ₂⁻¹(c₂) / G₂_{c₂}`, for their atlases
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientChartedSpace`. Neither `ψ` nor the
Lie group structures `d` and `d₂` of the stabilizers need to be compatible. -/
def orbitRelQuotientDiffeomorph :
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h₂.orbitRelQuotientChartedSpace c₂ hreg₂ hn₂ d₂
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
        𝓘(ℝ, ProperSMul.QuotientModelSpace F₂ (Fin n₂ → ℝ))⟯
      MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I₂ G₂).stabilizer c₂)
        (h₂.levelSubMulAction c₂) :=
  letI := h.levelSubMulActionChartedSpace c hreg hn
  letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
  letI := h.orbitRelQuotientChartedSpace c hreg hn d
  letI := h₂.orbitRelQuotientChartedSpace c₂ hreg₂ hn₂ d₂
  haveI := h.isManifold_levelSubMulAction hreg hn
  haveI := h₂.isManifold_levelSubMulAction hreg₂ hn₂
  -- Smoothness of the map and of its inverse is checked after composing with the orbit
  -- projections, which are surjective submersions; there they are `π₂ ∘ φ_Z` and `π ∘ φ_Z⁻¹`.
  { toEquiv := TauCeti.MulAction.orbitRelQuotientCongr ψ
      (h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ).toEquiv
      (h.levelDiffeomorph_smul h₂ hreg hn hreg₂ hn₂ φ hφ ψ hψ)
    contMDiff_toFun :=
      ((h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff_comp_iff
        Quotient.mk_surjective le_rfl).1 <|
        ((h₂.isSubmersion_quotientMk_levelSubMulAction hreg₂ hn₂ d₂).contMDiff.comp
          (h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ).contMDiff).congr fun z ↦
            TauCeti.MulAction.orbitRelQuotientCongr_mk ψ _ _ z
    contMDiff_invFun :=
      ((h₂.isSubmersion_quotientMk_levelSubMulAction hreg₂ hn₂ d₂).contMDiff_comp_iff
        Quotient.mk_surjective le_rfl).1 <|
        ((h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff.comp
          (h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ).symm.contMDiff).congr fun z ↦
            TauCeti.MulAction.orbitRelQuotientCongr_symm_mk ψ _ _ z }

/-- The diffeomorphism of reduced spaces sends the orbit of `z` to the orbit of `φ z`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_mk (z : h.levelSubMulAction c) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h₂.orbitRelQuotientChartedSpace c₂ hreg₂ hn₂ d₂
    h.orbitRelQuotientDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ d d₂ ψ hψ
        (Quotient.mk (MulAction.orbitRel _ _) z) =
      Quotient.mk (MulAction.orbitRel _ _) (h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ z) :=
  TauCeti.MulAction.orbitRelQuotientCongr_mk ψ _ _ z

/-- The inverse of the diffeomorphism of reduced spaces sends the orbit of `z` to the orbit of
`φ⁻¹ z`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_symm_mk (z : h₂.levelSubMulAction c₂) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h₂.orbitRelQuotientChartedSpace c₂ hreg₂ hn₂ d₂
    (h.orbitRelQuotientDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ d d₂ ψ hψ).symm
        (Quotient.mk (MulAction.orbitRel _ _) z) =
      Quotient.mk (MulAction.orbitRel _ _)
        ((h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ).symm z) :=
  TauCeti.MulAction.orbitRelQuotientCongr_symm_mk ψ _ _ z

/-- The diffeomorphism of reduced spaces intertwines the two orbit projections with the
restriction of `φ` to the levels: `Φ ∘ π = π₂ ∘ φ_Z`. -/
theorem orbitRelQuotientDiffeomorph_comp_quotientMk :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h₂.orbitRelQuotientChartedSpace c₂ hreg₂ hn₂ d₂
    h.orbitRelQuotientDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ d d₂ ψ hψ ∘
        Quotient.mk (MulAction.orbitRel _ _) =
      Quotient.mk (MulAction.orbitRel _ _) ∘ h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ :=
  funext <| h.orbitRelQuotientDiffeomorph_mk h₂ hreg hn hreg₂ hn₂ φ hφ d d₂ ψ hψ

/-- **Symplectomorphisms induce symplectomorphisms of reduced spaces.** If moreover `φ^* σ₂ = σ`,
then the diffeomorphism of reduced spaces induced by `φ` pulls a reduced form `η₂` of
`μ₂⁻¹(c₂) / G₂_{c₂}`, characterized by `π₂^* η₂ = i₂^* σ₂`, back to the reduced form `η` of
`μ⁻¹(c) / G_c`, characterized by `π^* η = i^* σ`. -/
theorem mpullback_orbitRelQuotientDiffeomorph (hσ : SmoothForm.mpullback φ φ.contMDiff σ₂ = σ) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h₂.orbitRelQuotientChartedSpace c₂ hreg₂ hn₂ d₂
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h₂.isManifold_levelSubMulAction hreg₂ hn₂
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    haveI := h₂.isManifold_orbitRelQuotient hreg₂ hn₂ d₂
    ∀ (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)))
      (η₂ : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F₂ (Fin n₂ → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I₂ G₂).stabilizer c₂)
          (h₂.levelSubMulAction c₂))),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        SmoothForm.mpullback _
            (h₂.isSubmersion_quotientMk_levelSubMulAction hreg₂ hn₂ d₂).contMDiff η₂ =
          SmoothForm.mpullback Subtype.val
            (h₂.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff σ₂ →
        SmoothForm.mpullback _
            (h.orbitRelQuotientDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ d d₂ ψ hψ).contMDiff η₂ =
          η := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h₂.levelSubMulActionChartedSpace c₂ hreg₂ hn₂
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  let := h₂.orbitRelQuotientChartedSpace c₂ hreg₂ hn₂ d₂
  have := h.isManifold_levelSubMulAction hreg hn
  have := h₂.isManifold_levelSubMulAction hreg₂ hn₂
  have := h.isManifold_orbitRelQuotient hreg hn d
  have := h₂.isManifold_orbitRelQuotient hreg₂ hn₂ d₂
  intro η η₂ hη hη₂
  have hπ := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  have hi := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  have hi₂ := h₂.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂
  set φZ := h.levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ
  -- The restriction of `φ` to the levels carries `i₂^* σ₂` to `i^* σ`, as `i₂ ∘ φ_Z = φ ∘ i`.
  have hφZ : SmoothForm.mpullback φZ φZ.contMDiff
      (SmoothForm.mpullback Subtype.val hi₂.contMDiff σ₂) =
        SmoothForm.mpullback Subtype.val hi.contMDiff σ := by
    rw [SmoothForm.mpullback_mpullback_of_comp_eq φZ.contMDiff hi₂.contMDiff hi.contMDiff
      φ.contMDiff (h.coe_comp_levelDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ), hσ]
  exact SmoothForm.mpullback_eq_of_mpullback_eq hi.contMDiff hπ.contMDiff hi₂.contMDiff
    (h₂.isSubmersion_quotientMk_levelSubMulAction hreg₂ hn₂ d₂).contMDiff hη hη₂
    Quotient.mk_surjective (fun z ↦ hπ.surjective_mfderiv (by simp) z) φZ.contMDiff hφZ
    (h.orbitRelQuotientDiffeomorph h₂ hreg hn hreg₂ hn₂ φ hφ d d₂ ψ hψ).contMDiff
    (h.orbitRelQuotientDiffeomorph_comp_quotientMk h₂ hreg hn hreg₂ hn₂ φ hφ d d₂ ψ hψ)

end Quotient

end General

/-! ### Equivariant symplectomorphisms -/

section Equivariant

variable {E₂' H₂' : Type*} [NormedAddCommGroup E₂'] [NormedSpace ℝ E₂'] [FiniteDimensional ℝ E₂']
  [TopologicalSpace H₂'] {I₂' : ModelWithCorners ℝ E₂' H₂'} [I₂'.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂' M₂] [IsManifold I₂' ∞ M₂]
  [MulAction G M₂] [ContMDiffSMul I I₂' ∞ G M₂] [ProperSMul G M] [ProperSMul G M₂]
  {σ₂ : SmoothTwoForm I₂' M₂} {μ₂ : M₂ → Module.Dual ℝ (GroupLieAlgebra I G)} {n₂ : ℕ}

/-- **Equivariant symplectomorphisms induce symplectomorphisms of reduced spaces.** Let
`φ : M ≃ M₂` be a `G`-equivariant diffeomorphism with `φ^* σ₂ = σ` and `μ₂ ∘ φ = μ`. Then for every
regular value `c` at which `G_c` acts freely on both levels, some diffeomorphism of the reduced
spaces `μ⁻¹(c) / G_c ≃ μ₂⁻¹(c) / G_c`, namely `[z] ↦ [φ z]`, pulls the reduced form of `M₂` back
to the reduced form of `M`. -/
theorem exists_diffeomorph_mpullback_eq_of_map_smul (h : σ.IsEquivariantMomentMap μ)
    (h₂ : σ₂.IsEquivariantMomentMap μ₂)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
    (hreg₂ : ∀ x, μ₂ x = c → Function.Surjective (h₂.differential x))
    (hn₂ : finrank ℝ E₂' - finrank ℝ (GroupLieAlgebra I G) = n₂)
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h₂.levelSubMulAction c)]
    (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
    (φ : M ≃ₘ⟮I', I₂'⟯ M₂) (hφG : ∀ (g : G) (x : M), φ (g • x) = g • φ x)
    (hμ : ∀ x, μ₂ (φ x) = μ x) (hσ : SmoothForm.mpullback φ φ.contMDiff σ₂ = σ) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h₂.levelSubMulActionChartedSpace c hreg₂ hn₂
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h₂.orbitRelQuotientChartedSpace c hreg₂ hn₂ d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h₂.isManifold_levelSubMulAction hreg₂ hn₂
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    haveI := h₂.isManifold_orbitRelQuotient hreg₂ hn₂ d
    ∀ (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)))
      (η₂ : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n₂ → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h₂.levelSubMulAction c))),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        SmoothForm.mpullback _
            (h₂.isSubmersion_quotientMk_levelSubMulAction hreg₂ hn₂ d).contMDiff η₂ =
          SmoothForm.mpullback Subtype.val
            (h₂.isSmoothEmbedding_coe_levelSubMulAction hreg₂ hn₂).contMDiff σ₂ →
        ∃ Φ : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
            (h.levelSubMulAction c) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
            𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n₂ → ℝ))⟯
            MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
              (h₂.levelSubMulAction c),
          SmoothForm.mpullback Φ Φ.contMDiff η₂ = η := fun η η₂ hη hη₂ ↦
  ⟨h.orbitRelQuotientDiffeomorph h₂ hreg hn hreg₂ hn₂ φ (fun x ↦ by rw [hμ]) d d
      (MulEquiv.refl _) (fun k x ↦ by simp [Subgroup.smul_def, hφG]),
    h.mpullback_orbitRelQuotientDiffeomorph h₂ hreg hn hreg₂ hn₂ φ _ d d _ _ hσ η η₂ hη hη₂⟩

end Equivariant

/-! ### Points of one coadjoint orbit -/

section Coadjoint

variable [ProperSMul G M] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [FiniteDimensional ℝ F']

/-- **The reduced space depends only on the coadjoint orbit.** For `g ∈ G`, the action
`x ↦ g • x` carries the level `μ⁻¹(c)` onto `μ⁻¹(Ad*_g c)` and intertwines `G_c` with
`G_{Ad*_g c} = g G_c g⁻¹` along conjugation by `g`. If `G` acts by symplectomorphisms, the induced
diffeomorphism of reduced spaces `μ⁻¹(c) / G_c ≃ μ⁻¹(Ad*_g c) / G_{Ad*_g c}`, `[z] ↦ [g • z]`, pulls
the reduced form at `Ad*_g c` back to the reduced form at `c`. -/
theorem exists_diffeomorph_mpullback_eq_coadjointRepresentation (h : σ.IsEquivariantMomentMap μ)
    (g : G)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
    [IsCancelSMul
      ((Lie.coadjointRepresentation ℝ I G).stabilizer (Lie.coadjointRepresentation ℝ I G g c))
      (h.levelSubMulAction (Lie.coadjointRepresentation ℝ I G g c))]
    (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
    (d' : Lie.EmbeddedLieSubgroupData I
      ((Lie.coadjointRepresentation ℝ I G).stabilizer (Lie.coadjointRepresentation ℝ I G g c)) F')
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    -- `Ad*_g c` is a regular value, as `c` is (`differential_surjective_of_apply_eq`).
    let hreg' : ∀ x, μ x = Lie.coadjointRepresentation ℝ I G g c →
        Function.Surjective (h.differential x) := fun _ hx ↦
      h.differential_surjective_of_apply_eq hreg hx
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.levelSubMulActionChartedSpace (Lie.coadjointRepresentation ℝ I G g c) hreg' hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h.orbitRelQuotientChartedSpace (Lie.coadjointRepresentation ℝ I G g c) hreg' hn d'
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_levelSubMulAction hreg' hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    haveI := h.isManifold_orbitRelQuotient hreg' hn d'
    ∀ (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)))
      (η' : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F' (Fin n → ℝ))
        (MulAction.orbitRel.Quotient
          ((Lie.coadjointRepresentation ℝ I G).stabilizer (Lie.coadjointRepresentation ℝ I G g c))
          (h.levelSubMulAction (Lie.coadjointRepresentation ℝ I G g c)))),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        SmoothForm.mpullback _
            (h.isSubmersion_quotientMk_levelSubMulAction hreg' hn d').contMDiff η' =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg' hn).contMDiff σ →
        ∃ Φ : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
            (h.levelSubMulAction c) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
            𝓘(ℝ, ProperSMul.QuotientModelSpace F' (Fin n → ℝ))⟯
            MulAction.orbitRel.Quotient
              ((Lie.coadjointRepresentation ℝ I G).stabilizer
                (Lie.coadjointRepresentation ℝ I G g c))
              (h.levelSubMulAction (Lie.coadjointRepresentation ℝ I G g c)),
          SmoothForm.mpullback Φ Φ.contMDiff η' = η := by
  intro hreg' η η' hη hη'
  let ψ : (Lie.coadjointRepresentation ℝ I G).stabilizer c ≃*
      (Lie.coadjointRepresentation ℝ I G).stabilizer (Lie.coadjointRepresentation ℝ I G g c) :=
    ((MulAut.conj g).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((Lie.coadjointRepresentation ℝ I G).stabilizer_conj g c).symm)
  -- The action of `g` carries `μ⁻¹(c)` onto `μ⁻¹(Ad*_g c)`, as `Ad*_g` is injective.
  have hφ : ∀ x, μ (Diffeomorph.smul I I' ∞ g x) = Lie.coadjointRepresentation ℝ I G g c ↔
      μ x = c := fun x ↦ by
    rw [Diffeomorph.smul_apply, h.apply_smul]
    refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ rfl⟩
    simpa only [Representation.inv_self_apply] using
      congrArg (Lie.coadjointRepresentation ℝ I G g⁻¹) hx
  have hψ : ∀ (k : (Lie.coadjointRepresentation ℝ I G).stabilizer c) (x : M),
      Diffeomorph.smul I I' ∞ g (k • x) = ψ k • Diffeomorph.smul I I' ∞ g x := fun k x ↦ by
    simp [ψ, Subgroup.smul_def, smul_smul]
  -- `mpullback` takes the smoothness proof as a dependent argument, so `hg` cannot be rewritten
  -- into this form; it is accepted as is because `⇑(Diffeomorph.smul I I' ∞ g)` unfolds to
  -- `fun x ↦ g • x` and any two smoothness proofs are equal.
  have hσ : SmoothForm.mpullback _ (Diffeomorph.smul I I' ∞ g).contMDiff σ = σ := hg
  exact ⟨h.orbitRelQuotientDiffeomorph h hreg hn hreg' hn _ hφ d d' ψ hψ,
    h.mpullback_orbitRelQuotientDiffeomorph h hreg hn hreg' hn _ hφ d d' ψ hψ hσ η η' hη hη'⟩

end Coadjoint

/-! ### Shifts by a coadjoint-fixed value -/

section Shift

variable [ProperSMul G M] {ν c' : Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **Reduction commutes with coadjoint-fixed shifts.** If `ν ∈ 𝔤*` is fixed by the coadjoint
action, then `μ + ν` is an equivariant moment map whose level at `c' = c + ν` is the level of `μ`
at `c`, with the same stabilizer, and the identity of `M` induces a diffeomorphism of reduced spaces
`μ⁻¹(c) / G_c ≃ (μ + ν)⁻¹(c') / G_{c'}` pulling the reduced form of `μ + ν` back to that of `μ`.
For a coadjoint-fixed `c`, taking `ν = -c` and `c' = 0` compares reduction of `μ` at `c` with
reduction of `μ - c` at zero. -/
theorem exists_diffeomorph_mpullback_eq_add_const (h : σ.IsEquivariantMomentMap μ)
    (hν : ∀ g : G, Lie.coadjointRepresentation ℝ I G g ν = ν) (hc' : c + ν = c')
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c')
      ((h.add_const hν).levelSubMulAction c')]
    (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
    (d' : Lie.EmbeddedLieSubgroupData I
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c') F) :
    -- `c'` is a regular value of `μ + ν`, as `c` is one of `μ`.
    let hreg' : ∀ x, μ x + ν = c' → Function.Surjective ((h.add_const hν).differential x) :=
      fun x hx ↦ (h.toIsMomentMap.differential_eq_differential (h.add_const hν).toIsMomentMap) ▸
        hreg x (add_right_cancel (hx.trans hc'.symm))
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := (h.add_const hν).levelSubMulActionChartedSpace c' hreg' hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := (h.add_const hν).orbitRelQuotientChartedSpace c' hreg' hn d'
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := (h.add_const hν).isManifold_levelSubMulAction hreg' hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    haveI := (h.add_const hν).isManifold_orbitRelQuotient hreg' hn d'
    ∀ (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)))
      (η' : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c')
          ((h.add_const hν).levelSubMulAction c'))),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        SmoothForm.mpullback _
            ((h.add_const hν).isSubmersion_quotientMk_levelSubMulAction hreg' hn d').contMDiff η' =
          SmoothForm.mpullback Subtype.val
            ((h.add_const hν).isSmoothEmbedding_coe_levelSubMulAction hreg' hn).contMDiff σ →
        ∃ Φ : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
            (h.levelSubMulAction c) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
            𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))⟯
            MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c')
              ((h.add_const hν).levelSubMulAction c'),
          SmoothForm.mpullback Φ Φ.contMDiff η' = η := by
  intro hreg' η η' hη hη'
  -- `Ad*_g (c + ν) = Ad*_g c + ν`, so `c' = c + ν` and `c` have the same stabilizer.
  have hstab : (Lie.coadjointRepresentation ℝ I G).stabilizer c =
      (Lie.coadjointRepresentation ℝ I G).stabilizer c' := by
    ext g
    rw [← hc', Representation.mem_stabilizer, Representation.mem_stabilizer, map_add, hν,
      add_left_inj]
  have hψ : ∀ (k : (Lie.coadjointRepresentation ℝ I G).stabilizer c) (x : M),
      Diffeomorph.refl I' M ∞ (k • x) =
        MulEquiv.subgroupCongr hstab k • Diffeomorph.refl I' M ∞ x :=
    fun k x ↦ by
      simp only [Diffeomorph.coe_refl, id, Subgroup.smul_def, MulEquiv.subgroupCongr_apply]
  have hσ : SmoothForm.mpullback _ (Diffeomorph.refl I' M ∞).contMDiff σ = σ := by
    simp only [Diffeomorph.coe_refl, SmoothForm.mpullback_id, LinearMap.id_apply]
  exact ⟨h.orbitRelQuotientDiffeomorph (h.add_const hν) hreg hn hreg' hn _
      (fun x ↦ hc' ▸ add_left_inj ν) d d' (MulEquiv.subgroupCongr hstab) hψ,
    h.mpullback_orbitRelQuotientDiffeomorph (h.add_const hν) hreg hn hreg' hn _ _ d d' _ hψ hσ η η'
      hη hη'⟩

end Shift

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
