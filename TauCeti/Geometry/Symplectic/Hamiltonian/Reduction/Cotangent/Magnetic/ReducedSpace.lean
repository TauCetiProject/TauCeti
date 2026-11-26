/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Twisted
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.Magnetic.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality

/-!
# The magnetic cotangent reduced space at a coadjoint-fixed value

Let a Lie group `G` act smoothly, freely and properly on a manifold `Q`, with orbit projection
`ρ : Q → Q ⧸ G` and cotangent moment map `⟨μ(q, p), ξ⟩ = p(ξ_Q(q))`
(`TauCeti.CotangentBundle.momentMap`). Let `α` be a `G`-invariant one-form on `Q` pairing every
fundamental vector field with the constant `-ν`, `α(ξ_Q) = -ν(ξ)`, as `α = ⟨ν, A⟩` does for a
principal connection `A` with `A(ξ_Q) = -ξ` and a coadjoint-fixed value `ν`. On a nonempty `Q` such
an `α` forces `ν` to be coadjoint-fixed, so the coadjoint stabilizer `G_ν` is all of `G`.

This file proves that the Marsden–Weinstein–Meyer reduced space of `T*Q` at `ν`, with the atlas of
the Marsden–Weinstein–Meyer theorem, is the cotangent bundle of the orbit space with a magnetic
term,

`T*Q //_ν G = μ⁻¹(ν) / G_ν ≅ (T*(Q ⧸ G), ω + π^* β)`,

where `β` is the closed two-form on `Q ⧸ G` with `ρ^* β = dα` (for `α = ⟨ν, A⟩`, the `ν`-component
of the curvature of `A`), and `ω + π^* β` is the twisted symplectic form
`TauCeti.CotangentBundle.twistedSymplecticForm β`.

* **The map.** The magnetic reduction map `Φ` (`TauCeti.CotangentBundle.magneticReductionMap`)
  sends a covector `p` at `q` in `μ⁻¹(ν)` to the unique covector `p'` at `[q]` with
  `p + α_q = p' ∘ dρ_q`. Its fibres on `μ⁻¹(ν)` are the `G`-orbits, which are the `G_ν`-orbits, and
  it is onto, so it descends to a bijection from the reduced space onto `T*(Q ⧸ G)`.
* **The forms.** Along `μ⁻¹(ν)` the magnetic reduction map pulls `ω + π^* β` back to the canonical
  symplectic form of `T*Q`. So the descended map pulls `ω + π^* β` back to the reduced symplectic
  form (`TauCeti.CotangentBundle.mpullback_magneticReducedSpaceDiffeomorph_twistedSymplecticForm`).
* **A diffeomorphism.** Since the reduced form is nondegenerate and both sides have dimension
  `2 (dim Q - dim G)` (`TauCeti.CotangentBundle.finrank_quotientModelSpace_level`), the recognition
  of reduced spaces (`TauCeti.SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq`) makes the
  descended map a diffeomorphism (`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph`).
* **Change of connection.** If `α'` is a second such one-form, with `α' - α = ρ^* γ`, the
  diffeomorphism of `α'` is that of `α` followed by the fibre translation of `T*(Q ⧸ G)` by `γ`
  (`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph_eq_vectorBundleTranslateDiffeomorph`).
  The magnetic term changes from `β` to `β + dγ`, and the translation by `γ` pulls
  `ω + π^* (β + dγ)` back to `ω + π^* β`
  (`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_twistedSymplecticForm`).
* **The zero value.** For `α = 0` and `ν = 0` this is cotangent reduction at zero, where
  `β = 0` and the twisted form is the canonical one; the diffeomorphism
  `TauCeti.CotangentBundle.zeroReducedSpaceDiffeomorph` of
  `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.ReducedSpace` is defined this way.

As for the reduced space at zero, the statements take as arguments the data `h`, `hreg`, `n` and
`d` from which the Marsden–Weinstein–Meyer theorem builds the atlas of the reduced space; `h` and
`hreg` hold by `TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap` and
`TauCeti.CotangentBundle.differential_momentMap_surjective`.

## Main definitions

* `TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph`: the diffeomorphism
  `μ⁻¹(ν) / G_ν ≅ T*(Q ⧸ G)` induced by the magnetic reduction map.

## Main results

* `TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph_mk`: the diffeomorphism sends the orbit
  of a covector `p` at `q` in `μ⁻¹(ν)` to its magnetic reduced covector.
* `TauCeti.CotangentBundle.mpullback_magneticReducedSpaceDiffeomorph_twistedSymplecticForm`:
  **magnetic cotangent reduction**, the diffeomorphism pulls `ω + π^* β` back to the reduced
  symplectic form.
* `TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph_eq_vectorBundleTranslateDiffeomorph`:
  changing the one-form changes the diffeomorphism by a fibre translation.

## References

* Jerrold E. Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor S. Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, §2.2
  (cotangent bundle reduction at a value fixed by the coadjoint action, the embedding version
  with its magnetic term).
* Juan-Pablo Ortega and Tudor S. Ratiu, *Cotangent bundle reduction*, in *Encyclopedia of
  Mathematical Physics*, Elsevier, 2006 (reduction at zero and the embedding version with its
  magnetic term).
-/

public section

noncomputable section

open Bundle Function Manifold Module
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {Q : Type*}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [MulAction G Q]
  [ContMDiffSMul IG I ∞ G Q] [ContMDiffConstSMul I ∞ G Q] [IsCancelSMul G Q]
  {h : (symplecticForm I Q).IsEquivariantMomentMap (momentMap IG G)}
  {α : SmoothForm I Q ℝ 1} {ν : Module.Dual ℝ (GroupLieAlgebra IG G)}

/-! ### The reduced space at a coadjoint-fixed value -/

section ReducedSpace

variable [ProperSMul G Q] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ}
  {hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α}
  {hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ}

variable (hreg : ∀ z, momentMap IG G z = ν → Surjective (h.differential z))
  (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
  (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν) F)

include hαinv hα in
/-- The magnetic reduction map on the level `μ⁻¹(ν)` descends to a diffeomorphism from the reduced
space onto `T*(Q ⧸ G)`, by the recognition of reduced spaces
`TauCeti.SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq`: its fibres are the `G`-orbits,
which are the `G_ν`-orbits; it is onto; it pulls the twisted form `ω + π^* β`, for `ρ^* β = dα`,
back to the restriction of the canonical form of `T*Q`; and both sides have dimension
`2 (dim Q - dim G)`, as `ν` is coadjoint-fixed. On an empty `Q` both sides are empty. -/
private theorem exists_diffeomorph_quotientMk_eq_magneticReductionMap :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    ∃ Φ : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν)
          (h.levelSubMulAction ν) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
          𝓘(ℝ, ProperSMul.QuotientModelSpace EG E).prod
            𝓘(ℝ, ProperSMul.QuotientModelSpace EG E →L[ℝ] ℝ)⟯
        CotangentBundle 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q),
      ∀ z : h.levelSubMulAction ν, Φ (Quotient.mk _ z) =
        magneticReductionMap I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
          (Quotient.mk (MulAction.orbitRel G Q)) α (z : CotangentBundle I Q) := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.levelSubMulActionChartedSpace ν hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · have : IsEmpty (MulAction.orbitRel.Quotient
        ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν) (h.levelSubMulAction ν)) :=
      ⟨fun x ↦ Quotient.inductionOn x fun z ↦ isEmptyElim (z : CotangentBundle I Q).proj⟩
    have : IsEmpty (CotangentBundle 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
        (MulAction.orbitRel.Quotient G Q)) :=
      ⟨fun w ↦ Quotient.inductionOn w.proj isEmptyElim⟩
    exact ⟨{ Equiv.equivOfIsEmpty _ _ with
      contMDiff_toFun := isEmptyElim
      contMDiff_invFun := isEmptyElim }, fun z ↦ isEmptyElim (z : CotangentBundle I Q).proj⟩
  -- The magnetic term `β` with `ρ^* β = dα`, and the reduced symplectic form `η`.
  obtain ⟨β, hβ, -⟩ := ProperSMul.existsUnique_mpullback_quotientMk_eq_mextDerivₗ hαinv
    (c := -ν) hα
  obtain ⟨η, ⟨hηs, hη⟩, -⟩ := h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg
    hn d isSymplectic_symplecticForm mpullback_smul_symplecticForm
  -- The invariant one-form `α` makes `ν` coadjoint-fixed: every one-parameter subgroup fixes `ν`,
  -- so every element of `𝔤` annihilates it, which fixes the dimension.
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have hν : lieAnnihilator ℝ (GroupLieAlgebra IG G) ν = ⊤ :=
    eq_top_iff.2 fun ξ _ ↦ Lie.mulInvariantExp_smul_mem_stabilizer_coadjointRepresentation_iff.1
      fun _ ↦ Representation.mem_stabilizer.2 <| neg_injective <| by
        rw [← map_neg]; exact coadjointRepresentation_apply_eq_self_of_forall_eval_eq hαinv hα _
  have hi := (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
  refine (SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d) Quotient.mk_surjective
    hηs.isNondegenerate _ (fun w ↦ ?_) (fun z z' ↦ ?_)
    ((finrank_quotientModelSpace_level hν hn d).trans
      ProperSMul.finrank_quotientModelSpace_prod_dual.symm)
    ((ProperSMul.mpullback_magneticReductionMap_comp_symplecticForm_add_mpullback_quotientMk hα hβ
      hi fun z ↦ h.mem_levelSubMulAction.1 z.property).trans hη.symm)).imp
    fun Φ hΦ z ↦ congrFun hΦ.1 z
  · obtain ⟨z, hz, rfl⟩ := ProperSMul.exists_momentMap_eq_and_magneticReductionMap_eq_quotientMk
      hα w
    exact ⟨⟨z, h.mem_levelSubMulAction.2 hz⟩, rfl⟩
  · rw [comp_apply, comp_apply,
      ProperSMul.magneticReductionMap_eq_magneticReductionMap_iff_quotientMk hαinv hα
        (h.mem_levelSubMulAction.1 z.property) (h.mem_levelSubMulAction.1 z'.property),
      Quotient.eq, h.orbitRel_levelSubMulAction_iff, MulAction.orbitRel_apply,
      MulAction.mem_orbit_iff]
    exact ⟨fun ⟨g, hg⟩ ↦ ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩,
      fun ⟨g, hg⟩ ↦ ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩⟩

variable (h hαinv hα) in
/-- **Magnetic cotangent bundle reduction.** For a free and proper smooth action of a Lie group `G`
on `Q` and a `G`-invariant one-form `α` on `Q` pairing every fundamental vector field with `-ν`,
the reduced space `T*Q //_ν G = μ⁻¹(ν) / G_ν` of the cotangent bundle, with the atlas of the
Marsden–Weinstein–Meyer theorem, is diffeomorphic to the cotangent bundle `T*(Q ⧸ G)` of the orbit
space. The diffeomorphism sends the orbit of a covector `p` at `q` in `μ⁻¹(ν)` to the unique
covector `p'` at `[q]` with `p + α_q = p' ∘ dρ_q`
(`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph_mk`), and it carries the reduced
symplectic form to the twisted form `ω + π^* β` of `T*(Q ⧸ G)`, where `ρ^* β = dα`
(`TauCeti.CotangentBundle.mpullback_magneticReducedSpaceDiffeomorph_twistedSymplecticForm`).

The hypotheses `h` and `hreg` are those of the atlas: they hold by
`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap` and
`TauCeti.CotangentBundle.differential_momentMap_surjective`. -/
def magneticReducedSpaceDiffeomorph :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν)
        (h.levelSubMulAction ν) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
        𝓘(ℝ, ProperSMul.QuotientModelSpace EG E).prod
          𝓘(ℝ, ProperSMul.QuotientModelSpace EG E →L[ℝ] ℝ)⟯
      CotangentBundle 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) :=
  (exists_diffeomorph_quotientMk_eq_magneticReductionMap (hαinv := hαinv) (hα := hα) hreg hn
    d).choose

/-- **The diffeomorphism of magnetic cotangent reduction sends the orbit of a covector in `μ⁻¹(ν)`
to its magnetic reduced covector**: the unique covector `p'` at `[q]` with `p + α_q = p' ∘ dρ_q`. -/
@[simp]
theorem magneticReducedSpaceDiffeomorph_mk (z : h.levelSubMulAction ν) :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d (Quotient.mk _ z) =
      magneticReductionMap I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
        (Quotient.mk (MulAction.orbitRel G Q)) α (z : CotangentBundle I Q) :=
  (exists_diffeomorph_quotientMk_eq_magneticReductionMap (hαinv := hαinv) (hα := hα) hreg hn
    d).choose_spec z

/-- **Magnetic cotangent bundle reduction: the symplectic forms.** Let `β` be the two-form on
`Q ⧸ G` with `ρ^* β = dα`, which exists and is closed
(`ProperSMul.existsUnique_mpullback_quotientMk_eq_mextDerivₗ`,
`ProperSMul.isClosed_of_mpullback_quotientMk_eq_mextDerivₗ`). The diffeomorphism
`μ⁻¹(ν) / G_ν ≅ T*(Q ⧸ G)` pulls the twisted form `ω + π^* β` of `T*(Q ⧸ G)` back to the reduced
symplectic form `η` of the Marsden–Weinstein–Meyer theorem, the form on the reduced space with
`π^* η = i^* ω` for the orbit projection `π` and the inclusion `i` of the level into `T*Q`
(`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback` in
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`). So the diffeomorphism is a symplectomorphism
`(T*Q //_ν G, ω_red) ≅ (T*(Q ⧸ G), ω + π^* β)`. -/
theorem mpullback_magneticReducedSpaceDiffeomorph_twistedSymplecticForm :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.levelSubMulActionChartedSpace ν hreg hn
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ {β : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
        (MulAction.orbitRel.Quotient G Q)},
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q))
          (ProperSMul.contMDiff_quotientMk (I := IG) (G := G) (I' := I) (M := Q)) β =
        mextDerivₗ I 1 α →
      ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
          (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν)
            (h.levelSubMulAction ν)),
        SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
            SmoothForm.mpullback Subtype.val
              (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (symplecticForm I Q) →
          SmoothForm.mpullback (magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d)
              (magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d).contMDiff
              (twistedSymplecticForm β) = η := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.levelSubMulActionChartedSpace ν hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  have hp := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  intro β hβ η hη
  -- Pulling back along the orbit projection `π` is injective, and the diffeomorphism composed with
  -- `π` is the magnetic reduction map on the level.
  refine SmoothForm.mpullback_injective_of_surjective hp.contMDiff Quotient.mk_surjective
    (hp.surjective_mfderiv (by simp)) (((SmoothForm.mpullback_mpullback _ _ _
      (magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d).contMDiff _).trans ?_).trans hη.symm)
  rw [twistedSymplecticForm_def]
  convert ProperSMul.mpullback_magneticReductionMap_comp_symplecticForm_add_mpullback_quotientMk
    hα hβ (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    fun z ↦ h.mem_levelSubMulAction.1 z.property using 3
  exact funext (magneticReducedSpaceDiffeomorph_mk hreg hn d)

/-- **Magnetic cotangent bundle reduction: change of connection.** Let `α'` be a second
`G`-invariant one-form pairing every fundamental vector field with `-ν`, and `γ` the one-form on
`Q ⧸ G` with `ρ^* γ = α' - α`, which exists and is unique
(`ProperSMul.existsUnique_mpullback_quotientMk_eq_sub`). The diffeomorphism
`μ⁻¹(ν) / G_ν ≅ T*(Q ⧸ G)` of `α'` is that of `α` followed by the fibre translation of
`T*(Q ⧸ G)` by `γ`. -/
theorem magneticReducedSpaceDiffeomorph_eq_vectorBundleTranslateDiffeomorph
    {α' : SmoothForm I Q ℝ 1}
    {hα'inv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α' = α'}
    {hα' : ∀ x ξ, α'.val x ![fundamentalVectorField I ξ x] = -ν ξ} :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    ∀ {γ : SmoothForm 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
        (MulAction.orbitRel.Quotient G Q) ℝ 1},
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q))
          (ProperSMul.contMDiff_quotientMk (I := IG) (G := G) (I' := I) (M := Q)) γ = α' - α →
        ∀ x, magneticReducedSpaceDiffeomorph h hα'inv hα' hreg hn d x =
          vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv γ)
            (SmoothForm.degreeOneEquiv γ).contMDiff
            (magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d x) := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  intro γ hγ x
  induction x using Quotient.inductionOn with | h z => ?_
  rw [magneticReducedSpaceDiffeomorph_mk, magneticReducedSpaceDiffeomorph_mk]
  exact ProperSMul.magneticReductionMap_eq_vectorBundleTranslateDiffeomorph_quotientMk hα
    (h.mem_levelSubMulAction.1 z.property) hγ

end ReducedSpace

end TauCeti.CotangentBundle
