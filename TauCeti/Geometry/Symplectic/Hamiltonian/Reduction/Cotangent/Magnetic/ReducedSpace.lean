/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Twisted
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.Magnetic.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.ReducedSpace

import TauCeti.Geometry.Lie.Subgroup.Differential
import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent

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
* **A diffeomorphism.** The twisted form is nondegenerate for every `β`
  (`TauCeti.CotangentBundle.isNondegenerate_twistedSymplecticForm`), so the descended map has
  injective differential; both sides have dimension `2 (dim Q - dim G)`
  (`TauCeti.CotangentBundle.finrank_quotientModelSpace_level`), so it is a local diffeomorphism,
  and being bijective it is a diffeomorphism
  (`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph`).
* **Change of connection.** If `α'` is a second such one-form, with `α' - α = ρ^* γ`, the
  diffeomorphism of `α'` is that of `α` followed by the fibre translation of `T*(Q ⧸ G)` by `γ`
  (`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph_eq_vectorBundleTranslateDiffeomorph`).
  The magnetic term changes from `β` to `β + dγ`, and the translation by `γ` pulls
  `ω + π^* (β + dγ)` back to `ω + π^* β`
  (`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_twistedSymplecticForm`).
* **The zero value.** For `α = 0` and `ν = 0` the diffeomorphism is that of cotangent reduction at
  zero (`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph_zero`).

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
* `TauCeti.CotangentBundle.finrank_quotientModelSpace_level`: the reduced space at a
  coadjoint-fixed value has dimension `2 (dim Q - dim G)`.
* `TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph_zero`: at `α = 0` and `ν = 0` it is the
  diffeomorphism of cotangent reduction at zero.

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

/-! ### The dimension of the reduced space -/

section Dimension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}

omit [I.Boundaryless] [IsManifold I ∞ Q] [MulAction G Q] [ContMDiffSMul IG I ∞ G Q]
  [ContMDiffConstSMul I ∞ G Q] [IsCancelSMul G Q] in
/-- **The dimension of the reduced space at an infinitesimally coadjoint-fixed value.** If every
element of `𝔤` annihilates `ν`, `ν ⁅ξ, ·⁆ = 0`, as for a coadjoint-fixed `ν`, the model space
`ℝ^(n - dim G_ν)` of the reduced space `μ⁻¹(ν) / G_ν` of `T*Q`, where `n = 2 dim Q - dim G` is the
dimension of the level `μ⁻¹(ν)` and `G_ν` carries the Lie group structure `d`, has dimension
`2 (dim Q - dim G)`, that of `T*(Q ⧸ G)`: the coadjoint stabilizer of `ν` has the dimension of `G`.
-/
theorem finrank_quotientModelSpace_level
    (hν : lieAnnihilator ℝ (GroupLieAlgebra IG G) ν = ⊤)
    (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
    (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν) F) :
    finrank ℝ (ProperSMul.QuotientModelSpace F (Fin n → ℝ)) = 2 * (finrank ℝ E - finrank ℝ EG) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have hF : finrank ℝ F = finrank ℝ EG := by
    rw [d.finrank_eq_finrank_lieSubalgebraOfSubgroup,
      Lie.finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation
        BoundarylessManifold.isInteriorPoint, hν]
    exact LieSubalgebra.topEquiv.toLinearEquiv.finrank_eq
  -- The Lie algebra `GroupLieAlgebra IG G` is by definition the tangent space `EG` at `1`.
  have hG : finrank ℝ (GroupLieAlgebra IG G) = finrank ℝ EG := rfl
  rw [ProperSMul.finrank_quotientModelSpace, Module.finrank_fin_fun, hF, ← hn, finrank_prod,
    ContinuousLinearMap.dual_finrank_eq, hG]
  omega

end Dimension

/-! ### The reduced space at a coadjoint-fixed value -/

section ReducedSpace

variable [ProperSMul G Q] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ}

omit [I.Boundaryless] [IsCancelSMul G Q] [ProperSMul G Q] in
/-- The coadjoint stabilizer of `ν` acts on the level `μ⁻¹(ν)` through its inclusion into `G`. This
holds by definition; `SubMulAction.val_smul` does not apply, since instance search would read the
right-hand side with the cotangent lift of the restricted action on `Q`, a different instance. -/
private theorem coe_stabilizer_smul_levelSubMulAction
    (k : (Lie.coadjointRepresentation ℝ IG G).stabilizer ν) (z : h.levelSubMulAction ν) :
    ((k • z : h.levelSubMulAction ν) : CotangentBundle I Q) = (k : G) • (z : CotangentBundle I Q) :=
  rfl

variable (h) in
/-- The magnetic reduction map, descended to the reduced space at `ν`. -/
private def magneticReducedSpaceMap
    (hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν)
        (h.levelSubMulAction ν) →
      CotangentBundle 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  Quotient.lift (fun z ↦ magneticReductionMap I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
      (Quotient.mk (MulAction.orbitRel G Q)) α (z : CotangentBundle I Q)) fun z z' hzz' ↦ by
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hzz')
    refine (ProperSMul.magneticReductionMap_eq_magneticReductionMap_iff_quotientMk hαinv hα
      (h.mem_levelSubMulAction.1 z.property) (h.mem_levelSubMulAction.1 z'.property)).2
      ⟨(k : G)⁻¹, ?_⟩
    rw [← hk, coe_stabilizer_smul_levelSubMulAction, inv_smul_smul]

variable {hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α}
  {hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ}

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ E] [I.Boundaryless] [IsCancelSMul G Q]
  [ProperSMul G Q] in
include hαinv hα in
/-- On a nonempty `Q`, a `G`-invariant one-form pairing every fundamental vector field with `-ν`
forces `ν` to be coadjoint-fixed. -/
private theorem coadjointRepresentation_apply_eq_self [Nonempty Q] (g : G) :
    Lie.coadjointRepresentation ℝ IG G g ν = ν := by
  refine neg_injective ?_
  rw [← map_neg]
  exact coadjointRepresentation_apply_eq_self_of_forall_eval_eq hαinv hα g

private theorem magneticReducedSpaceMap_mk (z : h.levelSubMulAction ν) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    magneticReducedSpaceMap h hαinv hα (Quotient.mk _ z) =
      magneticReductionMap I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
        (Quotient.mk (MulAction.orbitRel G Q)) α (z : CotangentBundle I Q) :=
  (rfl)

/-- The descended magnetic reduction map is a bijection: its fibres on the level are the
`G`-orbits, which are the `G_ν`-orbits as `ν` is coadjoint-fixed, and it is onto. -/
private theorem bijective_magneticReducedSpaceMap :
    Bijective (magneticReducedSpaceMap h hαinv hα) := by
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  refine ⟨fun x x' hxx' ↦ ?_, fun w ↦ ?_⟩
  · induction x using Quotient.inductionOn with | h z => ?_
    induction x' using Quotient.inductionOn with | h z' => ?_
    rw [magneticReducedSpaceMap_mk, magneticReducedSpaceMap_mk] at hxx'
    obtain ⟨g, hg⟩ := (ProperSMul.magneticReductionMap_eq_magneticReductionMap_iff_quotientMk
      hαinv hα (h.mem_levelSubMulAction.1 z.property) (h.mem_levelSubMulAction.1 z'.property)).1
      hxx'
    -- The invariant one-form `α` pairs the fundamental vector fields with `-ν`, so `ν` is
    -- coadjoint-fixed and `g` lies in its coadjoint stabilizer.
    have : Nonempty Q := ⟨(z : CotangentBundle I Q).proj⟩
    have hg0 : g ∈ (Lie.coadjointRepresentation ℝ IG G).stabilizer ν :=
      Representation.mem_stabilizer.2 (coadjointRepresentation_apply_eq_self (hαinv := hαinv)
        (hα := hα) g)
    refine Quotient.sound (MulAction.orbitRel_apply.2
      (MulAction.mem_orbit_iff.2 ⟨(⟨g, hg0⟩ : _)⁻¹, Subtype.ext ?_⟩))
    rw [coe_stabilizer_smul_levelSubMulAction, Subgroup.coe_inv, Subgroup.coe_mk, ← hg,
      inv_smul_smul]
  · obtain ⟨z, hz, rfl⟩ := ProperSMul.exists_momentMap_eq_and_magneticReductionMap_eq_quotientMk
      hα w
    exact ⟨Quotient.mk _ ⟨z, h.mem_levelSubMulAction.2 hz⟩, rfl⟩

variable (hreg : ∀ z, momentMap IG G z = ν → Surjective (h.differential z))
  (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
  (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν) F)

/-- The descended magnetic reduction map is smooth, since the orbit projection onto the reduced
space is a surjective submersion and the magnetic reduction map is smooth on the embedded level. -/
private theorem contMDiff_magneticReducedSpaceMap :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
      (𝓘(ℝ, ProperSMul.QuotientModelSpace EG E).prod
        𝓘(ℝ, ProperSMul.QuotientModelSpace EG E →L[ℝ] ℝ)) ∞
      (magneticReducedSpaceMap h hαinv hα) := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.levelSubMulActionChartedSpace ν hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  refine ((h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff_comp_iff
    Quotient.mk_surjective le_rfl).1 ?_
  exact contMDiff_magneticReductionMap_comp ProperSMul.isSubmersion_quotientMk
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    (fun z ↦ (momentMap_eq_iff_of_ker_eq (ProperSMul.ker_mfderiv_quotientMk _) hα).1
      (h.mem_levelSubMulAction.1 z.property)) le_rfl

/-- Along the orbit projection, the descended magnetic reduction map pulls the twisted form
`ω + π^* β` of `T*(Q ⧸ G)`, for `ρ^* β = dα`, back to the restriction of the canonical symplectic
form of `T*Q` to the level. -/
private theorem mpullback_quotientMk_mpullback_magneticReducedSpaceMap_twistedSymplecticForm :
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
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
          (SmoothForm.mpullback (magneticReducedSpaceMap h hαinv hα)
            (contMDiff_magneticReducedSpaceMap (h := h) hreg hn d) (twistedSymplecticForm β)) =
        SmoothForm.mpullback Subtype.val
          (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (symplecticForm I Q) := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.levelSubMulActionChartedSpace ν hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  intro β hβ
  refine (SmoothForm.mpullback_mpullback _ _ _
    (contMDiff_magneticReducedSpaceMap (h := h) hreg hn d) _).trans ?_
  rw [twistedSymplecticForm_def]
  -- The descended map composed with the orbit projection is the magnetic reduction map on the
  -- level.
  convert ProperSMul.mpullback_magneticReductionMap_comp_symplecticForm_add_mpullback_quotientMk
    hα hβ (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    fun z ↦ h.mem_levelSubMulAction.1 z.property using 3
  exact funext magneticReducedSpaceMap_mk

/-- The descended magnetic reduction map pulls the twisted form `ω + π^* β` of `T*(Q ⧸ G)` back to
every form `η` on the reduced space with `π^* η = i^* ω`, that is to the reduced symplectic form. -/
private theorem mpullback_magneticReducedSpaceMap_twistedSymplecticForm :
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
          SmoothForm.mpullback (magneticReducedSpaceMap h hαinv hα)
              (contMDiff_magneticReducedSpaceMap (h := h) hreg hn d) (twistedSymplecticForm β) =
            η := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.levelSubMulActionChartedSpace ν hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  have hp := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  intro β hβ η hη
  exact SmoothForm.mpullback_injective_of_surjective hp.contMDiff Quotient.mk_surjective
    (hp.surjective_mfderiv (by simp))
    ((mpullback_quotientMk_mpullback_magneticReducedSpaceMap_twistedSymplecticForm (h := h) hreg
      hn d hβ).trans hη.symm)

/-- The descended magnetic reduction map has injective differential, since it pulls the
nondegenerate twisted form back to the nondegenerate reduced form, and the two sides have the same
dimension `2 (dim Q - dim G)`, so it is a local diffeomorphism. -/
private theorem isLocalDiffeomorph_magneticReducedSpaceMap :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    IsLocalDiffeomorph 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
      (𝓘(ℝ, ProperSMul.QuotientModelSpace EG E).prod
        𝓘(ℝ, ProperSMul.QuotientModelSpace EG E →L[ℝ] ℝ)) ∞
      (magneticReducedSpaceMap h hαinv hα) := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.levelSubMulActionChartedSpace ν hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  have hΦ := contMDiff_magneticReducedSpaceMap (h := h) (hαinv := hαinv) (hα := hα) hreg hn d
  -- The magnetic term `β` with `ρ^* β = dα`, and the reduced symplectic form `η`.
  obtain ⟨β, hβ, -⟩ := ProperSMul.existsUnique_mpullback_quotientMk_eq_mextDerivₗ hαinv
    (c := -ν) hα
  obtain ⟨η, ⟨hηs, hη⟩, -⟩ := h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg
    hn d isSymplectic_symplecticForm mpullback_smul_symplecticForm
  have hΦη := mpullback_magneticReducedSpaceMap_twistedSymplecticForm (h := h) (hαinv := hαinv)
    (hα := hα) hreg hn d hβ η hη
  intro x
  induction x using Quotient.inductionOn with | h z => ?_
  have : Nonempty Q := ⟨(z : CotangentBundle I Q).proj⟩
  -- A map pulling a nondegenerate form back to a nondegenerate form has injective differential.
  have hinj := (((isNondegenerate_twistedSymplecticForm β).isNondegenerate_mpullback_iff hΦ).1
    (hΦη ▸ hηs.isNondegenerate)).2 (Quotient.mk _ z)
  -- The invariant one-form `α` makes `ν` coadjoint-fixed: every one-parameter subgroup fixes `ν`,
  -- so every element of `𝔤` annihilates it, which fixes the dimension.
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have hν : lieAnnihilator ℝ (GroupLieAlgebra IG G) ν = ⊤ :=
    eq_top_iff.2 fun ξ _ ↦ Lie.mulInvariantExp_smul_mem_stabilizer_coadjointRepresentation_iff.1
      fun _ ↦ Representation.mem_stabilizer.2
        (coadjointRepresentation_apply_eq_self (hαinv := hαinv) (hα := hα) _)
  exact isLocalDiffeomorphAt_of_injective_mfderiv hΦ.contMDiffOn isOpen_univ (Set.mem_univ _)
    BoundarylessManifold.isInteriorPoint (by simp) hinj
    ((finrank_quotientModelSpace_level hν hn d).trans
      ProperSMul.finrank_quotientModelSpace_prod_dual.symm)

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
  haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  letI := h.orbitRelQuotientChartedSpace ν hreg hn d
  letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  (isLocalDiffeomorph_magneticReducedSpaceMap (h := h) (hαinv := hαinv) (hα := hα) hreg hn
    d).diffeomorphOfBijective (bijective_magneticReducedSpaceMap (hαinv := hαinv) (hα := hα))

/-- **The diffeomorphism of magnetic cotangent reduction sends the orbit of a covector in `μ⁻¹(ν)`
to its magnetic reduced covector**: the unique covector `p'` at `[q]` with `p + α_q = p' ∘ dρ_q`. -/
@[simp]
theorem magneticReducedSpaceDiffeomorph_mk (z : h.levelSubMulAction ν) :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d (Quotient.mk _ z) =
      magneticReductionMap I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
        (Quotient.mk (MulAction.orbitRel G Q)) α (z : CotangentBundle I Q) := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  rw [magneticReducedSpaceDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective,
    magneticReducedSpaceMap_mk]

private theorem coe_magneticReducedSpaceDiffeomorph :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    ⇑(magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d) =
      magneticReducedSpaceMap h hαinv hα := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.orbitRelQuotientChartedSpace ν hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  rw [magneticReducedSpaceDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective]

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
  intro β hβ η hη
  convert mpullback_magneticReducedSpaceMap_twistedSymplecticForm (h := h) hreg hn d hβ η hη
    using 3
  exact coe_magneticReducedSpaceDiffeomorph (h := h) hreg hn d

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

/-! ### The zero value -/

section Zero

variable [ProperSMul G Q] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ}
  {hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g)
    (0 : SmoothForm I Q ℝ 1) = 0}
  {hα : ∀ x ξ, (0 : SmoothForm I Q ℝ 1).val x ![fundamentalVectorField I ξ x] =
    -(0 : Module.Dual ℝ (GroupLieAlgebra IG G)) ξ}
  (hreg : ∀ z, momentMap IG G z = 0 → Surjective (h.differential z))
  (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
  (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0) F)

/-- **Magnetic reduction at zero is cotangent reduction at zero.** For the one-form `α = 0` and the
value `ν = 0`, the diffeomorphism of magnetic cotangent reduction is the diffeomorphism
`μ⁻¹(0) / G_0 ≅ T*(Q ⧸ G)` of cotangent reduction at zero. -/
theorem magneticReducedSpaceDiffeomorph_zero :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d =
      zeroReducedSpaceDiffeomorph h hreg hn d := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  refine Diffeomorph.ext fun x ↦ ?_
  induction x using Quotient.inductionOn with | h z => ?_
  rw [magneticReducedSpaceDiffeomorph_mk, zeroReducedSpaceDiffeomorph_mk, magneticReductionMap_zero]

end Zero

end TauCeti.CotangentBundle
