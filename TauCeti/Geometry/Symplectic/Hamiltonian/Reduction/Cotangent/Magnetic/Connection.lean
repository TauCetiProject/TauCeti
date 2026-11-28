/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Quotient.Connection
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.Magnetic.ReducedSpace

/-!
# Magnetic cotangent reduction from a principal connection

Let a Lie group `G` act smoothly, freely and properly on a manifold `Q`, with orbit projection
`ρ : Q → Q ⧸ G` and cotangent moment map `⟨μ(q, p), ξ⟩ = p(ξ_Q(q))`
(`TauCeti.CotangentBundle.momentMap`), and let `ν ∈ 𝔤*` be fixed by the coadjoint action.
Magnetic cotangent reduction
(`TauCeti.CotangentBundle.mpullback_magneticReducedSpaceDiffeomorph_twistedSymplecticForm`)
identifies the reduced space `T*Q //_ν G = μ⁻¹(ν) / G_ν` with the cotangent bundle `T*(Q ⧸ G)`
carrying the twisted symplectic form `ω + π^* β`, once a `G`-invariant one-form `α` on `Q` with
`α(ξ_Q) = -ν(ξ)` is given; the magnetic term `β` is the two-form on `Q ⧸ G` with `ρ^* β = dα`.

This file produces `α` from a principal connection. The orbit projection is a smooth principal
`G`-bundle for the right action `x · g = g⁻¹ • x` (`ProperSMul.principalBundle_orbitRelFiber`), and
a connection form `A` of it, read on `Q` (`ProperSMul.orbitConnectionForm`), satisfies
`A_Q(ξ_Q) = -ξ` and `(g • ·)^* A_Q = Ad(g) ∘ A_Q`. So the pairing `α = ⟨ν, A_Q⟩` has
`α(ξ_Q) = -ν(ξ)` and, as `ν` is coadjoint-fixed, it is `G`-invariant
(`ProperSMul.mapCoeff_orbitConnectionForm_apply_fundamentalVectorField`,
`ProperSMul.mpullback_smul_mapCoeff_orbitConnectionForm`). Passing these two facts to
`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph` gives magnetic cotangent reduction for
the connection `A`, with magnetic term the two-form `β` on `Q ⧸ G` with `ρ^* β = d⟨ν, A_Q⟩`. A
coadjoint-fixed `ν` annihilates the brackets `⁅ξ, η⁆`, so `d⟨ν, A_Q⟩` is also the `ν`-component of
the curvature `dA + ½ ⁅A ∧ A⁆` of `A`, read on `Q`.

Since every principal bundle over a Hausdorff σ-compact base has a connection form
(`TauCeti.PrincipalBundle.exists_isConnectionForm`), this gives **magnetic cotangent reduction at
every coadjoint-fixed value**: for a σ-compact `Q`, the reduced space `T*Q //_ν G` is
symplectomorphic to `(T*(Q ⧸ G), ω + π^* β)` for a closed two-form `β` on `Q ⧸ G`
(`TauCeti.CotangentBundle.exists_isClosed_and_exists_mpullback_twistedSymplecticForm_eq`), with
no one-form `α` supplied. Changing the connection changes `β` by an exact form and the
diffeomorphism by a fibre translation
(`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph_eq_vectorBundleTranslateDiffeomorph`,
applied to the pairings of the two connection forms).

## Main result

* `TauCeti.CotangentBundle.exists_isClosed_and_exists_mpullback_twistedSymplecticForm_eq`:
  magnetic cotangent reduction at every coadjoint-fixed value of a free proper action on a
  σ-compact manifold.

## References

* Juan-Pablo Ortega and Tudor S. Ratiu, *Cotangent bundle reduction*, in *Encyclopedia of
  Mathematical Physics*, Elsevier, 2006 (the embedding version of cotangent reduction, with the
  magnetic term of a principal connection).
* Jerrold E. Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor S. Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, §2.2.
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
  [ContMDiffSMul IG I ∞ G Q] [ContMDiffConstSMul I ∞ G Q] [IsCancelSMul G Q] [ProperSMul G Q]
  {h : (symplecticForm I Q).IsEquivariantMomentMap (momentMap IG G)}
  {ν : Module.Dual ℝ (GroupLieAlgebra IG G)} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}

variable (hreg : ∀ z, momentMap IG G z = ν → Surjective (h.differential z))
  (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
  (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν) F)

/-- **Magnetic cotangent reduction at every coadjoint-fixed value.** Let a Lie group `G` act
smoothly, freely and properly on a σ-compact manifold `Q`, and let `ν ∈ 𝔤*` be fixed by the
coadjoint action. Then the reduced space `T*Q //_ν G = μ⁻¹(ν) / G_ν`, with the atlas and the
reduced symplectic form `η` of the Marsden–Weinstein–Meyer theorem, is symplectomorphic to the
cotangent bundle `T*(Q ⧸ G)` with the twisted symplectic form `ω + π^* β` of some closed two-form
`β` on `Q ⧸ G`.

The two-form `β` is the magnetic term of a principal connection: for a connection form `A` of the
bundle of orbits, which exists by `TauCeti.PrincipalBundle.exists_isConnectionForm`, it is the form
with `ρ^* β = d⟨ν, A_Q⟩`, and the diffeomorphism is
`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph` for the one-form `⟨ν, A_Q⟩`. -/
theorem exists_isClosed_and_exists_mpullback_twistedSymplecticForm_eq [SigmaCompactSpace Q]
    (hν : ∀ g : G, Lie.coadjointRepresentation ℝ IG G g ν = ν) :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.levelSubMulActionChartedSpace ν hreg hn
    letI := h.orbitRelQuotientChartedSpace ν hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν)
          (h.levelSubMulAction ν)),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (symplecticForm I Q) →
        ∃ β : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
            (MulAction.orbitRel.Quotient G Q), β.IsClosed ∧
          ∃ Φ : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν)
                (h.levelSubMulAction ν) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
                𝓘(ℝ, ProperSMul.QuotientModelSpace EG E).prod
                  𝓘(ℝ, ProperSMul.QuotientModelSpace EG E →L[ℝ] ℝ)⟯
              CotangentBundle 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
                (MulAction.orbitRel.Quotient G Q),
            SmoothForm.mpullback Φ Φ.contMDiff (twistedSymplecticForm β) = η := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  let _ := ProperSMul.orbitRelFiberBundle IG G I Q
  have := ProperSMul.contMDiffFiberBundle_orbitRelFiber (I := IG) (G := G) (I' := I) (M := Q)
  have := ProperSMul.principalBundle_orbitRelFiber (I := IG) (G := G) (I' := I) (M := Q)
  -- The orbit space is Hausdorff and σ-compact, so the bundle of orbits has a connection form.
  have : SigmaCompactSpace (MulAction.orbitRel.Quotient G Q) :=
    isSigmaCompact_univ_iff.1 (Quotient.mk_surjective.range_eq ▸
      isSigmaCompact_range continuous_quotient_mk')
  obtain ⟨A, hA⟩ := PrincipalBundle.exists_isConnectionForm (B := MulAction.orbitRel.Quotient G Q)
    (G := G) (IB := 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)) (IG := IG) (P := orbitRelFiber G Q)
  have hαinv g := ProperSMul.mpullback_smul_mapCoeff_orbitConnectionForm hA (hν g)
  have hα := ProperSMul.mapCoeff_orbitConnectionForm_apply_fundamentalVectorField hA ν
  -- The magnetic term `β` of `A`, with `ρ^* β = d⟨ν, A_Q⟩`.
  obtain ⟨β, hβ, -⟩ := ProperSMul.existsUnique_mpullback_quotientMk_eq_mextDerivₗ hαinv
    (c := -ν) hα
  intro η hη
  exact ⟨β, ProperSMul.isClosed_of_mpullback_quotientMk_eq_mextDerivₗ hβ,
    magneticReducedSpaceDiffeomorph h hαinv hα hreg hn d,
    mpullback_magneticReducedSpaceDiffeomorph_twistedSymplecticForm hreg hn d hβ η hη⟩

end TauCeti.CotangentBundle
